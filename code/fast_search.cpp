#include <algorithm>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <cstring>
#include <fstream>
#include <iostream>
#include <string>
#include <thread>
#include <vector>

// Fast, exact verifier for Conjecture 1 using ONLY forward BBWT and forward rho.
// Compiles with: clang++ -O3 -std=c++17 -pthread fast_search.cpp -o fast_search_bin

struct Task {
    int sigma;
    int n;
    uint32_t size;
    std::vector<int> p;
};

struct Result {
    int sigma;
    int n;
    uint32_t expected;
    uint32_t orbit;
    uint32_t max_depth;
    std::vector<int> p;
};

// Overflow-free multinomial ranking in [0, |S(p)| - 1].
// Since |S(p)| <= 200,000 and c_i <= n < 500, M * c_i <= 10^8 fits easily in uint64_t.
static inline uint32_t rank_ptr(const uint8_t* s, int n, int sigma,
                                const std::vector<int>& p, uint32_t total_mult) {
    int rem[6];
    for (int i = 0; i < sigma; ++i) rem[i] = p[i];
    uint64_t M = total_mult;
    uint32_t r = 0;
    int L = n;
    for (int pos = 0; pos < n; ++pos) {
        int ch = s[pos];
        for (int a = 0; a < ch; ++a) {
            if (rem[a] > 0) {
                r += static_cast<uint32_t>((M * static_cast<uint64_t>(rem[a])) / static_cast<uint64_t>(L));
            }
        }
        M = (M * static_cast<uint64_t>(rem[ch])) / static_cast<uint64_t>(L);
        --rem[ch];
        --L;
    }
    return r;
}

static inline void unrank_string(uint32_t r, int sigma, int n, const std::vector<int>& p,
                                 uint32_t total_mult, std::vector<uint8_t>& out) {
    int rem[6];
    for (int i = 0; i < sigma; ++i) rem[i] = p[i];
    uint64_t M = total_mult;
    int L = n;
    out.resize(n);
    for (int pos = 0; pos < n; ++pos) {
        for (int a = 0; a < sigma; ++a) {
            if (rem[a] == 0) continue;
            uint32_t cnt = static_cast<uint32_t>((M * static_cast<uint64_t>(rem[a])) / static_cast<uint64_t>(L));
            if (r < cnt) {
                out[pos] = static_cast<uint8_t>(a);
                M = cnt;
                --rem[a];
                --L;
                break;
            }
            r -= cnt;
        }
    }
}

struct RotRef {
    uint16_t buf_pos;
    uint16_t len;
    uint8_t last_ch;
};

struct Scratch {
    std::vector<uint8_t> cur;
    std::vector<uint8_t> nxt;
    std::vector<uint8_t> doubled;
    std::vector<uint8_t> rot_buf;
    std::vector<RotRef> rots;
    std::vector<uint8_t> visited;
    std::vector<uint32_t> queue;
    std::vector<uint32_t> depth;
};

static inline void compute_bbwt(const std::vector<uint8_t>& s, Scratch& sc) {
    int n = static_cast<int>(s.size());
    sc.rots.clear();
    sc.rots.reserve(n);
    sc.doubled.clear();
    sc.doubled.reserve(2 * n);

    // Duval's algorithm for Lyndon factorization + doubled-factor buffer
    int i = 0;
    while (i < n) {
        int j = i + 1;
        int k = i;
        while (j < n && s[k] <= s[j]) {
            if (s[k] < s[j]) {
                k = i;
            } else {
                ++k;
            }
            ++j;
        }
        int step = j - k;
        while (i <= k) {
            uint16_t base = static_cast<uint16_t>(sc.doubled.size());
            sc.doubled.insert(sc.doubled.end(), s.begin() + i, s.begin() + i + step);
            sc.doubled.insert(sc.doubled.end(), s.begin() + i, s.begin() + i + step);
            for (int r = 0; r < step; ++r) {
                int last_off = (r == 0) ? (step - 1) : (r - 1);
                sc.rots.push_back(RotRef{
                    static_cast<uint16_t>(base + r),
                    static_cast<uint16_t>(step),
                    s[i + last_off]
                });
            }
            i += step;
        }
    }

    const uint8_t* dptr = sc.doubled.data();
    auto omega_less = [dptr](const RotRef& a, const RotRef& b) -> bool {
        const uint8_t* pa = dptr + a.buf_pos;
        const uint8_t* pb = dptr + b.buf_pos;
        int la = a.len;
        int lb = b.len;
        if (la == lb) {
            return std::memcmp(pa, pb, la) < 0;
        }
        if (la < lb) {
            int c1 = std::memcmp(pa, pb, la);
            if (c1 != 0) return c1 < 0;
            int c2 = std::memcmp(pb, pb + la, lb - la);
            if (c2 != 0) return c2 < 0;
            return std::memcmp(pb + lb - la, pa, la) < 0;
        } else {
            int c1 = std::memcmp(pa, pb, lb);
            if (c1 != 0) return c1 < 0;
            int c2 = std::memcmp(pa + lb, pa, la - lb);
            if (c2 != 0) return c2 < 0;
            return std::memcmp(pb, pa + la - lb, lb) < 0;
        }
    };

    std::stable_sort(sc.rots.begin(), sc.rots.end(), omega_less);
    sc.nxt.resize(n);
    for (int idx = 0; idx < n; ++idx) {
        sc.nxt[idx] = sc.rots[idx].last_ch;
    }
}

static Result verify_task(const Task& t, Scratch& sc) {
    uint32_t sz = t.size;
    int n = t.n;
    int sigma = t.sigma;
    sc.visited.assign(sz, 0);
    sc.queue.clear();
    sc.queue.reserve(sz);
    bool track_depth = (sz <= 10000);

    if (track_depth) {
        sc.depth.assign(sz, 0);
        sc.visited[0] = 1;
        sc.queue.push_back(0);
        uint32_t head = 0;
        uint32_t max_d = 0;
        while (head < sc.queue.size()) {
            uint32_t u_rank = sc.queue[head++];
            uint32_t d = sc.depth[u_rank];
            if (d > max_d) max_d = d;
            unrank_string(u_rank, sigma, n, t.p, sz, sc.cur);

            // 1. Forward rho (left cyclic shift by 1)
            sc.nxt.resize(n);
            for (int i = 0; i < n - 1; ++i) sc.nxt[i] = sc.cur[i + 1];
            sc.nxt[n - 1] = sc.cur[0];
            uint32_t r_rho = rank_ptr(sc.nxt.data(), n, sigma, t.p, sz);
            if (!sc.visited[r_rho]) {
                sc.visited[r_rho] = 1;
                sc.queue.push_back(r_rho);
                sc.depth[r_rho] = d + 1;
            }

            // 2. Forward BBWT
            compute_bbwt(sc.cur, sc);
            uint32_t r_bbwt = rank_ptr(sc.nxt.data(), n, sigma, t.p, sz);
            if (!sc.visited[r_bbwt]) {
                sc.visited[r_bbwt] = 1;
                sc.queue.push_back(r_bbwt);
                sc.depth[r_bbwt] = d + 1;
            }
        }
        return Result{sigma, n, sz, static_cast<uint32_t>(sc.queue.size()), max_d, t.p};
    }

    // Fast path for sz > 10,000: immediate forward rho-cycle walk on every discovered string
    uint32_t total_visited = 0;
    auto add_with_rho_cycle = [&](const std::vector<uint8_t>& str) {
        uint32_t r0 = rank_ptr(str.data(), n, sigma, t.p, sz);
        if (sc.visited[r0]) return;
        sc.visited[r0] = 1;
        sc.queue.push_back(r0);
        ++total_visited;
        if (total_visited == sz) return;

        sc.rot_buf.resize(2 * n);
        std::memcpy(sc.rot_buf.data(), str.data(), n);
        std::memcpy(sc.rot_buf.data() + n, str.data(), n);
        for (int off = 1; off < n; ++off) {
            uint32_t r_rot = rank_ptr(sc.rot_buf.data() + off, n, sigma, t.p, sz);
            if (sc.visited[r_rot]) break;
            sc.visited[r_rot] = 1;
            sc.queue.push_back(r_rot);
            ++total_visited;
            if (total_visited == sz) break;
        }
    };

    unrank_string(0, sigma, n, t.p, sz, sc.cur);
    add_with_rho_cycle(sc.cur);

    while (!sc.queue.empty() && total_visited < sz) {
        uint32_t u_rank = sc.queue.back();
        sc.queue.pop_back();
        unrank_string(u_rank, sigma, n, t.p, sz, sc.cur);
        compute_bbwt(sc.cur, sc);
        add_with_rho_cycle(sc.nxt);
    }

    return Result{sigma, n, sz, total_visited, 0, t.p};
}

static void generate_tasks(int sigma, uint32_t max_S, std::vector<Task>& out) {
    std::vector<int> cur(sigma, 0);
    auto dfs = [&](auto& self, int idx, int cur_n, uint64_t cur_mult) -> void {
        if (idx == sigma) {
            out.push_back(Task{sigma, cur_n, static_cast<uint32_t>(cur_mult), cur});
            return;
        }
        int c = 1;
        while (true) {
            uint64_t m = cur_mult;
            bool ok = true;
            for (int t = 1; t <= c; ++t) {
                m = (m * static_cast<uint64_t>(cur_n + t)) / static_cast<uint64_t>(t);
                if (m > max_S) {
                    ok = false;
                    break;
                }
            }
            if (!ok) break;
            int rem = sigma - 1 - idx;
            uint64_t min_final = m;
            for (int r = 1; r <= rem; ++r) {
                min_final *= static_cast<uint64_t>(cur_n + c + r);
                if (min_final > max_S) {
                    ok = false;
                    break;
                }
            }
            if (!ok) break;
            cur[idx] = c;
            self(self, idx + 1, cur_n + c, m);
            ++c;
        }
    };
    dfs(dfs, 0, 0, 1);
}

int main(int argc, char** argv) {
    uint32_t max_S = 200000;
    int max_sigma = 5;
    std::string out_tsv = "exhaustive_search_raw.tsv";
    if (argc >= 2) max_S = static_cast<uint32_t>(std::stoul(argv[1]));
    if (argc >= 3) max_sigma = std::stoi(argv[2]);
    if (argc >= 4) out_tsv = argv[3];

    auto t0 = std::chrono::steady_clock::now();
    std::vector<Task> tasks;
    for (int sigma = 3; sigma <= max_sigma; ++sigma) {
        generate_tasks(sigma, max_S, tasks);
    }
    std::vector<size_t> order(tasks.size());
    for (size_t i = 0; i < tasks.size(); ++i) order[i] = i;
    std::sort(order.begin(), order.end(), [&](size_t a, size_t b) {
        return tasks[a].size > tasks[b].size;
    });

    std::vector<Result> results(tasks.size());
    std::atomic<size_t> next_idx{0};
    unsigned nthreads = std::thread::hardware_concurrency();
    if (nthreads == 0) nthreads = 8;

    std::vector<std::thread> workers;
    workers.reserve(nthreads);
    for (unsigned tid = 0; tid < nthreads; ++tid) {
        workers.emplace_back([&]() {
            Scratch sc;
            while (true) {
                size_t k = next_idx.fetch_add(1, std::memory_order_relaxed);
                if (k >= order.size()) break;
                size_t idx = order[k];
                results[idx] = verify_task(tasks[idx], sc);
            }
        });
    }
    for (auto& w : workers) w.join();

    auto t1 = std::chrono::steady_clock::now();
    double secs = std::chrono::duration<double>(t1 - t0).count();

    std::ofstream ofs(out_tsv);
    ofs << "sigma\tn\texpected\torbit\tmax_depth\tp\n";
    uint64_t bad = 0;
    for (const auto& r : results) {
        if (r.orbit != r.expected) ++bad;
        ofs << r.sigma << "\t" << r.n << "\t" << r.expected << "\t"
            << r.orbit << "\t" << r.max_depth << "\t";
        for (size_t i = 0; i < r.p.size(); ++i) {
            if (i) ofs << ",";
            ofs << r.p[i];
        }
        ofs << "\n";
    }
    ofs.close();

    std::cout << "Completed " << tasks.size() << " Parikh vectors (max_S=" << max_S
              << ", sigma=3.." << max_sigma << ") in " << secs << "s on "
              << nthreads << " threads. Counterexamples found: " << bad << "\n";
    return bad == 0 ? 0 : 1;
}
