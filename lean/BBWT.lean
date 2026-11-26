import Std

namespace BBWT

inductive Letter where
  | a | b | c
  deriving DecidableEq, Repr

open Letter
abbrev Word := List Letter

/-- The positions of all occurrences of a letter, in original order. -/
def positions (letter : Letter) (offset : Nat) : Word → List Nat
  | [] => []
  | x :: xs =>
    if x = letter then offset :: positions letter (offset + 1) xs
    else positions letter (offset + 1) xs

def stableRows (last : Word) : List Nat :=
  positions a 0 last ++ positions b 0 last ++ positions c 0 last

/-- Zero-based stable LF-inverse. The value outside the valid rows is unused. -/
def psi (last : Word) (j : Nat) : Nat :=
  (stableRows last)[j]?.getD 0

def first (last : Word) : Word :=
  List.replicate (positions a 0 last).length a ++
  List.replicate (positions b 0 last).length b ++
  List.replicate (positions c 0 last).length c

theorem positions_append (letter : Letter) (offset : Nat) (u v : Word) :
    positions letter offset (u ++ v) =
      positions letter offset u ++ positions letter (offset + u.length) v := by
  induction u generalizing offset with
  | nil => simp [positions]
  | cons x xs ih =>
    simp only [List.cons_append, positions, List.length_cons]
    by_cases h : x = letter <;> simp [h, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem positions_run (letter x : Letter) (offset length : Nat) :
    positions letter offset (List.replicate length x) =
      if x = letter then List.range' offset length else [] := by
  induction length generalizing offset with
  | zero => simp [positions]
  | succ k ih =>
    rw [List.replicate_succ]
    by_cases h : x = letter
    · subst x
      simp [positions, ih, List.range'_succ]
    · simp [positions, h, ih]

def run (x : Letter) (n : Nat) : Word := List.replicate n x

@[simp] theorem run_len (x : Letter) (n : Nat) : (run x n).length = n := by simp [run]

@[simp] theorem positions_run' (letter x : Letter) (s n : Nat) :
    positions letter s (run x n) =
      if x = letter then List.range' s n else [] :=
  positions_run letter x s n

def transferIn (A E R : Nat) : Word :=
  run a (A+1) ++ run b (E+1) ++ [c] ++ run b (R+1)

def transferLast (A E R : Nat) : Word :=
  [b] ++ run a A ++ run b R ++ [c,a] ++ run b (E+1)

def transferRot (A E R : Nat) : Word :=
  run a A ++ run b R ++ [c,a] ++ run b (E+2)

def transferOut (A E R : Nat) : Word :=
  [a] ++ run b (E+2) ++ [c] ++ run b R ++ run a A

def rotLeft (w : Word) : Word := w.drop 1 ++ w.take 1

theorem rot_transfer (A E R : Nat) :
    rotLeft (transferLast A E R) = transferRot A E R := by
  simp [rotLeft, transferLast, transferRot, run, List.replicate_succ, List.append_assoc,
    ← List.replicate_succ']

/-- Zero-based index map of the rotated last column in Theorem 3(c). -/
def transferPsi (A E R j : Nat) : Nat :=
  if j < A then j
  else if j = A then A+R+1
  else if j < A+R+1 then j-1
  else if j < A+E+R+3 then j+1
  else A+R

theorem rangeGet (s k i : Nat) :
      (List.range' s k)[i]? = if i < k then some (s+i) else none := by
  by_cases hi : i < k
  · rw [if_pos hi, List.getElem?_range' hi, Nat.one_mul]
  · rw [if_neg hi, List.getElem?_eq_none]
    simpa using hi

theorem psi_transferRot (A E R j : Nat) (hj : j < A+E+R+4) :
    psi (transferRot A E R) j = transferPsi A E R j := by
  simp only [psi, stableRows, transferRot, positions_append, positions_run',
    run_len, positions, List.length_cons, List.length_nil]
  simp (config := { decide := true }) only [reduceCtorEq, if_true, if_false,
    List.nil_append, List.append_nil, Nat.zero_add, Nat.add_zero, Nat.reduceAdd]
  simp only [transferPsi, List.getElem?_append, List.length_append, List.length_range',
    List.length_cons, List.length_nil, run_len]
  simp only [rangeGet, List.getElem?_cons, List.getElem?_nil]
  repeat' first | split | simp only [Option.getD_some, Option.getD_none]
  all_goals omega

/-- A row-by-row trace follows the given map and finishes at the stop row. -/
def Reads (step : Nat → Nat) (stop : Nat) (start : Nat) : List Nat → Prop
  | [] => start = stop
  | j :: js => start = j ∧ Reads step stop (step j) js

theorem reads_append {step : Nat → Nat} {start mid stop : Nat} {u v : List Nat} :
    Reads step mid start u → Reads step stop mid v → Reads step stop start (u ++ v) := by
  induction u generalizing start with
  | nil => intro h₁ h₂; simp only [Reads, List.nil_append] at *; rwa [h₁]
  | cons j js ih =>
    intro h₁ h₂
    exact ⟨h₁.1, ih h₁.2 h₂⟩

theorem reads_up {step : Nat → Nat} (s k : Nat)
    (h : ∀ j, s ≤ j → j < s+k → step j = j+1) :
    Reads step (s+k) s (List.range' s k) := by
  induction k generalizing s with
  | zero => simp [Reads]
  | succ k ih =>
    rw [List.range'_succ]
    constructor
    · rfl
    · have ht := h s (by omega) (by omega)
      rw [ht]
      have hh := ih (s+1) (fun j l u => h j (by omega) (by omega))
      rwa [show s+1+k = s+(k+1) by omega] at hh

/-- k decreasing rows, ending just above s-k. -/
def down (s : Nat) : Nat → List Nat
  | 0 => []
  | k+1 => s :: down (s-1) k

theorem reads_down {step : Nat → Nat} (s k : Nat) (hk : k ≤ s)
    (h : ∀ j, s-k < j → j ≤ s → step j = j-1) :
    Reads step (s-k) s (down s k) := by
  induction k generalizing s with
  | zero => simp [down, Reads]
  | succ k ih =>
    simp only [down, Reads, true_and]
    rw [h s (by omega) (by omega)]
    have hh := ih (s-1) (by omega) (fun j l u => h j (by omega) (by omega))
    rwa [show s-1-k = s-(k+1) by omega] at hh

theorem mem_down {s k j : Nat} (hk : k ≤ s) :
    j ∈ down s k ↔ s-k < j ∧ j ≤ s := by
  induction k generalizing s with
  | zero => simp [down]
  | succ k ih =>
    rw [down, List.mem_cons, ih (by omega)]
    omega

/-- The nontrivial cycle in the rotated inverse calculation, starting at row A. -/
def transferCycle (A E R : Nat) : List Nat :=
  [A] ++ List.range' (A+R+1) (E+2) ++ [A+E+R+3] ++ down (A+R) R

theorem transfer_cycle_trace (A E R : Nat) :
    Reads (psi (transferRot A E R)) A A (transferCycle A E R) := by
  let step := psi (transferRot A E R)
  have hStart : Reads step (A+R+1) A [A] := by
    simp [Reads, step, psi_transferRot A E R A (by omega), transferPsi]
  have hUp : Reads step (A+E+R+3) (A+R+1) (List.range' (A+R+1) (E+2)) := by
    rw [show A+E+R+3 = A+R+1+(E+2) by omega]
    apply reads_up
    intro j lo hi
    rw [show step j = transferPsi A E R j from psi_transferRot A E R j (by omega)]
    simp [transferPsi, show ¬j < A by omega, show j ≠ A by omega,
      show ¬j < A+R+1 by omega, show j < A+E+R+3 by omega]
  have hTop : Reads step (A+R) (A+E+R+3) [A+E+R+3] := by
    simp [Reads]
    rw [show step (A+E+R+3) = transferPsi A E R (A+E+R+3) from
      psi_transferRot A E R _ (by omega)]
    simp [transferPsi, show ¬ A+E+R+3 < A by omega,
      show A+E+R+3 ≠ A by omega, show ¬ A+E+R+3 < A+R+1 by omega]
  have hDown : Reads step A (A+R) (down (A+R) R) := by
    have hd : Reads step (A+R-R) (A+R) (down (A+R) R) := by
      apply reads_down _ _ (by omega)
      intro j lo hi
      rw [show step j = transferPsi A E R j from psi_transferRot A E R j (by omega)]
      simp [transferPsi, show ¬j < A by omega, show j ≠ A by omega,
        show j < A+R+1 by omega]
    simpa using hd
  exact reads_append (reads_append (reads_append hStart hUp) hTop) hDown

theorem transfer_fixed (A E R j : Nat) (hj : j < A) :
    psi (transferRot A E R) j = j := by
  simp [psi_transferRot A E R j (by omega), transferPsi, hj]


/-- A nonempty closed cycle, written with its strictly smallest row first. -/
def CanonicalCycle (step : Nat → Nat) : List Nat → Prop
  | [] => False
  | j :: js => Reads step j j (j :: js) ∧ ∀ i ∈ js, j < i

def leader (rows : List Nat) : Nat := rows.headD 0

/-- Cycle decoding with the scan convention in the paper.
Cycles cover exactly the valid row indices, start at their minima, and are
listed in decreasing order of these minima (reverse scan order). -/
def InverseRecipe (last out : Word) : Prop :=
  ∃ cycles : List (List Nat),
    (∀ cycle ∈ cycles, CanonicalCycle (psi last) cycle) ∧
    cycles.Pairwise (fun x y => leader y < leader x) ∧
    (∀ i, i ∈ cycles.flatten ↔ i < last.length) ∧
    out = cycles.flatten.map (fun i => (first last)[i]?.getD a)

theorem mem_up {s k i : Nat} : i ∈ List.range' s k ↔ s ≤ i ∧ i < s+k := by
  rw [List.mem_range']
  constructor
  · rintro ⟨j, hj, rfl⟩
    simp only [Nat.one_mul]
    omega
  · intro h
    exact ⟨i-s, by omega, by simp only [Nat.one_mul]; omega⟩

theorem length_down (s k : Nat) : (down s k).length = k := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih => simp [down, ih]

theorem map_constant {α β : Type} (f : α → β) (l : List α) (v : β)
    (h : ∀ i ∈ l, f i = v) : l.map f = List.replicate l.length v := by
  induction l with
  | nil => rfl
  | cons j js ih =>
    simp only [List.map_cons, List.length_cons, List.replicate_succ]
    rw [h j (by simp), ih (fun i hi => h i (by simp [hi]))]

def singletonCycles (s n : Nat) : List (List Nat) :=
  ((List.range' s n).reverse.map fun i => [i])

theorem fixed_cycles_good {step : Nat → Nat} {s n : Nat}
    (h : ∀ i, s ≤ i → i < s+n → step i = i) :
    ∀ cycle ∈ singletonCycles s n, CanonicalCycle step cycle := by
  intro cycle hc
  simp only [singletonCycles, List.mem_map, List.mem_reverse, mem_up] at hc
  obtain ⟨i, hi, rfl⟩ := hc
  simp [CanonicalCycle, Reads, h i hi.1 hi.2]

theorem fixed_cycles_order (s n : Nat) :
    (singletonCycles s n).Pairwise (fun x y => leader y < leader x) := by
  unfold singletonCycles
  rw [List.pairwise_map, List.pairwise_reverse]
  change (List.range' s n).Pairwise (· < ·)
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [List.range'_succ, List.pairwise_cons]
    exact ⟨fun i hi => by have := mem_up.1 hi; omega, ih _⟩

theorem fixed_cycles_flat (s n : Nat) :
    (singletonCycles s n).flatten = (List.range' s n).reverse := by
  unfold singletonCycles
  generalize (List.range' s n).reverse = xs
  induction xs with
  | nil => rfl
  | cons i is ih => simp [ih]

abbrev rowLetter (last : Word) (i : Nat) : Letter :=
  (first last)[i]?.getD a

def blockLetter (aLen bLen i : Nat) : Letter :=
  if i < aLen then a else if i < aLen+bLen then b else c

theorem row_block {last : Word} {aLen bLen i : Nat}
    (ha : (positions a 0 last).length = aLen)
    (hb : (positions b 0 last).length = bLen)
    (hi : i < aLen+bLen+(positions c 0 last).length) :
    rowLetter last i = blockLetter aLen bLen i := by
  simp only [rowLetter, first, ha, hb, blockLetter, List.getElem?_append, List.length_append,
    List.length_replicate, List.getElem?_replicate]
  repeat' first | split | simp only [Option.getD_some, Option.getD_none]
  all_goals try omega

theorem row_transferRot (A E R i : Nat) (hi : i < A+E+R+4) :
    rowLetter (transferRot A E R) i = blockLetter (A+1) (E+R+2) i := by
  have ha : (positions a 0 (transferRot A E R)).length = A+1 := by
    simp [transferRot, positions_append, positions]
  have hb : (positions b 0 (transferRot A E R)).length = E+R+2 := by
    simp [transferRot, positions_append, positions]
    omega
  have hc : (positions c 0 (transferRot A E R)).length = 1 := by
    simp [transferRot, positions_append, positions]
  exact row_block ha hb (by omega)

theorem transferRot_inverse (A E R : Nat) :
    InverseRecipe (transferRot A E R) (transferOut A E R) := by
  let fixed := singletonCycles 0 A
  let cycle := transferCycle A E R
  have hmem : ∀ i, i ∈ cycle ↔ A ≤ i ∧ i < A+E+R+4 := by
    intro i
    simp only [cycle, transferCycle, List.mem_append, List.mem_singleton, mem_up,
      mem_down (show R ≤ A+R by omega)]
    omega
  have hleader : leader cycle = A := rfl
  have hgood : CanonicalCycle (psi (transferRot A E R)) cycle := by
    refine ⟨transfer_cycle_trace A E R, ?_⟩
    intro i hi
    change i ∈ (List.range' (A+R+1) (E+2) ++ [A+E+R+3]) ++ down (A+R) R at hi
    simp only [List.mem_append, List.mem_singleton, mem_up,
      mem_down (show R ≤ A+R by omega)] at hi
    omega
  refine ⟨cycle :: fixed, ?_, ?_, ?_, ?_⟩
  · intro c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact hgood
    · exact fixed_cycles_good (fun j _ hj => transfer_fixed A E R j (by omega)) c hc
  · rw [List.pairwise_cons]
    refine ⟨?_, fixed_cycles_order 0 A⟩
    intro c hc
    simp only [fixed, singletonCycles, List.mem_map, List.mem_reverse, mem_up] at hc
    obtain ⟨i, hi, rfl⟩ := hc
    simpa [leader, hleader] using hi.2
  · intro i
    simp only [List.flatten_cons, List.mem_append, hmem, fixed, fixed_cycles_flat,
      List.mem_reverse, mem_up, transferRot, List.length_append, run_len,
      List.length_cons, List.length_nil]
    omega
  · let f := rowLetter (transferRot A E R)
    have ff : ∀ i < A+E+R+4, f i = blockLetter (A+1) (E+R+2) i :=
      row_transferRot A E R
    have hUp : (List.range' (A+R+1) (E+2)).map f = run b (E+2) := by
      unfold run
      rw [map_constant f _ b (fun i hi => by
        have := mem_up.1 hi
        rw [ff i (by omega)]
        simp [blockLetter, show ¬i < A+1 by omega, show i < A+1+(E+R+2) by omega])]
      simp
    have hDown : (down (A+R) R).map f = run b R := by
      unfold run
      rw [map_constant f _ b (fun i hi => by
        have := (mem_down (show R ≤ A+R by omega)).1 hi
        rw [ff i (by omega)]
        simp [blockLetter, show ¬i < A+1 by omega, show i < A+1+(E+R+2) by omega])]
      rw [length_down]
    have hFix : (fixed.flatten.map f) = run a A := by
      unfold fixed run
      rw [fixed_cycles_flat, map_constant f _ a (fun i hi => by
        have := mem_up.1 (List.mem_reverse.1 hi)
        rw [ff i (by omega)]
        simp [blockLetter, show i < A+1 by omega])]
      simp
    have ha : f A = a := by rw [ff A (by omega)]; simp [blockLetter]
    have hc : f (A+E+R+3) = c := by
      rw [ff _ (by omega)]
      simp [blockLetter, show ¬ A+E+R+3 < A+1 by omega,
        show ¬ A+E+R+3 < A+1+(E+R+2) by omega]
    change transferOut A E R = (cycle ++ fixed.flatten).map f
    simp [cycle, transferCycle, transferOut, List.map_append, hUp, hDown, hFix,
      ha, hc, List.append_assoc]


def beforePsi (A E R j : Nat) : Nat :=
  if j < A then j+1
  else if j = A then A+R+2
  else if j = A+1 then 0
  else if j < A+R+2 then j-1
  else if j < A+E+R+3 then j+1
  else A+R+1

theorem psi_transferLast (A E R j : Nat) (hj : j < A+E+R+4) :
    psi (transferLast A E R) j = beforePsi A E R j := by
  simp only [psi, stableRows, transferLast, positions_append, positions_run', run_len, positions,
    List.length_cons, List.length_nil]
  simp (config := { decide := true }) only [reduceCtorEq, if_true, if_false,
    List.nil_append, List.append_nil, Nat.zero_add, Nat.add_zero, Nat.reduceAdd]
  simp only [beforePsi, List.getElem?_append, List.length_append, List.length_range',
    List.length_cons, List.length_nil, run_len, rangeGet, List.getElem?_cons, List.getElem?_nil]
  repeat' first | split | simp only [Option.getD_some, Option.getD_none]
  all_goals omega

theorem row_transferLast (A E R i : Nat) (hi : i < A+E+R+4) :
    rowLetter (transferLast A E R) i = blockLetter (A+1) (E+R+2) i := by
  have ha : (positions a 0 (transferLast A E R)).length = A+1 := by
    simp [transferLast, positions_append, positions]
  have hb : (positions b 0 (transferLast A E R)).length = E+R+2 := by
    simp [transferLast, positions_append, positions]
    omega
  have hc : (positions c 0 (transferLast A E R)).length = 1 := by
    simp [transferLast, positions_append, positions]
  exact row_block ha hb (by omega)

theorem map_up {f : Nat → Letter} (s k : Nat) (v : Letter)
    (h : ∀ i, s ≤ i → i < s+k → f i = v) :
    (List.range' s k).map f = run v k := by
  rw [map_constant f _ v (fun i hi => h i (mem_up.1 hi).1 (mem_up.1 hi).2)]
  simp [run]

theorem map_down {f : Nat → Letter} (s k : Nat) (v : Letter) (hk : k ≤ s)
    (h : ∀ i, s-k < i → i ≤ s → f i = v) :
    (down s k).map f = run v k := by
  rw [map_constant f _ v (fun i hi => h i ((mem_down hk).1 hi).1 ((mem_down hk).1 hi).2)]
  simp [run, length_down]

theorem reads_one {step : Nat → Nat} {j stop : Nat} (h : step j = stop) :
    Reads step stop j [j] := ⟨rfl, h⟩

theorem start_up (s k : Nat) : List.range' s (k+1) = s :: List.range' (s+1) k := by
  simp [List.range'_succ]

theorem transferLast_inverse (A E R : Nat) :
    InverseRecipe (transferLast A E R) (transferIn A E R) := by
  let step := psi (transferLast A E R)
  let cycle := (List.range' 0 (A+1) ++ List.range' (A+R+2) (E+1) ++
    [A+E+R+3]) ++ down (A+R+1) (R+1)
  have hs : ∀ j < A+E+R+4, step j = beforePsi A E R j := psi_transferLast A E R
  have hUpA : Reads step A 0 (List.range' 0 A) := by
    simpa only [Nat.zero_add] using (reads_up (step := step) 0 A (by
      intro j _ hj
      rw [hs j (by omega)]
      simp [beforePsi, show j < A by omega]))
  have hJumpA : Reads step (A+R+2) A [A] := by
    apply reads_one
    rw [hs _ (by omega)]
    simp [beforePsi]
  have hUpB : Reads step (A+E+R+3) (A+R+2) (List.range' (A+R+2) (E+1)) := by
    rw [show A+E+R+3 = A+R+2+(E+1) by omega]
    apply reads_up
    intro j lo hi
    rw [hs _ (by omega)]
    simp [beforePsi, show ¬ j < A by omega, show j ≠ A by omega,
      show j ≠ A+1 by omega, show ¬ j < A+R+2 by omega, show j < A+E+R+3 by omega]
  have hJumpC : Reads step (A+R+1) (A+E+R+3) [A+E+R+3] := by
    apply reads_one
    rw [hs _ (by omega)]
    simp [beforePsi, show ¬ A+E+R+3 < A by omega, show A+E+R+3 ≠ A by omega,
      show A+E+R+3 ≠ A+1 by omega, show ¬ A+E+R+3 < A+R+2 by omega]
  have hDownB : Reads step 0 (A+R+1) (down (A+R+1) R ++ [A+1]) := by
    have hd : Reads step (A+1) (A+R+1) (down (A+R+1) R) := by
      have ht := reads_down (step := step) (A+R+1) R (by omega) (by
        intro j lo hi
        rw [hs _ (by omega)]
        simp [beforePsi, show ¬ j < A by omega, show j ≠ A by omega,
          show j ≠ A+1 by omega, show j < A+R+2 by omega])
      rwa [show A+R+1-R = A+1 by omega] at ht
    apply reads_append hd
    apply reads_one
    rw [hs _ (by omega)]
    simp [beforePsi]
  have downSnoc (s k : Nat) (hk : k ≤ s) : down s (k+1) = down s k ++ [s-k] := by
    induction k generalizing s with
    | zero => simp [down]
    | succ k ih =>
      change s :: down (s-1) (k+1) = (s :: down (s-1) k) ++ [s-(k+1)]
      rw [ih (s-1) (by omega), show s-1-k = s-(k+1) by omega]
      rfl
  have hTrace : Reads step 0 0 cycle := by
    unfold cycle
    rw [List.range'_1_concat, downSnoc _ _ (by omega)]
    simp only [Nat.zero_add, show A+R+1-R = A+1 by omega]
    exact reads_append (reads_append (reads_append (reads_append hUpA hJumpA) hUpB) hJumpC) hDownB
  refine ⟨[cycle], ?_, by simp, ?_, ?_⟩
  · intro cs hcs
    simp only [List.mem_singleton] at hcs
    subst cs
    change CanonicalCycle step cycle
    unfold cycle
    rw [start_up]
    refine ⟨hTrace, ?_⟩
    intro i hi
    change i ∈ List.range' 1 A ++ List.range' (A+R+2) (E+1) ++
      [A+E+R+3] ++ down (A+R+1) (R+1) at hi
    simp only [List.mem_append, List.mem_singleton, mem_up,
      mem_down (show R+1 ≤ A+R+1 by omega)] at hi
    omega
  · intro i
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil, cycle, List.mem_append,
      List.mem_singleton, mem_up, mem_down (show R+1 ≤ A+R+1 by omega),
      transferLast, List.length_append, run_len, List.length_cons, List.length_nil]
    omega
  · let f := rowLetter (transferLast A E R)
    have ff := row_transferLast A E R
    have ha : (List.range' 0 (A+1)).map f = run a (A+1) := by
      apply map_up
      intro i _ hi
      rw [show f i = _ from ff i (by omega)]
      simp [blockLetter, show i < A+1 by omega]
    have hb₁ : (List.range' (A+R+2) (E+1)).map f = run b (E+1) := by
      apply map_up
      intro i lo hi
      rw [show f i = _ from ff i (by omega)]
      simp [blockLetter, show ¬ i < A+1 by omega, show i < A+1+(E+R+2) by omega]
    have hb₂ : (down (A+R+1) (R+1)).map f = run b (R+1) := by
      apply map_down _ _ _ (by omega)
      intro i lo hi
      rw [show f i = _ from ff i (by omega)]
      simp [blockLetter, show ¬ i < A+1 by omega, show i < A+1+(E+R+2) by omega]
    have hc : f (A+E+R+3) = c := by
      rw [show f _ = _ from ff _ (by omega)]
      simp [blockLetter, show ¬ A+E+R+3 < A+1 by omega,
        show ¬ A+E+R+3 < A+1+(E+R+2) by omega]
    change transferIn A E R = ([cycle].flatten).map f
    simp [cycle, transferIn, List.map_append, ha, hb₁, hb₂, hc, List.append_assoc]

/-- Exact formal transfer at all positive exponents in the inverse recipe. -/
theorem maximal_singleton_transfer (A E R : Nat) :
    ∃ last, InverseRecipe last (transferIn A E R) ∧
      InverseRecipe (rotLeft last) (transferOut A E R) := by
  refine ⟨transferLast A E R, transferLast_inverse A E R, ?_⟩
  rw [rot_transfer]
  exact transferRot_inverse A E R


/-- A word with one a and one c, with the two possible orders distinguished. -/
def singletonLast (flip : Bool) (u v w : Nat) : Word :=
  run b u ++ [if flip then c else a] ++ run b v ++
    [if flip then a else c] ++ run b w

def singletonPsi (flip : Bool) (u v w j : Nat) : Nat :=
  if j = 0 then (if flip then u+v+1 else u)
  else if j ≤ u then j-1
  else if j ≤ u+v then j
  else if j < u+v+w+1 then j+1
  else if flip then u else u+v+1

theorem psi_singleton (flip : Bool) (u v w j : Nat) (hj : j < u+v+w+2) :
    psi (singletonLast flip u v w) j = singletonPsi flip u v w j := by
  cases flip <;>
    simp only [psi, stableRows, singletonLast, singletonPsi, positions_append,
      positions_run', positions, run_len, List.length_cons, List.length_nil, Bool.false_eq_true,
      if_false, if_true, reduceCtorEq, List.nil_append, List.append_nil, Nat.zero_add,
      Nat.add_zero, Nat.reduceAdd] <;>
    simp only [List.getElem?_append, List.length_append, List.length_range',
      List.length_cons, List.length_nil, run_len, rangeGet, List.getElem?_cons, List.getElem?_nil] <;>
    (repeat' first | split | simp only [Option.getD_some, Option.getD_none]) <;> omega

@[simp] theorem singleton_length (flip : Bool) (u v w : Nat) :
    (singletonLast flip u v w).length = u+v+w+2 := by
  simp [singletonLast]
  omega

theorem row_singleton (flip : Bool) (u v w i : Nat) (hi : i < u+v+w+2) :
    rowLetter (singletonLast flip u v w) i = blockLetter 1 (u+v+w) i := by
  have ha : (positions a 0 (singletonLast flip u v w)).length = 1 := by
    cases flip <;> simp [singletonLast, positions_append, positions]
  have hb : (positions b 0 (singletonLast flip u v w)).length = u+v+w := by
    cases flip <;> simp [singletonLast, positions_append, positions, Nat.add_assoc]
  have hc : (positions c 0 (singletonLast flip u v w)).length = 1 := by
    cases flip <;> simp [singletonLast, positions_append, positions]
  exact row_block ha hb (by omega)

theorem fixed_cycles_mem {s n : Nat} {cs : List Nat}
    (h : cs ∈ singletonCycles s n) : ∃ i, s ≤ i ∧ i < s+n ∧ cs = [i] := by
  simp only [singletonCycles, List.mem_map, List.mem_reverse, mem_up] at h
  obtain ⟨i, ⟨lo, hi⟩, eq⟩ := h
  exact ⟨i, lo, hi, eq.symm⟩

theorem singleton_inverse (flip : Bool) (u v w : Nat) :
    InverseRecipe (singletonLast flip u v w)
      (if flip then run b v ++ [a] ++ run b w ++ [c] ++ run b u
       else run b w ++ [c] ++ run b v ++ [a] ++ run b u) := by
  let step := psi (singletonLast flip u v w)
  let f := rowLetter (singletonLast flip u v w)
  let fixed := singletonCycles (u+1) v
  let bottom := [0] ++ down u u
  let top := List.range' (u+v+1) w ++ [u+v+w+1]
  have hstep : ∀ j < u+v+w+2, step j = singletonPsi flip u v w j :=
    psi_singleton flip u v w
  have hrow : ∀ j < u+v+w+2, f j = blockLetter 1 (u+v+w) j :=
    row_singleton flip u v w
  have hDown : Reads step 0 u (down u u) := by
    simpa using (reads_down (step := step) u u (Nat.le_refl u) (by
      intro j lo hi
      rw [hstep _ (by omega)]
      simp [singletonPsi, show j ≠ 0 by omega, hi]))
  have hUp : Reads step (u+v+w+1) (u+v+1) (List.range' (u+v+1) w) := by
    rw [show u+v+w+1 = u+v+1+w by omega]
    apply reads_up
    intro j lo hi
    rw [hstep _ (by omega)]
    simp [singletonPsi, show j ≠ 0 by omega, show ¬j ≤ u by omega,
      show ¬j ≤ u+v by omega, show j < u+v+w+1 by omega]
  have hFixGood : ∀ cs ∈ fixed, CanonicalCycle step cs :=
    fixed_cycles_good (by
      intro j lo hi
      rw [hstep _ (by omega)]
      simp [singletonPsi, show j ≠ 0 by omega, show ¬j ≤ u by omega, show j ≤ u+v by omega])
  have hFixOrder : fixed.Pairwise (fun x y => leader y < leader x) := fixed_cycles_order _ _
  have hFixMem (i : Nat) : i ∈ fixed.flatten ↔ u+1 ≤ i ∧ i < u+1+v := by
    simp only [fixed, fixed_cycles_flat, List.mem_reverse, mem_up]
  have hBottomMem (i : Nat) : i ∈ bottom ↔ i ≤ u := by
    simp only [bottom, List.mem_append, List.mem_singleton, mem_down (Nat.le_refl u)]
    omega
  have hTopMem (i : Nat) : i ∈ top ↔ u+v+1 ≤ i ∧ i ≤ u+v+w+1 := by
    simp only [top, List.mem_append, List.mem_singleton, mem_up]
    omega
  have hBottomLeader : leader bottom = 0 := rfl
  have hTopLeader : leader top = u+v+1 := by
    cases w <;> simp [top, List.range'_succ, leader, List.headD]
  have ha : f 0 = a := by rw [hrow _ (by omega)]; rfl
  have hc : f (u+v+w+1) = c := by
    rw [hrow _ (by omega)]
    simp [blockLetter, show ¬u+v+w+1 < 1 by omega,
      show ¬u+v+w+1 < 1+(u+v+w) by omega]
  have hB (i : Nat) (lo : 0 < i) (hi : i ≤ u+v+w) : f i = b := by
    rw [hrow _ (by omega)]
    simp [blockLetter, show ¬i < 1 by omega, show i < 1+(u+v+w) by omega]
  have hMapUp : (List.range' (u+v+1) w).map f = run b w :=
    map_up _ _ _ (fun i lo hi => hB i (by omega) (by omega))
  have hMapDown : (down u u).map f = run b u :=
    map_down _ _ _ (Nat.le_refl u) (fun i lo hi => hB i (by omega) (by omega))
  have hMapFixed : fixed.flatten.map f = run b v := by
    rw [map_constant f _ b (fun i hi => by have := (hFixMem i).1 hi; exact hB i (by omega) (by omega))]
    simp [fixed, fixed_cycles_flat, run]
  cases hFlip : flip
  · have hLow : CanonicalCycle step bottom := by
      refine ⟨reads_append (reads_one ?_) hDown, ?_⟩
      · rw [hstep _ (by omega)]; simp [singletonPsi, hFlip]
      · intro i hi
        have := (mem_down (Nat.le_refl u)).1 hi
        omega
    have hHighTrace : Reads step (u+v+1) (u+v+1) top := by
      apply reads_append hUp
      apply reads_one
      rw [hstep _ (by omega)]
      simp [singletonPsi, hFlip, show u+v+w+1 ≠ 0 by omega,
        show ¬u+v+w+1 ≤ u by omega, show ¬u+v+w+1 ≤ u+v by omega]
    have hHigh : CanonicalCycle step top := by
      cases w with
      | zero => exact ⟨hHighTrace, by simp⟩
      | succ k =>
        unfold top
        rw [start_up]
        refine ⟨hHighTrace, ?_⟩
        intro i hi
        change i ∈ List.range' (u+v+1+1) k ++ [u+v+(k+1)+1] at hi
        simp only [List.mem_append, List.mem_singleton, mem_up] at hi
        omega
    refine ⟨top :: (fixed ++ [bottom]), ?_, ?_, ?_, ?_⟩
    · intro cs hcs
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hcs
      rcases hcs with rfl | hm | rfl
      · simpa [step, hFlip] using hHigh
      · simpa [step, hFlip] using hFixGood _ hm
      · simpa [step, hFlip] using hLow
    · rw [List.pairwise_cons, List.pairwise_append]
      refine ⟨?_, hFixOrder, by simp, ?_⟩
      · intro cs hcs
        rw [hTopLeader]
        simp only [List.mem_append, List.mem_singleton] at hcs
        rcases hcs with hm | rfl
        · obtain ⟨i, _, hi, rfl⟩ := fixed_cycles_mem hm
          change i < u+v+1
          omega
        · rw [hBottomLeader]; omega
      · intro cs hcs ds hds
        obtain ⟨i, lo, _, rfl⟩ := fixed_cycles_mem hcs
        simp only [List.mem_singleton] at hds
        subst ds
        rw [hBottomLeader]
        change 0 < i
        omega
    · intro i
      simp only [List.flatten_cons, List.flatten_append, List.flatten_nil, List.append_nil,
        List.mem_append, hTopMem, hFixMem, hBottomMem, singleton_length]
      omega
    · have hout : run b w ++ [c] ++ run b v ++ [a] ++ run b u =
          (top ++ (fixed.flatten ++ bottom)).map f := by
        simp [top, bottom, List.map_append, hMapUp, hMapDown, hMapFixed, ha, hc, List.append_assoc]
      simpa [f, hFlip, List.flatten_append] using hout
  · let main := [0] ++ top ++ down u u
    have hMain : CanonicalCycle step main := by
      have hJump : Reads step (u+v+1) 0 [0] := by
        apply reads_one
        rw [hstep _ (by omega)]
        simp [singletonPsi, hFlip]
      have hReturn : Reads step u (u+v+w+1) [u+v+w+1] := by
        apply reads_one
        rw [hstep _ (by omega)]
        simp [singletonPsi, hFlip, show u+v+w+1 ≠ 0 by omega,
          show ¬u+v+w+1 ≤ u by omega, show ¬u+v+w+1 ≤ u+v by omega]
      refine ⟨reads_append (reads_append hJump (reads_append hUp hReturn)) hDown, ?_⟩
      intro i hi
      change i ∈ top ++ down u u at hi
      simp only [List.mem_append, hTopMem, mem_down (Nat.le_refl u)] at hi
      omega
    refine ⟨fixed ++ [main], ?_, ?_, ?_, ?_⟩
    · intro cs hcs
      simp only [List.mem_append, List.mem_singleton] at hcs
      rcases hcs with hm | rfl
      · simpa [step, hFlip] using hFixGood _ hm
      · simpa [step, hFlip] using hMain
    · rw [List.pairwise_append]
      refine ⟨hFixOrder, by simp, ?_⟩
      intro cs hcs ds hds
      obtain ⟨i, lo, _, rfl⟩ := fixed_cycles_mem hcs
      simp only [List.mem_singleton] at hds
      subst ds
      change 0 < i
      omega
    · intro i
      simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
        List.mem_append, hFixMem, main, List.mem_singleton, hTopMem,
        mem_down (Nat.le_refl u), singleton_length]
      omega
    · have hout : run b v ++ [a] ++ run b w ++ [c] ++ run b u =
          (fixed.flatten ++ main).map f := by
        simp [main, top, List.map_append, hMapUp, hMapDown, hMapFixed, ha, hc, List.append_assoc]
      simpa [f, hFlip, List.flatten_append] using hout


theorem cycle_step_mem {step : Nat → Nat} {stop start : Nat} {rows : List Nat}
    (h : Reads step stop start rows) {i : Nat} (hi : i ∈ rows) :
    step i ∈ rows ∨ step i = stop := by
  induction rows generalizing start with
  | nil => simp at hi
  | cons j js ih =>
    rcases List.mem_cons.1 hi with rfl | hj
    · cases js with
      | nil => exact Or.inr h.2
      | cons k ks => exact Or.inl (by simp [h.2.1])
    · rcases ih h.2 hj with hm | he
      · exact Or.inl (List.mem_cons_of_mem _ hm)
      · exact Or.inr he

theorem reads_invariant {step : Nat → Nat} {stop start : Nat} {rows : List Nat}
    (h : Reads step stop start rows) {P : Nat → Prop} (hp : ∀ i, P i → P (step i))
    (hs : P start) :
    P stop ∧ ∀ i ∈ rows, P i := by
  induction rows generalizing start with
  | nil => exact ⟨by rwa [h] at hs, by simp⟩
  | cons j js ih =>
    have hj : P j := h.1 ▸ hs
    obtain ⟨he, hall⟩ := ih h.2 (hp j hj)
    exact ⟨he, fun i hi => (List.mem_cons.1 hi).elim (fun e => e.symm ▸ hj) (hall i)⟩

theorem reads_intersection {step : Nat → Nat} {stop start : Nat} {rows : List Nat}
    (h : Reads step stop start rows) {P : Nat → Prop} (hp : ∀ i, P i → P (step i))
    {i : Nat} (hi : i ∈ rows) (hpi : P i) : P stop := by
  induction rows generalizing start with
  | nil => simp at hi
  | cons j js ih =>
    rcases List.mem_cons.1 hi with rfl | hm
    · exact (reads_invariant h.2 hp (hp i hpi)).1
    · exact ih h.2 hm

theorem reads_unique_tail {step : Nat → Nat} {stop start : Nat} {xs ys : List Nat}
    (hx : Reads step stop start xs) (hy : Reads step stop start ys)
    (hxm : stop ∉ xs) (hym : stop ∉ ys) : xs = ys := by
  induction xs generalizing start ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons j js =>
      have he := hy.1
      have hs : start = stop := hx
      exact False.elim (hym (List.mem_cons.2 (Or.inl (hs.symm.trans he))))
  | cons i is ih =>
    cases ys with
    | nil =>
      have he := hx.1
      have hs : start = stop := hy
      exact False.elim (hxm (List.mem_cons.2 (Or.inl (hs.symm.trans he))))
    | cons j js =>
      have hij := hx.1.symm.trans hy.1
      subst j
      have ht := ih hx.2 hy.2 (fun hi => hxm (List.mem_cons_of_mem _ hi))
        (fun hi => hym (List.mem_cons_of_mem _ hi))
      rw [ht]

theorem canonical_subset_of_overlap {step : Nat → Nat} {xs ys : List Nat}
    (hx : CanonicalCycle step xs) (hy : CanonicalCycle step ys)
    {i : Nat} (hix : i ∈ xs) (hiy : i ∈ ys) : ∀ j ∈ xs, j ∈ ys := by
  cases xs with
  | nil => exact False.elim hx
  | cons x xt =>
    cases ys with
    | nil => exact False.elim hy
    | cons y yt =>
      have hp (j : Nat) (hj : j ∈ y :: yt) : step j ∈ y :: yt := by
        rcases cycle_step_mem hy.1 hj with hm | he
        · exact hm
        · simp [he]
      have hStart := reads_intersection hx.1 hp hix hiy
      exact (reads_invariant hx.1 hp hStart).2

theorem canonical_overlap {step : Nat → Nat} {xs ys : List Nat}
    (hx : CanonicalCycle step xs) (hy : CanonicalCycle step ys)
    {i : Nat} (hix : i ∈ xs) (hiy : i ∈ ys) : xs = ys := by
  have hxy := canonical_subset_of_overlap hx hy hix hiy
  have hyx := canonical_subset_of_overlap hy hx hiy hix
  cases xs with
  | nil => exact False.elim hx
  | cons x xt =>
    cases ys with
    | nil => exact False.elim hy
    | cons y yt =>
      have le₁ : x ≤ y := by
        rcases List.mem_cons.1 (hyx y (by simp)) with he | hm
        · omega
        · have := hx.2 y hm; omega
      have le₂ : y ≤ x := by
        rcases List.mem_cons.1 (hxy x (by simp)) with he | hm
        · omega
        · have := hy.2 x hm; omega
      have he : x = y := by omega
      subst y
      have eq := reads_unique_tail hx.1.2 hy.1.2
        (fun hm => Nat.lt_irrefl x (hx.2 x hm)) (fun hm => Nat.lt_irrefl x (hy.2 x hm))
      rw [eq]

theorem ordered_cycles_unique {xs ys : List (List Nat)}
    (hx : xs.Pairwise (fun x y => leader y < leader x))
    (hy : ys.Pairwise (fun x y => leader y < leader x))
    (hm : ∀ x, x ∈ xs ↔ x ∈ ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons a as => have := (hm a).2 (by simp); simp at this
  | cons x xt ih =>
    cases ys with
    | nil => have := (hm x).1 (by simp); simp at this
    | cons y yt =>
      have eq : x = y := by
        rcases List.mem_cons.1 ((hm x).1 (by simp)) with e | tx
        · exact e
        rcases List.mem_cons.1 ((hm y).2 (by simp)) with e | ty
        · exact e.symm
        have hl := (List.pairwise_cons.1 hx).1 y ty
        have hr := (List.pairwise_cons.1 hy).1 x tx
        omega
      subst y
      have ht : ∀ z, z ∈ xt ↔ z ∈ yt := by
        intro z
        constructor
        · intro hz
          rcases List.mem_cons.1 ((hm z).1 (List.mem_cons_of_mem _ hz)) with he | ht
          · subst z
            exact False.elim (Nat.lt_irrefl _ ((List.pairwise_cons.1 hx).1 _ hz))
          · exact ht
        · intro hz
          rcases List.mem_cons.1 ((hm z).2 (List.mem_cons_of_mem _ hz)) with he | ht
          · subst z
            exact False.elim (Nat.lt_irrefl _ ((List.pairwise_cons.1 hy).1 _ hz))
          · exact ht
      rw [ih (List.pairwise_cons.1 hx).2 (List.pairwise_cons.1 hy).2 ht]

theorem inverseRecipe_unique {last x y : Word} (hx : InverseRecipe last x)
    (hy : InverseRecipe last y) : x = y := by
  obtain ⟨xs, xgood, xorder, xcover, xe⟩ := hx
  obtain ⟨ys, ygood, yorder, ycover, ye⟩ := hy
  have subset (cs ds : List (List Nat))
      (cg : ∀ c ∈ cs, CanonicalCycle (psi last) c)
      (dg : ∀ c ∈ ds, CanonicalCycle (psi last) c)
      (cv : ∀ i, i ∈ cs.flatten → i ∈ ds.flatten) :
      ∀ c ∈ cs, c ∈ ds := by
    intro c hc
    have hg := cg c hc
    cases c with
    | nil => exact False.elim hg
    | cons i is =>
      have hi : i ∈ i :: is := by simp
      have hi' := cv i (List.mem_flatten.2 ⟨i :: is, hc, hi⟩)
      obtain ⟨d, hd, hid⟩ := List.mem_flatten.1 hi'
      have he := canonical_overlap hg (dg d hd) hi hid
      exact he ▸ hd
  have eq := ordered_cycles_unique xorder yorder (fun c => ⟨
    subset xs ys xgood ygood (fun i hi => (ycover i).2 ((xcover i).1 hi)) c,
    subset ys xs ygood xgood (fun i hi => (xcover i).2 ((ycover i).1 hi)) c⟩)
  rw [xe, ye, eq]

/-- The paper's characterization of inverse BBWT, used as a named hypothesis
when relating the verified inverse recipe to the separate forward definition. -/
def InverseImplements (inverse : Word → Word) : Prop :=
  ∀ last, InverseRecipe last (inverse last)

theorem maximal_singleton_transfer_functions (forward inverse : Word → Word)
    (hRecipe : InverseImplements inverse)
    (hRight : ∀ last, forward (inverse last) = last) (A E R : Nat) :
    inverse (rotLeft (forward (transferIn A E R))) = transferOut A E R := by
  have hIn := inverseRecipe_unique (hRecipe (transferLast A E R)) (transferLast_inverse A E R)
  rw [← hIn, hRight, rot_transfer]
  exact inverseRecipe_unique (hRecipe (transferRot A E R)) (transferRot_inverse A E R)

def cPosition (word : Word) : Nat := (positions c 0 word).headD 0

/-- Position reflection for every inverse-cycle output of the singleton forms. -/
theorem singleton_reflection (flip : Bool) (u v w : Nat) {out : Word}
    (h : InverseRecipe (singletonLast flip u v w) out) :
    cPosition out + cPosition (singletonLast flip u v w) =
      (singletonLast flip u v w).length - 1 := by
  rw [inverseRecipe_unique h (singleton_inverse flip u v w)]
  cases flip <;> simp [cPosition, singletonLast, positions_append, positions, Nat.add_assoc] <;> omega


def letterRank : Letter → Nat
  | a => 0
  | b => 1
  | c => 2

def LexLess : Word → Word → Prop := List.Lex (fun l r => letterRank l < letterRank r)

def IsRotation (x y : Word) : Prop :=
  ∃ pre suf : Word, x = pre ++ suf ∧ y = suf ++ pre

theorem lex_prefix {x y : Word} (pre : Word) (h : LexLess x y) :
    LexLess (pre ++ x) (pre ++ y) := by
  induction pre with
  | nil => exact h
  | cons l ls ih => exact List.Lex.cons ih

def transferSmaller (A E R : Nat) : Word :=
  run a (A+1) ++ run b (E+2) ++ [c] ++ run b R

theorem transfer_decreases (A E R : Nat) :
    IsRotation (transferOut A E R) (transferSmaller A E R) ∧
      LexLess (transferSmaller A E R) (transferIn A E R) := by
  constructor
  · refine ⟨[a] ++ run b (E+2) ++ [c] ++ run b R, run a A, rfl, ?_⟩
    simp [transferSmaller, run, List.replicate_succ', List.append_assoc]
  · unfold transferSmaller transferIn
    rw [show run b (E+2) = run b (E+1) ++ [b] by simp [run, List.replicate_succ']]
    simp only [List.append_assoc]
    apply lex_prefix (run a (A+1))
    apply lex_prefix (run b (E+1))
    exact List.Lex.rel (by decide)

theorem length_positions_offset (letter : Letter) (word : Word) (s t : Nat) :
    (positions letter s word).length = (positions letter t word).length := by
  induction word generalizing s t with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : x = letter <;> simp [positions, h, ih (s+1) (t+1)]

def multiplicity (letter : Letter) (word : Word) : Nat := (positions letter 0 word).length

@[simp] theorem multiplicity_cons (letter x : Letter) (w : Word) :
    multiplicity letter (x :: w) =
      multiplicity letter w + (if x = letter then 1 else 0) := by
  by_cases h : x = letter <;> simp [multiplicity, positions, h, length_positions_offset letter w 1 0]

theorem all_b (word : Word) (ha : multiplicity a word = 0) (hc : multiplicity c word = 0) :
    ∃ k, word = run b k := by
  induction word with
  | nil => exact ⟨0, rfl⟩
  | cons x xs ih =>
    cases x <;> simp_all (config := {decide := true}) only [multiplicity_cons, reduceCtorEq,
      if_true, if_false, Nat.add_zero, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false]
    obtain ⟨k, rfl⟩ := ih trivial trivial
    exact ⟨k+1, rfl⟩

theorem one_other (letter : Letter) (hLetter : letter ≠ b) (word : Word)
    (hOne : multiplicity letter word = 1)
    (hOther : ∀ x, x ≠ b → x ≠ letter → multiplicity x word = 0) :
    ∃ u v : Nat, word = run b u ++ [letter] ++ run b v := by
  induction word with
  | nil => simp [multiplicity, positions] at hOne
  | cons x xs ih =>
    by_cases hb : x = b
    · subst x
      have hx : b ≠ letter := Ne.symm hLetter
      simp [hx] at hOne
      have ho (x : Letter) (h₁ : x ≠ b) (h₂ : x ≠ letter) :
          multiplicity x xs = 0 := by
        simpa [Ne.symm h₁] using hOther x h₁ h₂
      obtain ⟨u,v,rfl⟩ := ih hOne ho
      exact ⟨u+1,v,rfl⟩
    · by_cases hl : x = letter
      · subst x
        have hl0 : multiplicity letter xs = 0 := by simpa using hOne
        have hz (x : Letter) (hx : x ≠ b) : multiplicity x xs = 0 := by
          by_cases hl : x = letter
          · simpa [hl] using hl0
          · simpa [Ne.symm hl] using hOther x hx hl
        obtain ⟨k,rfl⟩ := all_b xs (hz a (by decide)) (hz c (by decide))
        exact ⟨0,k,rfl⟩
      · have h := hOther x hb hl
        simp at h

theorem singleton_forms (word : Word) (ha : multiplicity a word = 1)
    (hc : multiplicity c word = 1) : ∃ flip u v w, word = singletonLast flip u v w := by
  induction word with
  | nil => simp [multiplicity, positions] at ha
  | cons x xs ih =>
    cases x
    · have ha0 : multiplicity a xs = 0 := by simpa using ha
      have hc1 : multiplicity c xs = 1 := by simpa (config := {decide := true}) using hc
      have hOther : ∀ x, x ≠ b → x ≠ c → multiplicity x xs = 0 := by
        intro x h₁ h₂
        cases x
        · exact ha0
        · exact False.elim (h₁ rfl)
        · exact False.elim (h₂ rfl)
      obtain ⟨v,w,rfl⟩ := one_other c (by decide) xs hc1 hOther
      exact ⟨false,0,v,w,rfl⟩
    · have ha1 : multiplicity a xs = 1 := by simpa (config := {decide := true}) using ha
      have hc1 : multiplicity c xs = 1 := by simpa (config := {decide := true}) using hc
      obtain ⟨flip,u,v,w,rfl⟩ := ih ha1 hc1
      exact ⟨flip,u+1,v,w,rfl⟩
    · have hc0 : multiplicity c xs = 0 := by simpa using hc
      have ha1 : multiplicity a xs = 1 := by simpa (config := {decide := true}) using ha
      have hOther : ∀ x, x ≠ b → x ≠ a → multiplicity x xs = 0 := by
        intro x h₁ h₂
        cases x
        · exact False.elim (h₂ rfl)
        · exact False.elim (h₁ rfl)
        · exact hc0
      obtain ⟨v,w,rfl⟩ := one_other a (by decide) xs ha1 hOther
      exact ⟨true,0,v,w,rfl⟩

theorem inverse_reflects_unique_c {last out : Word}
    (ha : multiplicity a last = 1) (hc : multiplicity c last = 1)
    (h : InverseRecipe last out) :
    cPosition out + cPosition last = last.length - 1 := by
  obtain ⟨flip,u,v,w,rfl⟩ := singleton_forms last ha hc
  exact singleton_reflection flip u v w h

theorem singletonForward_recipe (flip : Bool) (u v w : Nat) :
    InverseRecipe (if flip then singletonLast false w v u else singletonLast true w u v)
      (singletonLast flip u v w) := by
  cases flip
  · simpa [singletonLast] using singleton_inverse true w u v
  · simpa [singletonLast] using singleton_inverse false w v u

/-- Forward direction conditional on the standard inverse characterization. -/
theorem forward_reflects_unique_c (forward inverse : Word → Word)
    (hRecipe : InverseImplements inverse)
    (hRight : ∀ last, forward (inverse last) = last)
    {word : Word} (ha : multiplicity a word = 1) (hc : multiplicity c word = 1) :
    cPosition (forward word) = word.length - 1 - cPosition word := by
  obtain ⟨flip,u,v,w,rfl⟩ := singleton_forms word ha hc
  let last := if flip then singletonLast false w v u else singletonLast true w u v
  have h := singletonForward_recipe flip u v w
  have he : inverse last = singletonLast flip u v w :=
    inverseRecipe_unique (hRecipe last) h
  have hf : forward (singletonLast flip u v w) = last := by rw [← he, hRight]
  rw [hf]
  cases flip <;> simp [last, cPosition, singletonLast, positions_append, positions, Nat.add_assoc] <;> omega

theorem cPosition_rotLeft (flip : Bool) (u v w : Nat) :
    cPosition (rotLeft (singletonLast flip u v w)) =
      if cPosition (singletonLast flip u v w) = 0 then u+v+w+1
      else cPosition (singletonLast flip u v w)-1 := by
  cases u with
  | zero =>
    cases flip <;>
      simp [rotLeft, singletonLast, cPosition, positions_append, positions, positions_run, run,
        List.append_assoc, ← List.replicate_succ', Nat.add_assoc] <;> omega
  | succ k =>
    cases flip <;>
      simp [rotLeft, singletonLast, cPosition, positions_append, positions, positions_run,
        run, List.replicate_succ, List.append_assoc, ← List.replicate_succ',
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega

/-- Rotation acts by decrement modulo the length on the position coordinate. -/
theorem rotate_shifts_unique_c {word : Word}
    (ha : multiplicity a word = 1) (hc : multiplicity c word = 1) :
    cPosition (rotLeft word) =
      if cPosition word = 0 then word.length-1 else cPosition word-1 := by
  obtain ⟨flip,u,v,w,rfl⟩ := singleton_forms word ha hc
  simpa using cPosition_rotLeft flip u v w


/-- Last column used in the b3 inverse calculation. The manuscript's
parameters e', e_c, r are E+1, C+1, R+1, respectively. -/
def b3Last (E C R : Nat) : Word := [c,a] ++ run b E ++ run c C ++ run b (R+2)

def b3Psi (E C R j : Nat) : Nat :=
  if j ≤ E then j+1
  else if j ≤ E+R+2 then j+C+1
  else if j = E+R+3 then 0
  else j-(R+2)

theorem psi_b3 (E C R j : Nat) (hj : j < E+C+R+4) :
    psi (b3Last E C R) j = b3Psi E C R j := by
  simp only [psi, stableRows, b3Last, positions_append, positions_run', run_len, positions,
    List.length_cons, List.length_nil]
  simp (config := { decide := true }) only [reduceCtorEq, if_true, if_false,
    List.nil_append, List.append_nil, Nat.zero_add, Nat.add_zero, Nat.reduceAdd]
  simp only [b3Psi, List.getElem?_append, List.length_append, List.length_range',
    List.length_cons, List.length_nil, run_len, rangeGet, List.getElem?_cons, List.getElem?_nil]
  repeat' first | split | simp only [Option.getD_some, Option.getD_none]
  all_goals omega

def strideDown (d s : Nat) : Nat → List Nat
  | 0 => []
  | k+1 => s :: strideDown d (s-d) k

theorem reads_stride {step : Nat → Nat} (d s k : Nat) (hPos : 0 < d) (hk : d*k ≤ s)
    (h : ∀ j, s-d*k < j → j ≤ s → step j = j-d) :
    Reads step (s-d*k) s (strideDown d s k) := by
  induction k generalizing s with
  | zero => simp [strideDown, Reads]
  | succ k ih =>
    simp only [Nat.mul_succ] at hk h ⊢
    simp only [strideDown, Reads, true_and]
    rw [h s (by omega) (by omega)]
    have hh := ih (s-d) (by omega) (fun j lo hi => h j (by omega) (by omega))
    rwa [show s-d-d*k = s-(d*k+d) by omega] at hh


/-- The exact b3 c-block trace and its first exit. The formula includes
the closing case (exit row 0) when e_c is divisible by r+1. -/
theorem b3_c_trace (E C R : Nat) (hEntry : R+1 ≤ C) :
    let d := R+2
    let q := (C+1)/d
    let h := (C+1)%d
    let rows := strideDown d (E+C+2) (q-1) ++ [E+R+3+h]
    0 < q ∧ q < C+1 ∧
      Reads (psi (b3Last E C R)) (if h = 0 then 0 else E+1+h) (E+C+2) rows ∧
      rows.length = q ∧
      ∀ i ∈ rows, E+R+3 ≤ i ∧ i < E+C+R+4 := by
  dsimp only
  let d := R+2
  let q := (C+1)/d
  let h := (C+1)%d
  let start := E+C+2
  let base := E+R+3
  let step := psi (b3Last E C R)
  change 0 < q ∧ q < C+1 ∧
    Reads step (if h = 0 then 0 else E+1+h) start
      (strideDown d start (q-1) ++ [base+h]) ∧
    (strideDown d start (q-1) ++ [base+h]).length = q ∧
    ∀ i ∈ strideDown d start (q-1) ++ [base+h], base ≤ i ∧ i < E+C+R+4
  have hd : 1 < d := by dsimp [d]; omega
  have hq : 0 < q := Nat.div_pos (by dsimp [d]; omega) (by omega)
  have hm : h < d := Nat.mod_lt _ (by omega)
  have hSmall : q < C+1 := Nat.div_lt_self (by omega) hd
  have hDecomp : h+d*q = C+1 := Nat.mod_add_div _ _
  have hMul : d*q = d*(q-1)+d := by
    conv => lhs; rw [show q = (q-1)+1 by omega, Nat.mul_succ]
  have hStart : start = base+h+d*(q-1) := by
    dsimp only [start, base] at *
    have hd' : d = R+2 := rfl
    omega
  have hFirst : Reads step (base+h) start (strideDown d start (q-1)) := by
    have ht := reads_stride (step := step) d start (q-1) (by omega) (by omega) (by
      intro j lo hi
      have hj : E+R+3 < j := by dsimp only [base] at *; omega
      have hj' : j < E+C+R+4 := by dsimp only [start] at *; omega
      rw [show step j = _ from psi_b3 E C R j hj']
      simp [b3Psi, d, show ¬j ≤ E by omega, show ¬j ≤ E+R+2 by omega,
        show j ≠ E+R+3 by omega])
    rwa [show start-d*(q-1) = base+h by omega] at ht
  have hLast : step (base+h) = if h = 0 then 0 else E+1+h := by
    have hb : base+h < E+C+R+4 := by dsimp only [start] at *; omega
    rw [show step (base+h) = _ from psi_b3 E C R _ hb]
    dsimp only [base]
    by_cases hz : h = 0
    · simp [b3Psi, hz, show ¬ E+R+3 ≤ E by omega, show ¬ E+R+3 ≤ E+R+2 by omega]
    · simp [b3Psi, hz, show ¬ E+R+3+h ≤ E by omega,
        show ¬ E+R+3+h ≤ E+R+2 by omega, show E+R+3+h ≠ E+R+3 by omega]
      omega
  have length_stride (s k : Nat) : (strideDown d s k).length = k := by
    induction k generalizing s with
    | zero => rfl
    | succ k ih => simp [strideDown, ih]
  have mem_stride (s k : Nat) (hs : d*k ≤ s) {i : Nat} (hi : i ∈ strideDown d s k) :
      s-d*k < i ∧ i ≤ s := by
    induction k generalizing s with
    | zero => simp [strideDown] at hi
    | succ k ih =>
      simp only [strideDown, List.mem_cons] at hi
      simp only [Nat.mul_succ] at hs ⊢
      rcases hi with rfl | hi
      · omega
      · obtain ⟨lo, hu⟩ := ih (s-d) (by omega) hi
        omega
  refine ⟨hq, hSmall, reads_append hFirst (reads_one hLast), ?_, ?_⟩
  · simp [length_stride]; omega
  · intro i hi
    have hBase : base = E+R+3 := rfl
    have hStart' : start = E+C+2 := rfl
    simp only [List.mem_append, List.mem_singleton] at hi
    rcases hi with hi | rfl
    · obtain ⟨lo, hu⟩ := mem_stride start (q-1) (by omega) hi
      omega
    · omega

theorem b3_nonclosing_exit_is_b (E C R : Nat)
    (hPositive : 0 < (C+1)%(R+2)) :
    1 ≤ E+1+(C+1)%(R+2) ∧ E+1+(C+1)%(R+2) ≤ E+R+2 := by
  have := Nat.mod_lt (C+1) (show 0 < R+2 by omega)
  omega

theorem singleton_position_surjective (k i : Nat) (hi : i < k+2) :
    ∃ word : Word, word.length = k+2 ∧ multiplicity a word = 1 ∧
      multiplicity b word = k ∧ multiplicity c word = 1 ∧ cPosition word = i := by
  by_cases h : i = 0
  · subst i
    refine ⟨singletonLast true 0 0 k, ?_⟩
    simp [singletonLast, multiplicity, cPosition, positions_append, positions]
  · refine ⟨singletonLast false 0 (i-1) (k+1-i), ?_⟩
    simp [singletonLast, multiplicity, cPosition, positions_append, positions]
    omega

def posPrev (n i : Nat) : Nat := if i = 0 then n-1 else i-1
def posNext (n i : Nat) : Nat := if i+1 = n then 0 else i+1
def posReflect (n i : Nat) : Nat := n-1-i

/-- The dihedral relations on the position coordinate. -/
theorem dihedral_position_relations (n i : Nat) (hn : 3 ≤ n) (hi : i < n) :
    posReflect n (posReflect n i) = i ∧
    posPrev n (posNext n i) = i ∧ posNext n (posPrev n i) = i ∧
    posReflect n (posPrev n (posReflect n i)) = posNext n i := by
  simp only [posReflect, posPrev, posNext]
  repeat' (first | split | constructor)
  all_goals omega

/-- Initial path in the b3 cycle, through the initial a and e' copies of b. -/
theorem b3_initial_trace (E C R : Nat) :
    Reads (psi (b3Last E C R)) (E+C+2) 0 (List.range' 0 (E+2)) := by
  rw [List.range'_1_concat, Nat.zero_add]
  apply reads_append (mid := E+1) (u := List.range' 0 (E+1)) (v := [E+1])
  · simpa using reads_up (step := psi (b3Last E C R)) 0 (E+1) (by
      intro j _ hj
      rw [psi_b3 E C R j (by omega)]
      simp [b3Psi, show j ≤ E by omega])
  · apply reads_one
    rw [psi_b3 E C R (E+1) (by omega)]
    simp [b3Psi, show ¬ E+1 ≤ E by omega, show E+1 ≤ E+R+2 by omega]
    omega

/-- Any cycle other than the one containing row 0 must begin in the b block. -/
theorem b3_positive_leader_is_b (E C R j : Nat) (rows : List Nat)
    (hCycle : CanonicalCycle (psi (b3Last E C R)) (j :: rows))
    (hPositive : 0 < j) (hBound : j < E+C+R+4) : j ≤ E+R+2 := by
  by_cases h : j ≤ E+R+2
  · exact h
  · have hLower : psi (b3Last E C R) j < j := by
      rw [psi_b3 E C R j hBound]
      simp only [b3Psi, show ¬ j ≤ E by omega, h, if_false]
      split <;> omega
    rcases cycle_step_mem hCycle.1 (show j ∈ j :: rows by simp) with hs | he
    · rcases List.mem_cons.1 hs with he | hm
      · omega
      · have := hCycle.2 _ hm
        omega
    · omega

/-- The transfer in forward/inverse notation, followed by a strict rotation descent. -/
theorem maximal_singleton_descent_functions (forward inverse : Word → Word)
    (hRecipe : InverseImplements inverse)
    (hRight : ∀ last, forward (inverse last) = last) (A E R : Nat) :
    IsRotation (inverse (rotLeft (forward (transferIn A E R)))) (transferSmaller A E R) ∧
      LexLess (transferSmaller A E R) (transferIn A E R) := by
  rw [maximal_singleton_transfer_functions forward inverse hRecipe hRight]
  exact transfer_decreases A E R

/-- Swap the outgoing edges at the first two sorted rows. -/
def swapSmallestOut (step : Nat → Nat) (i : Nat) : Nat :=
  if i = 0 then step 1 else if i = 1 then step 0 else step i

theorem reads_rewrite_on {step next : Nat → Nat} {start stop : Nat} {rows : List Nat}
    (trace : Reads step stop start rows) (h : ∀ i ∈ rows, next i = step i) :
    Reads next stop start rows := by
  induction rows generalizing start with
  | nil => exact trace
  | cons j js ih =>
    refine ⟨trace.1, ?_⟩
    rw [h j (by simp)]
    exact ih trace.2 (fun i hi => h i (List.mem_cons_of_mem _ hi))

theorem reads_cut {step : Nat → Nat} {start stop j : Nat} {u v : List Nat}
    (trace : Reads step stop start (u ++ j :: v)) :
    Reads step j start u ∧ Reads step stop j (j :: v) := by
  induction u generalizing start with
  | nil => exact ⟨trace.1, ⟨rfl, trace.2⟩⟩
  | cons i is ih =>
    obtain ⟨left, right⟩ := ih trace.2
    exact ⟨⟨trace.1, left⟩, right⟩

theorem swap_agrees_away {step : Nat → Nat} {start stop : Nat} {rows : List Nat}
    (trace : Reads step stop start rows) (h : ∀ i ∈ rows, 1 < i) :
    Reads (swapSmallestOut step) stop start rows := by
  apply reads_rewrite_on trace
  intro i hi
  have hRow := h i hi
  simp [swapSmallestOut, show i ≠ 0 by omega, show i ≠ 1 by omega]

/-- The two-cycle branch of the outgoing-edge exchange in Theorem 4(b). -/
theorem smallest_swap_merges_cycles {step : Nat → Nat} {u v : List Nat}
    (h0 : CanonicalCycle step (0 :: u)) (h1 : CanonicalCycle step (1 :: v)) :
    CanonicalCycle (swapSmallestOut step) (0 :: (v ++ 1 :: u)) := by
  have hu (i : Nat) (hi : i ∈ u) : 1 < i := by
    have hPositive := h0.2 i hi
    by_cases eq : i = 1
    · subst i
      have he := canonical_overlap h0 h1 (List.mem_cons_of_mem _ hi) (by simp)
      cases he
    · omega
  have traceU := swap_agrees_away h0.1.2 hu
  have traceV := swap_agrees_away h1.1.2 h1.2
  constructor
  · refine ⟨rfl, ?_⟩
    have traceOne : Reads (swapSmallestOut step) 0 1 (1 :: u) :=
      ⟨rfl, by simpa [swapSmallestOut] using traceU⟩
    simpa [swapSmallestOut] using reads_append traceV traceOne
  · intro i hi
    rcases List.mem_append.1 hi with hv | hi
    · have := h1.2 i hv
      omega
    · rcases List.mem_cons.1 hi with rfl | hi
      · decide
      · exact h0.2 i hi

/-- The one-cycle branch of the outgoing-edge exchange in Theorem 4(b). -/
theorem smallest_swap_splits_cycle {step : Nat → Nat} {u v : List Nat}
    (h : CanonicalCycle step (0 :: (u ++ 1 :: v)))
    (hu : ∀ i ∈ u, 1 < i) (hv : ∀ i ∈ v, 1 < i) :
    CanonicalCycle (swapSmallestOut step) (0 :: v) ∧
      CanonicalCycle (swapSmallestOut step) (1 :: u) := by
  obtain ⟨traceU, trace1⟩ := reads_cut h.1.2
  have hU := swap_agrees_away traceU hu
  have hV := swap_agrees_away trace1.2 hv
  refine ⟨⟨⟨rfl, ?_⟩, ?_⟩, ⟨⟨rfl, ?_⟩, hu⟩⟩
  · simpa [swapSmallestOut] using hV
  · intro i hi
    have := hv i hi
    omega
  · simpa [swapSmallestOut] using hU

end BBWT

#print axioms BBWT.inverseRecipe_unique
#print axioms BBWT.maximal_singleton_transfer
#print axioms BBWT.transfer_decreases
#print axioms BBWT.maximal_singleton_descent_functions
#print axioms BBWT.inverse_reflects_unique_c
#print axioms BBWT.forward_reflects_unique_c
#print axioms BBWT.rotate_shifts_unique_c
#print axioms BBWT.singleton_position_surjective
#print axioms BBWT.dihedral_position_relations
#print axioms BBWT.b3_initial_trace
#print axioms BBWT.b3_c_trace
#print axioms BBWT.b3_nonclosing_exit_is_b
#print axioms BBWT.b3_positive_leader_is_b
#print axioms BBWT.smallest_swap_merges_cycles
#print axioms BBWT.smallest_swap_splits_cycle
