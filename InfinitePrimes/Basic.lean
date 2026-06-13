import Cslib.Computability.Languages.RegularLanguage
import Cslib.Computability.Languages.MyhillNerode
import Mathlib.Algebra.Prime.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

variable {α : Type u}

open Computability Language

theorem Language.IsRegular.list_sum
    (ls : List (Language α)) (h : ∀ L ∈ ls, L.IsRegular) :
    ls.sum.IsRegular := by
  induction ls with
  | nil  => simp
  | cons L rest ih =>
      simp [List.sum_cons]
      exact (h L (List.mem_cons_self ..)).add
            (ih (fun l hl => h l (List.mem_cons_of_mem _ hl)))

theorem Language.IsRegular.finset_union (s : Finset ι) (L : ι → Language T)
    (h : ∀ i ∈ s, Language.IsRegular (L i)) :
    Language.IsRegular (s.toList.map L).sum :=
  Language.IsRegular.list_sum _
    (fun l hl => by
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
      exact h i (Finset.mem_toList.mp hi))

def ξ (w : List Bool) : ℤ := w.foldl (fun acc b => if b then acc + 1 else acc - 1) 0

private lemma foldl_offset (l : List Bool) (acc : ℤ) :
    l.foldl (fun a b => if b then a + 1 else a - 1) acc =
    acc + l.foldl (fun a b => if b then a + 1 else a - 1) 0 := by
  induction l generalizing acc with
  | nil  => simp
  | cons b rest ih =>
      simp only [List.foldl_cons]
      rw [ih, ih (if b then 0 + 1 else 0 - 1)]
      cases b <;> simp <;> ring

lemma ξ_additive (u v : List Bool) : ξ (u ++ v) = ξ u + ξ v := by
  unfold ξ
  rw [List.foldl_append, foldl_offset v]

lemma ξ_replicate_true (k : ℕ) : ξ (List.replicate k true) = k := by
  induction k with
  | zero => simp [ξ]
  | succ k ih =>
    rw [List.replicate_succ, ← List.singleton_append, ξ_additive, ih]
    simp [ξ]
    ring

lemma ξ_replicate_false (k : ℕ) : ξ (List.replicate k false) = -↑k := by
  induction k with
  | zero => simp [ξ]
  | succ k ih =>
    rw [List.replicate_succ, ← List.singleton_append, ξ_additive, ih]
    simp [ξ]

lemma fold_invariant {n : ℕ} (h : ∀ (z : List Bool),
    ↑n ∣ ξ (x ++ z) ↔ ↑n ∣ ξ (y ++ z)) :
  (↑(ξ x) : ZMod n) = ↑(ξ y) := by
  rw [ZMod.intCast_eq_intCast_iff']
  sorry

def L (n : ℕ) [NeZero n] : Language Bool := ((n : ℤ) ∣ ξ ·)  -- {w | ξ w % n = 0}

@[simp] lemma mem_L (n : ℕ) [NeZero n] (w : List Bool) : w ∈ L n ↔ (n : ℤ) ∣ ξ w := by rfl

theorem L_n_regular (n : ℕ) [NeZero n] : (L n).IsRegular := by
  unfold L
  apply IsRegular.iff_finite_nerodeQuotient.mpr
  unfold NerodeQuotient NerodeCongruence 
  apply Finite.of_injective (Quotient.lift (fun w => (ξ w : ZMod n)) _)
  · intro x y hxy
    induction x using Quotient.inductionOn with | h u =>
    induction y using Quotient.inductionOn with | h v =>
    set m := ξ u with hm; set k := ξ v with hk
    apply Quotient.sound
    intro z
    simp only [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    change (↑(ξ (u ++ z)) : ZMod n) = 0 ↔ (↑(ξ (v ++ z)) : ZMod n) = 0
    simp only [ξ_additive, Int.cast_add]
    rw [show (ξ u : ZMod n) = ξ v from hxy]
  · intro x y hxy
    have hxy' := Quotient.sound hxy
    exact fold_invariant hxy

def L_p : Language Bool := {w | ∃ (i : ℕ) (h : Prime i), w ∈ @L i ⟨h.ne_zero⟩}
def L_p' : Language Bool := (|ξ ·| = 1)  -- {w | |ξ w| = 1}

theorem L_p_eq_L_p' : L_p = L_p' := by sorry

theorem L_not_regular : ¬ L_p.IsRegular := by sorry

theorem infinite_primes : Set.Infinite {p : ℕ | Prime p} := by sorry

