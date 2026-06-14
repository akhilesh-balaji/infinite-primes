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

private lemma foldl_offset (l : List Bool) (acc : ℤ) :
    l.foldl (fun a b => if b then a + 1 else a - 1) acc =
    acc + l.foldl (fun a b => if b then a + 1 else a - 1) 0 := by
  induction l generalizing acc with
  | nil  => simp
  | cons b rest ih =>
      simp only [List.foldl_cons]
      rw [ih, ih (if b then 0 + 1 else 0 - 1)]
      cases b <;> simp <;> ring

def ξ (w : List Bool) : ℤ := w.foldl (fun acc b => if b then acc + 1 else acc - 1) 0

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

lemma fold_invariant {n : ℕ} [NeZero n] (h : ∀ (z : List Bool),
    ↑n ∣ ξ (x ++ z) ↔ ↑n ∣ ξ (y ++ z)) :
  (↑(ξ x) : ZMod n) = ↑(ξ y) := by
  simp only [ξ_additive] at h
  rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have e : ξ x - ξ y = -(ξ y + -ξ x) := by ring
  by_cases hx : 0 ≤ ξ x
  · have hk : ((ξ x).toNat : ℤ) = ξ x := Int.toNat_of_nonneg hx
    have hz : ξ (List.replicate (ξ x).toNat false) = -ξ x := by
      rw [ξ_replicate_false, hk]
    have h0 : (↑n : ℤ) ∣ (ξ x + ξ (List.replicate (ξ x).toNat false)) := by
      rw [hz]; simp
    have h1 := (h (List.replicate (ξ x).toNat false)).mp h0
    rw [hz] at h1
    rw [e]
    exact dvd_neg.mpr h1
  · push Not at hx
    have hk : ((-ξ x).toNat : ℤ) = -ξ x := Int.toNat_of_nonneg (by linarith)
    have hz : ξ (List.replicate (-ξ x).toNat true) = -ξ x := by
      rw [ξ_replicate_true, hk]
    have h0 : (↑n : ℤ) ∣ (ξ x + ξ (List.replicate (-ξ x).toNat true)) := by
      rw [hz]; simp
    have h1 := (h (List.replicate (-ξ x).toNat true)).mp h0
    rw [hz] at h1
    rw [e]
    exact dvd_neg.mpr h1

def L (n : ℕ) [NeZero n] : Language Bool := ((n : ℤ) ∣ ξ ·)  -- {w | ξ w % n = 0}

@[simp]
lemma mem_L (n : ℕ) [NeZero n] (w : List Bool) : w ∈ L n ↔ (n : ℤ) ∣ ξ w := by rfl

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
def L_p' : Language Bool := (|ξ ·| ≠ 1)  -- {w | |ξ w| = 1}

theorem L_p_eq_L_p' : L_p = L_p' := by
  unfold L_p L_p' L
  ext x
  constructor
  · intro h_L_p_mem
    rcases h_L_p_mem with ⟨i, h_prime, h_L_ξ_div_n⟩
    simp_rw [Int.dvd_iff_emod_eq_zero] at h_L_ξ_div_n
    have hi : 2 ≤ (i : ℤ) := by exact_mod_cast Nat.Prime.two_le (Nat.prime_iff.mpr h_prime)
    have hdvd : (i : ℤ) ∣ ξ x := Int.dvd_of_emod_eq_zero h_L_ξ_div_n
    simp [abs_eq]
    show ¬ξ x = 1 ∧ ¬ξ x = -1
    refine ⟨fun h1 => ?_, fun h1 => ?_⟩
    · rw [h1] at hdvd
      have := Int.le_of_dvd one_pos hdvd
      omega
    · rw [h1] at hdvd
      rw [dvd_neg] at hdvd
      have := Int.le_of_dvd one_pos hdvd
      omega
  · intro h_L_p'_mem
    have h_ne : |ξ x| ≠ 1 := h_L_p'_mem
    have hnatAbs : (ξ x).natAbs ≠ 1 := by
      intro hc
      apply h_ne
      rw [Int.abs_eq_natAbs, hc]
      norm_num
    obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd hnatAbs
    have hp_dvd' : (p : ℤ) ∣ ξ x := by
        rw [← Int.dvd_natAbs]
        exact_mod_cast hp_dvd
    exact ⟨p, hp_prime.prime, hp_dvd'⟩

theorem L_not_regular : ¬L_p.IsRegular := by sorry

theorem infinite_primes : Set.Infinite {p : ℕ | Prime p} := by sorry

