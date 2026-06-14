import Cslib.Computability.Languages.MyhillNerode
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

variable {α : Type u}

open Cslib Computability Language

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
    IsRegular (s.toList.map L).sum :=
  IsRegular.list_sum _
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

theorem L_p_eq_inf_union : {w | ∃ (i : ℕ), ∃ (h : Prime i), w ∈ @L i ⟨h.ne_zero⟩} = ⋃ i : ℕ, ⋃ (h : Prime i), @L i ⟨h.ne_zero⟩ := by
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  exact Eq.to_iff rfl

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

theorem L_p_not_regular : ¬L_p.IsRegular := by
  by_contra h
  rw [L_p_eq_L_p'] at h
  apply IsRegular.iff_finite_nerodeQuotient.mp at h
  unfold L_p' NerodeQuotient NerodeCongruence at h
  apply Finite.not_infinite h
  apply Infinite.of_injective (fun k : ℕ =>
    Quotient.mk _ (List.replicate (3 * k) true))
  intro i j hij
  by_contra hne
  rcases lt_or_gt_of_ne hne with h_lt | h_lt
  · have heq := Quotient.exact hij
    have hdist := heq (List.replicate (3 * i + 1) false)
    have hdist' :
        (|ξ (List.replicate (3 * i) true ++ List.replicate (3 * i + 1) false)| ≠ 1) ↔
        (|ξ (List.replicate (3 * j) true ++ List.replicate (3 * i + 1) false)| ≠ 1) := hdist
    rw [ξ_additive, ξ_additive, ξ_replicate_true, ξ_replicate_true, ξ_replicate_false] at hdist'
    have hA : ((3 * i : ℕ) : ℤ) + -((3 * i + 1 : ℕ) : ℤ) = -1 := by push_cast; ring
    rw [hA, abs_neg, abs_one] at hdist'
    have hcontra : ¬ ((1 : ℤ) ≠ 1) := fun hh => hh rfl
    have hB1 : |((3 * j : ℕ) : ℤ) + -((3 * i + 1 : ℕ) : ℤ)| = 1 := by
      by_contra hne'
      exact hcontra (hdist'.mpr hne')
    have hB : ((3 * j : ℕ) : ℤ) + -((3 * i + 1 : ℕ) : ℤ) = 3 * ((j : ℤ) - (i : ℤ)) - 1 := by
      push_cast; ring
    rw [hB] at hB1
    have hji : (1 : ℤ) ≤ (j : ℤ) - (i : ℤ) := by
      have h' : i + 1 ≤ j := h_lt
      have h'' : ((i : ℤ) + 1) ≤ (j : ℤ) := by exact_mod_cast h'
      linarith
    have hge : (2 : ℤ) ≤ 3 * ((j : ℤ) - (i : ℤ)) - 1 := by linarith
    rw [abs_of_pos (by linarith)] at hB1
    linarith
  · have heq := Quotient.exact hij.symm
    have hdist := heq (List.replicate (3 * j + 1) false)
    have hdist' :
        (|ξ (List.replicate (3 * j) true ++ List.replicate (3 * j + 1) false)| ≠ 1) ↔
        (|ξ (List.replicate (3 * i) true ++ List.replicate (3 * j + 1) false)| ≠ 1) := hdist
    rw [ξ_additive, ξ_additive, ξ_replicate_true, ξ_replicate_true, ξ_replicate_false] at hdist'
    have hA : ((3 * j : ℕ) : ℤ) + -((3 * j + 1 : ℕ) : ℤ) = -1 := by push_cast; ring
    rw [hA, abs_neg, abs_one] at hdist'
    have hcontra : ¬ ((1 : ℤ) ≠ 1) := fun hh => hh rfl
    have hB1 : |((3 * i : ℕ) : ℤ) + -((3 * j + 1 : ℕ) : ℤ)| = 1 := by
      by_contra hne'
      exact hcontra (hdist'.mpr hne')
    have hB : ((3 * i : ℕ) : ℤ) + -((3 * j + 1 : ℕ) : ℤ) = 3 * ((i : ℤ) - (j : ℤ)) - 1 := by
      push_cast; ring
    rw [hB] at hB1
    have hij' : (1 : ℤ) ≤ (i : ℤ) - (j : ℤ) := by
      have h' : j + 1 ≤ i := h_lt
      have h'' : ((j : ℤ) + 1) ≤ (i : ℤ) := by exact_mod_cast h'
      linarith
    have hge : (2 : ℤ) ≤ 3 * ((i : ℤ) - (j : ℤ)) - 1 := by linarith
    rw [abs_of_pos (by linarith)] at hB1
    linarith

theorem infinite_primes : {p : ℕ | Prime p}.Infinite := by
  have h_L_is_reg : ∀ (i : ℕ) (hp : Prime i), Language.IsRegular (@L i ⟨hp.ne_zero⟩) := by
    exact fun i hp => @L_n_regular i ⟨hp.ne_zero⟩
  have h_L_p'_not_reg : ¬Language.IsRegular L_p' := by rw [← L_p_eq_L_p']; exact L_p_not_regular
  by_contra h
  simp at h
  have hS : ∃ (S : Finset ℕ), ∀ p, p ∈ S ↔ Prime p := Set.Finite.exists_finset h
  rcases hS with ⟨S, hS_iff⟩
  let L_wrap (i : ℕ) : Language Bool := if hp : Prime i then @L i ⟨hp.ne_zero⟩ else 0
  have h_wrap_reg : ∀ i ∈ S, Language.IsRegular (L_wrap i) := by
    intro i _
    dsimp [L_wrap]
    split_ifs with hp
    · exact h_L_is_reg  i hp
    · exact IsRegular.zero
  have h_list_sum_mp : ∀ (l : List ℕ) (w : List Bool) (i : ℕ),
  i ∈ l → w ∈ L_wrap i → w ∈ (l.map L_wrap).sum := by
    intro l w i hi hw_i
    induction' l with head tail ih
    · contradiction
    · simp only [List.map_cons, List.sum_cons]
      simp only [List.mem_cons] at hi
      rcases hi with rfl | hi_tail
      · exact Or.inl hw_i
      · simp only [Language.mem_add]
        exact Or.inr (ih hi_tail)
  have h_list_sum_mpr : ∀ (l : List ℕ) (w : List Bool),
    w ∈ (l.map L_wrap).sum → ∃ i ∈ l, w ∈ L_wrap i := by
    intro l w 
    induction' l with head tail ih
    · intro hw
      contradiction
    · intro hw
      simp only [List.map_cons, List.sum_cons] at hw
      cases hw with
      | inl h_head =>
        use head
        exact ⟨by grind, h_head⟩
      | inr h_tail =>
        rcases ih h_tail with ⟨i, hi_tail, hw_i⟩
        use i
        exact ⟨by grind, hw_i⟩
  have h_sum_reg : Language.IsRegular (S.toList.map L_wrap).sum :=
    Language.IsRegular.finset_union S L_wrap h_wrap_reg 
  have h_L_p_eq_sum : L_p = (S.toList.map L_wrap).sum := by
    unfold L_p
    rw [L_p_eq_inf_union]
    ext w
    constructor
    · intro hw
      have h : w ∈ (⋃ p : ℕ, ⋃ hp : Prime p, (@L p ⟨hp.ne_zero⟩ : Set (List Bool))) := hw
      simp only [Set.mem_iUnion] at h
      obtain ⟨p, hp, hw_in_L⟩ := h
      have hi_mem_S : p ∈ S.toList := Finset.mem_toList.mpr ((hS_iff p).mpr hp)
      have hw_in_wrap : w ∈ L_wrap p := by
        show w ∈ if hp : Prime p then @L p ⟨hp.ne_zero⟩ else 0
        rw [dif_pos hp]
        exact hw_in_L
      exact h_list_sum_mp S.toList w p hi_mem_S hw_in_wrap
    · intro hw
      rcases h_list_sum_mpr S.toList w hw with ⟨i, hi_mem_S, hw_in_wrap⟩
      have hp : Prime i := (hS_iff i).mp (Finset.mem_toList.mp hi_mem_S)
      have hw_in_L : w ∈ @L i ⟨hp.ne_zero⟩ := by
        simp only [L_wrap, dif_pos hp] at hw_in_wrap
        exact hw_in_wrap
      show w ∈ (⋃ i : ℕ, ⋃ hp' : Prime i, (@L i ⟨hp'.ne_zero⟩ : Set (List Bool)))
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hp, hw_in_L⟩⟩
  have h_L_p_reg : Language.IsRegular L_p := h_L_p_eq_sum ▸ h_sum_reg
  have h_L_p'_reg : Language.IsRegular L_p' := L_p_eq_L_p' ▸ h_L_p_reg
  exact h_L_p'_not_reg h_L_p'_reg

