import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.RenameProdMapMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

section Factor

variable {R σ : Type*} [CommRing R] {w : σ → ℕ}

def weightSet (w : σ → ℕ) (p : MvPolynomial σ R) : Finset ℕ :=
  p.support.image (Finsupp.weight w)

theorem sum_weightSet_component (p : MvPolynomial σ R) :
    ∑ a ∈ weightSet w p, weightedHomogeneousComponent w a p = p := by
  classical
  ext d
  rw [coeff_sum]
  simp only [coeff_weightedHomogeneousComponent]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra hne
    apply h
    exact Finset.mem_image.mpr ⟨d, mem_support_iff.mpr (Ne.symm hne), rfl⟩

theorem mem_weightSet {p : MvPolynomial σ R} {a : ℕ} :
    a ∈ weightSet w p ↔ ∃ d ∈ p.support, Finsupp.weight w d = a := by
  unfold weightSet
  exact Finset.mem_image

theorem component_ne_zero_of_mem {p : MvPolynomial σ R} {a : ℕ} (ha : a ∈ weightSet w p) :
    weightedHomogeneousComponent w a p ≠ 0 := by
  classical
  obtain ⟨d, hd, rfl⟩ := mem_weightSet.mp ha
  intro h
  have := congrArg (coeff d) h
  rw [coeff_weightedHomogeneousComponent, if_pos rfl, coeff_zero] at this
  exact mem_support_iff.mp hd this

theorem component_mul_of_unique (p q : MvPolynomial σ R) (a b : ℕ)
    (h : ∀ a' ∈ weightSet w p, ∀ b' ∈ weightSet w q, a' + b' = a + b → a' = a ∧ b' = b) :
    weightedHomogeneousComponent w (a + b) (p * q) =
      weightedHomogeneousComponent w a p * weightedHomogeneousComponent w b q := by
  classical
  conv_lhs => rw [← sum_weightSet_component (w := w) p, ← sum_weightSet_component (w := w) q,
    Finset.sum_mul_sum]
  rw [map_sum]
  have hterm : ∀ a' ∈ weightSet w p, ∀ b' ∈ weightSet w q,
      weightedHomogeneousComponent w (a + b)
        (weightedHomogeneousComponent w a' p * weightedHomogeneousComponent w b' q) =
      if a' = a ∧ b' = b then weightedHomogeneousComponent w a p * weightedHomogeneousComponent w b q
        else 0 := by
    intro a' ha' b' hb'
    have hh := (weightedHomogeneousComponent_isWeightedHomogeneous (w := w) a' p).mul
      (weightedHomogeneousComponent_isWeightedHomogeneous (w := w) b' q)
    by_cases hs : a' + b' = a + b
    · obtain ⟨rfl, rfl⟩ := h a' ha' b' hb' hs
      rw [if_pos ⟨rfl, rfl⟩, hh.weightedHomogeneousComponent_same]
    · rw [hh.weightedHomogeneousComponent_ne _ (Ne.symm hs)]
      rw [if_neg]
      rintro ⟨rfl, rfl⟩
      exact hs rfl
  rw [Finset.sum_congr rfl fun a' ha' => map_sum _ _ _]
  rw [Finset.sum_congr rfl fun a' ha' => Finset.sum_congr rfl fun b' hb' => hterm a' ha' b' hb']
  by_cases ha : a ∈ weightSet w p
  · by_cases hb : b ∈ weightSet w q
    · rw [Finset.sum_eq_single a]
      · rw [Finset.sum_eq_single b]
        · rw [if_pos ⟨rfl, rfl⟩]
        · intro b' _ hb'
          rw [if_neg fun h => hb' h.2]
        · intro hb'
          exact absurd hb hb'
      · intro a' _ ha'
        exact Finset.sum_eq_zero fun b' _ => if_neg fun h => ha' h.1
      · intro ha'
        exact absurd ha ha'
    · have : weightedHomogeneousComponent w b q = 0 := by
        apply weightedHomogeneousComponent_eq_zero'
        intro d hd hdb
        exact hb (mem_weightSet.mpr ⟨d, hd, hdb⟩)
      rw [this, mul_zero]
      exact Finset.sum_eq_zero fun a' _ => Finset.sum_eq_zero fun b' _ => by
        split_ifs <;> simp
  · have : weightedHomogeneousComponent w a p = 0 := by
      apply weightedHomogeneousComponent_eq_zero'
      intro d hd hda
      exact ha (mem_weightSet.mpr ⟨d, hd, hda⟩)
    rw [this, zero_mul]
    exact Finset.sum_eq_zero fun a' _ => Finset.sum_eq_zero fun b' _ => by
      split_ifs <;> simp

theorem weightSet_nonempty {p : MvPolynomial σ R} (hp : p ≠ 0) : (weightSet w p).Nonempty := by
  classical
  obtain ⟨d, hd⟩ := Finset.nonempty_iff_ne_empty.mpr (mt MvPolynomial.support_eq_empty.mp hp)
  exact ⟨_, mem_weightSet.mpr ⟨d, hd, rfl⟩⟩

variable [IsDomain R]

theorem isWeightedHomogeneous_of_mul_left {p q : MvPolynomial σ R} {m : ℕ}
    (hpq : IsWeightedHomogeneous w (p * q) m) (hp : p ≠ 0) (hq : q ≠ 0) :
    ∃ a, IsWeightedHomogeneous w p a := by
  classical
  have hPn := weightSet_nonempty (w := w) hp
  have hQn := weightSet_nonempty (w := w) hq
  set A := (weightSet w p).max' hPn
  set a₀ := (weightSet w p).min' hPn
  set B := (weightSet w q).max' hQn
  set b₀ := (weightSet w q).min' hQn
  have htop : weightedHomogeneousComponent w (A + B) (p * q) ≠ 0 := by
    rw [component_mul_of_unique p q A B]
    · exact mul_ne_zero (component_ne_zero_of_mem (Finset.max'_mem _ _))
        (component_ne_zero_of_mem (Finset.max'_mem _ _))
    · intro a' ha' b' hb' hs
      have h1 := Finset.le_max' _ _ ha'
      have h2 := Finset.le_max' _ _ hb'
      constructor <;> omega
  have hbot : weightedHomogeneousComponent w (a₀ + b₀) (p * q) ≠ 0 := by
    rw [component_mul_of_unique p q a₀ b₀]
    · exact mul_ne_zero (component_ne_zero_of_mem (Finset.min'_mem _ _))
        (component_ne_zero_of_mem (Finset.min'_mem _ _))
    · intro a' ha' b' hb' hs
      have h1 := Finset.min'_le _ _ ha'
      have h2 := Finset.min'_le _ _ hb'
      constructor <;> omega
  have e1 : A + B = m := by
    by_contra hne
    exact htop (hpq.weightedHomogeneousComponent_ne _ hne)
  have e2 : a₀ + b₀ = m := by
    by_contra hne
    exact hbot (hpq.weightedHomogeneousComponent_ne _ hne)
  have hA : a₀ ≤ A := Finset.min'_le _ _ (Finset.max'_mem _ _)
  have hB : b₀ ≤ B := Finset.min'_le _ _ (Finset.max'_mem _ _)
  refine ⟨A, fun d hd => ?_⟩
  have hmem : Finsupp.weight w d ∈ weightSet w p := mem_weightSet.mpr ⟨d, mem_support_iff.mpr hd, rfl⟩
  have h1 := Finset.le_max' _ _ hmem
  have h2 := Finset.min'_le _ _ hmem
  show Finsupp.weight w d = A
  omega

end Factor

section Groups

variable {k n : ℕ}

def inGroup (i : Fin k) : Fin k × Fin n → ℕ := fun ij => if ij.1 = i then 1 else 0

theorem weight_groupWeight_apply (d : Fin k × Fin n →₀ ℕ) (i : Fin k) :
    Finsupp.weight (groupWeight k n) d i = Finsupp.weight (inGroup (n := n) i) d := by
  classical
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun ij _ => ?_
  simp only [groupWeight, inGroup, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  by_cases h : ij.1 = i
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h]

variable {R : Type*} [CommRing R]

theorem isMultiHomog_iff (δ : ℕ) (f : MvPolynomial (Fin k × Fin n) R) :
    IsMultiHomog δ f ↔ ∀ i : Fin k, IsWeightedHomogeneous (inGroup i) f δ := by
  constructor
  · intro h i d hd
    rw [← weight_groupWeight_apply, h hd]
  · intro h d hd
    funext i
    rw [weight_groupWeight_apply, h i hd]

theorem isWeightedHomogeneous_rename {σ τ : Type*} {e : σ → τ} (he : Function.Injective e)
    {w : σ → ℕ} {w' : τ → ℕ} (hw : ∀ x, w' (e x) = w x) {p : MvPolynomial σ R} {a : ℕ}
    (hp : IsWeightedHomogeneous w p a) : IsWeightedHomogeneous w' (rename e p) a := by
  classical
  intro d hd
  have hd' : d ∈ (rename e p).support := mem_support_iff.mpr hd
  rw [support_rename_of_injective he] at hd'
  obtain ⟨d₀, hd₀, rfl⟩ := Finset.mem_image.mp hd'
  have := hp (mem_support_iff.mp hd₀)
  rw [← this, Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum_mapDomain_index]
  · simp only [Finsupp.sum, hw]
  · intro _; simp
  · intro _ _ _; ring

variable {F : Type} [Field F]

theorem IsChowForm.degrees_eq {I : Ideal (MvPolynomial (Fin n) F)} {g : MvPolynomial (Fin k × Fin n) F}
    (hg : IsChowForm I k g) {a : Fin k → ℕ} (ha : ∀ i, IsWeightedHomogeneous (inGroup i) g (a i))
    (i j : Fin k) : a i = a j := by
  obtain ⟨c, hc2, hc⟩ := chowFormSwap F n k I g hg (Equiv.swap i j)
  have hc0 : c ≠ 0 := by rintro rfl; simp at hc2
  have h1 : IsWeightedHomogeneous (inGroup j) (rename (Prod.map (Equiv.swap i j) id) g) (a i) := by
    refine isWeightedHomogeneous_rename ((Equiv.swap i j).injective.prodMap Function.injective_id)
      (fun x => ?_) (ha i)
    simp only [inGroup, Prod.map_fst]
    by_cases h : x.1 = i
    · rw [if_pos h, if_pos (by rw [h, Equiv.swap_apply_left])]
    · rw [if_neg h, if_neg]
      intro h'
      apply h
      have := congrArg (Equiv.swap i j) h'
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
  rw [hc] at h1
  have h2 : IsWeightedHomogeneous (inGroup j) (C c * g) (a j) := (ha j).C_mul c
  exact h1.inj_right (mul_ne_zero (C_ne_zero.mpr hc0) hg.1) h2

end Groups

section Cycle

variable {k n : ℕ} {F : Type} [Field F]

theorem isWeightedHomogeneous_inGroup_of_dvd {f g : MvPolynomial (Fin k × Fin n) F} {δ : ℕ}
    (hf : IsMultiHomog δ f) (hf0 : f ≠ 0) (hgf : g ∣ f) (i : Fin k) :
    ∃ a, IsWeightedHomogeneous (inGroup i) g a := by
  obtain ⟨r, rfl⟩ := hgf
  exact isWeightedHomogeneous_of_mul_left ((isMultiHomog_iff δ _).mp hf i) (left_ne_zero_of_mul hf0)
    (right_ne_zero_of_mul hf0)

theorem exists_degrees_of_chowFormCycle (hk : 0 < k) (Z : ProjCycle F n) (c : F)
    (g : Ideal (MvPolynomial (Fin n) F) → MvPolynomial (Fin k × Fin n) F)
    (hg : ∀ W ∈ Z.support, IsChowForm W k (g W)) {δ : ℕ}
    (hf : IsMultiHomog δ (C c * ∏ W ∈ Z.support, g W ^ Z W)) (hf0 : C c * ∏ W ∈ Z.support, g W ^ Z W ≠ 0) :
    ∃ δW : Ideal (MvPolynomial (Fin n) F) → ℕ, (∀ W ∈ Z.support, IsMultiHomog (δW W) (g W)) ∧
      ∑ W ∈ Z.support, Z W * δW W = δ := by
  classical
  have hdeg : ∀ W ∈ Z.support, ∃ d, IsMultiHomog d (g W) := by
    intro W hW
    have hdvd : g W ∣ C c * ∏ W ∈ Z.support, g W ^ Z W := by
      apply Dvd.dvd.mul_left
      apply dvd_trans _ (Finset.dvd_prod_of_mem _ hW)
      exact dvd_pow_self _ (Finsupp.mem_support_iff.mp hW)
    have ha : ∀ i, ∃ a, IsWeightedHomogeneous (inGroup i) (g W) a := fun i =>
      isWeightedHomogeneous_inGroup_of_dvd hf hf0 hdvd i
    choose a ha using ha
    refine ⟨a ⟨0, hk⟩, (isMultiHomog_iff _ _).mpr fun i => ?_⟩
    rw [(hg W hW).degrees_eq ha ⟨0, hk⟩ i]
    exact ha i
  choose! δW hδW using hdeg
  refine ⟨δW, hδW, ?_⟩
  have hprod : IsMultiHomog (∑ W ∈ Z.support, Z W * δW W) (C c * ∏ W ∈ Z.support, g W ^ Z W) := by
    have h1 : IsWeightedHomogeneous (groupWeight k n) (∏ W ∈ Z.support, g W ^ Z W)
        (∑ W ∈ Z.support, Z W • fun _ : Fin k => δW W) :=
      IsWeightedHomogeneous.prod _ _ _ fun W hW => (hδW W hW).pow (Z W)
    have h2 := h1.C_mul c
    unfold IsMultiHomog
    convert h2 using 1
    funext i
    simp [Finset.sum_apply]
  have := hprod.inj_right hf0 hf
  exact congrFun this ⟨0, hk⟩

end Cycle

end

end GroundTheory.Heights₂.Heights
