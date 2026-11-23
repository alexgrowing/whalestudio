import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSmallSectionMixed
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BirationalYPt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftNefBig
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPerturbSemipos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBirationalModelExists
import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsHorizontalOfDimOne
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PConeTrdeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 Filter Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace SmallSectionMixedAlt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isMultiHomog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

theorem isMultiHomog_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem isMultiHomog_sub {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f - g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_sub _ f g hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem isMultiHomog_C (r : ℤ) : IsMultiHomog (C r : MRing ι) 0 := by
  classical
  intro m hm k
  have : m = 0 := by
    by_contra h
    rw [mem_support_iff, coeff_C, if_neg (Ne.symm h)] at hm
    exact hm rfl
  simp [this]

theorem isMultiHomog_X [DecidableEq K] (p : Σ k, ι k) : IsMultiHomog (X p : MRing ι) (Pi.single p.1 1) := by
  classical
  intro m hm k
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  obtain ⟨k₀, i₀⟩ := p
  by_cases h : k = k₀
  · subst h
    simp [Finsupp.single_apply]
  · have : ∀ j : ι k, (⟨k₀, i₀⟩ : Σ k, ι k) ≠ ⟨k, j⟩ := fun j e => h (congrArg Sigma.fst e).symm
    simp [h]

theorem isMultiHomog_coordProd (c : ∀ k, ι k) (d : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k) d := by
  classical
  have key : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRing ι) ^ d k)
      (∑ k ∈ s, d k • Pi.single k 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using isMultiHomog_C (ι := ι) 1
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      refine isMultiHomog_mul ?_ ih
      induction d k with
      | zero => simpa using isMultiHomog_C (ι := ι) 1
      | succ j hj =>
        rw [pow_succ, succ_nsmul]
        exact isMultiHomog_mul hj (isMultiHomog_X ⟨k, c k⟩)
  have e : (∑ k, d k • (Pi.single k 1 : K → ℕ)) = d := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have := key Finset.univ
  rwa [e] at this

theorem aeval_coordProd {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (d : K → ℕ) :
    aeval y (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k) = ∏ k, y ⟨k, c k⟩ ^ d k := by
  simp [map_prod]

theorem aeval_eq_zero_of_mem {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) {f : MRing ι}
    (hf : f ∈ mCoordIdeal y) : aeval y f = 0 := by
  have h1 : (aeval (fun _ : K => (1 : Ω))).toRingHom.comp (mConeMap y).toRingHom =
      (aeval y : MRing ι →ₐ[ℤ] Ω).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => by simp) (fun v => by simp [mConeMap])
  have h2 := congrArg (fun φ : MRing ι →+* Ω => φ f) h1
  have h3 : mConeMap y f = 0 := RingHom.mem_ker.mp hf
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h3, map_zero] at h2
  rw [← h2]

theorem mem_of_aeval_eq_zero {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) {f : MRing ι} {d : K → ℕ}
    (hf : IsMultiHomog f d) (h : aeval y f = 0) : f ∈ mCoordIdeal y := by
  rw [mCoordIdeal, RingHom.mem_ker, GroundTheory.Heights₂.Heights.ConeTrdeg.mConeMap_of_isMultiHomog y hf, h, C_0,
    zero_mul]

theorem coord_ne_zero {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) {p : Σ k, ι k}
    (hp : (X p : MRing ι) ∉ mCoordIdeal y) : y p ≠ 0 := by
  classical
  intro h
  exact hp (mem_of_aeval_eq_zero y (isMultiHomog_X p) (by rw [aeval_X, h]))

theorem exists_form_of_mem_chartRingZ {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {x : Ω} (hx : x ∈ chartRingZ y c) :
    ∃ (δ : K → ℕ) (e : MRing ι), IsMultiHomog e δ ∧ aeval y e = x * ∏ k, y ⟨k, c k⟩ ^ δ k := by
  classical
  have hpow : ∀ δ₁ δ₂ : K → ℕ, ∏ k, y ⟨k, c k⟩ ^ (δ₁ + δ₂) k =
      (∏ k, y ⟨k, c k⟩ ^ δ₁ k) * ∏ k, y ⟨k, c k⟩ ^ δ₂ k := fun δ₁ δ₂ => by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => by rw [Pi.add_apply, pow_add]
  rw [chartRingZ] at hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    refine ⟨Pi.single p.1 1, X p, isMultiHomog_X p, ?_⟩
    have h1 : ∏ k, y ⟨k, c k⟩ ^ (Pi.single p.1 1 : K → ℕ) k = y ⟨p.1, c p.1⟩ := by
      rw [Finset.prod_eq_single p.1 (fun k _ hk => by simp [hk])
        (fun h => absurd (Finset.mem_univ _) h)]
      simp
    rw [aeval_X, h1, div_mul_cancel₀ _ (hc p.1)]
  | algebraMap r =>
    exact ⟨0, C r, isMultiHomog_C r, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨δ₁, e₁, h₁, v₁⟩ := hx
    obtain ⟨δ₂, e₂, h₂, v₂⟩ := hz
    have hA : IsMultiHomog (e₁ * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ δ₂ k) (δ₁ + δ₂) :=
      isMultiHomog_mul h₁ (isMultiHomog_coordProd c δ₂)
    have hB' : IsMultiHomog (e₂ * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ δ₁ k) (δ₂ + δ₁) :=
      isMultiHomog_mul h₂ (isMultiHomog_coordProd c δ₁)
    rw [add_comm δ₂ δ₁] at hB'
    refine ⟨δ₁ + δ₂, e₁ * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ δ₂ k + e₂ * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ δ₁ k,
      isMultiHomog_add hA hB', ?_⟩
    · rw [map_add, map_mul, map_mul, v₁, v₂, aeval_coordProd, aeval_coordProd, hpow]
      ring
  | mul x z _ _ hx hz =>
    obtain ⟨δ₁, e₁, h₁, v₁⟩ := hx
    obtain ⟨δ₂, e₂, h₂, v₂⟩ := hz
    refine ⟨δ₁ + δ₂, e₁ * e₂, isMultiHomog_mul h₁ h₂, ?_⟩
    rw [map_mul, v₁, v₂, hpow]
    ring

theorem exists_chartForm {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (a : K → ℤ) (τ : ℕ) {s : Ω}
    (hs : s ∈ chartLat y a τ) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ∃ (d δ : K → ℕ) (e : MRing ι), IsMultiHomog e δ ∧ (∀ k, (δ k : ℤ) = τ * a k + d k) ∧
      aeval y e = s * ∏ k, y ⟨k, c k⟩ ^ d k := by
  obtain ⟨δ', e', he', hv'⟩ := exists_form_of_mem_chartRingZ y c hc (hs c hc)
  obtain ⟨ex, hexk⟩ : ∃ ex : K → ℕ, ∀ k, (ex k : ℤ) = (τ : ℤ) * a k + ((τ : ℤ) * a k).natAbs :=
    ⟨fun k => ((τ : ℤ) * a k + ((τ : ℤ) * a k).natAbs).toNat, fun k =>
      Int.toNat_of_nonneg (by have := Int.le_natAbs (a := -((τ : ℤ) * a k)); rw [Int.natAbs_neg] at this; omega)⟩
  refine ⟨fun k => δ' k + ((τ : ℤ) * a k).natAbs, δ' + ex, e' * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ ex k,
    isMultiHomog_mul he' (isMultiHomog_coordProd c ex), fun k => ?_, ?_⟩
  · simp only [Pi.add_apply, Nat.cast_add, hexk k]
    ring
  · rw [map_mul, hv', aeval_coordProd, mul_assoc, mul_assoc, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    have h0 := hc k
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ h0, ← zpow_add₀ h0, hexk k]
    congr 1
    push_cast
    ring

theorem divCycle_apply_of_mem {P W : Ideal (MRing ι)} {s : MRing ι} (h : W ∈ divSupp P s) :
    divCycle P s W = multAt (P ⊔ Ideal.span {s}) W := by
  classical
  simp only [divCycle, Finsupp.ofSupportFinite_coe]
  rw [if_pos h]

theorem divCycle_apply_of_not_mem {P W : Ideal (MRing ι)} {s : MRing ι} (h : W ∉ divSupp P s) :
    divCycle P s W = 0 := by
  classical
  simp only [divCycle, Finsupp.ofSupportFinite_coe]
  rw [if_neg h]

theorem divCycle_congr {P : Ideal (MRing ι)} {a b : MRing ι}
    (h : P ⊔ Ideal.span {a} = P ⊔ Ideal.span {b}) : divCycle P a = divCycle P b := by
  have hS : divSupp P a = divSupp P b := by
    ext W
    simp only [divSupp, h]
  ext W
  by_cases hW : W ∈ divSupp P a
  · rw [divCycle_apply_of_mem hW, divCycle_apply_of_mem (hS ▸ hW), h]
  · rw [divCycle_apply_of_not_mem hW, divCycle_apply_of_not_mem (hS ▸ hW)]

theorem sup_span_eq_of_sub_mem {P : Ideal (MRing ι)} {a b : MRing ι} (h : a - b ∈ P) :
    P ⊔ Ideal.span {a} = P ⊔ Ideal.span {b} := by
  apply le_antisymm <;> refine sup_le le_sup_left ?_ <;> rw [Ideal.span_singleton_le_iff_mem]
  · rw [show a = (a - b) + b by ring]
    exact Ideal.add_mem _ (Ideal.mem_sup_left h) (Ideal.mem_sup_right (Ideal.mem_span_singleton_self b))
  · rw [show b = -(a - b) + a by ring]
    exact Ideal.add_mem _ (Ideal.mem_sup_left (P.neg_mem h))
      (Ideal.mem_sup_right (Ideal.mem_span_singleton_self a))

theorem divCycle_le_of_chartLat {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} (hP : (mCoordIdeal y).IsPrime)
    {a : K → ℤ} {n : ℕ} {s : Ω} (hs : s ∈ chartLat y a n) (hs0 : s ≠ 0) {f g : MRing ι} {α β : K → ℕ}
    (hf : IsMultiHomog f α) (hg : IsMultiHomog g β) (hαβ : ∀ k, (α k : ℤ) = β k + n * a k)
    (hfg : aeval y f = s * aeval y g) (hg0 : aeval y g ≠ 0) :
    divCycle (mCoordIdeal y) g ≤ divCycle (mCoordIdeal y) f := by
  classical
  rw [Finsupp.le_iff]
  intro W _
  by_cases hW : W ∈ divSupp (mCoordIdeal y) g
  swap
  · rw [divCycle_apply_of_not_mem hW]
    exact Nat.zero_le _
  have hWp : W.IsPrime := hW.1.1.1
  have hPW : mCoordIdeal y ≤ W := le_sup_left.trans hW.1.1.2
  choose c' hc' using hW.2
  have hy' : ∀ k, y ⟨k, c' k⟩ ≠ 0 := fun k => coord_ne_zero y fun h => hc' k (hPW h)
  obtain ⟨d', δ', e', he', hδ', hv'⟩ := exists_chartForm y a n hs c' hy'
  obtain ⟨X', hX', hyX, hXW⟩ : ∃ X' : MRing ι, IsMultiHomog X' d' ∧ aeval y X' = ∏ k, y ⟨k, c' k⟩ ^ d' k ∧
      X' ∉ W := by
    refine ⟨∏ k, (X ⟨k, c' k⟩ : MRing ι) ^ d' k, isMultiHomog_coordProd c' d', aeval_coordProd y c' d', ?_⟩
    intro h
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hWp)).mp h
    exact hc' k (hWp.mem_of_pow_mem _ hk)
  have hyX0 : aeval y X' ≠ 0 := by
    rw [hyX]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hy' k)
  have hdeg : β + δ' = α + d' := by
    funext k
    have h1 := hαβ k
    have h2 := hδ' k
    simp only [Pi.add_apply]
    omega
  have hmem : f * X' - g * e' ∈ mCoordIdeal y := by
    refine mem_of_aeval_eq_zero y (isMultiHomog_sub (isMultiHomog_mul hf hX') ?_) ?_
    · rw [← hdeg]
      exact isMultiHomog_mul hg he'
    · rw [map_sub, map_mul, map_mul, hfg, hv', hyX]
      ring
  have hnot : ∀ t : MRing ι, aeval y t ≠ 0 → t ∉ mCoordIdeal y := fun t ht h =>
    ht (aeval_eq_zero_of_mem y h)
  have hf0 : aeval y f ≠ 0 := by rw [hfg]; exact mul_ne_zero hs0 hg0
  have he0 : aeval y e' ≠ 0 := by
    rw [hv']
    exact mul_ne_zero hs0 (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hy' k))
  have key := divCycle_congr (sup_span_eq_of_sub_mem hmem)
  rw [GroundTheory.Heights₂.Heights.Inter.divCycle_mul' hP (hnot f hf0) (hnot X' hyX0),
    GroundTheory.Heights₂.Heights.Inter.divCycle_mul' hP (hnot g hg0) (hnot e' he0)] at key
  have hW' := congrArg (fun F : Ideal (MRing ι) →₀ ℕ => F W) key
  simp only [Finsupp.add_apply] at hW'
  have hX0 : divCycle (mCoordIdeal y) X' W = 0 :=
    divCycle_apply_of_not_mem fun h => hXW (h.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  omega

theorem isSemipositiveRel_zcomb {P0 P : Ideal (MRing ι)} {M H : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hM : IsSemipositiveRel P0 P M)
    (hH : IsSemipositiveRel P0 P H) (m n : ℕ) : IsSemipositiveRel P0 P (HermLine.zcomb M H m n) := by
  open PerturbedSemipositivity in
  have hfun : (HermLine.zcomb M H m n).h = fun y => M.h y ^ m * H.h y ^ n := by
    funext y
    simp [HermLine.zcomb]
  refine ⟨?_, fun z hz w hw => ?_⟩
  · have hMs : IsSmoothHerm M := hM.1
    have hHs : IsSmoothHerm H := hH.1
    unfold IsSmoothHerm at hMs hHs ⊢
    rw [hfun]
    exact (hMs.pow m).mul (hHs.pow n)
  · have hz' := hz.1
    have hev : (fun y => Real.log ((HermLine.zcomb M H m n).h y)) =ᶠ[𝓝 z]
        fun y => (m : ℝ) * Real.log (M.h y) + (n : ℝ) * Real.log (H.h y) := by
      filter_upwards [PerturbedSemipositivity.blocks_mem_nhds hz'] with y hy
      rw [hfun, Real.log_mul (pow_ne_zero _ (M.pos y hy).ne') (pow_ne_zero _ (H.pos y hy).ne'),
        Real.log_pow, Real.log_pow]
    have hfM := PerturbedSemipositivity.contDiffAt_log_h M hM.1 hz'
    have hfH := PerturbedSemipositivity.contDiffAt_log_h H hH.1 hz'
    have hadd := ReciprocityTheory.AnForm.levi_add_smul (f := fun y => (m : ℝ) * Real.log (M.h y))
      (g := fun y => Real.log (H.h y)) (n : ℝ) (contDiffAt_const.mul hfM) hfH w
    beta_reduce at hadd
    have h1 : 0 ≤ leviForm (fun y => Real.log (M.h y)) z w := hM.2 z hz w hw
    have h2 : 0 ≤ leviForm (fun y => Real.log (H.h y)) z w := hH.2 z hz w hw
    change 0 ≤ ReciprocityTheory.AnForm.levi _ z w
    rw [ReciprocityTheory.AnForm.levi_congr hev, hadd, PerturbedSemipositivity.levi_const_mul (m : ℝ) hfM w]
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg m) h1) (mul_nonneg (Nat.cast_nonneg n) h2)

theorem isNefBigDatum_zcomb (hD : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement)
    (hB : NefPlusAmpleDegree.Statement) {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {D : ℕ}
    {P0 : Ideal (MRing ι)} {M H : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {q p : ℕ} (hP : IsArithVar (mCoordIdeal y) (D + 1))
    (hP0 : P0 ≤ mCoordIdeal y) (hMs : IsSemipositiveRel P0 (mCoordIdeal y) M)
    (hMn : NefOnFibres (mCoordIdeal y) M.a) (hMc : IsConjInvariantH M) (hHa : H.a = fun _ => (1 : ℤ))
    (hHs : IsSemipositiveRel P0 (mCoordIdeal y) H) (hHc : IsConjInvariantH H) (hp : 1 ≤ p) :
    IsNefBigDatum P0 y D (HermLine.zcomb M H q p) := by
  refine ⟨hP0, isSemipositiveRel_zcomb hMs hHs q p, HermLine.zcomb_isConjInvariantH hMc hHc _ _, ?_, ?_⟩
  · have ha : (HermLine.zcomb M H q p).a = (q : ℤ) • M.a + (p : ℤ) • H.a := rfl
    intro W hW hPW hch hdim
    rw [ha, ShiftedNefBig.geoNum_one_add]
    refine add_nonneg (mul_nonneg (Nat.cast_nonneg q) (hMn W hW hPW hch hdim)) ?_
    exact ProjLine.nefOnFibres_of_nonneg _ _ (fun k => by rw [hHa]; simp) W hW hPW hch hdim
  · have hs' := isSemipositiveRel_zcomb hMs hHs q (p - 1)
    have hnef := nefOnGenericDeg_of_semipos NefOnGenericOfSemipos.proof hD hP0 hs'
    have h := hB K ι (mCoordIdeal y) D _ hP hnef 1
    convert h using 2
    funext k
    simp only [HermLine.zcomb, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, hHa, Nat.cast_one,
      one_mul]
    rw [Nat.cast_sub hp]
    ring

end SmallSectionMixedAlt

open SmallSectionMixedAlt in

theorem SmallSectionMixed.proof (hG4 : G4.Statement) (hG41 : ArithmeticVolumeDimensionOne.Statement)
    (hD : GroundTheory.Heights₂.Heights.Inter.DegreeGeneric.Statement) (hB : NefPlusAmpleDegree.Statement) :
    SmallSectionMixed.Statement := by
  intro K _ ι _ P P0 d M H p q II hII hd hP hP0 hMs hMn hMc hHa hHs hHm hHc hp htop
  obtain ⟨Ω, _, y, rfl, hbir⟩ := BirationalModelExists.proof K ι P d hP
  have hinj : Function.Injective (algebraMap ℤ Ω) := by
    rw [injective_iff_map_eq_zero]
    intro m hm
    have hmem : (C m : MRing ι) ∈ mCoordIdeal y := by
      rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_C, MvPolynomial.algebraMap_apply, hm, map_zero]
    have h2 : m ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := hmem
    rw [show (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥ from hP.2.2.1] at h2
    exact (Ideal.mem_bot).1 h2
  have : CharZero Ω := charZero_of_injective_algebraMap hinj
  set N := HermLine.zcomb M H (q : ℤ) (p : ℤ) with hNdef
  obtain ⟨n, s, hn, hsL, hs0, c, hc, hbd⟩ : ∃ (n : ℕ) (s : Ω), 1 ≤ n ∧ s ∈ chartLat y N.a n ∧ s ≠ 0 ∧
      ∃ c : ℝ, c < 1 ∧ IsBoundedH (mCoordIdeal y) y N n c s := by
    obtain ⟨D, rfl⟩ : ∃ D, d = D + 1 := ⟨d - 1, by omega⟩
    have hN := isNefBigDatum_zcomb hD hB hP hP0 hMs hMn hMc hHa hHs hHc hp (q := q)
    rcases Nat.eq_zero_or_pos D with h0 | h0
    · subst h0
      exact hG41 K ι Ω y N P0 II hII hP hbir hN htop
    · exact hG4 K ι Ω y D N P0 II h0 hII hP hbir hN htop
  choose c0 hc0 using hP.2.1.2.2
  have hy0 : ∀ k, y ⟨k, c0 k⟩ ≠ 0 := fun k => coord_ne_zero y (hc0 k)
  obtain ⟨d0, δ0, e0, he0, hδ0, hv0⟩ := exists_chartForm y N.a n hsL c0 hy0
  have hg0 : aeval y (∏ k, (X ⟨k, c0 k⟩ : MRing ι) ^ d0 k) ≠ 0 := by
    rw [aeval_coordProd]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hy0 k)
  have hfg : aeval y e0 = s * aeval y (∏ k, (X ⟨k, c0 k⟩ : MRing ι) ^ d0 k) := by
    rw [aeval_coordProd, hv0]
  have hdeg : ∀ k, (δ0 k : ℤ) = d0 k + n * N.a k := fun k => by rw [hδ0 k]; ring
  refine ⟨n, e0, ∏ k, (X ⟨k, c0 k⟩ : MRing ι) ^ d0 k, hn, ⟨δ0, d0, he0, isMultiHomog_coordProd c0 d0, ?_, ?_, ?_⟩,
    divCycle_le_of_chartLat hP.2.1.1 hsL hs0 he0 (isMultiHomog_coordProd c0 d0) hdeg hfg hg0, ?_⟩
  · exact fun h => (by rw [hfg]; exact mul_ne_zero hs0 hg0 : aeval y e0 ≠ 0) (aeval_eq_zero_of_mem y h)
  · exact fun h => hg0 (aeval_eq_zero_of_mem y h)
  · intro k
    rw [hδ0 k]
    simp only [hNdef, HermLine.zcomb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  · intro z hz
    have h1 := hbd δ0 d0 e0 _ z he0 (isMultiHomog_coordProd c0 d0) hdeg hfg hz
    have hh : (HermLine.zcomb M H ((n * q : ℕ) : ℤ) ((n * p : ℕ) : ℤ)).h z = N.h z ^ n := by
      simp only [hNdef, HermLine.zcomb, zpow_natCast]
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm q n, mul_comm p n]
    rw [hh]
    have hX : 0 ≤ ‖eval z (map (Int.castRingHom ℂ) (∏ k, (X ⟨k, c0 k⟩ : MRing ι) ^ d0 k))‖ * N.h z ^ n :=
      mul_nonneg (norm_nonneg _) (pow_nonneg (N.pos z hz.1).le n)
    rw [mul_assoc] at h1
    nlinarith

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
