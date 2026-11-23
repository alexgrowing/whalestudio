import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.DcoShape
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.EigBasis
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.VandSum
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.Mac
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.HlEval
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.GapDom
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.PsDimDecomp
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.IntegralConv
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.ThPMul

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H
open GroundTheory.Automorphic.HeckeAlgebra GroundTheory.Automorphic.Parabolic

noncomputable section

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}

private abbrev Wz (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
    (z : Fin n → ℂˣ) : Submodule ℂ (GL (Fin n) F → ℂ) :=
  principalSeriesSpace F n (paramChar F z)

private abbrev rz (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
    (z : Fin n → ℂˣ) : Representation ℂ (GL (Fin n) F) (Wz F z) :=
  principalSeries F n (paramChar F z)

private abbrev Vz (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}
    (z : Fin n → ℂˣ) : Submodule ℂ (Wz F z) :=
  fixedVectors (rz F z) (iwahori F n)

private theorem sm (z : Fin n → ℂˣ) (v : Wz F z) : v ∈ smoothVectors (rz F z) :=
  isSmooth_parabolicInd (F := F) (n := n) (β := (id : Fin n → Fin n)) (charRep (paramChar F z)) v

private def evy (z : Fin n → ℂˣ) (y : GL (Fin n) F) : Module.Dual ℂ (Wz F z) :=
  (LinearMap.proj y).comp (Wz F z).subtype

private theorem oneK_mem : oneK F n ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ :=
  indicator_mem_locallyConstantCompactSupport (isCompact_integralGL F n) (isOpen_integralGL F n) 1

private theorem oneK_left (k : GL (Fin n) F) (hk : k ∈ integralGL F n) (x : GL (Fin n) F) :
    oneK F n (k * x) = oneK F n x := by
  have : k * x ∈ (integralGL F n : Set (GL (Fin n) F)) ↔ x ∈ (integralGL F n : Set (GL (Fin n) F)) :=
    ⟨fun h => by simpa using mul_mem (inv_mem hk) h, fun h => mul_mem hk h⟩
  by_cases hx : x ∈ (integralGL F n : Set (GL (Fin n) F))
  · rw [oneK, Set.indicator_of_mem hx, Set.indicator_of_mem (this.2 hx)]; rfl
  · rw [oneK, Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (this.1 h))]

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure]

private def act (z : Fin n → ℂˣ) {φ : GL (Fin n) F → ℂ} (hφ : φ ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) :
    Module.End ℂ (Wz F z) where
  toFun := heckeAct μ (rz F z) φ
  map_add' v w := heckeAct_add_right hφ (sm z v) (sm z w)
  map_smul' c v := heckeAct_smul_right hφ c (sm z v)

private theorem evy_act (z : Fin n → ℂˣ) {φ : GL (Fin n) F → ℂ}
    (hφ : φ ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) (y : GL (Fin n) F) (w : Wz F z) :
    evy z y (heckeAct μ (rz F z) φ w) = ∫ g, φ g * (w : GL (Fin n) F → ℂ) (y * g) ∂μ := by
  rw [dual_heckeAct μ hφ (sm z w)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [evy, LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply,
    LinearMap.coe_proj, Function.eval]
  rw [coe_indRep_apply]

private theorem heckeAct_sum {ι : Type*} (z : Fin n → ℂˣ) (s : Finset ι) (c : ι → ℂ) (φ : ι → GL (Fin n) F → ℂ)
    (hφ : ∀ i ∈ s, φ i ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) (v : Wz F z) :
    heckeAct μ (rz F z) (∑ i ∈ s, c i • φ i) v = ∑ i ∈ s, c i • heckeAct μ (rz F z) (φ i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using heckeAct_zero_left (μ := μ) (sm z v)
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      heckeAct_add_left (Submodule.smul_mem _ _ (hφ i (Finset.mem_insert_self i s)))
        (Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (hφ j (Finset.mem_insert_of_mem hj))) (sm z v),
      heckeAct_smul_left _ (hφ i (Finset.mem_insert_self i s)) (sm z v),
      ih fun j hj => hφ j (Finset.mem_insert_of_mem hj)]

private theorem th_mem {a : Fin n → ℤ} (ha : Antitone a) :
    th μ a ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ :=
  Submodule.smul_mem _ _ (dcoShape F n a ha).2.2.1

private theorem th_left {a : Fin n → ℤ} (ha : Antitone a) (k : GL (Fin n) F) (hk : k ∈ iwahori F n)
    (x : GL (Fin n) F) : th μ a (k * x) = th μ a x := by
  simp only [th, Pi.smul_apply, ((dcoShape F n a ha).2.2.2 x k hk).1]

private theorem th_zero :
    th μ (0 : Fin n → ℤ) = idem μ (isCompact_iwahori F n) (isOpen_iwahori F n) := by
  funext g
  have hd : g ∈ dco F (0 : Fin n → ℤ) ↔ g ∈ iwahori F n := by
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      rw [torusPow_zero, mul_one]
      exact mul_mem hx hy
    · intro hg
      exact ⟨g, hg, 1, one_mem _, by rw [torusPow_zero]; simp⟩
  by_cases hg : g ∈ iwahori F n
  · rw [idem_apply_of_mem _ _ hg]
    simp only [th, Pi.smul_apply, uFn, smul_eq_mul]
    rw [Set.indicator_of_mem (hd.2 hg), halfModulus_zero]
    simp
  · rw [idem_apply_of_notMem _ _ hg]
    simp only [th, Pi.smul_apply, uFn, smul_eq_mul]
    rw [Set.indicator_of_notMem (fun h => hg (hd.1 h)), mul_zero]

private theorem ell_theta (hK : μ (integralGL F n : Set (GL (Fin n) F)) = 1) (z : Fin n → ℂˣ) {a : Fin n → ℤ} (ha : Antitone a) :
    (evy z 1 ∘ₗ act μ z (oneK_mem (F := F) (n := n)))
        (heckeAct μ (rz F z) (th μ a) (sphericalVector (isUnramified_paramChar (F := F) z))) =
      ∫ g, th μ a g * zonalSpherical μ z g ∂μ := by
  rw [dual_heckeAct μ (th_mem μ ha) (sm z _)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only
  congr 1
  have hr : μ.real (integralGL F n : Set (GL (Fin n) F)) = 1 := by simp [Measure.real, hK]
  rw [zonalSpherical, hr]
  simp only [LinearMap.comp_apply]
  change evy z 1 (heckeAct μ (rz F z) (oneK F n) _) = _
  rw [evy_act μ z oneK_mem]
  simp only [Complex.ofReal_one, inv_one, one_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  congr 1

private theorem oneK_act (z : Fin n → ℂˣ) (w : Wz F z) :
    heckeAct μ (rz F z) (oneK F n) w =
      (evy z 1 (heckeAct μ (rz F z) (oneK F n) w)) • sphericalVector (isUnramified_paramChar (F := F) z) :=
  eq_smul_sphericalVector (isUnramified_paramChar (F := F) z)
    (heckeAct_mem_fixedVectors oneK_mem (fun k hk x => oneK_left k hk x) (sm z w))

private theorem finrank_Vz (z : Fin n → ℂˣ) :
    FiniteDimensional ℂ (Vz F z) ∧ Module.finrank ℂ (Vz F z) ≤ n.factorial := by
  obtain ⟨h1, h2⟩ := psDim F n z
  let L : Vz F z →ₗ[ℂ] psI F z :=
    { toFun := fun w => ⟨((w : Wz F z) : GL (Fin n) F → ℂ), (w : Wz F z).2, fun g y hy => by
        have := congrFun (congrArg Subtype.val (w.2 y hy)) g
        rw [coe_indRep_apply] at this
        exact this⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hL : Function.Injective L := fun v w h =>
    Subtype.ext (Subtype.ext (congrArg (fun x : psI F z => (x : GL (Fin n) F → ℂ)) h))
  exact ⟨FiniteDimensional.of_injective L hL, (LinearMap.finrank_le_finrank_of_injective hL).trans h2⟩

private theorem alg1 (V A B M : ℂ) (hV : V ≠ 0) (hB : B ≠ 0) : V * (A / B / V * M) = A / B * M := by
  field_simp

private theorem alg2 (V A B : ℂ) (hV : V ≠ 0) (hB : B ≠ 0) : V * (A / B / V) * B = A := by
  field_simp

private theorem exists_eig (hK : μ (integralGL F n : Set (GL (Fin n) F)) = 1) (z : Fin n → ℂˣ)
    (hz : Function.Injective z)
    (hd : ∀ σ : Equiv.Perm (Fin n), evalAt (z ∘ σ) (dPol n ((qF F : ℂ))⁻¹) ≠ 0) :
    ∃ (b : Module.Basis (Equiv.Perm (Fin n)) ℂ (Vz F z)) (c : Equiv.Perm (Fin n) → ℂ),
      (∀ σ a, Antitone a → heckeAct μ (rz F z) (th μ a) (b σ : Wz F z) = monomialChar a (z ∘ σ) • (b σ : Wz F z)) ∧
      (∀ σ, heckeAct μ (rz F z) (oneK F n) (b σ : Wz F z) = sphericalVector (isUnramified_paramChar (F := F) z)) ∧
      (sphericalVector (isUnramified_paramChar (F := F) z) = ∑ σ, c σ • (b σ : Wz F z)) ∧
      (∀ σ, vPoly n ((qF F : ℂ))⁻¹ * c σ * evalAt (z ∘ σ) (dPol n 1) = evalAt (z ∘ σ) (dPol n ((qF F : ℂ))⁻¹)) := by
  classical
  have hχ := isUnramified_paramChar (F := F) z
  have hv : vPoly n ((qF F : ℂ))⁻¹ ≠ 0 := vPoly_ne_zero injective_qInv_pow n
  have hd1 : ∀ σ : Equiv.Perm (Fin n), evalAt (z ∘ σ) (dPol n 1) ≠ 0 := (hlEval n ((qF F : ℂ))⁻¹ z hz 0).1
  have hpres : ∀ a (ha : Antitone a), ∀ x ∈ Vz F z, act μ z (th_mem μ ha) x ∈ Vz F z := fun a ha x _ =>
    heckeAct_mem_fixedVectors (th_mem μ ha) (fun k hk y => th_left μ ha k hk y) (sm z x)
  let θ : (Fin n → ℤ) → Module.End ℂ (Vz F z) := fun a =>
    if ha : Antitone a then (act μ z (th_mem μ ha)).restrict (hpres a ha) else 0
  have hθ : ∀ a (ha : Antitone a) (x : Vz F z),
      ((θ a x : Vz F z) : Wz F z) = heckeAct μ (rz F z) (th μ a) x := by
    intro a ha x
    simp only [θ, dif_pos ha]
    rfl
  have h0 : θ 0 = 1 := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    rw [hθ 0 (fun _ _ _ => le_rfl), th_zero]
    exact heckeAct_idem_of_mem _ _ x.2
  have hadd : ∀ a b, Antitone a → Antitone b → θ (a + b) = θ a * θ b := by
    intro a b ha hb
    refine LinearMap.ext fun x => Subtype.ext ?_
    rw [Module.End.mul_apply, hθ (a + b) (ha.add hb), hθ a ha, hθ b hb, ← thMul F n μ a b ha hb,
      heckeAct_groupConv (th_mem μ ha) (th_mem μ hb) (sm z _)]
  let u : Vz F z := ⟨sphericalVector hχ, fun k hk =>
    sphericalVector_mem_fixedVectors hχ k (iwahori_le_integralGL F n hk)⟩
  let ℓ : Module.Dual ℂ (Vz F z) := (evy z 1 ∘ₗ act μ z (oneK_mem (F := F) (n := n))) ∘ₗ (Vz F z).subtype
  obtain ⟨hfd, hdim⟩ := finrank_Vz (F := F) z
  let c : Equiv.Perm (Fin n) → ℂ := fun σ =>
    evalAt (z ∘ σ) (dPol n ((qF F : ℂ))⁻¹) / evalAt (z ∘ σ) (dPol n 1) / vPoly n ((qF F : ℂ))⁻¹
  have hc : ∀ σ, c σ ≠ 0 := fun σ => div_ne_zero (div_ne_zero (hd σ) (hd1 σ)) hv
  have hu : ∀ a, Antitone a → ℓ (θ a u) = ∑ σ, c σ * monomialChar a (z ∘ σ) := by
    intro a ha
    have h1 : ℓ (θ a u) = ∫ g, th μ a g * zonalSpherical μ z g ∂μ := by
      rw [← ell_theta μ hK z ha]
      simp only [ℓ, LinearMap.comp_apply, Submodule.subtype_apply]
      rw [hθ a ha]
    have h2 := mac F n μ z a ha
    rw [(hlEval n ((qF F : ℂ))⁻¹ z hz a).2] at h2
    rw [h1]
    apply mul_left_cancel₀ hv
    rw [h2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    exact (alg1 _ _ _ _ hv (hd1 σ)).symm
  obtain ⟨b, hb1, hb2, hb3⟩ := eigBasis n (Vz F z) hdim θ h0 hadd u ℓ z c hz hc hu
  refine ⟨b, c, fun σ a ha => ?_, fun σ => ?_, ?_, fun σ => ?_⟩
  · rw [← hθ a ha, hb1 σ a ha]
    rfl
  · rw [oneK_act]
    have : evy z 1 (heckeAct μ (rz F z) (oneK F n) (b σ : Wz F z)) = 1 := hb2 σ
    rw [this, one_smul]
  · have := congrArg (Subtype.val) hb3
    simpa [u] using this
  · exact alg2 _ _ _ hv (hd1 σ)

private theorem anti_of_gap {ν : Fin n → ℤ} (h : Gap n ν) : Antitone ν := by
  intro i j hij
  rcases hij.eq_or_lt with rfl | hlt
  · exact le_rfl
  · have := h i j hlt
    omega

private theorem sand_terms_mem {ν₁ ν₂ : Fin n → ℤ} (h₁ : Gap n ν₁) (h₂ : Gap n ν₂) :
    ∀ S ∈ (pairs n).powerset, groupConv μ (th μ (ν₁ + eL S)) (groupConv μ (oneK F n) (th μ (ν₂ + eR S))) ∈
      locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ := fun S hS =>
  groupConv_mem μ (th_mem μ ((gapDom n ν₁ h₁).1 S hS).1)
    (groupConv_mem μ oneK_mem (th_mem μ ((gapDom n ν₂ h₂).1 S hS).2))

private theorem sand_mem {ν₁ ν₂ : Fin n → ℤ} (h₁ : Gap n ν₁) (h₂ : Gap n ν₂) :
    sand μ ν₁ ν₂ ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ :=
  Submodule.sum_mem _ fun S hS => Submodule.smul_mem _ _ (sand_terms_mem μ h₁ h₂ S hS)

private theorem dom_R {ν₁ ν₂ : Fin n → ℤ} (h₁ : Gap n ν₁) (h₂ : Gap n ν₂) (t : ℂ) :
    Dom (monomial (ν₁ + ν₂) * dPol n t) :=
  (gapDom n (ν₁ + ν₂) ((gapDom n ν₂ h₂).2.2 ν₁ (anti_of_gap h₁))).2.1 t

private theorem thP_act (z : Fin n → ℂˣ) (r : LaurentRing n) (hr : Dom r) (w : Fin n → ℂˣ) (x : Wz F z)
    (hx : ∀ a, Antitone a → heckeAct μ (rz F z) (th μ a) x = monomialChar a w • x) :
    heckeAct μ (rz F z) (thP μ r) x = evalAt w r • x := by
  have h1 : thP μ r = ∑ a ∈ r.coeff.support, r.coeff a • th μ a := rfl
  rw [h1, heckeAct_sum μ z _ _ _ (fun a ha => th_mem μ (hr a ha)) x, evalAt_apply, Finsupp.sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [hx a (hr a ha), smul_smul]

private theorem key (hK : μ (integralGL F n : Set (GL (Fin n) F)) = 1) {ν₁ ν₂ : Fin n → ℤ} (h₁ : Gap n ν₁) (h₂ : Gap n ν₂)
    (z : Fin n → ℂˣ) (hz : Function.Injective z)
    (hd : ∀ σ : Equiv.Perm (Fin n), evalAt (z ∘ σ) (dPol n ((qF F : ℂ))⁻¹) ≠ 0) (x : Vz F z) :
    vPoly n ((qF F : ℂ))⁻¹ • heckeAct μ (rz F z) (sand μ ν₁ ν₂) (x : Wz F z) =
      heckeAct μ (rz F z) (thP μ (monomial (ν₁ + ν₂) * dPol n ((qF F : ℂ))⁻¹)) (x : Wz F z) := by
  classical
  obtain ⟨b, c, e1, e2, e3, e4⟩ := exists_eig μ hK z hz hd
  set t : ℂ := ((qF F : ℂ))⁻¹ with ht
  have hR := dom_R (n := n) h₁ h₂ t
  have hRm := (thPMul F n μ _ _ hR hR).2.1
  let L₁ : Vz F z →ₗ[ℂ] Wz F z := (vPoly n t • act μ z (sand_mem μ h₁ h₂)) ∘ₗ (Vz F z).subtype
  let L₂ : Vz F z →ₗ[ℂ] Wz F z := act μ z hRm ∘ₗ (Vz F z).subtype
  have hL : L₁ = L₂ := b.ext fun τ => ?_
  · exact LinearMap.congr_fun hL x
  have hτ : ∀ S ∈ (pairs n).powerset,
      heckeAct μ (rz F z) (groupConv μ (th μ (ν₁ + eL S)) (groupConv μ (oneK F n) (th μ (ν₂ + eR S)))) (b τ : Wz F z) =
        ∑ σ, (monomialChar (ν₂ + eR S) (z ∘ τ) * c σ * monomialChar (ν₁ + eL S) (z ∘ σ)) • (b σ : Wz F z) := by
    intro S hS
    have a₁ := ((gapDom n ν₁ h₁).1 S hS).1
    have a₂ := ((gapDom n ν₂ h₂).1 S hS).2
    rw [heckeAct_groupConv (th_mem μ a₁) (groupConv_mem μ oneK_mem (th_mem μ a₂)) (sm z _),
      heckeAct_groupConv oneK_mem (th_mem μ a₂) (sm z _), e1 τ _ a₂,
      heckeAct_smul_right oneK_mem _ (sm z _), e2 τ, heckeAct_smul_right (th_mem μ a₁) _ (sm z _), e3]
    have hsum : heckeAct μ (rz F z) (th μ (ν₁ + eL S)) (∑ σ, c σ • (b σ : Wz F z)) =
        ∑ σ, (c σ * monomialChar (ν₁ + eL S) (z ∘ σ)) • (b σ : Wz F z) := by
      change act μ z (th_mem μ a₁) _ = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [map_smul]
      change c σ • heckeAct μ (rz F z) (th μ (ν₁ + eL S)) _ = _
      rw [e1 σ _ a₁, smul_smul]
    rw [hsum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [smul_smul, mul_assoc]
  change vPoly n t • heckeAct μ (rz F z) (sand μ ν₁ ν₂) (b τ : Wz F z) =
    heckeAct μ (rz F z) (thP μ (monomial (ν₁ + ν₂) * dPol n t)) (b τ : Wz F z)
  rw [thP_act μ z _ hR (z ∘ τ) _ (e1 τ), map_mul, show (monomial (ν₁ + ν₂) : LaurentRing n) = AddMonoidAlgebra.single (ν₁ + ν₂) 1 from rfl,
    evalAt_single, one_mul, sand, heckeAct_sum μ z _ _ _ (sand_terms_mem μ h₁ h₂)]
  rw [Finset.sum_congr rfl fun S hS => by rw [hτ S hS]]
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have hcol : ∀ σ, ∑ S ∈ (pairs n).powerset,
      (vPoly n t * (sgS S * (monomialChar (ν₂ + eR S) (z ∘ τ) * c σ * monomialChar (ν₁ + eL S) (z ∘ σ)))) =
      vPoly n t * c σ * monomialChar ν₁ (z ∘ σ) * monomialChar ν₂ (z ∘ τ) *
        (if σ = τ then evalAt (z ∘ σ) (dPol n 1) else 0) := by
    intro σ
    rw [← vandSum n z σ τ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [monomialChar_add, monomialChar_add]
    ring
  simp only [← Finset.sum_smul, hcol]
  rw [Finset.sum_eq_single τ]
  · rw [if_pos rfl, monomialChar_add]
    congr 1
    have := e4 τ
    rw [← this]
    ring
  · intro σ _ hσ
    rw [if_neg hσ, mul_zero, zero_smul]
  · simp

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.H.sandPS :
    ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)
      [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)] (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure], μ (integralGL F n : Set (GL (Fin n) F)) = 1 →
      ∀ ν₁ ν₂ : Fin n → ℤ, Gap n ν₁ → Gap n ν₂ → ∀ z : Fin n → ℂˣ, Function.Injective z →
      (∀ σ : Equiv.Perm (Fin n), evalAt (z ∘ σ) (dPol n ((qF F : ℂ))⁻¹) ≠ 0) → ∀ f ∈ psI F z,
        vPoly n ((qF F : ℂ))⁻¹ * ∫ g, sand μ ν₁ ν₂ g * f g ∂μ = ∫ g, thP μ (monomial (ν₁ + ν₂) * dPol n ((qF F : ℂ))⁻¹) g * f g ∂μ := by
  intro F _ _ _ _ n _ _ μ _ hK ν₁ ν₂ h₁ h₂ z hz hd f hf
  let w : Wz F z := ⟨f, hf.1⟩
  have hw : w ∈ Vz F z := fun y hy => Subtype.ext (funext fun g => by
    rw [coe_indRep_apply]
    exact hf.2 g y hy)
  have hR := dom_R (n := n) h₁ h₂ ((qF F : ℂ))⁻¹
  have hRm := (thPMul F n μ _ _ hR hR).2.1
  have h := congrArg (evy z 1) (key μ hK h₁ h₂ z hz hd ⟨w, hw⟩)
  rw [map_smul, evy_act μ z (sand_mem μ h₁ h₂), evy_act μ z hRm, smul_eq_mul] at h
  simpa only [one_mul] using h

end
