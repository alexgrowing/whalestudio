import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFiniteAlgebraJacobsonRadical
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitOneAddJacobsonTensor
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.FirstApprox

private theorem tensorProduct_congr_refl_pow_tmul_lemma {O O' κ : Type} [CommRing O] [CommRing O']
    [Algebra O O'] [CommRing κ] [Algebra O κ] (τ : O' ≃ₐ[O] O') (j : ℕ) (k : κ) (x : O') :
    (Algebra.TensorProduct.congr (AlgEquiv.refl : κ ≃ₐ[κ] κ) τ ^ j) (k ⊗ₜ[O] x) =
      k ⊗ₜ[O] (τ ^ j) x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', AlgEquiv.mul_apply, ih, pow_succ', AlgEquiv.mul_apply,
      Algebra.TensorProduct.congr_apply]
    exact Algebra.TensorProduct.map_tmul ..

theorem res_fixed (O O' κ : Type) [CommRing O] [CommRing O'] [Algebra O O'] [CommRing κ] [Algebra O κ] (ℓ : ℕ) (τ : O' ≃ₐ[O] O') (hs : Function.Surjective (algebraMap O κ)) (hℓ : 0 < ℓ) (hτ : τ ^ ℓ = 1) (hfix : ∀ z : O', τ z = z → z ∈ Set.range (algebraMap O O')) (htr : ∃ a : O', ∑ j ∈ Finset.range ℓ, (τ ^ j) a = 1) (z : κ ⊗[O] O') (hz : Algebra.TensorProduct.congr (AlgEquiv.refl : κ ≃ₐ[κ] κ) τ z = z) : z ∈ Set.range (algebraMap κ (κ ⊗[O] O')) := by
  obtain ⟨a, ha⟩ := htr
  obtain ⟨σ, hσ⟩ : ∃ σ : κ ⊗[O] O' ≃ₐ[κ] κ ⊗[O] O',
      σ = Algebra.TensorProduct.congr (AlgEquiv.refl : κ ≃ₐ[κ] κ) τ := ⟨_, rfl⟩
  rw [← hσ] at hz
  have hpow : ∀ (j : ℕ) (k : κ) (x : O'), (σ ^ j) (k ⊗ₜ[O] x) = k ⊗ₜ[O] (τ ^ j) x := by
    intro j k x
    rw [hσ]
    exact tensorProduct_congr_refl_pow_tmul_lemma τ j k x
  have hzfix : ∀ j : ℕ, (σ ^ j) z = z := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', AlgEquiv.mul_apply, ih, hz]
  have htrace : ∀ t : κ ⊗[O] O',
      ∑ j ∈ Finset.range ℓ, (σ ^ j) t ∈ Set.range (algebraMap κ (κ ⊗[O] O')) := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul k x =>
      have hfx : τ (∑ j ∈ Finset.range ℓ, (τ ^ j) x) = ∑ j ∈ Finset.range ℓ, (τ ^ j) x := by
        rw [map_sum]
        have e := (Finset.sum_range_succ' (fun j => (τ ^ j) x) ℓ).symm.trans
          (Finset.sum_range_succ (fun j => (τ ^ j) x) ℓ)
        rw [hτ, pow_zero] at e
        rw [← add_right_cancel e]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [pow_succ', AlgEquiv.mul_apply]
      obtain ⟨c, hc⟩ := hfix _ hfx
      refine ⟨c • k, ?_⟩
      simp only [hpow]
      rw [← TensorProduct.tmul_sum, ← hc, Algebra.algebraMap_eq_smul_one (A := O') c,
        ← TensorProduct.smul_tmul, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply]
    | add t₁ t₂ h₁ h₂ =>
      obtain ⟨u₁, hu₁⟩ := h₁
      obtain ⟨u₂, hu₂⟩ := h₂
      exact ⟨u₁ + u₂, by simp only [map_add, Finset.sum_add_distrib, hu₁, hu₂]⟩
  have key : ∑ j ∈ Finset.range ℓ, (σ ^ j) ((1 ⊗ₜ[O] a) * z) = z := by
    simp only [map_mul, hpow, hzfix]
    rw [← Finset.sum_mul, ← TensorProduct.tmul_sum, ha, ← Algebra.TensorProduct.one_def, one_mul]
  rw [← key]
  exact htrace _

theorem res_compare (O O' R κ A : Type) [CommRing O] [CommRing O'] [Algebra O O'] [CommRing R] [Algebra O R] [CommRing κ] [Algebra O κ] [CommRing A] [Algebra O A] [Algebra κ A] [IsScalarTower O κ A] (π : R →ₐ[O] A) (hπ : Function.Surjective π) : ∃ ψ : O' ⊗[O] R →+* (κ ⊗[O] O') ⊗[κ] A, Function.Surjective ψ ∧ RingHom.ker ψ ≤ Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) (RingHom.ker π) ∧ (∀ x : R, ψ ((Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) x) = Algebra.TensorProduct.includeRight (π x)) ∧ ∀ (f : O' →ₐ[O] O') (s : O' ⊗[O] R), ψ (Algebra.TensorProduct.map f (AlgHom.id O R) s) = Algebra.TensorProduct.map (Algebra.TensorProduct.map (AlgHom.id κ κ) f) (AlgHom.id κ A) (ψ s) := by
  let ψ : O' ⊗[O] R →+* (κ ⊗[O] O') ⊗[κ] A :=
    (((Algebra.TensorProduct.comm κ A (κ ⊗[O] O') :
        A ⊗[κ] (κ ⊗[O] O') →+* (κ ⊗[O] O') ⊗[κ] A).comp
      ((Algebra.TensorProduct.cancelBaseChange O κ κ A O').symm :
        A ⊗[O] O' →+* A ⊗[κ] (κ ⊗[O] O'))).comp
      (Algebra.TensorProduct.comm O O' A : O' ⊗[O] A →+* A ⊗[O] O')).comp
      (Algebra.TensorProduct.map (AlgHom.id O O') π : O' ⊗[O] R →+* O' ⊗[O] A)
  have hψ : ∀ t, ψ t = Algebra.TensorProduct.comm κ A (κ ⊗[O] O')
      ((Algebra.TensorProduct.cancelBaseChange O κ κ A O').symm
        (Algebra.TensorProduct.comm O O' A (Algebra.TensorProduct.map (AlgHom.id O O') π t))) :=
    fun t => rfl
  have hψt : ∀ (x : O') (r : R), ψ (x ⊗ₜ[O] r) = (1 ⊗ₜ[O] x) ⊗ₜ[κ] π r := by
    intro x r
    rw [hψ, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.comm_tmul,
      Algebra.TensorProduct.cancelBaseChange_symm_tmul, Algebra.TensorProduct.comm_tmul]
  refine ⟨ψ, ?_, ?_, ?_, ?_⟩
  · intro w
    obtain ⟨t, ht⟩ := Algebra.TensorProduct.map_surjective (AlgHom.id O O') π Function.surjective_id hπ
      ((Algebra.TensorProduct.comm O O' A).symm ((Algebra.TensorProduct.cancelBaseChange O κ κ A O')
        ((Algebra.TensorProduct.comm κ A (κ ⊗[O] O')).symm w)))
    refine ⟨t, ?_⟩
    rw [hψ, ht]
    simp only [AlgEquiv.apply_symm_apply, AlgEquiv.symm_apply_apply]
  · intro t ht
    have hm : Algebra.TensorProduct.map (AlgHom.id O O') π t = 0 := by
      rw [RingHom.mem_ker, hψ] at ht
      simpa using ht
    have hker : RingHom.ker (Algebra.TensorProduct.map (AlgHom.id O O') π) =
        Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) (RingHom.ker π) := by
      rw [Algebra.TensorProduct.map_ker _ _ Function.surjective_id hπ,
        (RingHom.injective_iff_ker_eq_bot (AlgHom.id O O')).mp Function.injective_id, Ideal.map_bot,
        bot_sup_eq]
    rw [← hker]
    exact hm
  · intro x
    simp only [Algebra.TensorProduct.includeRight_apply, hψt, ← Algebra.TensorProduct.one_def]
  · intro f s
    induction s using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x r => simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hψt]
    | add x y hx hy => simp only [map_add, hx, hy]

theorem main : PositivityTheory.Rg.Tf.Loc.N1 → ∀ (O O' R : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Finite (IsLocalRing.ResidueField O)] [CommRing O'] [Algebra O O'] [Module.Finite O O'] [Module.Free O O'] [CommRing R] [Algebra O R] [Module.Finite O R] (ℓ : ℕ) (τ : O' ≃ₐ[O] O'), 0 < ℓ → τ ^ ℓ = 1 → (∀ z : O', τ z = z → z ∈ Set.range (algebraMap O O')) → (∃ x y : Fin ℓ → O', ∀ j < ℓ, ∑ i, x i * (τ ^ j) (y i) = if j = 0 then 1 else 0) → (∃ a : O', ∑ j ∈ Finset.range ℓ, (τ ^ j) a = 1) → ∀ r : Rˣ, ∃ s : (O' ⊗[O] R)ˣ, (∏ j ∈ Finset.range ℓ, Algebra.TensorProduct.map ((τ ^ j : O' ≃ₐ[O] O').toAlgHom) (AlgHom.id O R) (s : O' ⊗[O] R)) - (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) (r : R) ∈ Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) (⊥ : Ideal R).jacobson := by
  intro hNI O O' R _ _ _ _ _ _ _ _ _ _ _ _ ℓ τ hℓ hτ hfix hdual htr r
  obtain ⟨J, hJ⟩ : ∃ J : Ideal R, J = (⊥ : Ideal R).jacobson := ⟨_, rfl⟩
  have hmJ : Ideal.map (algebraMap O R) (IsLocalRing.maximalIdeal O) ≤ J :=
    hJ ▸ (GlobalTheory.CompanionTheory.LocalFinite.map_maximalIdeal_le_jacobson_and_pow_le O R).1
  letI : Algebra (IsLocalRing.ResidueField O) (R ⧸ J) :=
    (Ideal.Quotient.lift (IsLocalRing.maximalIdeal O) (algebraMap O (R ⧸ J)) fun c hc => by
      first
        | exact Ideal.Quotient.eq_zero_iff_mem.mpr (hmJ (Ideal.mem_map_of_mem _ hc))
        | (rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
           exact hmJ (Ideal.mem_map_of_mem _ hc))).toAlgebra
  haveI : IsScalarTower O (IsLocalRing.ResidueField O) (R ⧸ J) :=
    IsScalarTower.of_algebraMap_eq fun c => rfl
  haveI : Module.Finite O (R ⧸ J) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ O J).toLinearMap (Ideal.Quotient.mkₐ_surjective O J)
  haveI : Module.Finite (IsLocalRing.ResidueField O) (R ⧸ J) :=
    Module.Finite.of_restrictScalars_finite O _ _
  have hrad : J.IsRadical := by
    rw [hJ]
    exact Ideal.radical_le_jacobson.trans Ideal.jacobson_idem.le
  haveI : IsReduced (R ⧸ J) := (Ideal.isRadical_iff_quotient_reduced J).mp hrad
  haveI : Module.Finite (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] O') :=
    Module.Finite.base_change O _ O'
  have hres : Function.Surjective (algebraMap O (IsLocalRing.ResidueField O)) :=
    IsLocalRing.residue_surjective
  obtain ⟨x, y, hxy⟩ := hdual
  have hτ' : Algebra.TensorProduct.congr
      (AlgEquiv.refl : IsLocalRing.ResidueField O ≃ₐ[IsLocalRing.ResidueField O] IsLocalRing.ResidueField O)
      τ ^ ℓ = 1 := by
    refine AlgEquiv.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul k w => rw [tensorProduct_congr_refl_pow_tmul_lemma, hτ]; rfl
    | add t₁ t₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  have hfix' : ∀ z : IsLocalRing.ResidueField O ⊗[O] O',
      Algebra.TensorProduct.congr
        (AlgEquiv.refl : IsLocalRing.ResidueField O ≃ₐ[IsLocalRing.ResidueField O] IsLocalRing.ResidueField O)
        τ z = z →
      z ∈ Set.range (algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] O')) :=
    fun z hz => GlobalTheory.CompanionTheory.FirstApprox.res_fixed O O'
      (IsLocalRing.ResidueField O) ℓ τ hres hℓ hτ hfix htr z hz
  have hdual' : ∃ x' y' : Fin ℓ → IsLocalRing.ResidueField O ⊗[O] O', ∀ j < ℓ,
      ∑ i, x' i * (Algebra.TensorProduct.congr
        (AlgEquiv.refl : IsLocalRing.ResidueField O ≃ₐ[IsLocalRing.ResidueField O] IsLocalRing.ResidueField O)
        τ ^ j) (y' i) = if j = 0 then 1 else 0 := by
    refine ⟨fun i => 1 ⊗ₜ[O] x i, fun i => 1 ⊗ₜ[O] y i, fun j hj => ?_⟩
    simp only [tensorProduct_congr_refl_pow_tmul_lemma, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [← TensorProduct.tmul_sum, hxy j hj]
    split_ifs
    · exact (Algebra.TensorProduct.one_def).symm
    · exact TensorProduct.tmul_zero _ _
  obtain ⟨sb, hsb⟩ := hNI (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O ⊗[O] O') (R ⧸ J) ℓ
    (Algebra.TensorProduct.congr
      (AlgEquiv.refl : IsLocalRing.ResidueField O ≃ₐ[IsLocalRing.ResidueField O] IsLocalRing.ResidueField O) τ)
    hℓ hτ' hfix' hdual' (Units.map (Ideal.Quotient.mk J).toMonoidHom r)
  obtain ⟨ψ, hψs, hψk, hψi, hψe⟩ := GlobalTheory.CompanionTheory.FirstApprox.res_compare O O' R
    (IsLocalRing.ResidueField O) (R ⧸ J) (Ideal.Quotient.mkₐ O J) (Ideal.Quotient.mkₐ_surjective O J)
  have hkerπ : RingHom.ker (Ideal.Quotient.mkₐ O J) = J := by
    ext w
    rw [RingHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem
  rw [hkerπ] at hψk
  obtain ⟨s0, hs0⟩ := hψs ↑sb
  obtain ⟨t0, ht0⟩ := hψs ↑(sb⁻¹)
  have hunit : IsUnit s0 := by
    have h1 : s0 * t0 - 1 ∈ Ideal.map (Algebra.TensorProduct.includeRight : R →ₐ[O] O' ⊗[O] R) J :=
      hψk (by rw [RingHom.mem_ker, map_sub, map_mul, hs0, ht0, Units.mul_inv, map_one, sub_self])
    have h2 : IsUnit (1 + (s0 * t0 - 1)) :=
      GlobalTheory.CompanionTheory.JacUnit.main O O' R _ (by rw [← hJ]; exact h1)
    rw [show (1 : O' ⊗[O] R) + (s0 * t0 - 1) = s0 * t0 by ring] at h2
    exact isUnit_of_mul_isUnit_left h2
  have hmap : ∀ j : ℕ, Algebra.TensorProduct.map (AlgHom.id (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O))
      ((τ ^ j : O' ≃ₐ[O] O').toAlgHom) =
      (Algebra.TensorProduct.congr
        (AlgEquiv.refl : IsLocalRing.ResidueField O ≃ₐ[IsLocalRing.ResidueField O] IsLocalRing.ResidueField O)
        τ ^ j).toAlgHom := by
    intro j
    refine AlgHom.ext fun t => ?_
    induction t using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul k w =>
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, AlgEquiv.toAlgHom_eq_coe,
        AlgEquiv.coe_algHom, tensorProduct_congr_refl_pow_tmul_lemma]
    | add t₁ t₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  refine ⟨hunit.unit, ?_⟩
  rw [IsUnit.unit_spec, ← hJ]
  refine hψk ?_
  rw [RingHom.mem_ker, map_sub, map_prod]
  simp_rw [hψe]
  rw [hψi, hs0, sub_eq_zero]
  refine Eq.trans ?_ (hsb.trans ?_)
  · refine Finset.prod_congr rfl fun j _ => ?_
    exact congrArg (fun g : (IsLocalRing.ResidueField O ⊗[O] O') →ₐ[IsLocalRing.ResidueField O]
        (IsLocalRing.ResidueField O ⊗[O] O') =>
      Algebra.TensorProduct.map g (AlgHom.id (IsLocalRing.ResidueField O) (R ⧸ J)) (sb : _)) (hmap j)
  · first
      | rfl
      | simp [Units.coe_map]

end GlobalTheory.CompanionTheory.FirstApprox
