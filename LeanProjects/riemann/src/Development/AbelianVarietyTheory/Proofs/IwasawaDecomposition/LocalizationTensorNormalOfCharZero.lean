import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DomainIntegrallyClosedOfCompletionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionNormalOfUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorLocalizationNoetherianStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalDomainValuationDominatedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorPrimeContractionMaximalStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorLocalizationNormalDomainStatement

open IsLocalRing GlobalTheory.Toroidal TensorProduct

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.TensorNormal.localization_tensor_normal_of_charZero : ∀ (A C R : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A] [CommRing C] [Algebra A C] [Algebra.EssFiniteType A C] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra A R], (∀ (P : Ideal C) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧ IsIntegrallyClosed (Localization.AtPrime P) ∧ CharZero (Localization.AtPrime P)) → IsEtaleCompletion (algebraMap A R) → ((residue R).comp (algebraMap A R)).FormallyUnramified → ∀ (Q : Ideal (TensorProduct A C R)) [Q.IsPrime], IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) ∧ IsNoetherianRing (Localization.AtPrime Q) := by
  intro A C R _ _ _ _ _ _ _ _ _ _ hC hEt hFU Q _
  have hnoeth : IsNoetherianRing (Localization.AtPrime Q) := by
    haveI : IsNoetherianRing (R ⊗[A] C) := Algebra.EssFiniteType.isNoetherianRing R (R ⊗[A] C)
    haveI : IsNoetherianRing (C ⊗[A] R) :=
      isNoetherianRing_of_ringEquiv _ (Algebra.TensorProduct.comm A R C).toRingEquiv
    infer_instance
  suffices h : IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) from
    ⟨h.1, h.2, hnoeth⟩
  obtain ⟨Q', _, hQ'm, htr⟩ := GlobalTheory.T.tensor_prime_contraction_maximal A C R Q
  set P := Q.comap (Algebra.TensorProduct.includeLeft : C →ₐ[A] C ⊗[A] R) with hP
  set B := Localization.AtPrime P
  obtain ⟨hBd, hBi, hBc⟩ := hC P
  haveI := hBd; haveI := hBi; haveI := hBc
  haveI : Algebra.EssFiniteType C B := .of_isLocalization B P.primeCompl
  haveI : Algebra.EssFiniteType A B := .comp A C B
  set W' := Localization.AtPrime Q'
  let k := ResidueField W'
  let φ : B →+* k := (residue W').comp ((algebraMap (B ⊗[A] R) W').comp
    (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R).toRingHom)
  let ρ : R →+* k := (residue W').comp ((algebraMap (B ⊗[A] R) W').comp
    (Algebra.TensorProduct.includeRight : R →ₐ[A] B ⊗[A] R).toRingHom)
  obtain ⟨V, hV, hVloc⟩ := IsLocalRing.exists_factor_valuationRing ρ
  have hker : RingHom.ker φ = maximalIdeal B := by
    ext b
    rw [RingHom.mem_ker, ← hQ'm, Ideal.mem_comap]
    change residue W' (algebraMap _ W' ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] R) b)) = 0 ↔ _
    rw [residue_eq_zero_iff]
    exact IsLocalization.AtPrime.to_map_mem_maximal_iff W' Q' _
  have hφρ : ∀ a : A, φ (algebraMap A B a) = ρ (algebraMap A R a) := fun a => by
    simp only [φ, ρ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  have ha1 : ∀ a : A, V.valuation (φ (algebraMap A B a)) ≤ 1 := fun a => by
    rw [hφρ, ValuationSubring.valuation_le_one_iff]; exact hV _
  have ha2 : ∀ a ∈ maximalIdeal A, V.valuation (φ (algebraMap A B a)) < 1 := fun a ha => by
    have hR : algebraMap A R a ∈ maximalIdeal R := hEt.2.1 ▸ Ideal.mem_map_of_mem _ ha
    have hm : ρ.codRestrict V.toSubring hV (algebraMap A R a) ∈ maximalIdeal V := fun hu =>
      hR (IsUnit.of_map (ρ.codRestrict V.toSubring hV) _ hu)
    rw [hφρ]
    exact (ValuationSubring.valuation_lt_one_iff V _).1 hm
  obtain ⟨D, _, _, _, _, ι, hDi, hDe, hinj, hv1, hvm, hsurj⟩ := GlobalTheory.T.exists_local_domain_valuation_dominated A B k φ V hker ha1 ha2
  haveI := hDi; haveI := hDe
  haveI : CharZero D := ⟨fun m n h => Nat.cast_injective (R := B) (by simpa using congrArg ι h)⟩
  haveI : Algebra.EssFiniteType ℤ D := .comp ℤ A D
  have hunit1 : ∀ d : D, IsUnit d → V.valuation (φ (ι d)) = 1 := fun d hd => by
    obtain ⟨u, rfl⟩ := hd
    have h1 := hv1 u
    have h2 := hv1 ↑u⁻¹
    have h3 : V.valuation (φ (ι u)) * V.valuation (φ (ι ↑u⁻¹)) = 1 := by
      rw [← map_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, map_one]
    exact le_antisymm h1 (by
      by_contra hlt
      push_neg at hlt
      have := mul_lt_one_of_lt_of_le hlt h2
      rw [h3] at this
      exact lt_irrefl _ this)
  haveI : IsLocalHom (algebraMap A D) := ⟨fun a ha => by
    by_contra hna
    have hv := hunit1 _ ha
    rw [AlgHom.commutes] at hv
    exact (ha2 a ((mem_maximalIdeal a).2 hna)).ne hv⟩
  let ψ : D ⊗[A] R →ₐ[A] W' := (IsScalarTower.toAlgHom A (B ⊗[A] R) W').comp
    (Algebra.TensorProduct.map ι (AlgHom.id A R))
  let θ : D ⊗[A] R →+* k := (residue W').comp ψ.toRingHom
  have hθt : ∀ (d : D) (r : R), θ (d ⊗ₜ r) = φ (ι d) * ρ r := fun d r => by
    simp only [θ, φ, ρ, ψ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.coe_toAlgHom',
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply, ← map_mul,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hθt1 : ∀ d : D, θ (d ⊗ₜ[A] (1 : R)) = φ (ι d) := fun d => by
    simp only [θ, φ, ψ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.comp_apply,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.coe_toAlgHom',
      Algebra.TensorProduct.includeLeft_apply]
  have hθ0 : ∀ x, θ x = residue W' (algebraMap (B ⊗[A] R) W' (Algebra.TensorProduct.map ι (AlgHom.id A R) x)) :=
    fun x => rfl
  clear_value θ
  have hθV : ∀ x, θ x ∈ V := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simpa using V.zero_mem
    | tmul d r => rw [hθt]; exact V.mul_mem _ _ ((ValuationSubring.valuation_le_one_iff V _).1 (hv1 d)) (hV r)
    | add x y hx hy => rw [map_add]; exact V.add_mem _ _ hx hy
  let θV : D ⊗[A] R →+* V := θ.codRestrict V.toSubring hθV
  let q : Ideal (D ⊗[A] R) := (maximalIdeal V).comap θV
  have hmq : ∀ d ∈ maximalIdeal D, d ⊗ₜ[A] (1 : R) ∈ q := by
    intro d hd
    rw [Ideal.mem_comap]
    refine (ValuationSubring.valuation_lt_one_iff V _).2 ?_
    have e2 := hθt1 d
    have e : ((θV (d ⊗ₜ[A] (1 : R)) : V) : k) = θ (d ⊗ₜ[A] (1 : R)) := rfl
    exact (congrArg V.valuation (e.trans e2)).trans_lt (hvm d hd)
  have hQq : Q'.comap (Algebra.TensorProduct.map ι (AlgHom.id A R)) ≤ q := by
    intro x hx
    have h0 : θ x = 0 := by
      rw [hθ0, residue_eq_zero_iff]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff W' Q' _).2 hx
    show θV x ∈ maximalIdeal V
    have : θV x = 0 := Subtype.ext h0
    rw [this]; exact zero_mem _
  obtain ⟨hTn, hTl, hTf, hTm, hTfin, hTfu⟩ := GlobalTheory.T.tensor_localization_noetherian A D R hEt hFU q hmq
  obtain ⟨c1, c2⟩ := GlobalTheory.T.completion_normal_of_unramified D (Localization.AtPrime q) _ hTn hTl hTf hTm hTfin hTfu
  haveI := hTn
  obtain ⟨t1, t2⟩ := GlobalTheory.T.domain_integrally_closed_of_completion _ c1 c2
  obtain ⟨w1, w2⟩ := GlobalTheory.T.tensor_localization_normal_domain A B D R ι hinj hsurj Q' q hQq t1 t2
  exact htr w1 w2
