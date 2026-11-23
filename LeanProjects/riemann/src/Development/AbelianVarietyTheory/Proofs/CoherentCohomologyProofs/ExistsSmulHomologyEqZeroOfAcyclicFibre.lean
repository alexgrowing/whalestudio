import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndKerBaseChangeOfForallResidueField
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard

open CategoryTheory CategoryTheory.Limits TensorProduct Function

namespace GlobalTheory

theorem exists_smul_mem_range_of_exact_fibre {R : Type*} [CommRing R] {A B C : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    [Module.Finite R B] [Module.Projective R B] [Module.Finite R C] [Module.Projective R C]
    (K : Type*) [Field K] [Algebra R K] {f : A →ₗ[R] B} {g : B →ₗ[R] C} (hfg : g ∘ₗ f = 0)
    (h : Exact (f.lTensor K) (g.lTensor K)) (b : B) (hb : g b = 0) :
    ∃ r : R, algebraMap R K r ≠ 0 ∧ r • b ∈ LinearMap.range f := by
  let P : Ideal R := RingHom.ker (algebraMap R K)
  haveI : P.IsPrime := RingHom.ker_isPrime _
  let O := Localization.AtPrime P
  have h1 := (exact_lTensor_iff_residueField P K rfl f g).1 h
  have h2 : Exact (AlgebraTensorModule.lTensor O P.ResidueField f)
      (AlgebraTensorModule.lTensor O P.ResidueField g) ↔
      Exact ((f.baseChange O).lTensor P.ResidueField) ((g.baseChange O).lTensor P.ResidueField) :=
    Function.Exact.iff_of_ladder_linearEquiv
      (e₁ := AlgebraTensorModule.cancelBaseChange R O O P.ResidueField A)
      (e₂ := AlgebraTensorModule.cancelBaseChange R O O P.ResidueField B)
      (e₃ := AlgebraTensorModule.cancelBaseChange R O O P.ResidueField C)
      (by ext; simp) (by ext; simp)
  have h3 := h2.1 h1
  have hfg' : g.baseChange O ∘ₗ f.baseChange O = 0 := by
    rw [← LinearMap.baseChange_comp, hfg, LinearMap.baseChange_zero]
  obtain ⟨s, t, hst⟩ := exists_homotopy_of_forall_exact_residueField hfg'
    (fun m _ => forall_exact_residueField_of_isLocalRing h3 m)
  have h4 := exact_of_homotopy hfg' hst
  obtain ⟨x, hx⟩ := (h4 ((1 : O) ⊗ₜ[R] b)).1 (by simp [hb])
  obtain ⟨⟨a, u⟩, ha⟩ := IsLocalizedModule.surj P.primeCompl (TensorProduct.mk R O A 1) x
  have h5 : TensorProduct.mk R O B 1 ((u : R) • b) = TensorProduct.mk R O B 1 (f a) := by
    have := congrArg (f.lTensor O) ha
    rw [Submonoid.smul_def, map_smul] at this
    have hx' : f.lTensor O x = (1 : O) ⊗ₜ[R] b := hx
    rw [hx'] at this
    simpa using this
  obtain ⟨v, hv⟩ := IsLocalizedModule.exists_of_eq (S := P.primeCompl) h5
  refine ⟨(v * u : P.primeCompl), (v * u).2, (v : R) • a, ?_⟩
  rw [map_smul, Submonoid.coe_mul, mul_smul]
  exact hv.symm

set_option backward.isDefEq.respectTransparency false in

theorem exists_smul_homology_eq_zero_of_acyclic_fibre (R : Type) [CommRing R] [IsNoetherianRing R]
    (K : Type) [Field K] (χ : R →+* K) (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ)
    (hn : ∀ p, n < p → IsZero (C.X p)) (hflat : ∀ p, Module.Flat R (C.X p))
    (hfin : ∀ p, Module.Finite R (C.homology p))
    (hac : (((ModuleCat.extendScalars.{0, 0, 0} χ).mapHomologicalComplex _).obj C).Acyclic)
    (p : ℕ) : ∃ r : R, χ r ≠ 0 ∧ ∀ z : C.homology p, r • z = 0 := by
  letI : Algebra R K := χ.toAlgebra
  obtain ⟨L, φ, -, h2, -, h4, h5, -, h7⟩ :=
    exists_finite_projective_complex_quasiIso.{0, 0} C n hn hflat hfin
  have h8 : QuasiIso
      (((ModuleCat.extendScalars.{0, 0, 0} χ).mapHomologicalComplex _).map φ) := h7 K
  have h9 : (((ModuleCat.extendScalars.{0, 0, 0} χ).mapHomologicalComplex _).obj L).ExactAt p :=
    (exactAt_iff_of_quasiIsoAt
      (((ModuleCat.extendScalars.{0, 0, 0} χ).mapHomologicalComplex _).map φ) p).2 (hac p)
  have h10 : Exact ((L.sc p).f.hom.lTensor K) ((L.sc p).g.hom.lTensor K) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 h9
  have hpt : ∀ z : L.homology p, ∃ r : R, χ r ≠ 0 ∧ r • z = 0 := by
    intro z
    let e := (L.sc p).moduleCatHomologyIso.toLinearEquiv
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (e z)
    haveI : Module.Finite R (L.sc p).X₂ := h2 _
    haveI : Module.Finite R (L.sc p).X₃ := h2 _
    haveI : Module.Projective R (L.sc p).X₂ := h4 _
    haveI : Module.Projective R (L.sc p).X₃ := h4 _
    obtain ⟨r, hr, a, ha⟩ := exists_smul_mem_range_of_exact_fibre K
      (congrArg ModuleCat.Hom.hom (L.sc p).zero) h10 b.1 b.2
    refine ⟨r, hr, e.injective ?_⟩
    rw [map_smul, map_zero, ← hb]
    exact (Submodule.Quotient.mk_eq_zero _).2 (show r • b ∈ _ from ⟨a, Subtype.ext ha⟩)
  let e := (isoOfQuasiIsoAt φ p).toLinearEquiv
  let P : PrimeSpectrum R := ⟨RingHom.ker χ, RingHom.ker_isPrime χ⟩
  have hP : P ∉ Module.support R (C.homology p) := by
    rw [Module.notMem_support_iff']
    intro z
    obtain ⟨r, hr, hz⟩ := hpt (e.symm z)
    refine ⟨r, hr, ?_⟩
    rw [← e.apply_symm_apply z, ← map_smul, hz, map_zero]
  haveI := hfin p
  rw [Module.mem_support_iff_of_finite, SetLike.not_le_iff_exists] at hP
  obtain ⟨r, hr, hr'⟩ := hP
  exact ⟨r, hr', Module.mem_annihilator.1 hr⟩

end GlobalTheory
