import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatQuotientOfUniversallyInjectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearMapZeroOfInjectiveFullRankStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFreeKernelSplittingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSplittingKernelBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelFreeAtPrimesOfConstantRankStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelBaseChangeTowerEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RetractBaseChangeKernelCompatibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasiIsomorphismDegreeOneKernelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CochainBaseChangeEquivalencesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniversalCoefficientDegreeZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelEquivCohomologyOfQuasiIsomorphismStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstCohomologyBaseChangeOfCochainEquivsStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.PerfectFirstCohomology

theorem proj_coker (R P₀ P₁ : Type) [CommRing R] [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁]
    [Module.Finite R P₀] [Module.Finite R P₁] [Module.Projective R P₀] [Module.Projective R P₁]
    (a₀ : P₀ →ₗ[R] P₁) (u : P₀) (hu : a₀ u = 0)
    (hU : ∀ (M : Type) [AddCommGroup M] [Module R M], Function.Injective (fun m : M ↦ m ⊗ₜ[R] u) ∧
      ∀ x : M ⊗[R] P₀, a₀.lTensor M x = 0 → ∃ m : M, m ⊗ₜ[R] u = x) :
    Module.Projective R (P₁ ⧸ LinearMap.range a₀) := by
  have hle : Submodule.span R {u} ≤ LinearMap.ker a₀ := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hu
  have hcomp : (Submodule.span R {u}).liftQ a₀ hle ∘ₗ (Submodule.span R {u}).mkQ = a₀ :=
    Submodule.liftQ_mkQ _ _ _
  have hflat : Module.Flat R (P₁ ⧸ LinearMap.range ((Submodule.span R {u}).liftQ a₀ hle)) := by
    apply GlobalTheory.T.flat_quotient_of_universally_injective
    intro M _ _
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨x, rfl⟩ := LinearMap.lTensor_surjective M (Submodule.mkQ_surjective (Submodule.span R {u})) z
    have hx : a₀.lTensor M x = 0 := by
      rw [← hcomp, LinearMap.lTensor_comp_apply]
      exact hz
    obtain ⟨m, rfl⟩ := (hU M).2 x hx
    rw [LinearMap.lTensor_tmul, Submodule.mkQ_apply,
      (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self u), TensorProduct.tmul_zero]
  rw [Submodule.range_liftQ] at hflat
  haveI := hflat
  haveI : Module.FinitePresentation R P₁ := Module.finitePresentation_of_projective R P₁
  haveI : Module.FinitePresentation R (P₁ ⧸ LinearMap.range a₀) :=
    Module.finitePresentation_of_surjective (LinearMap.range a₀).mkQ (Submodule.mkQ_surjective _)
      (by rw [Submodule.ker_mkQ, LinearMap.range_eq_map]; exact Module.Finite.fg_top.map a₀)
  exact Module.Flat.projective_of_finitePresentation

theorem local_regular (A Q P : Type) [CommRing A] [IsLocalRing A] [AddCommGroup Q] [Module A Q] [AddCommGroup P]
    [Module A P] [Module.Finite A Q] [Module.Free A Q] [Module.Finite A P] [Module.Free A P] (d : Q →ₗ[A] P) (g : ℕ)
    (h1 : Module.Free A (LinearMap.ker d)) (h2 : Module.Finite A (LinearMap.ker d))
    (h3 : Module.finrank A (LinearMap.ker d) = g)
    (h4 : Module.finrank (IsLocalRing.ResidueField A) (LinearMap.ker (d.baseChange (IsLocalRing.ResidueField A))) = g) :
    ∃ r : P →ₗ[A] Q, d ∘ₗ r ∘ₗ d = d := by
  obtain ⟨r, hidem, hfree, hfin, hrank⟩ := GlobalTheory.T.local_free_kernel_splitting A Q P d
  refine ⟨r, ?_⟩
  have hrank' : Module.finrank A (LinearMap.ker (r ∘ₗ d)) = g := hrank.trans h4
  have hle : LinearMap.ker d ≤ LinearMap.ker (r ∘ₗ d) := fun x hx => by
    rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mem_ker.mp hx, map_zero]
  let b := Module.finBasisOfFinrankEq A (LinearMap.ker d) h3
  let φ : (Fin g → A) →ₗ[A] LinearMap.ker (r ∘ₗ d) :=
    Submodule.inclusion hle ∘ₗ b.equivFun.symm.toLinearMap
  have hφ : Function.Injective φ := (Submodule.inclusion_injective hle).comp b.equivFun.symm.injective
  have hzero : (d ∘ₗ (LinearMap.ker (r ∘ₗ d)).subtype) ∘ₗ φ = 0 := LinearMap.ext fun v => by
    change d ((b.equivFun.symm v : LinearMap.ker d) : Q) = 0
    exact LinearMap.mem_ker.mp (b.equivFun.symm v).2
  have key := GlobalTheory.T.linear_map_zero_of_injective_full_rank A _ P g φ
    (d ∘ₗ (LinearMap.ker (r ∘ₗ d)).subtype) hrank' hφ hzero
  ext x
  have hx : x - r (d x) ∈ LinearMap.ker (r ∘ₗ d) := by
    have h := LinearMap.congr_fun hidem x
    simp only [LinearMap.comp_apply] at h
    rw [LinearMap.mem_ker, map_sub, LinearMap.comp_apply, LinearMap.comp_apply, h, sub_self]
  have h := LinearMap.congr_fun key ⟨_, hx⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.zero_apply, map_sub, sub_eq_zero] at h
  simp only [LinearMap.comp_apply]
  exact h.symm

theorem regular_of_fibres (R Q P : Type) [CommRing R] [AddCommGroup Q] [Module R Q] [AddCommGroup P] [Module R P]
    [Module.Finite R Q] [Module.Projective R Q] [Module.Finite R P] [Module.Projective R P] (d : Q →ₗ[R] P) (g : ℕ)
    (hVB : VB R (LinearMap.ker d) g)
    (hfib : ∀ (k : Type) [Field k] [Algebra R k], Module.finrank k (LinearMap.ker (d.baseChange k)) = g) :
    ∃ r : P →ₗ[R] Q, d ∘ₗ r ∘ₗ d = d := by
  obtain ⟨hfin, hproj, hrank⟩ := hVB
  apply GlobalTheory.T.local_splitting_kernel_base_change R Q P d
  intro p hp
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.kernel_free_at_primes_of_constant_rank R Q P d g hfin hproj hrank p
  haveI : Module.Flat (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] Q) :=
    Module.Flat.baseChange R _ Q
  haveI : Module.Flat (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] P) :=
    Module.Flat.baseChange R _ P
  haveI : Module.Free (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] Q) :=
    Module.free_of_flat_of_isLocalRing
  haveI : Module.Free (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] P) :=
    Module.free_of_flat_of_isLocalRing
  refine GlobalTheory.CompanionTheory.PerfectFirstCohomology.local_regular (Localization.AtPrime p) _ _
    (d.baseChange (Localization.AtPrime p)) g h1 h2 h3 ?_
  obtain ⟨e⟩ := GlobalTheory.T.kernel_base_change_tower_equiv R (Localization.AtPrime p)
    (IsLocalRing.ResidueField (Localization.AtPrime p)) Q P d
  rw [e.finrank_eq]
  exact hfib _

theorem stein_univ (R C : Type) [CommRing R] [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')]
    (F : C ⥤ CommAlgCat.{0} R) (hS : SteinU F) (M : Type) [AddCommGroup M] [Module R M] :
    Function.Injective (fun m : M ↦ m ⊗ₜ[R] (1 : C0 F)) ∧
      ∀ x : M ⊗[R] C0 F, (d0 F).lTensor M x = 0 → ∃ m : M, m ⊗ₜ[R] (1 : C0 F) = x := by
  letI : Module Rᵐᵒᵖ M := Module.compHom M ((RingHom.id R).fromOpposite fun x y => Commute.all _ _)
  haveI : IsCentralScalar R M := ⟨fun _ _ => rfl⟩
  haveI : IsScalarTower R Rᵐᵒᵖ M := ⟨fun r s m => mul_smul r (MulOpposite.unop s) m⟩
  haveI : SMulCommClass R Rᵐᵒᵖ M := ⟨fun r s m => smul_comm r (MulOpposite.unop s) m⟩
  obtain ⟨F', m, hF'⟩ := hS (TrivSqZeroExt R M)
  obtain ⟨E₀, E₁, E₂, h0, -, -, h01, -⟩ :=
    GlobalTheory.T.cochain_base_change_equivalences R (TrivSqZeroExt R M) C F F' m
  have hone : E₀ (1 ⊗ₜ[R] (1 : GlobalTheory.CatCoh.C0 F)) = 1 := by
    rw [h0]
    funext T
    first
      | exact map_one _
      | simp
  refine GlobalTheory.T.retract_base_change_kernel_compatible R (TrivSqZeroExt R M) M _ _ _ _
    (TrivSqZeroExt.inrHom R M) (TrivSqZeroExt.sndHom R M) (GlobalTheory.CatCoh.d0 F)
    (GlobalTheory.CatCoh.d0 F') E₀ E₁ 1 (LinearMap.ext fun _ => rfl) h01 ?_ ?_
  · intro r hr
    rw [hone, ← Algebra.algebraMap_eq_smul_one] at hr
    exact hF'.2 (hr.trans (map_zero _).symm)
  · intro z hz
    obtain ⟨r, hr⟩ := (hF'.1 z).mp hz
    exact ⟨r, by rw [hone, ← Algebra.algebraMap_eq_smul_one, ← Algebra.linearMap_apply]; exact hr⟩

theorem qiso_transport {R S A₀ A₁ A₂ B₀ B₁ B₂ A₀' A₁' A₂' B₀' B₁' B₂' : Type} [CommRing R] [CommRing S]
    [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
    [Module R A₀] [Module R A₁] [Module R A₂] [Module R B₀] [Module R B₁] [Module R B₂]
    [AddCommGroup A₀'] [AddCommGroup A₁'] [AddCommGroup A₂'] [AddCommGroup B₀'] [AddCommGroup B₁'] [AddCommGroup B₂']
    [Module S A₀'] [Module S A₁'] [Module S A₂'] [Module S B₀'] [Module S B₁'] [Module S B₂']
    {a₀ : A₀ →ₗ[R] A₁} {a₁ : A₁ →ₗ[R] A₂} {b₀ : B₀ →ₗ[R] B₁} {b₁ : B₁ →ₗ[R] B₂} {f : A₁ →ₗ[R] B₁}
    {a₀' : A₀' →ₗ[S] A₁'} {a₁' : A₁' →ₗ[S] A₂'} {b₀' : B₀' →ₗ[S] B₁'} {b₁' : B₁' →ₗ[S] B₂'} {f' : A₁' →ₗ[S] B₁'}
    (h : QIsoAt a₀ a₁ b₀ b₁ f) (ε₀ : A₀ ≃+ A₀') (ε₁ : A₁ ≃+ A₁') (ε₂ : A₂ ≃+ A₂')
    (η₀ : B₀ ≃+ B₀') (η₁ : B₁ ≃+ B₁') (η₂ : B₂ ≃+ B₂')
    (h0 : ∀ y, a₀' (ε₀ y) = ε₁ (a₀ y)) (h1 : ∀ x, a₁' (ε₁ x) = ε₂ (a₁ x))
    (k0 : ∀ y, b₀' (η₀ y) = η₁ (b₀ y)) (k1 : ∀ x, b₁' (η₁ x) = η₂ (b₁ x))
    (hf : ∀ x, f' (ε₁ x) = η₁ (f x)) : QIsoAt a₀' a₁' b₀' b₁' f' := by
  unfold MainStatements.Hodge.QIsoAt at h ⊢
  obtain ⟨hA, hB⟩ := h
  refine ⟨fun x' hx' ⟨y', hy'⟩ => ?_, fun z' hz' => ?_⟩
  · have ha : a₁ (ε₁.symm x') = 0 := by
      apply ε₂.injective
      rw [← h1, ε₁.apply_symm_apply, hx', map_zero]
    have hb : b₀ (η₀.symm y') = f (ε₁.symm x') := by
      apply η₁.injective
      rw [← k0, ← hf, η₀.apply_symm_apply, ε₁.apply_symm_apply, hy']
    obtain ⟨y, hy⟩ := hA _ ha ⟨_, hb⟩
    exact ⟨ε₀ y, by rw [h0, hy, ε₁.apply_symm_apply]⟩
  · have hz : b₁ (η₁.symm z') = 0 := by
      apply η₂.injective
      rw [← k1, η₁.apply_symm_apply, hz', map_zero]
    obtain ⟨x, y, hx, hxy⟩ := hB _ hz
    refine ⟨ε₁ x, η₀ y, by rw [h1, hx, map_zero], ?_⟩
    rw [hf, k0, ← hxy, map_sub, η₁.apply_symm_apply]

theorem lid_natural {R X Y : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (h : X →ₗ[R] Y) (y : R ⊗[R] X) : h (TensorProduct.lid R X y) = TensorProduct.lid R Y (h.lTensor R y) := by
  induction y with
  | zero => simp
  | tmul a b => simp
  | add a b ha hb => simp only [map_add, ha, hb]

theorem qiso_lid {R A₀ A₁ A₂ B₀ B₁ B₂ : Type} [CommRing R]
    [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
    [Module R A₀] [Module R A₁] [Module R A₂] [Module R B₀] [Module R B₁] [Module R B₂]
    {a₀ : A₀ →ₗ[R] A₁} {a₁ : A₁ →ₗ[R] A₂} {b₀ : B₀ →ₗ[R] B₁} {b₁ : B₁ →ₗ[R] B₂} {f : A₁ →ₗ[R] B₁}
    (h : QIsoAt (a₀.lTensor R) (a₁.lTensor R) (b₀.lTensor R) (b₁.lTensor R) (f.lTensor R)) :
    QIsoAt a₀ a₁ b₀ b₁ f :=
  qiso_transport h (TensorProduct.lid R A₀).toAddEquiv (TensorProduct.lid R A₁).toAddEquiv
    (TensorProduct.lid R A₂).toAddEquiv (TensorProduct.lid R B₀).toAddEquiv
    (TensorProduct.lid R B₁).toAddEquiv (TensorProduct.lid R B₂).toAddEquiv
    (lid_natural a₀) (lid_natural a₁) (lid_natural b₀) (lid_natural b₁) (lid_natural f)

section Core

variable {R C : Type} [CommRing R] [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
  {P₀ P₁ P₂ : Type} [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂]
  (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (ψ₀ : P₀ →ₗ[R] C0 F) (ψ₁ : P₁ →ₗ[R] C1 F) (ψ₂ : P₂ →ₗ[R] C2 F)

theorem mem_Z1_iff_cocycle {S : Type} [CommRing S] (G : C ⥤ CommAlgCat.{0} S) (z : C1 G) : z ∈ Z1 G ↔ d1 G z = 0 := by
  rw [GlobalTheory.CatCoh.commAlgFunctorCocyclesOne_eq_ker, LinearMap.mem_ker]

variable {F a₀ a₁ ψ₀ ψ₁ ψ₂} in

theorem ker_equiv_H1 (c0 : ψ₁ ∘ₗ a₀ = d0 F ∘ₗ ψ₀) (c1 : ψ₂ ∘ₗ a₁ = d1 F ∘ₗ ψ₁)
    (d : (P₁ ⧸ LinearMap.range a₀) →ₗ[R] P₂) (hdπ : d ∘ₗ (LinearMap.range a₀).mkQ = a₁)
    (hp : QIsoAt a₀ a₁ (d0 F) (d1 F) ψ₁) : Nonempty (LinearMap.ker d ≃ₗ[R] H1 F) := by
  refine GlobalTheory.T.kernel_equiv_cohomology_of_quasi_isomorphism R P₀ P₁ P₂ (P₁ ⧸ LinearMap.range a₀) _ _ _ a₀ a₁
    (LinearMap.range a₀).mkQ d (GlobalTheory.CatCoh.Z1 F)
    (LinearMap.codRestrict _ (GlobalTheory.CatCoh.d0 F) (GlobalTheory.CatCoh.commAlgFunctorCoboundaryZero_mem_cocyclesOne F))
    (GlobalTheory.CatCoh.d1 F) ψ₁ ψ₀ (Submodule.mkQ_surjective _) (LinearMap.exact_map_mkQ_range a₀) hdπ
    (GlobalTheory.CompanionTheory.PerfectFirstCohomology.mem_Z1_iff_cocycle F) ?_ (fun y => LinearMap.congr_fun c0 y) ?_
  · intro x hx
    rw [← LinearMap.comp_apply (GlobalTheory.CatCoh.d1 F) ψ₁, ← c1, LinearMap.comp_apply, hx, map_zero]
  · rwa [LinearMap.subtype_comp_codRestrict]

variable {F a₀ a₁ ψ₀ ψ₁ ψ₂} in

theorem ker_equiv_base {k : Type} [CommRing k] [Algebra R k] (G : C ⥤ CommAlgCat.{0} k)
    (E₀ : k ⊗[R] C0 F ≃ₗ[k] C0 G) (E₁ : k ⊗[R] C1 F ≃ₗ[k] C1 G) (E₂ : k ⊗[R] C2 F ≃ₗ[k] C2 G)
    (h01 : ∀ x, E₁ ((d0 F).baseChange k x) = d0 G (E₀ x)) (h12 : ∀ x, E₂ ((d1 F).baseChange k x) = d1 G (E₁ x))
    (c0 : ψ₁ ∘ₗ a₀ = d0 F ∘ₗ ψ₀) (c1 : ψ₂ ∘ₗ a₁ = d1 F ∘ₗ ψ₁)
    (d : (P₁ ⧸ LinearMap.range a₀) →ₗ[R] P₂) (hdπ : d ∘ₗ (LinearMap.range a₀).mkQ = a₁)
    (hq : QIsoAt (a₀.lTensor k) (a₁.lTensor k) ((d0 F).lTensor k) ((d1 F).lTensor k) (ψ₁.lTensor k)) :
    Nonempty (LinearMap.ker (d.baseChange k) ≃ₗ[k] H1 G) := by
  refine GlobalTheory.T.kernel_equiv_cohomology_of_quasi_isomorphism k (k ⊗[R] P₀) (k ⊗[R] P₁) (k ⊗[R] P₂)
    (k ⊗[R] (P₁ ⧸ LinearMap.range a₀)) _ _ _ (a₀.baseChange k) (a₁.baseChange k)
    ((LinearMap.range a₀).mkQ.baseChange k) (d.baseChange k) (GlobalTheory.CatCoh.Z1 G)
    (LinearMap.codRestrict _ (GlobalTheory.CatCoh.d0 G) (GlobalTheory.CatCoh.commAlgFunctorCoboundaryZero_mem_cocyclesOne G))
    (GlobalTheory.CatCoh.d1 G) (E₁.toLinearMap ∘ₗ ψ₁.baseChange k) (E₀.toLinearMap ∘ₗ ψ₀.baseChange k)
    ?_ ?_ ?_ (GlobalTheory.CompanionTheory.PerfectFirstCohomology.mem_Z1_iff_cocycle G) ?_ ?_ ?_
  · rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective k (Submodule.mkQ_surjective _)
  · rw [LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor]
    exact lTensor_exact k (LinearMap.exact_map_mkQ_range a₀) (Submodule.mkQ_surjective _)
  · rw [← LinearMap.baseChange_comp, hdπ]
  · intro x hx
    have h := LinearMap.congr_fun (congrArg (LinearMap.baseChange k) c1) x
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp, LinearMap.comp_apply, LinearMap.comp_apply, hx,
      map_zero] at h
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← h12, ← h, map_zero]
  · intro y
    have h := LinearMap.congr_fun (congrArg (LinearMap.baseChange k) c0) y
    rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp, LinearMap.comp_apply, LinearMap.comp_apply] at h
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.codRestrict_apply]
    rw [h, h01]
  · rw [LinearMap.subtype_comp_codRestrict]
    exact GlobalTheory.CompanionTheory.PerfectFirstCohomology.qiso_transport hq (AddEquiv.refl _) (AddEquiv.refl _) (AddEquiv.refl _)
      E₀.toAddEquiv E₁.toAddEquiv E₂.toAddEquiv
      (fun y => congrFun (LinearMap.baseChange_eq_ltensor a₀) y)
      (fun x => congrFun (LinearMap.baseChange_eq_ltensor a₁) x)
      (fun y => (h01 y).symm.trans (congrArg E₁ (congrFun (LinearMap.baseChange_eq_ltensor _) y)))
      (fun x => (h12 x).symm.trans (congrArg E₂ (congrFun (LinearMap.baseChange_eq_ltensor _) x)))
      (fun x => congrArg E₁ (congrFun (LinearMap.baseChange_eq_ltensor ψ₁) x))

variable {F a₀ a₁ ψ₀ ψ₁ ψ₂} in

theorem core [Finite C] [∀ T T' : C, Finite (T ⟶ T')] [Module.Finite R P₀] [Module.Finite R P₁] [Module.Projective R P₀]
    [Module.Projective R P₁] [Module.Finite R P₂] [Module.Projective R P₂] (g : ℕ)
    (h10 : a₁ ∘ₗ a₀ = 0) (c0 : ψ₁ ∘ₗ a₀ = d0 F ∘ₗ ψ₀) (c1 : ψ₂ ∘ₗ a₁ = d1 F ∘ₗ ψ₁)
    (hq0 : ∀ (M : Type) [AddCommGroup M] [Module R M],
      QIsoAt (0 : R →ₗ[R] M ⊗[R] P₀) (a₀.lTensor M) (0 : R →ₗ[R] M ⊗[R] C0 F) ((d0 F).lTensor M) (ψ₀.lTensor M))
    (hq' : ∀ (M : Type) [AddCommGroup M] [Module R M], QIsoAt (a₀.lTensor M) (a₁.lTensor M)
      ((d0 F).lTensor M) ((d1 F).lTensor M) (ψ₁.lTensor M))
    (hS : SteinU F) (hVB : VB R (H1 F) g)
    (hfib : ∀ (k : Type) [Field k] [Algebra R k], ∃ (F' : C ⥤ CommAlgCat.{0} k) (_ : BC F F'),
      Module.finrank k (H1 F') = g) : H1CommutesBaseChange F := by
  have h1zero : GlobalTheory.CatCoh.d0 F 1 = 0 := by
    funext T T' φ
    rw [GlobalTheory.CatCoh.amitsur_d0_apply]
    simp
  obtain ⟨u, hu, hU⟩ := GlobalTheory.T.universal_coefficient_degree_zero R _ _ P₀ P₁
    (GlobalTheory.CatCoh.d0 F) a₀ ψ₀ ψ₁ 1 c0 h1zero hq0
    (fun M _ _ => GlobalTheory.CompanionTheory.PerfectFirstCohomology.stein_univ R C F hS M)
  haveI : Module.Projective R (P₁ ⧸ LinearMap.range a₀) :=
    GlobalTheory.CompanionTheory.PerfectFirstCohomology.proj_coker R P₀ P₁ a₀ u hu hU
  have hle : LinearMap.range a₀ ≤ LinearMap.ker a₁ := by
    rintro _ ⟨y, rfl⟩
    exact LinearMap.congr_fun h10 y
  obtain ⟨d, hdπ⟩ : ∃ d : (P₁ ⧸ LinearMap.range a₀) →ₗ[R] P₂, d ∘ₗ (LinearMap.range a₀).mkQ = a₁ :=
    ⟨_, Submodule.liftQ_mkQ _ _ hle⟩
  obtain ⟨e⟩ := GlobalTheory.CompanionTheory.PerfectFirstCohomology.ker_equiv_H1 c0 c1 d hdπ (GlobalTheory.CompanionTheory.PerfectFirstCohomology.qiso_lid (hq' R))
  obtain ⟨hfin, hproj, hrank⟩ := hVB
  have hVBd : MainStatements.Hodge.VB R (LinearMap.ker d) g :=
    ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm, fun p => by
      rw [Module.rankAtStalk_eq_of_equiv e]
      exact hrank p⟩
  have hfibd : ∀ (k : Type) [Field k] [Algebra R k], Module.finrank k (LinearMap.ker (d.baseChange k)) = g := by
    intro k _ _
    obtain ⟨F', m, hg⟩ := hfib k
    obtain ⟨E₀, E₁, E₂, -, -, -, h01, h12⟩ := GlobalTheory.T.cochain_base_change_equivalences R k C F F' m
    obtain ⟨e'⟩ := GlobalTheory.CompanionTheory.PerfectFirstCohomology.ker_equiv_base F' E₀ E₁ E₂ h01 h12 c0 c1 d hdπ (hq' k)
    rw [e'.finrank_eq, hg]
  obtain ⟨r', hr'⟩ := GlobalTheory.CompanionTheory.PerfectFirstCohomology.regular_of_fibres R _ P₂ d g hVBd hfibd
  obtain ⟨r, hr⟩ := Module.projective_lifting_property (LinearMap.range a₀).mkQ r' (Submodule.mkQ_surjective _)
  have har : a₁ ∘ₗ r ∘ₗ a₁ = a₁ := by
    rw [← hdπ]
    ext x
    have h₁ := LinearMap.congr_fun hr (d ((LinearMap.range a₀).mkQ x))
    have h₂ := LinearMap.congr_fun hr' ((LinearMap.range a₀).mkQ x)
    simp only [LinearMap.comp_apply] at h₁ h₂ ⊢
    rw [h₁, h₂]
  intro R' _ _ F' m
  obtain ⟨E₀, E₁, E₂, -, hE₁, -, h01, h12⟩ := GlobalTheory.T.cochain_base_change_equivalences R R' C F F' m
  obtain ⟨H₁, H₂⟩ := GlobalTheory.T.quasi_isomorphism_degree_one_kernel R _ _ _ P₀ P₁ P₂
    (GlobalTheory.CatCoh.d0 F) (GlobalTheory.CatCoh.d1 F) a₀ a₁ ψ₀ ψ₁ ψ₂ r
    (GlobalTheory.CatCoh.Z1 F)
    (LinearMap.codRestrict _ (GlobalTheory.CatCoh.d0 F) (GlobalTheory.CatCoh.commAlgFunctorCoboundaryZero_mem_cocyclesOne F))
    (GlobalTheory.CompanionTheory.PerfectFirstCohomology.mem_Z1_iff_cocycle F) (fun _ => rfl) h10 c0 c1 har hq' R'
  exact GlobalTheory.T.first_cohomology_base_change_of_cochain_equivs R R' C F F' m E₀ E₁ E₂ hE₁ h01 h12 H₁ H₂

end Core

theorem perfect_first_cohomology_base_change : PerfectH1BaseChange := by
  intro R _ P _ _ F g hP hS hVB hfib
  haveI : Finite Pᵒᵖ := Finite.of_equiv P Opposite.equivToOpposite
  haveI : ∀ T T' : Pᵒᵖ, Finite (T ⟶ T') := fun _ _ => Finite.of_subsingleton
  obtain ⟨P₀, P₁, P₂, P₃, a₀, a₁, a₂, ψ₀, ψ₁, ψ₂, ⟨f0, p0⟩, ⟨f1, p1⟩, ⟨f2, p2⟩, -, h10, -, c0, c1, -, hq⟩ := hP
  exact GlobalTheory.CompanionTheory.PerfectFirstCohomology.core g h10 c0 c1
    (fun M _ _ => (hq (ModuleCat.of R M)).1) (fun M _ _ => (hq (ModuleCat.of R M)).2.1) hS ⟨hVB.1, hVB.2.1, hVB.2.2⟩ hfib

end GlobalTheory.CompanionTheory.PerfectFirstCohomology
