import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPullOneBijectiveLatticeCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictFiniteAffineCoverInfClosedPull2BijectiveStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MumfordBundleCechFiniteVanishesOffOrigin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechToCatCochainsZeroCoboundaryCommStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechToCatCochainsOneCoboundaryCommStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingToOrderedCechDegreeTwoMemCocyclesTwoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechDegreeZeroCocyclesCorrespondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechCocycleCohomologousPosetOneCocycleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechPrimitiveOfImageCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosetTwoCocycleEqCechImageAddCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechCoboundaryOfDegreeTwoImageCoboundaryAlStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictCompatibleFamilyToIntersectionsBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTrivialBundleCechDifferentialCommStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTrivialBundleCechBijectiveOfAffineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTrivialBundleCechOneTmulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeTrivialBundleCechPullbackCommStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechH1PullbackRefinementCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechH2PullbackRefinementCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechDifferentialZeroConstOneStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CechPoset

theorem orderedCech_toCat_differential_zero_comm : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (c : CC F 0), d0 F (e0 F c) = e1 F (δ F 0 c) := GlobalTheory.T.orderedCechToCatCochainsZero_coboundary_comm
theorem orderedCech_toCat_differential_one_comm : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (c : CC F 1), d1 F (e1 F c) = e2 F (δ F 1 c) := GlobalTheory.T.orderedCech_cochainsOne_coboundary_comm
theorem orderedCech_degreeTwo_cocycle_mem : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (c : CC F 2), δ F 2 c = 0 → e2 F c ∈ Z2 F := GlobalTheory.T.alternatingToOrderedCechDegreeTwo_mem_cocyclesTwo
theorem ker0 : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R), (∀ c : CC F 0, δ F 0 c = 0 → e0 F c = 0 → c = 0) ∧ ∀ g : C0 F, d0 F g = 0 → ∃ c : CC F 0, δ F 0 c = 0 ∧ e0 F c = g := GlobalTheory.T.orderedCechDegreeZero_cocycles_correspond
theorem h1_surj : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (f : Z1 F), ∃ z : CC F 1, δ F 1 z = 0 ∧ ∃ g : C0 F, f.1 - e1 F z = d0 F g := GlobalTheory.T.exists_cech_cocycle_cohomologous_posetOneCocycle
theorem h1_inj : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (z : CC F 1), δ F 1 z = 0 → ∀ g : C0 F, e1 F z = d0 F g → ∃ c : CC F 0, δ F 0 c = z := GlobalTheory.T.exists_cech_primitive_of_image_coboundary
theorem h2_surj : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (w : Z2 F), ∃ y : CC F 2, δ F 2 y = 0 ∧ ∃ f : C1 F, w.1 - e2 F y = d1 F f := GlobalTheory.T.exists_cocycle_sub_e2_eq_d1
theorem h2_inj : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (y : CC F 2), δ F 2 y = 0 → ∀ f : C1 F, e2 F y = d1 F f → ∃ c : CC F 1, δ F 1 c = y := GlobalTheory.T.exists_cech_coboundary_of_degreeTwo_image_coboundary'
theorem restrictCompatibleFamilyToIntersections_bijective_affine_cover : ∀ {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) {κ : Type} [LinearOrder κ] [Fintype κ] (D : κ → X.Opens) (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)), ⨆ i, D i = ⊤ → Function.Bijective (res0 s D hD) := GlobalTheory.T.res0_bijective_of_affine_intersections_of_iSup_eq_top
theorem Φ_δ : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (w : φ ≫ s = s' ≫ spMap (algebraMap R R')) {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)) (p : ℕ) (x : R' ⊗[R] (GlobalTheory.AbLaw.cechLB s (LB.triv X) D).X p), Φ w D hD' (p + 1) (dB (GlobalTheory.AbLaw.cechLB s (LB.triv X) D) R' p (p + 1) x) = δ _ p (Φ w D hD' p x) := GlobalTheory.T.baseChangeTrivialBundleCech_differential_comm
theorem Φ_bijective : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (h : IsPullback φ s' s (spMap (algebraMap R R'))) {κ : Type} [LinearOrder κ] [Fintype κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)), (∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) → ∀ p : ℕ, Function.Bijective (Φ h.w D hD' p) := GlobalTheory.T.baseChangeTrivialBundleCech_bijective_of_affine
theorem Φ_one : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X} (w : φ ≫ s = s' ≫ spMap (algebraMap R R')) {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)), Φ w D hD' 0 ((1 : R') ⊗ₜ[R] one s D) = fun _ => 1 := GlobalTheory.T.baseChangeTrivialBundleCech_one_tmul
theorem Φ_pull : ∀ {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] [Algebra R R'] [Algebra R R''] {X X' X'' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {φ : X' ⟶ X} {φ' : X'' ⟶ X} (w' : φ ≫ s = s' ≫ spMap (algebraMap R R')) (w'' : φ' ≫ s = s'' ≫ spMap (algebraMap R R'')) (α : R' →ₐ[R] R'') (ψ : X'' ⟶ X') (wψ : ψ ≫ s' = s'' ≫ spMap (α : R' →+* R'')), ψ ≫ φ = φ' → ∀ {κ : Type} [LinearOrder κ] (D : κ → X.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i)) (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ' ⁻¹ᵁ D i)) (hle : ∀ i, φ' ⁻¹ᵁ D i ≤ ψ ⁻¹ᵁ (φ ⁻¹ᵁ D i)) (p : ℕ) (z : R' ⊗[R] (GlobalTheory.AbLaw.cechLB s (LB.triv X) D).X p) (t : {s : Finset κ // s.card = p + 1}), Φ w'' D hD'' p (GlobalTheory.AbCoh.ext α _ z) t = (pullCoef wψ (fun i => φ ⁻¹ᵁ D i) hD' (fun i => φ' ⁻¹ᵁ D i) hD'' hle).α (ne t.1 (card_nonempty t)) (Φ w' D hD' p z t) := GlobalTheory.T.baseChangeTrivialBundleCech_pullback_comm
theorem pullHO1_cov : ∀ {R' R'' : Type} [CommRing R'] [CommRing R''] {X' X'' : Scheme.{0}} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R' →+* R''} {ψ : X'' ⟶ X'} (w : ψ ≫ s' = s'' ≫ spMap σ) {κ : Type} [LinearOrder κ] (D' : κ → X'.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D' i)) (D'' : κ → X''.Opens) (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D'' i)) (hle : ∀ i, D'' i ≤ ψ ⁻¹ᵁ D' i) (y : HO1 s'), (CoefMap.restrict (OAff s'') (cov_mono D'' hD'').functor.op).pull1 (pullHO1 w y) = (pullCoef w D' hD' D'' hD'' hle).pull1 ((CoefMap.restrict (OAff s') (cov_mono D' hD').functor.op).pull1 y) := GlobalTheory.T.cech_h1_pullback_refinement_compat
theorem pullHO2_cov : ∀ {R' R'' : Type} [CommRing R'] [CommRing R''] {X' X'' : Scheme.{0}} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R' →+* R''} {ψ : X'' ⟶ X'} (w : ψ ≫ s' = s'' ≫ spMap σ) {κ : Type} [LinearOrder κ] (D' : κ → X'.Opens) (hD' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D' i)) (D'' : κ → X''.Opens) (hD'' : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D'' i)) (hle : ∀ i, D'' i ≤ ψ ⁻¹ᵁ D' i) (y : HO2 s'), (CoefMap.restrict (OAff s'') (cov_mono D'' hD'').functor.op).pull2 (pullHO2 w y) = (pullCoef w D' hD' D'' hD'' hle).pull2 ((CoefMap.restrict (OAff s') (cov_mono D' hD').functor.op).pull2 y) := GlobalTheory.T.cech_h2_pullback_refinement_compat

theorem δ_one : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R), δ F 0 (fun _ => 1) = 0 := GlobalTheory.T.orderedCechDifferential_zero_const_one

end GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset

section Assembly

def kerEquiv {R : Type} [CommRing R] {M N M' N' : Type} [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N'] (f : M →ₗ[R] N)
    (g : M' →ₗ[R] N') (a : M →ₗ[R] M') (b : N →ₗ[R] N') (ha : Function.Bijective a)
    (hb : Function.Injective b) (h : ∀ x, b (f x) = g (a x)) :
    LinearMap.ker f ≃ₗ[R] LinearMap.ker g :=
  LinearEquiv.ofBijective (a.restrict fun x hx => by
      rw [LinearMap.mem_ker] at hx ⊢; rw [← h, hx, map_zero])
    ⟨fun x y e => Subtype.ext (ha.1 (congrArg Subtype.val e)), fun y => by
      obtain ⟨x, hx⟩ := ha.2 y.1
      refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
      rw [LinearMap.mem_ker]
      apply hb
      rw [h, hx, map_zero, LinearMap.mem_ker.1 y.2]⟩

variable {κ : Type} [LinearOrder κ]

theorem cov_inf {X : Scheme.{0}} (D : κ → X.Opens) (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i))
    (I J : NE κ) : (cov D hD (I ⊓ J)).1 = (cov D hD I).1 ⊓ (cov D hD J).1 :=
  Finset.iInf_union

theorem cov_sup {X : Scheme.{0}} (D : κ → X.Opens) (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i))
    (hc : ⨆ i, D i = ⊤) : ⨆ I, (cov D hD I).1 = ⊤ := by
  refine eq_top_iff.2 (hc.symm.le.trans (iSup_le fun i => ?_))
  refine le_trans (le_of_eq ?_) (le_iSup (fun I => (cov D hD I).1) (OrderDual.toDual ⟨{i}, Finset.singleton_nonempty i⟩))
  simp [cov]

variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [Fintype κ] (D : κ → X.Opens)

omit [Fintype κ] in
theorem preimage_sup {X' : Scheme.{0}} (φ : X' ⟶ X) (hc : ⨆ i, D i = ⊤) :
    ⨆ i, φ ⁻¹ᵁ D i = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, hc]; rfl

variable (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) (hc : ⨆ i, D i = ⊤)

variable {R' : Type} [CommRing R'] [Algebra R R'] {X' : Scheme.{0}} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}
  (h : IsPullback φ s' s (spMap (algebraMap R R')))

omit [Fintype κ] in
include h hD in
theorem hDp : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, φ ⁻¹ᵁ D i) :=
  fun _ hI => GlobalTheory.AbLaw.isAffineOpen_biInf_preimage h (hD _ hI)

def rst1 : HO1 s' ≃ₗ[R'] CatCoh.H1 (covF s' (fun i => φ ⁻¹ᵁ D i) (hDp s D hD h)) :=
  LinearEquiv.ofBijective (CoefMap.restrict (OAff s') (cov_mono _ (hDp s D hD h)).functor.op).pull1
    (GlobalTheory.T.cech_pull_one_bijective_lattice_cover R' X' s' (NE κ) (cov _ (hDp s D hD h)) (cov_mono _ _) (cov_inf _ _)
      (cov_sup _ _ (preimage_sup D φ hc)))

def rst2 : HO2 s' ≃ₗ[R'] CatCoh.H2 (covF s' (fun i => φ ⁻¹ᵁ D i) (hDp s D hD h)) :=
  LinearEquiv.ofBijective (CoefMap.restrict (OAff s') (cov_mono _ (hDp s D hD h)).functor.op).pull2
    (GlobalTheory.T.restrict_finite_affineCover_infClosed_pull2_bijective R' X' s' (NE κ) (cov _ (hDp s D hD h)) (cov_mono _ _) (cov_inf _ _)
      (cov_sup _ _ (preimage_sup D φ hc)))

abbrev KK := GlobalTheory.AbLaw.cechLB s (LB.triv X) D

def kerΦ (p : ℕ) : LinearMap.ker (dB (KK s D) R' p (p + 1)) ≃ₗ[R']
    LinearMap.ker (δ (covF s' (fun i => φ ⁻¹ᵁ D i) (hDp s D hD h)) p) :=
  kerEquiv _ _ (Φ h.w D (hDp s D hD h) p) (Φ h.w D (hDp s D hD h) (p + 1))
    (Φ_bijective h D _ hD p) (Φ_bijective h D _ hD (p + 1)).1 (Φ_δ h.w D _ p)

def θ0 : LinearMap.ker (dB (KK s D) R' 0 1) ≃ₗ[R'] LinearMap.ker (d0 (OAff s')) :=
  (kerΦ s D hD h 0).trans ((LinearEquiv.ofBijective
    ((e0 _).restrict (p := LinearMap.ker (δ _ 0)) (q := LinearMap.ker (d0 _)) fun c hc => by
      rw [LinearMap.mem_ker] at hc ⊢; rw [orderedCech_toCat_differential_zero_comm, hc, map_zero])
    ⟨fun x y e => by
      have := (ker0 _).1 (x.1 - y.1) (by rw [map_sub, x.2, y.2, sub_zero])
        (by rw [map_sub]; exact sub_eq_zero.2 (congrArg Subtype.val e))
      exact Subtype.ext (sub_eq_zero.1 this),
     fun g => by
      obtain ⟨c, hc, e⟩ := (ker0 _).2 g.1 g.2
      exact ⟨⟨c, hc⟩, Subtype.ext e⟩⟩).trans
    (LinearEquiv.ofBijective (res0 s' _ (hDp s D hD h)) (restrictCompatibleFamilyToIntersections_bijective_affine_cover s' _ _ (preimage_sup D φ hc))).symm)

def θ1 : LinearMap.ker (dB (KK s D) R' 1 2) →ₗ[R'] HO1 s' :=
  (rst1 s D hD hc h).symm.toLinearMap ∘ₗ H1.mk _ ∘ₗ
    ((e1 _ ∘ₗ (LinearMap.ker (δ _ 1)).subtype ∘ₗ (kerΦ s D hD h 1).toLinearMap).codRestrict (Z1 _) fun z => by
      rw [commAlgFunctorCocyclesOne_eq_ker, LinearMap.mem_ker]
      simp only [LinearMap.comp_apply, Submodule.subtype_apply]
      rw [orderedCech_toCat_differential_one_comm]
      exact (congrArg (e2 _) (LinearMap.mem_ker.1 ((kerΦ s D hD h 1) z).2)).trans (map_zero _))

def θ2 : LinearMap.ker (dB (KK s D) R' 2 3) →ₗ[R'] HO2 s' :=
  (rst2 s D hD hc h).symm.toLinearMap ∘ₗ H2.mk _ ∘ₗ
    ((e2 _ ∘ₗ (LinearMap.ker (δ _ 2)).subtype ∘ₗ (kerΦ s D hD h 2).toLinearMap).codRestrict (Z2 _) fun z =>
      orderedCech_degreeTwo_cocycle_mem _ _ (LinearMap.mem_ker.1 ((kerΦ s D hD h 2) z).2))

theorem orderedCech_restrictionOne_comparison (z : LinearMap.ker (dB (KK s D) R' 1 2)) :
    rst1 s D hD hc h (θ1 s D hD hc h z) = H1.mk _ ⟨e1 _ (Φ h.w D (hDp s D hD h) 1 z.1), (by
      rw [commAlgFunctorCocyclesOne_eq_ker, LinearMap.mem_ker, orderedCech_toCat_differential_one_comm]
      exact (congrArg (e2 _) (LinearMap.mem_ker.1 ((kerΦ s D hD h 1) z).2)).trans (map_zero _))⟩ :=
  (rst1 s D hD hc h).apply_symm_apply _

theorem orderedCech_restrictionTwo_comparison (z : LinearMap.ker (dB (KK s D) R' 2 3)) :
    rst2 s D hD hc h (θ2 s D hD hc h z) = H2.mk _ ⟨e2 _ (Φ h.w D (hDp s D hD h) 2 z.1),
      orderedCech_degreeTwo_cocycle_mem _ _ (LinearMap.mem_ker.1 ((kerΦ s D hD h 2) z).2)⟩ :=
  (rst2 s D hD hc h).apply_symm_apply _

theorem θ1_exact : Function.Surjective (θ1 s D hD hc h) ∧
    ∀ z, θ1 s D hD hc h z = 0 ↔ z.1 ∈ LinearMap.range (dB (KK s D) R' 0 1) := by
  have hb := fun p => Φ_bijective h D (hDp s D hD h) hD p
  refine ⟨fun y => ?_, fun z => ?_⟩
  · obtain ⟨f, hf⟩ := H1.mk_surjective _ (rst1 s D hD hc h y)
    obtain ⟨w, hw, g, hg⟩ := h1_surj _ f
    refine ⟨(kerΦ s D hD h 1).symm ⟨w, hw⟩, (rst1 s D hD hc h).injective ?_⟩
    rw [orderedCech_restrictionOne_comparison, ← hf, H1.mk_eq_mk]
    refine ⟨-g, ?_⟩
    have e : Φ h.w D (hDp s D hD h) 1 ((kerΦ s D hD h 1).symm ⟨w, hw⟩).1 = w :=
      congrArg Subtype.val ((kerΦ s D hD h 1).apply_symm_apply ⟨w, hw⟩)
    simp only [e, map_neg, ← hg]; abel
  · rw [← (rst1 s D hD hc h).map_eq_zero_iff, orderedCech_restrictionOne_comparison, H1.mk_eq_zero]
    constructor
    · rintro ⟨g, hg⟩
      obtain ⟨c, hc'⟩ := h1_inj _ _ (LinearMap.mem_ker.1 ((kerΦ s D hD h 1) z).2) g hg.symm
      obtain ⟨x, rfl⟩ := (hb 0).2 c
      refine ⟨x, (hb 1).1 ?_⟩
      rw [Φ_δ, hc']; rfl
    · rintro ⟨x, hx⟩
      refine ⟨e0 _ (Φ h.w D (hDp s D hD h) 0 x), ?_⟩
      rw [orderedCech_toCat_differential_zero_comm, ← Φ_δ, hx]

theorem θ2_exact : Function.Surjective (θ2 s D hD hc h) ∧
    ∀ z, θ2 s D hD hc h z = 0 ↔ z.1 ∈ LinearMap.range (dB (KK s D) R' 1 2) := by
  have hb := fun p => Φ_bijective h D (hDp s D hD h) hD p
  refine ⟨fun y => ?_, fun z => ?_⟩
  · obtain ⟨f, hf⟩ := H2.mk_surjective _ (rst2 s D hD hc h y)
    obtain ⟨w, hw, g, hg⟩ := h2_surj _ f
    refine ⟨(kerΦ s D hD h 2).symm ⟨w, hw⟩, (rst2 s D hD hc h).injective ?_⟩
    rw [orderedCech_restrictionTwo_comparison, ← hf, H2.mk_eq_mk]
    refine ⟨-g, ?_⟩
    have e : Φ h.w D (hDp s D hD h) 2 ((kerΦ s D hD h 2).symm ⟨w, hw⟩).1 = w :=
      congrArg Subtype.val ((kerΦ s D hD h 2).apply_symm_apply ⟨w, hw⟩)
    simp only [e, map_neg, ← hg]; abel
  · rw [← (rst2 s D hD hc h).map_eq_zero_iff, orderedCech_restrictionTwo_comparison, H2.mk_eq_zero]
    constructor
    · rintro ⟨g, hg⟩
      obtain ⟨c, hc'⟩ := h2_inj _ _ (LinearMap.mem_ker.1 ((kerΦ s D hD h 2) z).2) g hg.symm
      obtain ⟨x, rfl⟩ := (hb 1).2 c
      refine ⟨x, (hb 2).1 ?_⟩
      rw [Φ_δ, hc']; rfl
    · rintro ⟨x, hx⟩
      refine ⟨e1 _ (Φ h.w D (hDp s D hD h) 1 x), ?_⟩
      rw [orderedCech_toCat_differential_one_comm, ← Φ_δ, hx]

end Assembly

section Nat

variable {κ : Type} [LinearOrder κ]

theorem orderedCechToCatCochainsOne_natural {R R'' : Type} [CommRing R] [CommRing R''] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)
    (F'' : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R'') (α : ∀ T, F.obj T →+* F''.obj T)
    (hα : ∀ {T T' : (NE κ)ᵒᵖ} (f : T ⟶ T') (b : F.obj T), α T' (mp F f b) = mp F'' f (α T b))
    (c : CC F 1) (a b : (NE κ)ᵒᵖ) (f : a ⟶ b) :
    e1 F'' (fun t => α _ (c t)) a b f = α b (e1 F c a b f) := by
  simp only [e1, LinearMap.pi_apply]
  split_ifs <;> simp [hα]

theorem alternatingToOrderedCechDegreeTwo_natural {R R'' : Type} [CommRing R] [CommRing R''] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)
    (F'' : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R'') (α : ∀ T, F.obj T →+* F''.obj T)
    (hα : ∀ {T T' : (NE κ)ᵒᵖ} (f : T ⟶ T') (b : F.obj T), α T' (mp F f b) = mp F'' f (α T b))
    (c : CC F 2) (a b d : (NE κ)ᵒᵖ) (f : a ⟶ b) (g : b ⟶ d) :
    e2 F'' (fun t => α _ (c t)) a b d f g = α d (e2 F c a b d f g) := by
  simp only [e2, LinearMap.pi_apply]
  split_ifs <;> simp [hα]

variable {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [Fintype κ] (D : κ → X.Opens)
  (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) (hc : ⨆ i, D i = ⊤)
  {R' : Type} [CommRing R'] [Algebra R R'] {X' : Scheme.{0}} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}
  (h : IsPullback φ s' s (spMap (algebraMap R R')))
  {R'' : Type} [CommRing R''] [Algebra R R''] {X'' : Scheme.{0}} {s'' : X'' ⟶ Sp R''} {φ' : X'' ⟶ X}
  (h' : IsPullback φ' s'' s (spMap (algebraMap R R''))) (α : R' →ₐ[R] R'') (ψ : X'' ⟶ X')
  (w : ψ ≫ s' = s'' ≫ spMap (α : R' →+* R'')) (hcomp : ψ ≫ φ = φ')

include hcomp in
theorem hle : ∀ i, φ' ⁻¹ᵁ D i ≤ ψ ⁻¹ᵁ (φ ⁻¹ᵁ D i) := fun i => by subst hcomp; exact le_rfl

include hcomp in
theorem θ1_nat (z : LinearMap.ker (dB (KK s D) R' 1 2)) (z' : LinearMap.ker (dB (KK s D) R'' 1 2))
    (hz : z'.1 = GlobalTheory.AbCoh.ext α _ z.1) :
    θ1 s D hD hc h' z' = pullHO1 w (θ1 s D hD hc h z) := by
  apply (rst1 s D hD hc h').injective
  rw [orderedCech_restrictionOne_comparison]
  change _ = (CoefMap.restrict _ _).pull1 (pullHO1 w _)
  rw [pullHO1_cov w _ (hDp s D hD h) _ (hDp s D hD h') (hle D ψ hcomp)]
  rw [show (CoefMap.restrict (OAff s') (cov_mono _ (hDp s D hD h)).functor.op).pull1 (θ1 s D hD hc h z) =
    rst1 s D hD hc h (θ1 s D hD hc h z) from rfl, orderedCech_restrictionOne_comparison, CoefMap.pullCohomologyOne_class]
  congr 1
  apply Subtype.ext
  funext a b f
  show e1 _ (Φ h'.w D (hDp s D hD h') 1 z'.1) a b f = (pullCoef w _ (hDp s D hD h) _ (hDp s D hD h')
      (hle D ψ hcomp)).α b (e1 _ (Φ h.w D (hDp s D hD h) 1 z.1) a b f)
  have e : Φ h'.w D (hDp s D hD h') 1 z'.1 = fun t => (pullCoef w _ (hDp s D hD h) _ (hDp s D hD h')
      (hle D ψ hcomp)).α _ (Φ h.w D (hDp s D hD h) 1 z.1 t) := by
    rw [hz]; funext t; exact Φ_pull h.w h'.w α ψ w hcomp D _ _ (hle D ψ hcomp) 1 z.1 t
  rw [e]
  exact orderedCechToCatCochainsOne_natural _ _ _ (fun f b => (pullCoef w _ (hDp s D hD h) _ (hDp s D hD h') (hle D ψ hcomp)).naturality f b) _ a b f

include hcomp in
theorem θ2_nat (z : LinearMap.ker (dB (KK s D) R' 2 3)) (z' : LinearMap.ker (dB (KK s D) R'' 2 3))
    (hz : z'.1 = GlobalTheory.AbCoh.ext α _ z.1) :
    θ2 s D hD hc h' z' = pullHO2 w (θ2 s D hD hc h z) := by
  apply (rst2 s D hD hc h').injective
  rw [orderedCech_restrictionTwo_comparison]
  change _ = (CoefMap.restrict _ _).pull2 (pullHO2 w _)
  rw [pullHO2_cov w _ (hDp s D hD h) _ (hDp s D hD h') (hle D ψ hcomp)]
  rw [show (CoefMap.restrict (OAff s') (cov_mono _ (hDp s D hD h)).functor.op).pull2 (θ2 s D hD hc h z) =
    rst2 s D hD hc h (θ2 s D hD hc h z) from rfl, orderedCech_restrictionTwo_comparison, CoefMap.pullCohomologyTwo_class]
  congr 1
  apply Subtype.ext
  funext a b d f g
  show e2 _ (Φ h'.w D (hDp s D hD h') 2 z'.1) a b d f g = (pullCoef w _ (hDp s D hD h) _ (hDp s D hD h')
      (hle D ψ hcomp)).α d (e2 _ (Φ h.w D (hDp s D hD h) 2 z.1) a b d f g)
  have e : Φ h'.w D (hDp s D hD h') 2 z'.1 = fun t => (pullCoef w _ (hDp s D hD h) _ (hDp s D hD h')
      (hle D ψ hcomp)).α _ (Φ h.w D (hDp s D hD h) 2 z.1 t) := by
    rw [hz]; funext t; exact Φ_pull h.w h'.w α ψ w hcomp D _ _ (hle D ψ hcomp) 2 z.1 t
  rw [e]
  exact alternatingToOrderedCechDegreeTwo_natural _ _ _ (fun f b => (pullCoef w _ (hDp s D hD h) _ (hDp s D hD h') (hle D ψ hcomp)).naturality f b) _ a b d f g

end Nat

end GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset

section Main

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [Fintype κ]
  (D : κ → X.Opens) (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) (hc : ⨆ i, D i = ⊤)
  {R' : Type} [CommRing R'] [Algebra R R'] {X' : Scheme.{0}} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}
  (h : IsPullback φ s' s (spMap (algebraMap R R')))

include hD h in
theorem one_mem : (1 : R') ⊗ₜ[R] one s D ∈ LinearMap.ker (dB (KK s D) R' 0 1) := by
  rw [LinearMap.mem_ker]
  apply (Φ_bijective h D (hDp s D hD h) hD 1).1
  rw [Φ_δ, Φ_one, δ_one, map_zero]

theorem θ0_one (T : AffOp X') : (θ0 s D hD hc h ⟨_, one_mem s D hD h⟩).1 T = 1 := by
  have h1 : (fun _ => 1 : C0 (OAff s')) ∈ LinearMap.ker (d0 (OAff s')) := by
    rw [LinearMap.mem_ker]; funext T T' f; simp [amitsur_d0_apply]
  suffices e : θ0 s D hD hc h ⟨_, one_mem s D hD h⟩ = ⟨_, h1⟩ from congrArg (fun g => g.1 T) e
  unfold θ0
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq]
  apply Subtype.ext
  funext I
  show e0 _ (Φ h.w D (hDp s D hD h) 0 ((1 : R') ⊗ₜ[R] one s D)) I = 1
  rw [Φ_one]
  simp only [e0, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, AlgHom.toLinearMap_apply, map_one]

end Main

end GlobalTheory.CechPoset

theorem GlobalTheory.CechPoset.model_cechLB : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (κ : Type)
    [LinearOrder κ] [Fintype κ] (D : κ → X.Opens), IsSeparated s → (∀ i, IsAffineOpen (D i)) →
    ⨆ i, D i = ⊤ → Nonempty (Model s (GlobalTheory.AbLaw.cechLB s (LB.triv X) D)) := by
  intro R _ X s κ _ _ D hs hDa hc
  haveI := hs
  have hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i) := fun I hI =>
    GlobalTheory.MumfordSupport.isAffineOpen_biInf_of_isSeparated s hDa I hI
  exact ⟨{
    θ0 := fun h => GlobalTheory.CechPoset.θ0 s D hD hc h
    one := GlobalTheory.CechPoset.one s D
    θ0_one := fun h => ⟨GlobalTheory.CechPoset.one_mem s D hD h, GlobalTheory.CechPoset.θ0_one s D hD hc h⟩
    θ1 := fun h => GlobalTheory.CechPoset.θ1 s D hD hc h
    θ2 := fun h => GlobalTheory.CechPoset.θ2 s D hD hc h
    exact := fun h => ⟨(GlobalTheory.CechPoset.θ1_exact s D hD hc h).1, (GlobalTheory.CechPoset.θ1_exact s D hD hc h).2,
      (GlobalTheory.CechPoset.θ2_exact s D hD hc h).1, (GlobalTheory.CechPoset.θ2_exact s D hD hc h).2⟩
    nat := fun {R'} _ _ {X'} {s'} {φ} h {R''} _ _ {X''} {s''} {φ'} h' α ψ w hcomp => ⟨fun z z' hz => GlobalTheory.CechPoset.θ1_nat s D hD hc h h' α ψ w hcomp z z' hz,
      fun z z' hz => GlobalTheory.CechPoset.θ2_nat s D hD hc h h' α ψ w hcomp z z' hz⟩ }⟩
