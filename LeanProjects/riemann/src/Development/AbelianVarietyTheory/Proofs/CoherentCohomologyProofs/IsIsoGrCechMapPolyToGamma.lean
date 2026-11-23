import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsFormOfEqRatioPowMul
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsResMEqSecHomSecToPow
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NonemptyBasisPolyGrading

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Filter DirectSum
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG resG_self)

namespace GlobalTheory

namespace ProjCoh

open MvPolynomial Twist

section General

variable {X : Scheme.{0}} {L : LB X} {ι : Type} (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)]
  (x : ι → LB.Sec L) (hL : L.IsLB) {n m : ℤ}

def oneSection : sectionsOn (twistZ (structureModule X) L 0) ⊤ :=
  (sectionsOn.toΓ _ ⊤).symm ((twistZZeroIso (structureModule X) hL).hom.app ⊤ (1 : Γ(X, ⊤)))

def polyToGamma : MvPolynomial ι R →ₗ[MvPolynomial ι R] GammaStar R x (structureModule X) ⊤ :=
  LinearMap.toSpanSingleton _ _ (gammaOf R x _ ⊤ 0 (oneSection hL))

theorem isGradedMap_polyToGamma :
    IsGradedMap (polyGrading ι R) (gammaGrading R x _ ⊤) (polyToGamma R x hL) := fun _ _ hp => by
  have := grSMul_mem (gammaGrading R x _ ⊤) hp (GrSum.of_mem_grading _ 0 (oneSection hL))
  rwa [zero_add] at this

def formSection (n : ℤ) :
    polyGrading ι R n →ₗ[R] sectionsOn (twistZ (structureModule X) L n) ⊤ :=
  (GrSum.pieceEquiv _ n).symm.toLinearMap ∘ₗ (isGradedMap_polyToGamma R x hL).piece n

theorem gammaOf_formSection (p : polyGrading ι R n) :
    gammaOf R x _ ⊤ n (formSection R x hL n p) = polyToGamma R x hL p :=
  congrArg Subtype.val ((GrSum.pieceEquiv _ n).apply_symm_apply _)

theorem gammaCoord_polyToGamma (i : L.ι) {V : X.Opens} (p : MvPolynomial ι R) :
    (sectionsOn.toΓ _ _ (gammaCoord R x _ V i (gammaRes R x _ le_top (polyToGamma R x hL p))) :
      Γ(X, V ⊓ L.U i)) = chartEval R x i inf_le_right p := by
  rw [polyToGamma, LinearMap.toSpanSingleton_apply, map_smul, gammaCoord_smul, gammaRes_gammaOf,
    gammaCoord_gammaOf]
  refine (congrArg (_ • ·) ((zcoord_resM le_top _ i).trans (congrArg _
    (zcoord_twistZZeroIso_hom_app (F := structureModule X) hL (1 : Γ(X, ⊤)) i)))).trans ?_
  change _ * resG X _ (resG X _ 1) = _
  rw [map_one, map_one, mul_one]

theorem zcoord_formSection (p : polyGrading ι R n) (i : L.ι) :
    (zcoord (sectionsOn.toΓ _ ⊤ (formSection R x hL n p)) i : Γ(X, ⊤ ⊓ L.U i)) =
      chartEval R x i inf_le_right p.1 := by
  rw [← gammaCoord_polyToGamma R x hL, ← gammaOf_formSection, gammaRes_gammaOf,
    gammaCoord_gammaOf, sectionsOn.res_refl, LinearMap.id_apply]

theorem globalEquiv_formSection (p : polyGrading ι R n) :
    LB.globalEquiv _ ((unitTwistIso (lbZPow L n)).hom.app ⊤
      (sectionsOn.toΓ _ ⊤ (formSection R x hL n p))) = Twist.formSec x p.2 := by
  refine zglobal_ext fun i => ?_
  rw [zfun_formSec, ← resG_chartEval R x i (inf_le_right : ⊤ ⊓ L.U i ≤ _) (le_inf le_top le_rfl),
    ← zcoord_formSection R x hL]
  exact (resG_resG _ _ _).trans (resG_resG _ _ _).symm

include hL in

theorem eq_zero_of_gammaCoord {F : X.Modules} {V : X.Opens} {i : L.ι} (h : V ≤ L.U i)
    {y : GammaStar R x F V} (hy : y ∈ gammaGrading R x F V n)
    (h0 : sectionsOn.toΓ _ _ (gammaCoord R x F V i y) = 0) : y = 0 := by
  obtain ⟨a, rfl⟩ := hy
  rw [gammaCoord_gammaOf] at h0
  have : sectionsOn.toΓ _ V a = 0 := (zchartEquiv hL n i h).injective (by
    rw [zchartEquiv_apply, h0, map_zero, map_zero])
  rw [(map_eq_zero_iff _ (sectionsOn.toΓ _ V).injective).1 this, map_zero]

theorem gammaRes_smul_sub_eq_zero {V : X.Opens} {i : L.ι} (h : V ≤ L.U i) {p q : MvPolynomial ι R}
    {y : GammaStar R x (structureModule X) ⊤} (h₁ : q • y ∈ gammaGrading R x _ ⊤ n)
    (h₂ : p ∈ polyGrading ι R n) (u : Γ(X, V ⊓ L.U i))
    (hu : u = sectionsOn.toΓ _ _ (gammaCoord R x _ V i (gammaRes R x _ le_top y)))
    (e : chartEval R x i inf_le_right q * u = chartEval R x i inf_le_right p) :
    gammaRes R x _ (le_top : V ≤ ⊤) (q • y - polyToGamma R x hL p) = 0 := by
  refine eq_zero_of_gammaCoord R x hL h
    (isGradedMap_gammaRes R _ _ _ (sub_mem h₁ (isGradedMap_polyToGamma R x hL h₂))) ?_
  rw [map_sub, map_sub, map_sub, map_smul, gammaCoord_smul, sub_eq_zero, ← hu]
  exact e.trans (gammaCoord_polyToGamma R x hL i _).symm

def formSecAdd (n : ℤ) : polyGrading ι R n →+ LB.Sec (lbZPow L n) :=
  AddMonoidHom.mk' (fun p => Twist.formSec x p.2) fun p q => zglobal_ext fun i => by
    simp only [zfun_add, zfun_formSec, Submodule.coe_add, map_add]

theorem formSec_one (h : (1 : MvPolynomial ι R) ∈ polyGrading ι R 0) :
    Twist.formSec x h = zone L :=
  zglobal_ext fun i => by rw [zfun_formSec, map_one, zfun_zone]

theorem formSec_mul {p q : MvPolynomial ι R} (hp : p ∈ polyGrading ι R n)
    (hq : q ∈ polyGrading ι R m) (h : p * q ∈ polyGrading ι R (n + m)) :
    Twist.formSec x h = zmul (Twist.formSec x hp) (Twist.formSec x hq) :=
  zglobal_ext fun i => by simp only [zfun_zmul, zfun_formSec, map_mul]

theorem formSec_smul (r : R) {p : MvPolynomial ι R} (hp : p ∈ polyGrading ι R n)
    (h : r • p ∈ polyGrading ι R n) :
    Twist.formSec x h = algebraMap R Γ(X, ⊤) r • Twist.formSec x hp :=
  zglobal_ext fun i => by
    rw [zfun_smul, zfun_formSec, zfun_formSec, smul_eq_C_mul, map_mul, chartEval_C]

def formsToSecRing : (⨁ n, polyGrading ι R n) →+* SecRing L :=
  DirectSum.toSemiring (fun n => (SecRing.of n).comp (formSecAdd R x n))
    (congrArg (SecRing.of 0) (formSec_one R x SetLike.GradedOne.one_mem))
    (fun {n m} p q => (congrArg (SecRing.of (n + m))
      (formSec_mul R x p.2 q.2 (SetLike.mul_mem_graded p.2 q.2))).trans
        (SecRing.of_mul_of _ _).symm)

def polyToSecRing : MvPolynomial ι R →+* SecRing L :=
  (formsToSecRing R x).comp (DirectSum.decomposeRingEquiv (polyGrading ι R)).toRingHom

theorem polyToSecRing_of_mem {p : MvPolynomial ι R} (hp : p ∈ polyGrading ι R n) :
    polyToSecRing R x p = SecRing.of n (Twist.formSec x hp) :=
  (congrArg (formsToSecRing R x) (DirectSum.decompose_of_mem _ hp)).trans
    (DirectSum.toSemiring_of _ _ _ _ _)

theorem polyToSecRing_bijective (h : ∀ n, Function.Bijective (formSecAdd R x n)) :
    Function.Bijective (polyToSecRing R x) := by
  have e : ⇑(polyToSecRing R x) = DirectSum.map (β := RingPiece L) (formSecAdd R x) ∘
      DirectSum.decompose (polyGrading ι R) := funext fun p => by
    induction p using Decomposition.inductionOn (polyGrading ι R) with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb, Function.comp_apply, decompose_add]
    | homogeneous a =>
      rw [polyToSecRing_of_mem R x a.2, Function.comp_apply, decompose_coe]
      exact (DirectSum.map_of (β := RingPiece L) (formSecAdd R x) _ a).symm
  rw [e]
  exact Function.Bijective.comp ⟨(DirectSum.map_injective _).2 fun n => (h n).1,
    (DirectSum.map_surjective _).2 fun n => (h n).2⟩ (DirectSum.decompose _).bijective

end General

section Proj

open GlobalTheory.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type) [CommRing R] (N : ℕ)

abbrev sheafO (n : ℤ) : (PSpace R N).Modules :=
  twistZ (structureModule (PSpace R N)) (O1 R N) n

instance isQuasicoherent_sheafO (n : ℤ) : (sheafO R N n).IsQuasicoherent :=
  isQuasicoherent_twist (isLB_lbZPow (O1_isLB R N) n)

def sheafOIso (n : ℤ) : sheafO R N n ≅ LB.toMod (On R N n) := unitTwistIso _

theorem isCompact_top : IsCompact ((⊤ : (PSpace R N).Opens) : Set (PSpace R N)) := by
  rw [← iSup_chart, Opens.coe_iSup]
  exact isCompact_iUnion fun i => (isAffineOpen_chart R N i).isCompact

theorem isQuasiSeparated_top :
    IsQuasiSeparated ((⊤ : (PSpace R N).Opens) : Set (PSpace R N)) := isQuasiSeparated_univ

theorem isAffineOpen_biInf_coord (s : Finset (Fin (N + 1))) (hs : s.Nonempty) :
    IsAffineOpen (⨅ i ∈ s, Out.nonzeroLocus (ProjSpace.coord R N i)) :=
  isAffineOpen_finset_biInf (fun i => by
    rw [nonzeroLocus_coord]; exact isAffineOpen_chart R N i) s hs

variable {R N} in

theorem chartEval_coord (i : Fin (N + 1)) {U : (PSpace R N).Opens} (h : U ≤ chart R N i)
    (p : MvPolynomial (Fin (N + 1)) R) :
    chartEval (L := O1 R N) R (ProjSpace.coord R N) i h p = aeval (ratioOn U i h) p := by
  induction p using MvPolynomial.induction_on with
  | C r => exact (chartEval_C _ _ _ _ r).trans ((resG_algebraMap _ r).trans (algHom_C _ r).symm)
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    rw [map_mul, map_mul, hp, aeval_X]
    exact congrArg (_ * ·) (chartEval_X _ _ _ _ j)

theorem formSection_injective (n : ℤ) :
    Function.Injective (formSection R (ProjSpace.coord R N) (O1_isLB R N) n) := by
  refine (injective_iff_map_eq_zero _).2 fun p hp => Subtype.ext ?_
  rcases lt_or_ge n 0 with h | h
  · exact (Submodule.eq_bot_iff _).1 (polyGrading_of_neg _ R h) _ p.2
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    have hf := mem_polyGrading_natCast.1 p.2
    have e := zcoord_formSection R (ProjSpace.coord R N) (O1_isLB R N) p (0 : Fin (N + 1))
    rw [hp, map_zero] at e
    replace e := (zcoord_zero _).symm.trans e
    have e' := congrArg (resG _ (le_inf le_top le_rfl : chart R N 0 ≤ ⊤ ⊓ chart R N 0)) e
    refine (formOn_chart_inj R N 0 hf (isHomogeneous_zero _ R n)).1 ?_
    rw [formOn_zero, formOn_eq_aeval, ← chartEval_coord]
    exact ((resG_chartEval _ _ _ _ _ _).symm.trans e'.symm).trans (map_zero _)

theorem polyToGamma_injective :
    Function.Injective (polyToGamma R (ProjSpace.coord R N) (O1_isLB R N)) :=
  (isGradedMap_polyToGamma R _ _).injective_iff.2 fun n _ _ h =>
    formSection_injective R N n (congrArg (GrSum.pieceEquiv _ n).symm h)

theorem exists_pow_smul_mem_range (i : Fin (N + 1))
    (y : GammaStar R (ProjSpace.coord R N) (structureModule _) ⊤) :
    ∃ k : ℕ, (X i : MvPolynomial (Fin (N + 1)) R) ^ k • y ∈
      LinearMap.range (polyToGamma R (ProjSpace.coord R N) (O1_isLB R N)) := by
  induction y using Decomposition.inductionOn
    (gammaGrading R (ProjSpace.coord R N) (structureModule _) ⊤) with
  | zero => exact ⟨0, by simp⟩
  | add y z hy hz =>
    obtain ⟨k, hk⟩ := hy
    obtain ⟨l, hl⟩ := hz
    refine ⟨k + l, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [add_comm k, pow_add, mul_smul]; exact Submodule.smul_mem _ _ hk
    · rw [pow_add, mul_smul]; exact Submodule.smul_mem _ _ hl
  | @homogeneous n y =>
    obtain ⟨y, hy⟩ := y
    let V := chart R N i
    let u : Γ(PSpace R N, V ⊓ V) := sectionsOn.toΓ _ _
      (gammaCoord R (ProjSpace.coord R N) _ V i (gammaRes R _ _ le_top y))
    obtain ⟨d, f, hf, hu⟩ := Model.exists_formOn i (resG _ (le_inf le_rfl le_rfl) u)
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (a := d + n.natAbs - n) (by omega)
    have h₁ : (X i : MvPolynomial (Fin (N + 1)) R) ^ k • y ∈
        gammaGrading R (ProjSpace.coord R N) _ ⊤ (d + n.natAbs : ℕ) := by
      have := grSMul_mem _ (mem_polyGrading_natCast.2 (isHomogeneous_X_pow (R := R) i k)) hy
      rwa [show n + k = (d + n.natAbs : ℕ) by omega] at this
    have h₃ := gammaRes_smul_sub_eq_zero R _ (O1_isLB R N) (V := V) (i := i) le_rfl h₁
      (mem_polyGrading_natCast.2 (hf.mul (isHomogeneous_X_pow i n.natAbs))) u rfl (by
      have e : u = formOn (V ⊓ V) i inf_le_right d f hf :=
        ((resG_resG _ _ _).trans (resG_self _ _)).symm.trans
          (congrArg (resG _ (inf_le_right : V ⊓ V ≤ V)) hu)
      rw [e, formOn_eq_aeval]
      refine (congrArg (· * _) (chartEval_coord i inf_le_right _)).trans
        (Eq.trans ?_ (chartEval_coord i inf_le_right _).symm)
      simp [V])
    obtain ⟨l, hl⟩ := (eventually_xProd_pow_smul_eq_zero R (ProjSpace.coord R N) _ (O1_isLB R N)
      (isCompact_top R N) (I := {i}) le_top (by simp [nonzeroLocus_coord, V]) _ h₃).exists
    rw [xProd, Finset.prod_singleton, smul_sub, sub_eq_zero, ← map_smul, ← mul_smul,
      ← pow_add] at hl
    exact ⟨l + k, _, hl.symm⟩

instance isIso_grCechMap_polyToGamma (n : ℤ) :
    IsIso (grCechMap (isGradedMap_polyToGamma R (ProjSpace.coord R N) (O1_isLB R N)) n) :=
  isIso_grCechMap _ (fun _ m hm => ⟨0, by
    rw [polyToGamma_injective R N (hm.trans (map_zero _).symm), smul_zero]⟩)
    (exists_pow_smul_mem_range R N) n

def grCechIso (n : ℤ) : grCech (Fin (N + 1)) (polyGrading (Fin (N + 1)) R) n ≅
    cech R (sheafO R N n) ⊤ fun j => Out.nonzeroLocus (ProjSpace.coord R N j) :=
  asIso (grCechMap (isGradedMap_polyToGamma R (ProjSpace.coord R N) (O1_isLB R N)) n) ≪≫
    gammaCechIso R _ _ (O1_isLB R N) (isCompact_top R N) (isQuasiSeparated_top R N) n

def grHEquiv (n : ℤ) (p : ℕ) :
    grH (Fin (N + 1)) (polyGrading (Fin (N + 1)) R) n p ≃ₗ[R] coh (sheafO R N n) p :=
  ((HomologicalComplex.homologyFunctor _ _ p).mapIso (grCechIso R N n)).toLinearEquiv.trans
    (cechHEquivCoh R (iSup_nonzeroLocus_coord R N) (isAffineOpen_biInf_coord R N) _ p)

variable {N} in

theorem formSection_bijective (hN : 1 ≤ N) (n : ℤ) :
    Function.Bijective (formSection R (ProjSpace.coord R N) (O1_isLB R N) n) := by
  have hφ := isGradedMap_polyToGamma R (ProjSpace.coord R N) (O1_isLB R N)
  have e := (cubeFunctor _ R).mapIso (gammaCubeIso R (ProjSpace.coord R N) (structureModule _)
    (O1_isLB R N) (isCompact_top R N) (isQuasiSeparated_top R N) n)
  have hc := cechCube_exactAt_zero_one R (sheafO R N n) (iSup_nonzeroLocus_coord R N).ge
  have h₁ := (grAug_bijective_iff _ n).2 ⟨hc.1.of_iso e.symm, hc.2.of_iso e.symm⟩
  have h₂ : Function.Bijective (grHMap hφ n 0).hom := ConcreteCategory.bijective_of_isIso _
  have h₃ := h₂.comp (grAug_bijective R N n hN)
  rw [show (grHMap hφ n 0).hom ∘ grAug _ _ n = grAug _ _ n ∘ hφ.piece n from
    funext (grHMap_grAug hφ n), h₁.of_comp_iff'] at h₃
  exact (GrSum.pieceEquiv _ n).symm.bijective.comp h₃

variable {N} in

def formsEquivSections (hN : 1 ≤ N) (n : ℤ) :
    polyGrading (Fin (N + 1)) R n ≃ₗ[R] sectionsOn (sheafO R N n) ⊤ :=
  .ofBijective _ (formSection_bijective R hN n)

variable {N} in

def formsEquivCohZero (hN : 1 ≤ N) (n : ℤ) :
    polyGrading (Fin (N + 1)) R n ≃ₗ[R] coh (sheafO R N n) 0 :=
  (formsEquivSections R hN n).trans (cohOn.zeroEquiv R _ ⊤).symm

variable {N} in

theorem formSecAdd_bijective (hN : 1 ≤ N) (n : ℤ) :
    Function.Bijective (formSecAdd R (ProjSpace.coord R N) n) := by
  have := (LB.globalEquiv _).bijective.comp ((ConcreteCategory.bijective_of_isIso
    ((unitTwistIso (lbZPow (O1 R N) n)).hom.app ⊤)).comp
      ((sectionsOn.toΓ _ ⊤).bijective.comp (formSection_bijective R hN n)))
  convert this using 1
  exact funext fun p => (globalEquiv_formSection R _ (O1_isLB R N) p).symm

variable {N} in

def polyEquivSecRing (hN : 1 ≤ N) : MvPolynomial (Fin (N + 1)) R ≃+* SecRing (O1 R N) :=
  .ofBijective _ (polyToSecRing_bijective R (ProjSpace.coord R N) (formSecAdd_bijective R hN))

variable {R N} in

theorem formSec_eq {n : ℕ} {f : MvPolynomial (Fin (N + 1)) R} (hf : f.IsHomogeneous n) :
    ProjSpace.formSec n f hf =
      Twist.formSec (ProjSpace.coord R N) (mem_polyGrading_natCast.2 hf) :=
  zglobal_ext (L := O1 R N) (m := n) fun i => by
    rw [zfun_formSec]
    exact (formOn_eq_aeval (U := chart R N i) (hi := le_rfl) hf).trans
      (chartEval_coord i le_rfl f).symm

theorem subsingleton_coh (n : ℤ) {p : ℕ} (h0 : p ≠ 0) (hp : p ≠ N) :
    Subsingleton (coh (sheafO R N n) p) :=
  have := ModuleCat.subsingleton_of_isZero (isZero_grH_poly R N n h0 hp)
  (grHEquiv R N n p).symm.injective.subsingleton

variable {N} in

theorem nonempty_basis_coh_top (hN : 1 ≤ N) (n : ℤ) :
    Nonempty (Module.Basis (NegExp N n) R (coh (sheafO R N n) N)) :=
  (nonempty_basis_grH_top R N n hN).map fun b => b.map (grHEquiv R N n N)

variable {N} in

theorem subsingleton_coh_top (hN : 1 ≤ N) {n : ℤ} (hn : -(N : ℤ) ≤ n) :
    Subsingleton (coh (sheafO R N n) N) :=
  have ⟨b⟩ := nonempty_basis_coh_top R hN n
  have := isEmpty_negExp N hn
  b.repr.injective.subsingleton

theorem subsingleton_coh_of_neg_le {n : ℤ} (hn : -(N : ℤ) ≤ n) {p : ℕ} (hp : 0 < p) :
    Subsingleton (coh (sheafO R N n) p) := by
  by_cases h : p = N
  · subst h
    exact subsingleton_coh_top R hp hn
  · exact subsingleton_coh R N n hp.ne' h

variable {N} in

theorem subsingleton_coh_zero (hN : 1 ≤ N) {n : ℤ} (hn : n < 0) :
    Subsingleton (coh (sheafO R N n) 0) :=
  have : Subsingleton (polyGrading (Fin (N + 1)) R n) := by
    rw [polyGrading_of_neg _ R hn]; infer_instance
  (formsEquivCohZero R hN n).symm.injective.subsingleton

theorem nonempty_coh_zero_equiv (n : ℤ) : Nonempty (coh (sheafO R 0 n) 0 ≃ₗ[R] R) :=
  (nonempty_grH_zero_equiv R n).map (grHEquiv R 0 n 0).symm.trans

theorem finite_free_coh (n : ℤ) (p : ℕ) :
    Module.Finite R (coh (sheafO R N n) p) ∧ Module.Free R (coh (sheafO R N n) p) := by
  by_cases hp : p ≠ 0 ∧ p ≠ N
  · have := subsingleton_coh R N n hp.1 hp.2
    exact ⟨inferInstance, inferInstance⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · obtain rfl : p = 0 := by tauto
    obtain ⟨e⟩ := nonempty_coh_zero_equiv R n
    exact ⟨.equiv e.symm, .of_equiv e.symm⟩
  by_cases h0 : p = 0
  · subst h0
    obtain ⟨b⟩ := nonempty_basis_polyGrading R N n
    exact ⟨.of_basis (b.map (formsEquivCohZero R hN n)),
      .of_basis (b.map (formsEquivCohZero R hN n))⟩
  · obtain rfl : p = N := by tauto
    obtain ⟨b⟩ := nonempty_basis_coh_top R hN n
    exact ⟨.of_basis b, .of_basis b⟩

instance finite_coh (n : ℤ) (p : ℕ) : Module.Finite R (coh (sheafO R N n) p) :=
  (finite_free_coh R N n p).1

instance free_coh (n : ℤ) (p : ℕ) : Module.Free R (coh (sheafO R N n) p) :=
  (finite_free_coh R N n p).2

variable {N} in

theorem finrank_coh_zero [Nontrivial R] (hN : 1 ≤ N) (n : ℤ) :
    Module.finrank R (coh (sheafO R N n) 0) = (n + N).toNat.choose N := by
  obtain ⟨b⟩ := nonempty_basis_polyGrading R N n
  rw [Module.finrank_eq_nat_card_basis (b.map (formsEquivCohZero R hN n)), card_natVec N hN]

variable {N} in

theorem finrank_coh_top [Nontrivial R] (hN : 1 ≤ N) (n : ℤ) :
    Module.finrank R (coh (sheafO R N n) N) = (-n - 1).toNat.choose N := by
  obtain ⟨b⟩ := nonempty_basis_coh_top R hN n
  rw [Module.finrank_eq_nat_card_basis b, card_negExp N hN]

end Proj

section Field

open GlobalTheory.ProjSpace

variable (k : Type) [Field k] (N : ℕ)

theorem chi_sheafO (n : ℤ) : chi k (sheafO k N n) = Ring.choose (n + N) N := by
  rcases N with _ | N
  · obtain ⟨e⟩ := nonempty_coh_zero_equiv k n
    rw [chi_eq_hdim_zero k fun p hp => subsingleton_coh k 0 n hp.ne' hp.ne', hdim_def,
      e.finrank_eq, Ring.choose_zero_right]
    simp
  · rw [chi_eq_sum_range k (N + 1 + 1) fun _ hp => subsingleton_coh k _ n (by omega) (by omega),
      Finset.sum_range_succ, Finset.sum_range_succ', Finset.sum_eq_zero fun p hp => ?_,
      hdim_def, hdim_def, finrank_coh_zero k (by omega), finrank_coh_top k (by omega),
      choose_eq_add _ (by omega)]
    · simp
    · have := subsingleton_coh k (N + 1) n (p := p + 1) (by omega)
        (by have := Finset.mem_range.1 hp; omega)
      simp [hdim_eq_zero_of_subsingleton]

theorem chi_sheafO_eq_eval (n : ℤ) :
    (chi k (sheafO k N n) : ℚ) = (Polynomial.preHilbertPoly ℚ N 0).eval (n : ℚ) := by
  have e := congrArg (Int.cast : ℤ → ℚ) (Ring.factorial_nsmul_multichoose_eq_ascPochhammer (n + 1) N)
  rw [Polynomial.ascPochhammer_smeval_eq_eval, nsmul_eq_mul] at e
  have e' : (((ascPochhammer ℤ N).eval (n + 1) : ℤ) : ℚ) = (ascPochhammer ℚ N).eval ((n : ℚ) + 1) := by
    rw [← ascPochhammer_map (Int.castRingHom ℚ), show (n : ℚ) + 1 = ((n + 1 : ℤ) : ℚ) by simp]
    exact (Polynomial.eval_map_apply (Int.castRingHom ℚ) _).symm
  rw [chi_sheafO, Ring.choose, add_sub_cancel_right, Polynomial.preHilbertPoly,
    Polynomial.eval_smul, Polynomial.eval_comp]
  have h : (N.factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.2 N.factorial_ne_zero
  simp only [Nat.cast_zero, map_zero, sub_zero, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one, smul_eq_mul, ← e', ← e]
  push_cast
  field_simp

end Field

end ProjCoh

end GlobalTheory
