import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulOriginSec
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsStandardSmoothOfRelativeDimensionAwayJacobian
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddXYZOrChordXYZOrOriginXYZNeZero
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.ExistsLiftAddOfIsReducedEq
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsGrpObjIsAddLawHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeSchemeOver
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveFst
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsoLineBundleOfRegularPullbacksSameZeroScheme
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SymmetricLineBundleOfRegularSection
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.KernelPolarisationTrivialOfSectionsVanishZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.OriginLineBundlePolarisation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

namespace GlobalTheory.WeierstrassCurve

variable {R : Type} [CommRing R] (W : _root_.WeierstrassCurve R)

variable [W.IsElliptic]

theorem appLE_originSec_eq_zero_iff_eSec (T : Scheme.{0}) (t : T ⟶ (schemeOver W).left)
    (i : (originLB W).ι) (h : ⊤ ≤ t ⁻¹ᵁ (originLB W).U i) :
    (t.appLE ((originLB W).U i) ⊤ h).hom ((originSec W).f i) = 0 ↔
      t = t ≫ (schemeOver W).hom ≫ eSec (schemeOver W) := by
  rw [show eSec (schemeOver W) = zero W from one_left W]
  exact appLE_originSec_eq_zero_iff W t i h

theorem rigidified_originLB : Out.Rigidified (schemeOver W) (originLB W) := by
  unfold Out.Rigidified
  rw [show eSec (schemeOver W) = zero W from one_left W]
  exact ⟨_, isGen_one_pull_zero W⟩

theorem sym_originLB : Out.Sym (schemeOver W) (originLB W) := by
  intro s
  refine ⟨⊤, trivial, ?_⟩
  have : IsIso (GrpObj.inv : schemeOver W ⟶ schemeOver W).left :=
    inferInstanceAs (IsIso ((Over.forget _).map (GrpObj.inv : schemeOver W ⟶ schemeOver W)))
  have hreg := fun i V h => ((isRegularSec_originSec W i).resG (V := V) h).mem
  refine SameZeroScheme.exists_isGen_linComb (schemeOver W).left _ (originLB W) (originSec W) _ _
    (originLB_isLB W)
    (fun i V h => SymOfZeroDivisor.appLE_mem_nonZeroDivisors _ _ _ (hreg i) V h)
    (fun i V h => SymOfZeroDivisor.appLE_mem_nonZeroDivisors _ _ _ (hreg i) V h) ?_
  intro T t i j h h'
  rw [appLE_originSec_eq_zero_iff_eSec, appLE_originSec_eq_zero_iff_eSec, ← Category.assoc t]
  exact SymOfZeroDivisor.inv_eq_zero_iff (schemeOver W) _

theorem kTriv_originLB : Out.KTriv (schemeOver W) (originLB W) := by
  refine kTriv_of_sections_vanish_on_zero _ (schemeOver W) (originLB W) (originSec W)
    (originLB_isLB W) (appLE_originSec_eq_zero_iff_eSec W) ?_
  intro R' _ f Y φ q H s T t j h e
  rw [show eSec (schemeOver W) = zero W from one_left W] at e
  exact appLE_sec_pull_originLB_eq_zero W H s t j h e

def ellPolAV : Out.PolAV (Spec (CommRingCat.of R)) where
  A := schemeOver W
  grp := grpObj W
  isAb := isAbelianScheme_schemeOver R W W.isUnit_Δ (isCommMonObj W)
  g := 1
  smoothDim := smoothOfRelativeDimension_toSpec_of_isUnit W W.isUnit_Δ
  L := originLB W
  isLB := originLB_isLB W
  rigid := rigidified_originLB W
  sym := sym_originLB W
  ample := relAmple_originLB W
  ktriv := kTriv_originLB W

theorem ellPolAV_A : (ellPolAV W).A = schemeOver W := rfl

theorem ellPolAV_hom : (ellPolAV W).A.hom = toSpec W := rfl

theorem ellPolAV_grp : (ellPolAV W).grp = grpObj W := rfl

@[simp] theorem ellPolAV_g : (ellPolAV W).g = 1 := rfl

theorem ellPolAV_L : (ellPolAV W).L = originLB W := rfl

theorem eSec_ellPolAV : eSec (ellPolAV W).A = zero W := one_left W

theorem isAddLawHom_ellPolAV : IsAddLawHom W μ[(ellPolAV W).A] := isAddLawHom_mul W

theorem ptHom_ellPolAV_inv {A : Type} [CommRing A] (ρ : R →+* A) (P : Fin 3 → A)
    (hP : IsUnimodularSol (W.map ρ) P) :
    ∃ hN : IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.neg P),
      ptHom W ρ P hP ≫ (GrpObj.inv : (ellPolAV W).A ⟶ (ellPolAV W).A).left = ptHom W ρ _ hN :=
  ⟨hP.neg, (congrArg (_ ≫ ·) (inv_left W)).trans (ptHom_negHom W ρ P hP)⟩

def ellTheta : (ellPolAV W).L.Sec := originSec W

theorem ellTheta_eq : ellTheta W = originSec W := rfl

theorem nonzeroLocus_ellTheta : Out.nonzeroLocus (ellTheta W) = coordOpen W 2 :=
  nonzeroLocus_originSec W

theorem secPull_ellTheta_eq_zero_iff {T : Scheme.{0}} (t : T ⟶ (ellPolAV W).A.left) :
    (∀ j, (Cartier.secPull (ellTheta W) t).f j = 0) ↔
      t = t ≫ (ellPolAV W).A.hom ≫ eSec (ellPolAV W).A := by
  rw [eSec_ellPolAV]
  exact secPull_originSec_eq_zero_iff W t

theorem existsUnique_eq_const_mul_ellTheta (s : (ellPolAV W).L.Sec) :
    ∃! c : R, ∀ i, s.f i = constFn (ellPolAV W).A.hom ((ellPolAV W).L.U i) c * (ellTheta W).f i :=
  existsUnique_eq_const_mul_originSec W s

theorem exists_isLieBasis_ellPolAV : ∃ v : epsR R ⟶ (ellPolAV W).A,
    (∃ h : IsUnimodularSol (W.map (algebraMap R (DualNumber R))) ![DualNumber.eps, -1, 0],
      v.left = ptHom W (algebraMap R (DualNumber R)) ![DualNumber.eps, -1, 0] h) ∧
    IsLieBasis ![v] :=
  WeierstrassLie.isLieBasis_eps R W (one_left W)

section BaseChange

variable {R' : Type} [CommRing R'] {W' : _root_.WeierstrassCurve R'} [W'.IsElliptic]
  (f : R →+* R') (h : W.map f = W')

theorem isGrpPullback_ellPolAV :
    IsGrpPullback (ellPolAV W').A (ellPolAV W).A (spMap f) (mapHom W f h) :=
  isGrpPullback_mapHom W f h

theorem lbIso_ellPolAV : LBIso (ellPolAV W').L ((ellPolAV W).L.pull (mapHom W f h)) :=
  lbIso_pull_originLB W f h

theorem ellPolAV_baseChange : (ellPolAV W').g = (ellPolAV W).g ∧
    IsGrpPullback (ellPolAV W').A (ellPolAV W).A (spMap f) (mapHom W f h) ∧
    LBIso ((ellPolAV W).L.pull (mapHom W f h)) (ellPolAV W').L :=
  ⟨rfl, isGrpPullback_ellPolAV W f h, (lbIso_ellPolAV W f h).symm⟩

end BaseChange

theorem not_isGen_ellPolAV [Nontrivial R] (t : (ellPolAV W).L.Gen) : ¬ t.IsGen :=
  not_isGen_originLB W t

theorem weierstrass_0_0_1_neg_one_0_isElliptic : (⟨0, 0, 1, -1, 0⟩ : _root_.WeierstrassCurve ℚ).IsElliptic :=
  ⟨by
    have : (⟨0, 0, 1, -1, 0⟩ : _root_.WeierstrassCurve ℚ).Δ = 37 := by
      norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
        WeierstrassCurve.b₈]
    rw [this]
    exact Ne.isUnit (by norm_num)⟩

example : ∃ P : Out.PolAV (Spec (CommRingCat.of ℚ)), P.g = 1 ∧ ∀ t : P.L.Gen, ¬ t.IsGen :=
  haveI := weierstrass_0_0_1_neg_one_0_isElliptic
  ⟨ellPolAV ⟨0, 0, 1, -1, 0⟩, rfl, not_isGen_ellPolAV _⟩

example :
    let E : _root_.WeierstrassCurve ℚ := ⟨0, 0, 1, -1, 0⟩
    haveI : E.IsElliptic := weierstrass_0_0_1_neg_one_0_isElliptic
    ∃ x y z : specOver ℚ ℚ ⟶ (ellPolAV E).A,
      (∃ h, x.left = pt E ![0, 0, 1] h) ∧ (∃ h, y.left = pt E ![0, -1, 1] h) ∧
      (∃ h, z.left = pt E ![1, 0, 1] h) ∧ x⁻¹ = y ∧ x * x = z := by
  intro E
  have : E.IsElliptic := weierstrass_0_0_1_neg_one_0_isElliptic
  have h : ∀ a b : ℚ, b ^ 2 + b = a ^ 3 - a → IsUnimodularSol (E.baseChange ℚ) ![a, b, 1] :=
    fun a b e => isUnimodularSol_some (by
      rw [WeierstrassCurve.Affine.equation_iff]
      simp [E]
      linear_combination e)
  have h₀ := h 0 0 (by norm_num)
  have h₁ := h 0 (-1) (by norm_num)
  have h₂ := h 1 0 (by norm_num)
  refine ⟨ptOver E _ h₀, ptOver E _ h₁, ptOver E _ h₂, ⟨h₀, rfl⟩, ⟨h₁, rfl⟩, ⟨h₂, rfl⟩, ?_, ?_⟩
  · refine (ptOver_inv E h₀).trans (Over.OverMorphism.ext (pt_congr E _ h₀.neg ?_ h₁))
    simp [E, WeierstrassCurve.Projective.neg, WeierstrassCurve.Projective.negY]
  · refine ptOver_mul_ptOver E h₀ h₀ h₂ ⟨fun i j => ?_, fun i j => ?_⟩
    · rw [WeierstrassCurve.Projective.addXYZ_self]
      fin_cases i <;> fin_cases j <;> simp
    · fin_cases i <;> fin_cases j <;>
        simp [E, diagXYZ, diagX, diagY, diagZ, negDiagY, WeierstrassCurve.Projective.negY] <;>
        norm_num

end GlobalTheory.WeierstrassCurve
