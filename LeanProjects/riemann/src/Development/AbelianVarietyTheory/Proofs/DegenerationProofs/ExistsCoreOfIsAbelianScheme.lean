import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LinCombTrivG
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsClassicalLiftOfSmooth
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValueAtUnitSection

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem isGen_one_of_g_eq_one {X : Scheme.{0}} (L : LB X) (h : ∀ i j, L.g i j = 1) :
    (⟨fun _ => 1⟩ : LB.Gen L).IsGen := fun i j =>
  (map_one _).trans ((congrArg₂ (· * ·) (h i j) (map_one _)).trans (_root_.mul_one _)).symm

theorem div_g_eq_one {X : Scheme.{0}} (M L : LB X) (hM : ∀ i j, M.g i j = 1) (hL : ∀ i j, L.g i j = 1)
    (i j : (LB.div M L).ι) : (LB.div M L).g i j = 1 := by
  simp only [LB.div, hM, hL, map_one, inv_one, _root_.mul_one]
  rfl

theorem isGen_one_linComb_triv {X Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    (⟨fun _ => 1⟩ : LB.Gen (LB.LinComb (Out.Inh.trivLB X) φ ε)).IsGen :=
  isGen_one_of_g_eq_one _ (Out.Inh.linComb_triv_g φ ε)

def splitExtOfAbelian {S : Scheme.{0}} (B : Over S) [GrpObj B] (h : IsAbelianScheme B) : SplitExt S where
  B := B
  isAbelian := h
  X := PUnit
  O := fun _ => ⟨Out.Inh.trivLB _, ⟨fun _ => 1⟩, Out.Inh.trivLB_isLB _, isGen_one_linComb_triv _ _⟩
  addIso := fun _ _ => ⟨⟨fun _ => 1⟩, isGen_one_of_g_eq_one _
    (div_g_eq_one _ _ (div_g_eq_one _ _ (fun _ _ => rfl) fun _ _ => rfl) fun _ _ => rfl)⟩
  zeroTriv := ⟨⟨fun _ => 1⟩, isGen_one_of_g_eq_one _ fun _ _ => rfl⟩
  primitive := fun _ => ⟨⟨fun _ => 1⟩, isGen_one_linComb_triv _ _⟩

theorem isGt_splitExtOfAbelian {S : Scheme.{0}} (B : Over S) [GrpObj B] (h : IsAbelianScheme B) :
    (splitExtOfAbelian B h).IsGt B := by
  have := h.comm
  have := isIso_toUnit_splitTorus_punit S
  have hk : IsPullback (toUnit (splitTorus S PUnit) ≫ η[B]) (toUnit _) (𝟙 B) η[B] :=
    IsPullback.of_vert_isIso ⟨Category.comp_id _⟩
  refine CoordToExt.isGt_of_units (splitExtOfAbelian B h) (𝟙 B) (toUnit _ ≫ η[B])
    (inferInstanceAs (IsMonHom (𝟙 B)))
    (inferInstanceAs (IsMonHom (toUnit (splitTorus S PUnit) ≫ η[B])))
    (inferInstanceAs (Flat (𝟙 B.left))) (inferInstanceAs (Surjective (𝟙 B.left)))
    (inferInstanceAs (IsAffineHom (𝟙 B.left))) hk (fun _ _ => 1) ?_ ?_ ?_
  · intro χ Z r z a a' _ _
    exact (map_one _).trans ((congrArg₂ (· * ·) (map_one _) (map_one _)).trans (_root_.mul_one _)).symm
  · intro χ a Z t g z _
    have e : charUnit S PUnit χ = 1 := by
      have e₀ : Multiplicative.ofAdd (α := PUnit) χ = 1 := rfl
      unfold charUnit
      rw [e₀]
      simp only [map_one]
      exact (congrArg _ (map_one _)).trans (map_one _)
    exact (map_one _).trans ((congrArg₂ (· * ·) ((congrArg _ e).trans (map_one _)) (map_one _)).trans
      (_root_.mul_one _)).symm
  · intro χ a y _
    exact (congrArg₂ (· * ·) (map_one _) (map_one _)).trans (_root_.mul_one _)

def Core.ofAbelian (Z : Scheme.{0}) [IsIntegral Z] (π : Z ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π] [QuasiCompact π]
    [IsSeparated π] (hZ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z) (A : Over Z) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) : Core where
  Z := Z
  π := π
  flat := inferInstance
  lft := inferInstance
  qc := inferInstance
  sep := inferInstance
  normal := hZ
  U := ⊤
  ne := Set.univ_nonempty
  g := g
  A := (Over.pullback (⊤ : Z.Opens).ι).obj A
  comm := (isAbelianScheme_pullback_obj _ A hA).comm
  ab := isAbelianScheme_pullback_obj _ A hA
  dim := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hg
  P := A
  intP := by
    have := hA.smooth
    have := hA.geomConnected
    have := grpObj_geometricallyIntegral_of_smooth Z A
    have := LocallyOfFiniteType.isLocallyNoetherian π
    exact GeometricallyIntegral.isIntegral_of_isLocallyNoetherian A.hom
  proper := hA.proper
  G := ⊤
  a := pullback.fst A.hom (⊤ : Z.Opens).ι ≫ A.left.topIso.inv
  cart := by
    rw [Category.assoc, Scheme.toIso_inv_ι, Category.comp_id]
    exact IsPullback.of_hasPullback _ _
  e := eSec A ≫ A.left.topIso.inv
  e_sec := by
    rw [Category.assoc, Scheme.toIso_inv_ι_assoc]
    exact Over.w η[A]
  e_zero := by
    rw [← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ A.left.topIso.inv) (UnitValue.eSec_pullback_fst _ A).symm

section

variable {T V Z G H : Scheme.{0}} {f : H ⟶ G} {s : H ⟶ V} {t : G ⟶ Z} {y₀ : V ⟶ Z}

end

section

variable (Z : Scheme.{0}) [IsIntegral Z] (π : Z ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π] [QuasiCompact π]
    [IsSeparated π] (hZ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z) (A : Over Z) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom)

end

end GlobalTheory.ZJ

end
