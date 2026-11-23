import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

namespace GlobalTheory.PowGrp

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{0}}

theorem prop_powObj (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    (G : Over S) (hG : P G.hom) : ∀ n : ℕ, P (powObj G n).hom
  | 0 => P.id_mem S
  | n + 1 =>
    P.comp_mem (pullback.fst G.hom (powObj G n).hom) G.hom
      (P.pullback_fst _ _ (prop_powObj P G hG n)) hG

theorem smooth_isMultiplicative : MorphismProperty.IsMultiplicative (C := Scheme.{0}) @Smooth where
  id_mem _ := inferInstance
  comp_mem f g (_ : Smooth f) (_ : Smooth g) := inferInstance

attribute [local instance] smooth_isMultiplicative

theorem exists_iso_powObj {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ} (p : IsPowGrp G' G j) :
    ∃ e : G'.left ⟶ (powObj G j).left, IsIso e ∧ G'.hom = e ≫ (powObj G j).hom := by
  let e : G' ≅ powObj G j := p.lim.conePointUniqueUpToIso (powIsLimit G j)
  exact ⟨e.hom.left, inferInstanceAs (IsIso ((Over.forget _).map e.hom)), (Over.w e.hom).symm⟩

theorem prop_of_isPowGrp (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ} (p : IsPowGrp G' G j) (hG : P G.hom) : P G'.hom := by
  obtain ⟨e, he, hw⟩ := exists_iso_powObj p
  rw [hw]
  exact (P.cancel_left_of_respectsIso e _).2 (prop_powObj P G hG j)

theorem relDim_powObj (G : Over S) (g : ℕ) (hG : SmoothOfRelativeDimension g G.hom) :
    ∀ n : ℕ, SmoothOfRelativeDimension (n * g) (powObj G n).hom
  | 0 => by
    have h : SmoothOfRelativeDimension 0 (𝟙 S) := inferInstance
    rw [Nat.zero_mul]
    exact h
  | n + 1 => by
    have ih := relDim_powObj G g hG n
    have h1 : SmoothOfRelativeDimension (n * g) (pullback.fst G.hom (powObj G n).hom) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
        (IsPullback.of_hasPullback _ _).flip ih
    have h2 : SmoothOfRelativeDimension (n * g + g) (pullback.fst G.hom (powObj G n).hom ≫ G.hom) :=
      inferInstance
    rw [Nat.succ_mul]
    exact h2

theorem geomConnected_of_isIso {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] : GeometricallyConnected f := by
  refine ⟨fun K _ y Z fst snd h ↦ ?_⟩
  have : IsIso snd := h.isIso_snd_of_isIso
  exact snd.homeomorph.symm.surjective.connectedSpace snd.homeomorph.symm.continuous

theorem geomConnected_powObj (G : Over S) [Smooth G.hom] [GeometricallyConnected G.hom] :
    ∀ n : ℕ, GeometricallyConnected (powObj G n).hom
  | 0 => geomConnected_of_isIso (𝟙 S)
  | n + 1 => by
    have := geomConnected_powObj G n
    have : Smooth (powObj G n).hom := prop_powObj @Smooth G ‹_› n
    show GeometricallyConnected (pullback.fst G.hom (powObj G n).hom ≫ G.hom)
    exact GeometricallyConnected.comp _ _

theorem comm_of_isPowGrp {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ} (p : IsPowGrp G' G j)
    (hG : IsCommMonObj G) : IsCommMonObj G' := by
  refine ⟨p.lim.hom_ext fun ⟨i⟩ => ?_⟩
  have := p.hom i
  show ((β_ G' G').hom ≫ μ) ≫ p.pr i = μ ≫ p.pr i
  rw [Category.assoc, IsMonHom.mul_hom, ← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm]

theorem powers : ∀ (S : Scheme.{0}) (G' G : Over S) [GrpObj G'] [GrpObj G] (j : ℕ) (p : IsPowGrp G' G j), (Smooth G.hom → Smooth G'.hom) ∧ (IsSeparated G.hom → IsSeparated G'.hom) ∧ (∀ g : ℕ, SmoothOfRelativeDimension g G.hom → SmoothOfRelativeDimension (j * g) G'.hom) ∧ (IsAbelianScheme G → IsAbelianScheme G') ∧ (IsSemiAbelian G → IsCommMonObj G') := by
  intro S G' G _ _ j p
  refine ⟨prop_of_isPowGrp @Smooth p, prop_of_isPowGrp @IsSeparated p, fun g hg => ?_, fun hG => ?_,
    fun hG => comm_of_isPowGrp p hG.comm⟩
  · obtain ⟨e, he, hw⟩ := exists_iso_powObj p
    have h1 := relDim_powObj G g hg j
    have h2 : SmoothOfRelativeDimension (0 + j * g) G'.hom := by
      rw [hw]; infer_instance
    rwa [Nat.zero_add] at h2
  · refine ⟨comm_of_isPowGrp p hG.comm, prop_of_isPowGrp @Smooth p hG.smooth,
      prop_of_isPowGrp @IsProper p hG.proper, ?_⟩
    obtain ⟨e, he, hw⟩ := exists_iso_powObj p
    have := hG.smooth
    have := hG.geomConnected
    have := geomConnected_powObj G j
    have : Smooth (powObj G j).hom := prop_powObj @Smooth G ‹_› j
    have := geomConnected_of_isIso e
    rw [hw]
    exact GeometricallyConnected.comp _ _

end GlobalTheory.PowGrp
