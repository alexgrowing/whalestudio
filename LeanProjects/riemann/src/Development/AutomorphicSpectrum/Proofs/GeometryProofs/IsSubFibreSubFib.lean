import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Sp Ω ⟶ X}
  {Li : Type} [AddCommGroup Li] [Module Ω Li] {L : Type} [Field L] [NumberField L]

def subGens (M : LieModel G ξ Li) (U : Submodule Ω Li) (z : Sp (𝓞 L) ⟶ X) {V : Type} [AddCommGroup V]
    [Module (𝓞 L) V] (MB : LieModel G z V) : Set V :=
  {x' | ∃ e ∈ U, ∃ v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G,
    M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e v ∧ MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) x' v}

def subFib (M : LieModel G ξ Li) (U : Submodule Ω Li) (z : Sp (𝓞 L) ⟶ X) {V : Type} [AddCommGroup V]
    [Module (𝓞 L) V] (MB : LieModel G z V) : Submodule (𝓞 L) V where
  carrier := {x | ∃ a : 𝓞 L, a ≠ 0 ∧ a • x ∈ Submodule.span (𝓞 L) (subGens M U z MB)}
  add_mem' := by
    rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hx
    · rw [mul_smul]; exact Submodule.smul_mem _ _ hy
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  smul_mem' := by
    rintro c x ⟨a, ha, hx⟩
    refine ⟨a, ha, ?_⟩
    rw [smul_comm]; exact Submodule.smul_mem _ _ hx

theorem mem_subFib {M : LieModel G ξ Li} {U : Submodule Ω Li} {z : Sp (𝓞 L) ⟶ X} {V : Type} [AddCommGroup V]
    [Module (𝓞 L) V] {MB : LieModel G z V} {x : V} :
    x ∈ subFib M U z MB ↔ ∃ a : 𝓞 L, a ≠ 0 ∧ a • x ∈ Submodule.span (𝓞 L) (subGens M U z MB) := Iff.rfl

theorem isSubFibre_subFib (M : LieModel G ξ Li) (U : Submodule Ω Li) (z : Sp (𝓞 L) ⟶ X) {V : Type} [AddCommGroup V]
    [Module (𝓞 L) V] (MB : LieModel G z V) : IsSubFibre M U z MB (subFib M U z MB) := fun _ => Iff.rfl

theorem subFib_mono (M : LieModel G ξ Li) {U U' : Submodule Ω Li} (h : U ≤ U') (z : Sp (𝓞 L) ⟶ X) {V : Type}
    [AddCommGroup V] [Module (𝓞 L) V] (MB : LieModel G z V) : subFib M U z MB ≤ subFib M U' z MB := by
  rintro x ⟨a, ha, hx⟩
  refine ⟨a, ha, Submodule.span_mono ?_ hx⟩
  rintro y ⟨e, he, r⟩
  exact ⟨e, h he, r⟩

theorem subFib_saturated (M : LieModel G ξ Li) (U : Submodule Ω Li) (z : Sp (𝓞 L) ⟶ X)
    (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel G z B.carrier) : B.Saturated (subFib M U z MB) := by
  rintro a x ha ⟨b, hb, hx⟩
  exact ⟨b * a, mul_ne_zero hb ha, by rwa [mul_smul]⟩

end GlobalTheory.CompanionTheory.Ar.FlagFib
