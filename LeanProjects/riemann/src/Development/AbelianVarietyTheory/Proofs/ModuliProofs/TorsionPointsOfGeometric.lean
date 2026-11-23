import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.UniformityLowerBounds
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem torsionSection_eq_labelled_of_isDomain : ∀ (R : Type) [CommRing R] [IsDomain R] (P : PolAV (Sp R)) (M : ℕ) (I : Type) (pt : I → (baseOver (Sp R) ⟶ P.A)), (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (z : Over.mk x ⟶ P.A), z ^ M = 1 → ∃ a, (Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp R)) ≫ pt a = z) → ∀ y : baseOver (Sp R) ⟶ P.A, y ^ M = 1 → ∃ a, pt a = y := by
  intro R _ _ P M I pt h y hy
  let K := AlgebraicClosure (FractionRing R)
  let j : R →+* K := (algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R))
  have hj : Function.Injective j :=
    (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R (FractionRing R))
  have hdom : IsDominant (Geo.Tor.spMap j) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical j).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot j).1 hj]; exact bot_le)⟩
  have hprop : IsProper P.A.hom := P.isAb.proper
  obtain ⟨a, ha⟩ := h K (Geo.Tor.spMap j)
    ((Over.homMk (Geo.Tor.spMap j) (by simp) : Over.mk (Geo.Tor.spMap j) ⟶ baseOver (Sp R)) ≫ y)
    (by rw [← MonObj.comp_pow, hy, MonObj.comp_one])
  exact ⟨a, Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Sp R) P.A.hom
    ((Over.w (pt a)).trans (Over.w y).symm) (Geo.Tor.spMap j) (congrArg Over.Hom.left ha))⟩

end GlobalTheory
