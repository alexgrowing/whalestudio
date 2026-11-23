import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull

noncomputable section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem MChart.nonempty_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (M : MChart Y), ∀ (R : Type) [CommRing R] [Algebra c.F R] (f : Γ(Y.X, M.U) →+* R) (xF : Sp R ⟶ Xo.XF c), xF ≫ pullback.snd _ _ = spMap (algebraMap c.F R) → xF ≫ Y.j = spMap f ≫ M.hU.fromSpec → Nonempty (M.Lift f (xF ≫ pullback.fst _ _)) := by
  intro E _ _ _ H Dw l Xo c O _ β Y M R _ _ f xF h1 h2
  have hComp : SABCompSt := sabComp pullCubComp
  have hP : ∃ t' : SAB H (Sp R), Nonempty (SABMap t' Y.oF.t xF) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull xF Y.oF.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨t', ⟨m'⟩⟩ := hP
  obtain ⟨m1, hm1⟩ := hComp _ _ _ _ _ _ _ _ _ _ Y.m0.toSABMap m'
  have key : ∀ g : Sp R ⟶ Y.X, xF ≫ Y.j = g → ∃ m2 : SABMap t' Y.t g, m2.φ = m'.φ ≫ Y.m.φ := by
    rintro g rfl
    exact hComp _ _ _ _ _ _ _ _ _ _ Y.m m'
  obtain ⟨m2, hm2⟩ := key _ h2
  exact ⟨⟨xF, rfl, h1, h2, t', m', m1, m2, hm1, hm2⟩⟩

end GlobalTheory.Reg
