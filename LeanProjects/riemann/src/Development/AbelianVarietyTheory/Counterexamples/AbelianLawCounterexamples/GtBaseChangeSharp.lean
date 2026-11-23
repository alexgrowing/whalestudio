import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Laws3

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PullSharp

theorem cube_pull_sharp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G]
    [GrpObj G'] [IsCommMonObj G'] (m : CubeMap G' G) (L : RigLB G) (c : CubicalStr G L) :
    ∃ (hL : (L.L.pull m.F).IsLB) (hr : (m.rigPull L.L L.rig).IsGen)
      (c' : CubicalStr G' (m.rigLB L hL hr)), c'.t = m.thetaPull L.L c.t := by
  obtain ⟨hL, hr, -, -⟩ := CubePf.cubePull S S' G G' m L c
  exact ⟨hL, hr, CubePf.cubical m L c hL hr, (CubePf.thetaPull_eq m L.L c.t).symm⟩

theorem both : GtBaseChangeSt ∧ CubePullSt := ⟨GlobalTheory.laws3.1, GlobalTheory.laws3.2⟩

end GlobalTheory.PullSharp
