import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LeCovCoeff
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.SectionBaseChangeOfBasis

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldBC

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
  Formalism.BasicNotions

theorem actLev_of_le {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {G : Type} [Group G]
    (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La))
    (hL : ActLev (Xo := Xo) c lev) : ActLev (Xo := Xo) c' lev := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g S _ _ y
    letI := resAlg hle S
    have h : AlgOver c c' hle S := fun _ => rfl
    obtain ⟨z, hz⟩ := hL.total g S (y.res hle h)
    exact ⟨z.ext hle h, hz⟩
  · intro g S _ _ y y₁ y₂ h₁ h₂
    letI := resAlg hle S
    have h : AlgOver c c' hle S := fun _ => rfl
    exact hL.func g S (y.res hle h) (y₁.res hle h) (y₂.res hle h) h₁ h₂
  · intro S _ _ y
    letI := resAlg hle S
    have h : AlgOver c c' hle S := fun _ => rfl
    exact hL.one S (y.res hle h)
  · intro g g' S _ _ y y₁ y₂ h₁ h₂
    letI := resAlg hle S
    have h : AlgOver c c' hle S := fun _ => rfl
    exact hL.mul g g' S (y.res hle h) (y₁.res hle h) (y₂.res hle h) h₁ h₂
  · intro g S T _ _ _ _ φ y y' z z' h₀ h₁ h₂
    letI := resAlg hle S
    letI := resAlg hle T
    have hS : AlgOver c c' hle S := fun _ => rfl
    have hT : AlgOver c c' hle T := fun _ => rfl
    let ψ : S →ₐ[c.F] T := { φ.toRingHom with commutes' := fun x => φ.commutes _ }
    exact hL.nat g S T ψ (y.res hle hS) (y'.res hle hS) (z.res hle hT) (z'.res hle hT) h₀ h₁ h₂
  · intro g S _ _ t y y' z z' h₀ h₁ h₂
    letI := resAlg hle S
    have h : AlgOver c c' hle S := fun _ => rfl
    exact hL.bor g S t (y.res hle h) (y'.res hle h) (z.res hle h) (z'.res hle h) h₀ h₁ h₂

theorem actLev_and_actBC (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (G : Type) [Group G]
    (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La))
    (hL : ActLev (Xo := Xo) c lev) :
    ActLev (Xo := Xo) c' lev ∧ ActBC hle (actLev (Xo := Xo) c lev) (actLev (Xo := Xo) c' lev) :=
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hc := fun c => GlobalTheory.Frames.chartCoverF_of_secBaseChange hS D.host.E H Dw l Xo c
  ⟨actLev_of_le hle lev hL, actBC_of hle lev (evalWD_fr (frChartF_of (hc c))) (evalWD_fr (frChartF_of (hc c'))) hL
    (actLev_of_le hle lev hL)⟩

end GlobalTheory.FieldBC
