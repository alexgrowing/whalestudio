import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingFrameDeltaChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CXiValIff
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FieldBC GlobalTheory.OneMapAll
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolding_frame_delta_change : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (n r : ℕ) (c c' : Coeff l) (hle : c.F ≤ c'.F) (V : HSp D) (hr : V.rank = r) (d : DeltaDat Xo c n) (u : c'.F) (U₂ : Unf d.Xo₂ d.c₂ (c.F.val.toRingHom.comp (d.eF.symm : d.c₂.F →+* c.F)) r) (dict₂ : GA D V → Σ k, Frame (U₂.X k).Ψ r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (c0 : ℂ), d.cδ ∈ sec d.Xo₂ d.c₂ 0 0 → CXiAt V hr c.F.val.toRingHom d U₂ dict₂ io x₀ xi c0 → CXiAt V hr c'.F.val.toRingHom (covBC hle d u) (covUnf hle d u U₂) dict₂ io x₀ xi ((u : ℂ) * c0) := by
  first | exact @GlobalTheory.OneMapAll.cXiAt_covBC | exact GlobalTheory.OneMapAll.cXiAt_covBC | (intros; apply GlobalTheory.OneMapAll.cXiAt_covBC <;> assumption)
