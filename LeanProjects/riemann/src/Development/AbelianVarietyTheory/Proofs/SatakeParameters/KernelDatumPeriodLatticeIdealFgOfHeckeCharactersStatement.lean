import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumPeriodLatticeIdealFgOfHeckeCharacters
import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelDatum_periodLatticeIdeal_fg_of_heckeCharacters : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → (∀ μ k, D.host.g k ∉ Y.Qp μ) → t.Hyp0 := by
  first | exact @GlobalTheory.kernel_datum_of_hecke_character_values | exact GlobalTheory.kernel_datum_of_hecke_character_values | (intros; apply GlobalTheory.kernel_datum_of_hecke_character_values <;> assumption)
