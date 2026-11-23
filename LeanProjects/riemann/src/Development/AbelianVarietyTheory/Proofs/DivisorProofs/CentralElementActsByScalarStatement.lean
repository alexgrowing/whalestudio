import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralElementActsByScalar
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainMulRight
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThetaCplV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_element_acts_by_scalar : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ z, IsCentral σ (c • G.W.J.map σ) z → ∃ (N : ℕ) (b : Fin N → ℂ), ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M, (dop z)^[N] (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc).symm x)) = ∑ i : Fin N, b i • (dop z)^[i.val] (fun x => G.M.I om Φ ((toGAd hσ G.W.J hc).symm x)) := by
  first | exact @GlobalTheory.ThK.ZoneV.zone | exact GlobalTheory.ThK.ZoneV.zone | (intros; apply GlobalTheory.ThK.ZoneV.zone <;> assumption)
