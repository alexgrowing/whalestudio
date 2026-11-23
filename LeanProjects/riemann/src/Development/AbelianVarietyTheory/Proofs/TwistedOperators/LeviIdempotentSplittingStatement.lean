import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIdempotentSplitting
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_idempotent_splitting : ∀ (D : D7) (V : HSp D) (Φ : WittFrame V) (u : SV (wittIndex V)), u ≠ 0 → ∃ (ε : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (hW : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.IsIsotropic V (Φ.sub u)), ε * ε = ε ∧ 0 < ε.rank ∧ ε.rank < V.rank ∧ (∀ γ : GF V, rat V γ ∈ Φ.levi D.sp.cm (AF D.host.F) {u} → γ.1.1 * ε = ε * γ.1.1) ∧ ∀ v (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (g : GLoc D.sp.cm.sig V.gram v), ε.map τ * ((splitHom D.sp.cm.sig V.gram τ g).1 - 1) * (1 - ε.map τ) = (splitHom D.sp.cm.sig V.gram τ g).1 - 1 → emb D.sp.cm.sig V.gram v g ∈ NA (IsoFlag.single hW) := by
  first | exact @GlobalTheory.SignProj.exists_proj_unip | exact GlobalTheory.SignProj.exists_proj_unip | (intros; apply GlobalTheory.SignProj.exists_proj_unip <;> assumption)
