import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsGenFamRevInvSubfamily
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenUIsGenFam
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGenFam_revInv_subfamily : ∀ (Ω G : Type) [Field Ω] [Field G] [Algebra Ω G] (S : Type) [Finite S] (r : S → ℕ) (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G) (P : S → Prop) [DecidablePred P], IsGenFam Ω G u → IsGenFam Ω G (fun s => if P s then revInv (u s) else u s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.isGenFam_revInv_ite | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.isGenFam_revInv_ite | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl.isGenFam_revInv_ite <;> assumption)
