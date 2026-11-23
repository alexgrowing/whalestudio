import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLetterEquivConjugate
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsMemRowHighestTotalDegreeEqTwo
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section
namespace GlobalTheory.FockLetters
variable {D : D7} {H : Geo.Tor.Host D.host.E}

def tauPsi (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) : D.what₂.Tau ≃ {τ : D.host.E →+* ℂ // InPsi H τ} :=
  Equiv.ofBijective (fun ρ => ⟨tauE D ρ, (hΨ _).2 ⟨ρ, rfl⟩⟩)
    ⟨fun _ _ h => GlobalTheory.StdRat.tauE_injective D (congrArg Subtype.val h), fun τ => by
      obtain ⟨ρ, h⟩ := (hΨ τ.1).1 τ.2
      exact ⟨ρ, Subtype.ext h.symm⟩⟩

theorem tauPsi_apply (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (ρ : D.what₂.Tau) :
    ((tauPsi hΨ ρ : {τ : D.host.E →+* ℂ // InPsi H τ}) : D.host.E →+* ℂ) = tauE D ρ := rfl

def fockVarEquiv (Dw : Datum H) {m n : ℕ} (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ)
    (hm : m = Dw.p + Dw.q) : FVar D m n ≃ GlobalTheory.Harm.Var {τ : D.host.E →+* ℂ // InPsi H τ} Dw.p Dw.q (Fin n) :=
  (tauPsi hΨ).prodCongr (((finCongr hm).trans finSumFinEquiv.symm).prodCongr (Equiv.refl _))

def letterEquiv (Dw : Datum H) {m n : ℕ} (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ)
    (hm : m = Dw.p + Dw.q) : LtN Dw n ≃ FVar D m n :=
  (GlobalTheory.Harm.thetaLetterEquiv Dw n).trans (fockVarEquiv Dw hΨ hm).symm

def stepsX (Dw : Datum H) (a : (D.host.E →+* ℂ) × ℕ → ℕ) : {τ : D.host.E →+* ℂ // InPsi H τ} → Fin Dw.p → ℕ :=
  fun t => GlobalTheory.Harm.diffOf fun i : Fin Dw.p => a (t.1, i)

def stepsY (Dw : Datum H) (a : (D.host.E →+* ℂ) × ℕ → ℕ) : {τ : D.host.E →+* ℂ // InPsi H τ} → Fin Dw.q → ℕ :=
  fun t => GlobalTheory.Harm.diffOf fun i : Fin Dw.q => a (ComplexEmbedding.conjugate t.1, i)

end GlobalTheory.FockLetters
