import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftDatumConjugateHalfFiniteFourierSum
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_datum_conjugate_half_finite_fourier_sum : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)),
    (∃ t, Q ⊆ R.Q t) → (∀ PP ∈ Q, ξR PP ≠ 1) → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) →
    ∀ eQ : AE D, IsIdemSum eQ Q → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) →
    ∃ (Y : Finset (WO (Vc D i) (Wc D i))) (a : WO (Vc D i) (Wc D i) → ℂ) (Gc : ℂ), UnitOff N Gc ∧ (∀ y ∈ Y, IsHalf eQ y) ∧
      (∀ t, (if IsHalf (cA D eQ) t ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) t) then
        omegaQ Q (Wc D i).rank ξR (-1) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) t)) else 0) =
        halfInd (cA D eQ) (lattice₂ R i) t * ∑ y ∈ Y, a y * R.ψ (symplO (Vc D i) (Wc D i) t y)) ∧
      ∀ t, ∑ y ∈ Y, a y * halfInd eQ (lattice₂ R i) (t + y) = Gc * flatDat R i Q ξR eQ (dil i (ϖ : D.host.E) t) := by
  first | exact @GlobalTheory.LiftFour.datum_conj_half_fourier | exact GlobalTheory.LiftFour.datum_conj_half_fourier | (intros; apply GlobalTheory.LiftFour.datum_conj_half_fourier <;> assumption)
