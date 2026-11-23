import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPAdicPowerSeriesValueAddSmulMap
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.QLog

open MvPowerSeries in

theorem _root_.GlobalTheory.QLog.hasPeriod_reduce : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : _root_.GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε), ∀ F : _root_.GlobalTheory.QLog.BFrame ε, ∀ (G : _root_.GlobalTheory.PDivGroup p O) (d : ℕ) (c : _root_.GlobalTheory.QLog.Chart G d) (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) F.B), _root_.GlobalTheory.QLog.IsLift F.θ μ' → (∀ i, map F.θ (μ' i) = c.μ i) → ∀ (E : Type) [CommRing E] [Algebra O E], _root_.GlobalTheory.QLog.IsFrame p E (RingHom.id O) → ∀ Θ : F.Q →+* E, (∀ b, Θ (algebraMap F.B F.Q b) = algebraMap O E (F.θ b)) → ∀ (f : MvPowerSeries (Fin d) F.Q) (t : G.Tate) (y : F.B), _root_.GlobalTheory.QLog.QL μ' ⊤ f → c.HasPeriod F.θ t f y → c.HasPeriod (RingHom.id O) t (map Θ f) (F.θ y) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε _ F G d c μ' _ _ E _ _ hE Θ hΘ f t y _ hy
  have hF := F.frame
  rw [_root_.GlobalTheory.QLog.Chart.hasPeriod_iff c hF] at hy
  rw [_root_.GlobalTheory.QLog.Chart.hasPeriod_iff c hE]
  intro n z hz
  choose w hw using fun i => hF.surj (z i)
  obtain ⟨q, hq, b, hb⟩ := hy n w (fun i => by rw [hw]; exact hz i)
  refine ⟨Θ q, ?_, F.θ b, ?_⟩
  · have hmap := (_root_.GlobalTheory.QLog.ValLin.hasVal_add_smul_map p _ O _ F.θ hF _ w f f q q
      hq).2.2 O E F.θ Θ hΘ
    simpa [hw] using hmap
  · have h2 := congrArg Θ hb
    rw [map_mul, map_pow, map_natCast, hΘ, map_add, map_mul, map_pow, map_natCast] at h2
    exact h2

end GlobalTheory.QLog
