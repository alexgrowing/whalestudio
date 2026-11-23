import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelOperatorsAtPrimeOffLevelDatum
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_operators_at_prime_off_level_datum : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : LevDat D.host.E ℂ V.rank), IsBaseFrame V β Λ N → ∀ P : Pl D.host.E, ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → (∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) → (∀ k ∈ hyp V P, k ∈ levG V β L ∧ levChi V β L k = 1) ∧ (∀ SF d B, Hecke₂ V (levS V β L) (levChi V β L) SF P d B ↔ OffS D SF P ∧ SphOp V P d B) ∧ (∀ c Φ, HasType V β L Φ → HasType V β L (hk V P c Φ)) ∧ (∀ c (g0 : G0 L.Pg L.r) Φ, (∀ k ∈ hyp V P, ∀ h, Φ (h * k) = Φ h) → actG0 V β L g0 (hk V P c Φ) = hk V P c (actG0 V β L g0 Φ)) ∧ ∀ (S : D.what₂.Tau → SPar) (θ : InfFam D) (M : DSModel V S) c, IsInfFam θ → ∀ U ∈ Mult θ M (levS V β L) (levChi V β L), postOn M (hk V P c) U ∈ Mult θ M (levS V β L) (levChi V β L) := by
  first | exact @GlobalTheory.LevOp.level_operators | exact GlobalTheory.LevOp.level_operators | (intros; apply GlobalTheory.LevOp.level_operators <;> assumption)
