import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingClassGroupDescentsDifferByPowerPrimeToL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringClassGroup_descents_differ_by_power_prime_to_l : ∀ (D : D7) (i : D.ntw.Tw) (k : ℕ) (b b' : Bool) (v v' : D.what₂.places.Pl) (ρ : Reading i k b v) (ρ' : Reading i k b' v') (Q : Finset (PlE D.host)) (ψ ψ' : D.ntw.RCG i Q →* (D.ntw.Ok i k)ˣ) (ψ₀ : G D.host.E D.nd.Om →* (D.what₂.LL)ˣ), (∃ z : D.what₂.LL, IsPrimitiveRoot z (D.ntw.l i ^ k)) → (∀ g, ψ₀ g ^ (D.ntw.l i ^ k) = 1) → ρ.Pulls ψ ψ₀ → ρ'.Pulls ψ' ψ₀ → ∃ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l i) ∧ ψ' = ψ ^ a := by
  first | exact @GlobalTheory.LevCmp.pulls_eq_zpow | exact GlobalTheory.LevCmp.pulls_eq_zpow | (intros; apply GlobalTheory.LevCmp.pulls_eq_zpow <;> assumption)
