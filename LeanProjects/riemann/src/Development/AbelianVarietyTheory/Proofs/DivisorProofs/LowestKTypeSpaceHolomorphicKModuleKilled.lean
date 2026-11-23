import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PMinusAnnihilatesLowestKTypeHolomorphicChamberStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KTypeLeKFiniteVectorsFiniteDimensionalStatement
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.LowKType

theorem lowKSub_mem_of_forall {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {lam : Fin n → ℝ} {D : Submodule ℂ H} (Q : Submodule ℂ D)
    (hD : ∀ S : Submodule ℂ H, IsKTypeOf ε σ (lowK ε lam) S → S ≤ D)
    (hQ : ∀ S : Submodule ℂ H, IsKTypeOf ε σ (lowK ε lam) S → ∀ y : D, (y : H) ∈ S → y ∈ Q) :
    ∀ y : D, (y : H) ∈ lowKSub ε lam σ → y ∈ Q := by
  have hle : lowKSub ε lam σ ≤ Q.map D.subtype := by
    unfold lowKSub
    refine sSup_le fun S hS x hx => ?_
    exact ⟨⟨x, hD S hS hx⟩, hQ S hS ⟨x, hD S hS hx⟩ hx, rfl⟩
  intro y hy
  obtain ⟨z, hz, hzy⟩ := hle hy
  have : z = y := Subtype.ext hzy
  exact this ▸ hz

end GlobalTheory.LowKType

open GlobalTheory.LowKType in
theorem GlobalTheory.HolDS.lowKSub_kMod : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ D) (lam : Fin n → ℝ), IsHCParam lam → IsHolChamber ε lam → IsDS ε lam σ → IsKMod ε σ D E → lowKSub ε lam σ ≤ D ∧ KStab ε E ((lowKSub ε lam σ).comap D.subtype) ∧ (lowKSub ε lam σ).comap D.subtype ≠ ⊥ ∧ ∀ a b : Fin n, ε a = true → ε b = false → ∀ x ∈ (lowKSub ε lam σ).comap D.subtype, E b a x = 0 := by
  intro n ε H _ _ σ D E lam hHC hch hDS hK
  obtain ⟨hC, _, hU, hI, _, hEx, hmin⟩ := hDS
  have hT := fun μ S hS => GlobalTheory.T.kType_le_kFiniteVectors_finiteDimensional n ε H σ D E hC hU hI hK μ S hS
  have hD : ∀ S : Submodule ℂ H, IsKTypeOf ε σ (lowK ε lam) S → S ≤ D := fun S hS => (hT _ S hS).1
  have hM : IsMin ε E lam := fun μ x hx0 hx => by
    obtain ⟨T, hT'⟩ := hK.ty μ x hx0 hx
    exact hmin μ T hT'
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold lowKSub
    exact sSup_le fun S hS => hD S hS
  · intro a b hab v hv
    exact lowKSub_mem_of_forall ((lowKSub ε lam σ).comap D.subtype |>.comap (E a b)) hD
      (fun S hS y hy => by
        have h3 := (hT _ S hS).2.2.1 a b hab y hy
        show ((E a b y : D) : H) ∈ lowKSub ε lam σ
        exact (le_sSup hS : S ≤ lowKSub ε lam σ) h3) v hv
  · obtain ⟨S, hS⟩ := hEx
    obtain ⟨v, hv0, hvS, _⟩ := hK.hw _ S hS
    intro hbot
    have hv : v ∈ (lowKSub ε lam σ).comap D.subtype := (le_sSup hS : S ≤ lowKSub ε lam σ) hvS
    rw [hbot] at hv
    exact hv0 ((Submodule.mem_bot ℂ).1 hv)
  · intro a b ha hb x hx
    exact (lowKSub_mem_of_forall (LinearMap.ker (E b a)) hD
      (fun S hS y hy => by
        have h := hT _ S hS
        haveI := h.2.1
        exact GlobalTheory.T.pMinus_annihilates_lowestKType_holomorphicChamber n ε D E lam hK.gl hK.unit hHC.1 hch hM (S.comap D.subtype) h.2.1 h.2.2.1 h.2.2.2
          a b ha hb y hy) x hx : x ∈ LinearMap.ker (E b a))
