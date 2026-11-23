import Mathlib
import GroundTheory.PAdicHodge.FWGalois
import GroundTheory.PAdicHodge.FWCharP
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

variable (F E : Type*) [Field F] [Field E] [Algebra F E] [IsAlgClosed E] in

def absoluteGaloisGroupEquivAlgebraicClosure :
    Field.absoluteGaloisGroup F ≃ₜ* (algebraicClosure F E ≃ₐ[F] algebraicClosure F E) :=
  autCongrHomeomorph (IsAlgClosure.equiv F (AlgebraicClosure F) (algebraicClosure F E))

section InC

variable {K C : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [NontriviallyNormedField C] [IsUltrametricDist C] [NormedAlgebra K C] [IsAlgClosed C]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p] [IsPerfectoidField C p]

local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p
local notation "C♭" => Tilt C NormedField.valuation (normInteger C) normInteger_integers p
local notation "Ω" => algebraicClosure K C
local notation "Ω♭" => algebraicClosure K♭ C♭

variable (C) in
include C in

theorem isAlgClosed_iff_isAlgClosed_tilt_of_isAlgClosed : IsAlgClosed K ↔ IsAlgClosed K♭ := by
  constructor
  · intro _
    infer_instance
  · intro _
    refine IsAlgClosed.of_exists_root K fun f hmon hirr => ?_
    have hdeg : f.degree ≠ 0 := (Polynomial.degree_pos_of_irreducible hirr).ne'
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_aeval_eq_zero C f hdeg
    have hint : IsIntegral K z := ⟨f, hmon, by rwa [← Polynomial.aeval_def]⟩
    have : FiniteDimensional K (IntermediateField.adjoin K {z}) :=
      IntermediateField.adjoin.finiteDimensional hint
    obtain ⟨hfin, -⟩ := untiltField_tiltIntermediateField (p := p) (IntermediateField.adjoin K {z})
    have h1 : tiltIntermediateField p (IntermediateField.adjoin K {z}) = ⊥ :=
      IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _
    have h2 : Module.finrank K (IntermediateField.adjoin K {z}) = 1 := by
      rw [← finrank_tiltIntermediateField (p := p), h1, IntermediateField.finrank_bot]
    have h3 := IntermediateField.finrank_eq_one_iff.1 h2
    have hzb : z ∈ (⊥ : IntermediateField K C) := h3 ▸ IntermediateField.mem_adjoin_simple_self K z
    obtain ⟨k, rfl⟩ := IntermediateField.mem_bot.1 hzb
    refine ⟨k, ?_⟩
    rw [Polynomial.aeval_algebraMap_apply] at hz
    have := (algebraMap K C).injective (hz.trans (map_zero _).symm)
    rwa [Polynomial.coe_aeval_eq_eval] at this

variable (K C p) in

def galoisTiltEquiv : (Ω ≃ₐ[K] Ω) ≃ₜ* (Ω♭ ≃ₐ[K♭] Ω♭) :=
  (untiltGalHomeomorph K C p).symm

theorem untiltGalEquiv_galoisTiltEquiv (σ : Ω ≃ₐ[K] Ω) :
    untiltGalEquiv K C p (galoisTiltEquiv K C p σ) = σ :=
  (untiltGalEquiv K C p).apply_symm_apply σ

theorem galoisTiltEquiv_fixes_iff (L : IntermediateField K C) [FiniteDimensional K L]
    (σ : Ω ≃ₐ[K] Ω) :
    (∀ y : Ω♭, (y : C♭) ∈ tiltIntermediateField p L → galoisTiltEquiv K C p σ y = y) ↔
      (∀ x : Ω, (x : C) ∈ L → σ x = x) := by
  obtain ⟨hfin, hL⟩ := untiltField_tiltIntermediateField (p := p) L
  have key := untiltGalEquiv_fixes_iff (galoisTiltEquiv K C p σ) (tiltIntermediateField p L)
  rw [untiltGalEquiv_galoisTiltEquiv, hL] at key
  exact key.symm

end InC

section Absolute

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]

local notation "K♭" => Tilt K NormedField.valuation (normInteger K) normInteger_integers p

theorem isAlgClosed_iff_isAlgClosed_tilt : IsAlgClosed K ↔ IsAlgClosed K♭ := by
  rcases IsPerfectoidField.charZero_or_charP (K := K) p with h0 | hp
  · have := IsPerfectoidField.completeSpace (K := K) p
    have : IsPerfectoidField (CompletedAlgClosure K) p :=
      isPerfectoidField_of_isAlgClosed_of_normedAlgebra K (CompletedAlgClosure K) p
    exact isAlgClosed_iff_isAlgClosed_tilt_of_isAlgClosed (CompletedAlgClosure K)
  · exact ⟨fun _ => IsAlgClosed.of_ringEquiv K K♭ (tiltRingEquivOfCharP K p).symm,
      fun _ => IsAlgClosed.of_ringEquiv K♭ K (tiltRingEquivOfCharP K p)⟩

variable (K p) in

def absoluteGaloisGroupTiltEquiv [CharZero K] :
    Field.absoluteGaloisGroup K ≃ₜ* Field.absoluteGaloisGroup K♭ :=
  haveI := IsPerfectoidField.completeSpace (K := K) p
  haveI : IsPerfectoidField (CompletedAlgClosure K) p :=
    isPerfectoidField_of_isAlgClosed_of_normedAlgebra K (CompletedAlgClosure K) p
  (absoluteGaloisGroupEquivAlgebraicClosure K (CompletedAlgClosure K)).trans
    ((galoisTiltEquiv K (CompletedAlgClosure K) p).trans
      (absoluteGaloisGroupEquivAlgebraicClosure K♭ (Tilt (CompletedAlgClosure K) NormedField.valuation
          (normInteger (CompletedAlgClosure K)) normInteger_integers p)).symm)

variable (K p) in

def absoluteGaloisGroupTiltEquivOfCharP [CharP K p] :
    Field.absoluteGaloisGroup K ≃ₜ* Field.absoluteGaloisGroup K♭ :=
  absoluteGaloisGroupCongr K K♭ (tiltRingEquivOfCharP K p).symm

theorem nonempty_absoluteGaloisGroup_tilt :
    Nonempty (Field.absoluteGaloisGroup K ≃ₜ* Field.absoluteGaloisGroup K♭) := by
  rcases IsPerfectoidField.charZero_or_charP (K := K) p with h0 | hp
  · exact ⟨absoluteGaloisGroupTiltEquiv K p⟩
  · exact ⟨absoluteGaloisGroupTiltEquivOfCharP K p⟩

end Absolute

end GroundTheory.PAdicHodge
