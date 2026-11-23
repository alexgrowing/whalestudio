import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
import GroundTheory.AutomorphicForms.TraceNormComp

open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.twoProj :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Λ E Λ' E' Y : H →L[ℂ] H), Λ + E = Λ' + E' → Λ ∘L Λ = Λ → E ∘L E = E → Λ' ∘L Λ' = Λ' → E' ∘L E' = E' →
      Λ ∘L E = 0 → E ∘L Λ = 0 → Λ' ∘L E' = 0 → E' ∘L Λ' = 0 → IsTraceClass (Λ ∘L Y ∘L Λ) → IsTraceClass (E ∘L Y) →
      IsTraceClass (Y ∘L E) → IsTraceClass (Y ∘L E') →
      IsTraceClass (Λ' ∘L Y ∘L Λ') ∧ trace (Λ ∘L Y ∘L Λ) + trace (E ∘L Y) = trace (Λ' ∘L Y ∘L Λ') + trace (Y ∘L E') := by
  intro H _ _ _ Λ E Λ' E' Y hs h1 h2 h3 h4 h5 h6 h7 h8 t1 t2 t3 t4
  have key : ∀ A B Z : H →L[ℂ] H, A * A = A → B * B = B → A * B = 0 → B * A = 0 → IsTraceClass ((A + B) * Z * (A + B)) →
      IsTraceClass (A * Z * A) ∧ trace ((A + B) * Z * (A + B)) = trace (A * Z * A) + trace (B * Z * B) := by
    intro A B Z a b ab ba h
    have e1 : A * ((A + B) * Z * (A + B)) * A = A * Z * A := by
      rw [← mul_assoc, ← mul_assoc, mul_add A A, a, ab, add_zero, mul_assoc, add_mul, a, ba, add_zero]
    have e2 : B * ((A + B) * Z * (A + B)) * B = B * Z * B := by
      rw [← mul_assoc, ← mul_assoc, mul_add B A, b, ba, zero_add, mul_assoc, add_mul, b, ab, zero_add]
    set Q := (A + B) * Z * (A + B) with hQ
    have e3 : Q = A * Q + B * Q := by
      rw [← add_mul, hQ, ← mul_assoc, ← mul_assoc, add_mul A B (A + B), mul_add A, mul_add B, a, b, ab, ba, add_zero, zero_add]
    have c : ∀ P : H →L[ℂ] H, P * P = P → trace (P * Q) = trace (P * Q * P) := fun P hP => by
      have := trace_comp_comm (h.comp_left P) P
      change trace (P * (P * Q)) = trace (P * Q * P) at this
      rwa [← mul_assoc, hP] at this
    refine ⟨e1 ▸ (h.comp_left A).comp_right A, ?_⟩
    rw [← e1, ← e2, ← c A a, ← c B b]
    conv_lhs => rw [e3]
    exact trace_add (h.comp_left A) (h.comp_left B)
  have hT : IsTraceClass ((Λ + E) * Y * (Λ + E)) := by
    have : (Λ + E) * Y * (Λ + E) = Λ * (Y * Λ) + (Λ * (Y * E) + E * Y * (Λ + E)) := by noncomm_ring
    rw [this]
    exact t1.add ((t3.comp_left Λ).add (t2.comp_right (Λ + E)))
  obtain ⟨-, k1⟩ := key Λ E Y h1 h2 h5 h6 hT
  rw [hs] at hT k1
  obtain ⟨k2, k3⟩ := key Λ' E' Y h3 h4 h7 h8 hT
  have c1 : trace (E * Y * E) = trace (E * Y) := by
    have := trace_comp_comm t2 E
    change trace (E * (E * Y)) = trace (E * Y * E) at this
    rw [← this, ← mul_assoc]; exact congrArg (fun Z => trace (Z * Y)) h2
  have c2 : trace (E' * Y * E') = trace (Y * E') := by
    have := trace_comp_comm t4 E'
    change trace (E' * (Y * E')) = trace (Y * E' * E') at this
    rw [mul_assoc, this, mul_assoc]; exact congrArg (fun Z => trace (Y * Z)) h4
  refine ⟨k2, ?_⟩
  change trace (Λ * (Y * Λ)) + trace (E * Y) = trace (Λ' * (Y * Λ')) + trace (Y * E')
  rw [← mul_assoc, ← mul_assoc, ← c1, ← c2, ← k1, k3]
