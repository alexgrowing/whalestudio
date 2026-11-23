import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryCentralizerOfCommutePadicPointsSpli
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormGroupToPadicPointsDegreeOneEqUnitaryPoints
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical
theorem _root_.GlobalTheory.T.exists_unitaryCentralizer_of_commute_padicPoints_split : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ), sh G β = β → ∀ (y₀ : grp G β) (c : Gr G 1), c * toP1 G β y₀ = toP1 G β y₀ * c → ∃ z : (ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ, InT G ℚ_[p] β (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) z ∧ psiP G z = c := by
  first | exact @GlobalTheory.TorCls.centraliser_at_p | exact GlobalTheory.TorCls.centraliser_at_p | (intros; apply GlobalTheory.TorCls.centraliser_at_p <;> assumption)
