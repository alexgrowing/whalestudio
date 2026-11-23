import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusOfPadic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumScalarActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixOfIntertwinerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameMatrixCompositionUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrobeniusTwistedFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePsiCoordinatesPadicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameTransitionPsiMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantFrameComparisonStatement

noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem exists_freeForm : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (N h : ℕ) , h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) (ψ : RL p O Λ →+* RL p O Λ), IsPsi ψ → Nonempty (FreeForm D N ψ) := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ N h hh D ψ hψ
  obtain ⟨eT, eM, hT, hM, hrat⟩ := GlobalTheory.T.determinant_frame_comparison p C v O hv ε hε Λ N h hh D
  obtain ⟨tM, htM, htw⟩ := GlobalTheory.T.exists_frobenius_twisted_frame p O Λ N h ψ D.ρM eM hψ hM
  have hTw := GlobalTheory.T.frame_psi_coordinates_padic p O Λ N h ψ eT hψ hrat
  obtain ⟨hscal, hFG, hG, hΨ, hΨ'⟩ := GlobalTheory.T.sandwich_datum_scalar_action p C v O hv ε hε Λ h D
  obtain ⟨-, -, ψ₀, φ₀, hψ₀, -, -, hφψ⟩ := GlobalTheory.DetInv.psi_phi_tensor p O Λ
  have hψeq : ∀ r, ψ r = ψ₀ r := by
    intro r
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul a l => rw [hψ, hψ₀]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hsurj : Function.Surjective ψ := fun r => ⟨φ₀ r, by rw [hψeq, hφψ]⟩
  have calc₁ := fun (e e' e'' : (Fin N → RL p O Λ) ≃ₗ[Ainf p O] (Fin h → Ainf p O)) =>
    GlobalTheory.T.frame_matrix_composition_unique p O Λ N h e e' e''
  obtain ⟨F, hF⟩ := GlobalTheory.T.exists_matrix_of_intertwiner p O Λ N h (rhoTA D) D.ρM eT eM D.F hT hM (fun l => D.F_act l)
  obtain ⟨G, hGm⟩ := GlobalTheory.T.exists_matrix_of_intertwiner p O Λ N h D.ρM (rhoTA D) eM eT D.G hM hT hG
  obtain ⟨Ψ, hΨm⟩ := GlobalTheory.T.exists_matrix_of_intertwiner p O Λ N h (fun l => (D.ρM l).map (phiInv p O)) D.ρM tM eM D.Ψ
    htM hM hΨ
  obtain ⟨Ψ', hΨ'm⟩ := GlobalTheory.T.exists_matrix_of_intertwiner p O Λ N h D.ρM (fun l => (D.ρM l).map (phiInv p O)) eM tM D.Ψ'
    hM htM hΨ'
  have hFψ := GlobalTheory.T.frame_transition_psi_matrix p O Λ N h ψ eT eM eT tM D.F F hsurj hTw htw hF
  refine ⟨⟨eT, eM, F, G, Ψ, Ψ', hT, hM, hF, hGm, ?_, ?_, ?_, ?_⟩⟩
  · have h1 := (calc₁ eT eM eT).1 _ _ _ _ hF hGm
    rw [D.G_mul_F] at h1
    exact (calc₁ eT eT eT).2.1 _ _ _ h1 ((calc₁ eT eT eT).2.2 (mu ε))
  · have h1 := (calc₁ eM eT eM).1 _ _ _ _ hGm hF
    rw [hFG] at h1
    exact (calc₁ eM eM eM).2.1 _ _ _ h1 ((calc₁ eM eM eM).2.2 (mu ε))
  · have h1 := (calc₁ eT tM eM).1 _ _ _ _ hFψ hΨm
    rw [← D.F_eq] at h1
    exact (calc₁ eT eM eM).2.1 _ _ _ hF h1
  · have h1 := (calc₁ eM tM eM).1 _ _ _ _ hΨ'm hΨm
    rw [D.Ψ_mul] at h1
    exact (calc₁ eM eM eM).2.1 _ _ _ h1 ((calc₁ eM eM eM).2.2 (xi ε))

end GlobalTheory.DetInv
