import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrderStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumEigenMultiplicityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumScalarActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaProjectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaProjectionIntertwiningStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaProjectionSurjectiveEigenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDetLineCoordinateIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeScalingValuationEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwinerMapsEigenspacesStatement

noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem iotaScalar_of_freeForm : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (N h : ℕ) , h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) (ψ : RL p O Λ →+* RL p O Λ) (Φ : FreeForm D N ψ) (τ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta τ f → ∀ ι (lam : C), IsIota C D τ N ι → ι '' (detLattice C (actT D) τ N : Set (detLine C (actT D) τ N)) = (fun w => lam • w) '' (detLattice C (actH D) τ N : Set (detLine C (actH D) τ N)) → ∃ l₀ : C, v l₀ = v lam ∧ IotaScalar (Φ.F.map ((algebraMap O C).comp f)) (Φ.G.map ((algebraMap O C).comp f)) (D.lieRank τ) l₀ := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ N h hh D ψ Φ τ f hf ι lam hι hlat
  obtain ⟨-, -, -, hθs, -, -, -⟩ := GlobalTheory.T.fontaineAinf_localDomain_xiAdic_order p C v O hv ε hε
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨a, rfl⟩ := hθs y
    exact ⟨a ⊗ₜ 1, by rw [hf]; simp⟩
  obtain ⟨⟨-, hTtop, hTrk⟩, ⟨-, hHtop, hHrk⟩⟩ := GlobalTheory.T.sandwich_datum_eigen_multiplicity p C v O hv ε hε Λ N h hh D
  obtain ⟨πT, hπT⟩ := GlobalTheory.T.exists_theta_projection p O C Λ N h τ f Φ.eT hf
  obtain ⟨πH, hπH⟩ := GlobalTheory.T.exists_theta_projection p O C Λ N h τ f Φ.eM hf
  obtain ⟨qT, hqT, hqTL⟩ : ∃ q : eig C (actT D) τ ≃ₗ[C] (Fin N → C), (∀ x, q x = πT x) ∧
      ∀ x, x ∈ quotLattice C (actT D) τ ↔ ∀ i, q x i ∈ (algebraMap O C).range :=
    GlobalTheory.T.theta_projection_surjective_eigen p O C Λ N h τ f (rhoTA D) Φ.eT πT hinj hθs hfs hf Φ.frameT hπT hTtop (hTrk τ)
  obtain ⟨qH, hqH, hqHL⟩ : ∃ q : eig C (actH D) τ ≃ₗ[C] (Fin N → C), (∀ x, q x = πH x) ∧
      ∀ x, x ∈ quotLattice C (actH D) τ ↔ ∀ i, q x i ∈ (algebraMap O C).range :=
    GlobalTheory.T.theta_projection_surjective_eigen p O C Λ N h τ f D.ρM Φ.eM πH hinj hθs hfs hf Φ.frameM hπH hHtop (hHrk τ)
  obtain ⟨δT, hδT, hδTL⟩ := GlobalTheory.T.exists_det_line_coordinate_iso C O Λ h N (actT D) τ qT hqTL
  obtain ⟨δH, hδH, hδHL⟩ := GlobalTheory.T.exists_det_line_coordinate_iso C O Λ h N (actH D) τ qH hqHL
  obtain ⟨l₀, hl₀v, hl₀⟩ := GlobalTheory.T.lattice_scaling_valuation_eq C v O _ _
    (detLattice C (actT D) τ N : Set (detLine C (actT D) τ N))
    (detLattice C (actH D) τ N : Set (detLine C (actH D) τ N)) δT δH ι lam hv
    (fun w => hδTL w) (fun w => hδHL w) hlat
  obtain ⟨-, -, hGρ, -, -⟩ := GlobalTheory.T.sandwich_datum_scalar_action p C v O hv ε hε Λ h D
  have hG : ∀ l, D.G.map (WittVector.fontaineTheta O p) * actH D l =
      actT D l * D.G.map (WittVector.fontaineTheta O p) := by
    intro l
    have e := congrArg (fun M => M.map (WittVector.fontaineTheta O p)) (hGρ l)
    simpa [Matrix.map_mul, actH, actT, rhoTA, Matrix.map_map, padicToO] using e
  have hF : ∀ l, D.F.map (WittVector.fontaineTheta O p) * actT D l =
      actH D l * D.F.map (WittVector.fontaineTheta O p) := by
    intro l
    have e := congrArg (fun M => M.map (WittVector.fontaineTheta O p)) (D.F_act l)
    simpa [Matrix.map_mul, actH, actT, Matrix.map_map, padicToO] using e
  have hbmem : ∀ y : eig C (actH D) τ, bC C D y ∈ eig C (actT D) τ := by
    intro y
    apply (GlobalTheory.T.intertwiner_maps_eigenspaces C O Λ h (actH D) (actT D) _ hG).1 τ
    exact ⟨y, y.2, rfl⟩
  have hamem : ∀ x : eig C (actT D) τ, alC C D x ∈ eig C (actH D) τ := by
    intro x
    apply (GlobalTheory.T.intertwiner_maps_eigenspaces C O Λ h (actT D) (actH D) _ hF).1 τ
    exact ⟨x, x.2, rfl⟩
  refine ⟨l₀, hl₀v, ?_⟩
  intro X Y hX hY
  have h1 : ∀ i : Fin N, (i : ℕ) < D.lieRank τ →
      ((qT.symm (X i) : eig C (actT D) τ) : Fin h → C) = bC C D (qH.symm (Y i)) := by
    intro i hi
    have hz : qT ⟨bC C D (qH.symm (Y i)), hbmem _⟩ = X i := by
      rw [hqT]
      show πT (redC C D.G (qH.symm (Y i))) = X i
      rw [GlobalTheory.T.theta_projection_intertwining p O C Λ N h f Φ.eM Φ.eT πH πT D.G Φ.G hπH hπT Φ.matG, ← hqH,
        qH.apply_symm_apply, hX i hi]
    rw [← hz, qT.symm_apply_apply]
  have h2 : ∀ i : Fin N, D.lieRank τ ≤ (i : ℕ) →
      ((qH.symm (Y i) : eig C (actH D) τ) : Fin h → C) = alC C D (qT.symm (X i)) := by
    intro i hi
    have hz : qH ⟨alC C D (qT.symm (X i)), hamem _⟩ = Y i := by
      rw [hqH]
      show πH (redC C D.F (qT.symm (X i))) = Y i
      rw [GlobalTheory.T.theta_projection_intertwining p O C Λ N h f Φ.eT Φ.eM πT πH D.F Φ.F hπT hπH Φ.matF, ← hqT,
        qT.apply_symm_apply, hY i hi]
    rw [← hz, qH.symm_apply_apply]
  have e := hl₀ (exteriorPower.ιMulti C N fun i => qT.symm (X i))
  rw [hι _ _ h1 h2, hδH, hδT] at e
  simpa using e

end GlobalTheory.DetInv
