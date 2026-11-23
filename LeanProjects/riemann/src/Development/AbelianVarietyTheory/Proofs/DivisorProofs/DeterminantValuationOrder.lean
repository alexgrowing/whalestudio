import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrderStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumEigenMultiplicityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SandwichDatumScalarActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaProjectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaProjectionIntertwiningStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaProjectionSurjectiveEigenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwinerMapsEigenspacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieRankEqFinrankEigenInterStatement

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem rank_G_map_eq_lieRank : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (N h : ℕ) , h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) (ψ : RL p O Λ →+* RL p O Λ) (Φ : FreeForm D N ψ) (σ : Λ →+* O) (f : RL p O Λ →+* O), IsTheta σ f → (Φ.G.map ((algebraMap O C).comp f)).rank = D.lieRank σ := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ N h hh D ψ Φ σ f hf
  obtain ⟨-, -, -, hθ, -⟩ := GlobalTheory.T.fontaineAinf_localDomain_xiAdic_order p C v O hv ε hε
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨a, rfl⟩ := hθ y
    exact ⟨a ⊗ₜ (1 : Λ), by rw [hf]; simp⟩
  obtain ⟨⟨indT, supT, dimT⟩, ⟨-, supH, dimH⟩⟩ := GlobalTheory.T.sandwich_datum_eigen_multiplicity p C v O hv ε hε Λ N h hh D
  obtain ⟨πT, hπT⟩ := GlobalTheory.T.exists_theta_projection p O C Λ N h σ f Φ.eT hf
  obtain ⟨πH, hπH⟩ := GlobalTheory.T.exists_theta_projection p O C Λ N h σ f Φ.eM hf
  have hT : (fun l => (rhoTA D l).map (WittVector.fontaineTheta O p)) = actT D := by
    funext l; rw [rhoTA, Matrix.map_map]; rfl
  have hH : (fun l => (D.ρM l).map (WittVector.fontaineTheta O p)) = actH D := rfl
  have keyT := GlobalTheory.T.theta_projection_surjective_eigen p O C Λ N h σ f (rhoTA D) Φ.eT πT hinj hθ hfs hf Φ.frameT hπT
  rw [hT] at keyT
  obtain ⟨qT, hqT, -⟩ := keyT supT (dimT σ)
  have keyH := GlobalTheory.T.theta_projection_surjective_eigen p O C Λ N h σ f (fun l => D.ρM l) Φ.eM πH hinj hθ hfs hf Φ.frameM hπH
  rw [hH] at keyH
  obtain ⟨qH, hqH, -⟩ := keyH supH (dimH σ)
  obtain ⟨-, -, hGρ, -, -⟩ := GlobalTheory.T.sandwich_datum_scalar_action p C v O hv ε hε Λ h D
  have hX : ∀ l, D.G.map (WittVector.fontaineTheta O p) * actH D l =
      actT D l * D.G.map (WittVector.fontaineTheta O p) := by
    intro l
    rw [← congrFun hT l, ← congrFun hH l]
    rw [← Matrix.map_mul, ← Matrix.map_mul, hGρ l]
  obtain ⟨hle, hrange⟩ := GlobalTheory.T.intertwiner_maps_eigenspaces C O Λ h (actH D) (actT D) (D.G.map (WittVector.fontaineTheta O p)) hX
  have hb : Matrix.toLin' ((D.G.map (WittVector.fontaineTheta O p)).map (algebraMap O C)) = bC C D := by
    rw [Matrix.map_map]; rfl
  rw [hb] at hle hrange
  have hlie := GlobalTheory.T.lie_rank_eq_finrank_eigen_inter p C v O hv ε Λ h D σ
  rw [hrange supH indT σ] at hlie
  let g : eig C (actH D) σ →ₗ[C] eig C (actT D) σ :=
    (bC C D).restrict (fun x hx => hle σ (Submodule.mem_map_of_mem hx))
  have hmat := GlobalTheory.T.theta_projection_intertwining p O C Λ N h f Φ.eM Φ.eT πH πT D.G Φ.G hπH hπT Φ.matG
  have hcomm : qT.toLinearMap ∘ₗ g = (Φ.G.map ((algebraMap O C).comp f)).mulVecLin ∘ₗ qH.toLinearMap := by
    apply LinearMap.ext; intro x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.mulVecLin_apply]
    rw [hqT, hqH]
    exact hmat x
  have e1 : (eig C (actH D) σ).map (bC C D) = (LinearMap.range g).map (eig C (actT D) σ).subtype := by
    have : bC C D ∘ₗ (eig C (actH D) σ).subtype = (eig C (actT D) σ).subtype ∘ₗ g :=
      LinearMap.ext fun x => rfl
    rw [← LinearMap.range_comp, ← this, LinearMap.range_comp, Submodule.range_subtype]
  rw [hlie, e1, ← (Submodule.equivMapOfInjective _ (eig C (actT D) σ).injective_subtype
    (LinearMap.range g)).finrank_eq, ← qT.finrank_map_eq (LinearMap.range g),
    ← LinearMap.range_comp, hcomm,
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range qH)]
  rfl

end GlobalTheory.DetInv
