import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDetEltOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrderStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfElementThetaCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeadDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeadMulUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTensorExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantFrameComparisonUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantValuationOrderStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantValuationOrderSumStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantValuationIotaScalarStatement

noncomputable section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem isTheta_unique {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]
    {σ : Λ →+* O} {f f' : RL p O Λ →+* O} (hf : IsTheta σ f) (hf' : IsTheta σ f') : f = f' := by
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a l => rw [hf, hf']
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem exists_detElt_lieRank : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (ψ : RL p O Λ →+* RL p O Λ), IsPsi ψ → ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) (τ : Λ →+* O) ι (lam : C), IsIota C D τ N ι → ι '' (detLattice C (actT D) τ N : Set (detLine C (actT D) τ N)) = (fun w => lam • w) '' (detLattice C (actH D) τ N : Set (detLine C (actH D) τ N)) → ∃ (Δ : RL p O Λ) (c : (Λ →+* O) → C), IsDetElt ε ψ N Δ ∧ HasOrders C ε N Δ D.lieRank c ∧ v (c τ) = v lam * v (algebraMap O C (WittVector.fontaineTheta O p (nu ε))) ^ D.lieRank τ := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ ψ hψ N h hh D τ ι lam hι hlat
  classical
  obtain ⟨Φ⟩ := GlobalTheory.T.determinant_frame_comparison_unit p C v O hv ε hε Λ N h hh D ψ hψ
  obtain ⟨-, -, -, -, -, hxi, -⟩ := GlobalTheory.T.fontaineAinf_localDomain_xiAdic_order p C v O hv ε hε
  let c : (Λ →+* O) → C := fun σ =>
    if hσ : ∃ f, IsTheta σ f then
      Classical.choose (GlobalTheory.T.determinant_valuation_iota_scalar p C v O hv ε hε Λ N h hh D ψ Φ σ hσ.choose hσ.choose_spec).2
    else 0
  have hc : ∀ σ f, IsTheta σ f → D.lieRank σ ≤ N ∧ c σ ≠ 0 ∧
      Lead ((algebraMap O C).comp f) (inA (xi ε)) Φ.F.det (D.lieRank σ) (c σ) := by
    intro σ f hf
    have hσ : ∃ f, IsTheta σ f := ⟨f, hf⟩
    have hfe : hσ.choose = f := isTheta_unique hσ.choose_spec hf
    have H := GlobalTheory.T.determinant_valuation_iota_scalar p C v O hv ε hε Λ N h hh D ψ Φ σ hσ.choose hσ.choose_spec
    have hcs := Classical.choose_spec H.2
    have hcσ : c σ = Classical.choose H.2 := by simp only [c, dif_pos hσ]
    rw [hcσ]
    refine ⟨H.1, hcs.1, ?_⟩
    rw [← hfe]
    exact hcs.2
  have hψdet : ψ Φ.F.det = (Φ.F.map ψ).det := by rw [RingHom.map_det]; rfl
  refine ⟨Φ.F.det, c, ⟨⟨Φ.G.det, ?_⟩, Φ.Ψ.det, ?_, ⟨Φ.Ψ'.det, ?_⟩⟩, fun σ f hf => hc σ f hf, ?_⟩
  · rw [← Matrix.det_mul, Φ.F_mul_G, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  · rw [hψdet, ← Matrix.det_mul, ← Φ.F_eq]
  · rw [← Matrix.det_mul, Φ.Ψ_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
  · obtain ⟨f, hf, -, -, -⟩ := theta_tensor_exists p C v O hv ε hε Λ τ
    obtain ⟨l₀, hl₀, hiota⟩ := GlobalTheory.T.determinant_valuation_order_sum p C v O hv ε hε Λ N h hh D ψ Φ τ f hf ι lam hι hlat
    have hrank := GlobalTheory.T.determinant_valuation_order p C v O hv ε hε Λ N h hh D ψ Φ τ f hf
    have hmu : (inA (mu ε) : RL p O Λ) = (inA (xi ε) : RL p O Λ) * inA (nu ε) := by
      rw [← map_mul, xi_mul_nu]
    have hFG : Φ.F * Φ.G =
        ((inA (xi ε) : RL p O Λ) * inA (nu ε)) • (1 : Matrix (Fin N) (Fin N) (RL p O Λ)) := by
      rw [Φ.F_mul_G, hmu]
    rw [← hrank] at hiota
    have hlead := GlobalTheory.LeadDet.lead_det (RL p O Λ) C ((algebraMap O C).comp f) (inA (xi ε))
      (inA (nu ε)) N Φ.F Φ.G l₀ hFG hiota
    rw [hrank] at hlead
    obtain ⟨-, -, hcl⟩ := hc τ f hf
    have hξreg : (inA (xi ε) : RL p O Λ) ∈ nonZeroDivisors (RL p O Λ) :=
      GlobalTheory.T.ainf_element_theta_compatible p C v O hv ε hε Λ (xi ε) hxi
    have heq := GlobalTheory.DetInv.lead_mul_unique (RL p O Λ) C ((algebraMap O C).comp f) (inA (xi ε))
      Φ.F.det 1 (D.lieRank τ) _ (c τ) hξreg hlead (by rwa [one_mul])
    have hA : f (inA (nu ε)) = WittVector.fontaineTheta O p (nu ε) := by
      show f (algebraMap (Ainf p O) (RL p O Λ) (nu ε)) = _
      rw [Algebra.TensorProduct.algebraMap_apply, hf]
      simp
    rw [heq, map_one, one_mul, map_mul, map_pow, hl₀, RingHom.comp_apply, hA]

end GlobalTheory.DetInv
