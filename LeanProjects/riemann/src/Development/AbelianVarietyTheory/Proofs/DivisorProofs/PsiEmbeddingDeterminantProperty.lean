import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDetEltOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusOfPadic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomsDvrCardEqFinrank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FontaineAinfLocalDomainXiAdicOrder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiDeterminantElementPropertyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiDeterminantValuationBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiDeterminantRankPropertyStatement
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem detConst_linear_isom : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ τ₀ : Λ →+* O, ∃ (κ₀ : ℝ) (κ : (Λ →+* O) → ℝ), ∀ (γ : O ≃+* O), IsIsom C v γ → ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) ι (lam : C), IsIota C D ((γ : O →+* O).comp τ₀) N ι → lam ≠ 0 → ι '' (detLattice C (actT D) ((γ : O →+* O).comp τ₀) N : Set (detLine C (actT D) ((γ : O →+* O).comp τ₀) N)) = (fun w => lam • w) '' (detLattice C (actH D) ((γ : O →+* O).comp τ₀) N : Set (detLine C (actH D) ((γ : O →+* O).comp τ₀) N)) → Real.log (v lam) = N * κ₀ + ∑ᶠ σ, (D.lieRank ((γ : O →+* O).comp σ) : ℝ) * κ σ := by
  classical
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ τ₀
  obtain ⟨-, -, ψ, -, hψ, -⟩ := GlobalTheory.DetInv.psi_phi_tensor p O Λ
  obtain ⟨κ₀, κ, hlin⟩ := GlobalTheory.T.psi_determinant_valuation_bound p C v O hv ε hε Λ ψ hψ τ₀
  obtain ⟨hfin, -⟩ := GlobalTheory.card_ringHom_to_integers_eq_finrank p C v O hv Λ
  obtain ⟨-, -, -, -, hθν, -, -⟩ := GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hε
  set t : ℝ := Real.log (v (algebraMap O C (WittVector.fontaineTheta O p (nu ε)))) with ht
  refine ⟨κ₀, fun σ => κ σ - if σ = τ₀ then t else 0, ?_⟩
  intro γ hγ N h hh D ι lam hι hlam hlat
  obtain ⟨Δ, c, hΔ, hord, hc⟩ :=
    GlobalTheory.T.psi_determinant_element_property p C v O hv ε hε Λ ψ hψ N h hh D ((γ : O →+* O).comp τ₀) ι lam hι hlat
  obtain ⟨Δ', c', hΔ', hord', hc'⟩ :=
    GlobalTheory.T.psi_determinant_rank_property p C v O hv ε hε Λ ψ hψ γ hγ N Δ D.lieRank c hΔ hord
  have key := hlin N Δ' _ c' hΔ' hord'
  rw [hc' τ₀, hc] at key
  have hv0 : v lam ≠ 0 := (Valuation.ne_zero_iff v).mpr hlam
  have hθ0 : algebraMap O C (WittVector.fontaineTheta O p (nu ε)) ≠ 0 := by
    intro h0
    apply hθν
    apply hv.hom_inj
    rw [h0, map_zero]
  have hvθ : v (algebraMap O C (WittVector.fontaineTheta O p (nu ε))) ≠ 0 :=
    (Valuation.ne_zero_iff v).mpr hθ0
  have hlog : Real.log ((v lam * v (algebraMap O C (WittVector.fontaineTheta O p (nu ε))) ^
      D.lieRank ((γ : O →+* O).comp τ₀) : NNReal) : ℝ) =
      Real.log (v lam) + (D.lieRank ((γ : O →+* O).comp τ₀) : ℝ) * t := by
    rw [NNReal.coe_mul, NNReal.coe_pow, Real.log_mul, Real.log_pow]
    · exact_mod_cast hv0
    · exact pow_ne_zero _ (by exact_mod_cast hvθ)
  rw [hlog] at key
  haveI := hfin
  letI := Fintype.ofFinite (Λ →+* O)
  rw [finsum_eq_sum_of_fintype] at key ⊢
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  linarith

end GlobalTheory.DetInv
