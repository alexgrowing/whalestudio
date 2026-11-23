import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasisOfBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomsDvrCardEqFinrank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TiltLatticeBoundSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TiltLatticeBoundThirdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiEmbeddingDeterminantPropertyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrAlphaDeterminantValuationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdjoinEqTopPadicInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicIntRingHomExtOfIsHausdorff
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem ringHom_eq_of_eq_on_generator {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]
    [IsHausdorff (Ideal.span {(p : O)}) O] {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]
    {α : Λ} (hα : Algebra.adjoin ℤ_[p] {α} = ⊤) (σ τ : Λ →+* O) (h : σ α = τ α) : σ = τ := by
  have hbase : σ.comp (algebraMap ℤ_[p] Λ) = τ.comp (algebraMap ℤ_[p] Λ) :=
    GlobalTheory.padicInt_ringHom_ext_of_isHausdorff p O _ _
  ext x
  have hx : x ∈ Algebra.adjoin ℤ_[p] {α} := hα ▸ Algebra.mem_top
  refine Algebra.adjoin_induction (fun y hy => ?_) (fun r => ?_) (fun y z _ _ hy hz => ?_)
    (fun y z _ _ hy hz => ?_) hx
  · rw [Set.mem_singleton_iff.1 hy]; exact h
  · exact congrArg (fun f : ℤ_[p] →+* O => f r) hbase
  · rw [map_add, map_add, hy, hz]
  · rw [map_mul, map_mul, hy, hz]

theorem shift_linear_isom : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ τ₀ : Λ →+* O, ∃ (κ₀ : ℝ) (κ : (Λ →+* O) → ℝ), ∀ (γ : O ≃+* O), IsIsom C v γ → ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ), ∃ r : NNReal, r ≠ 0 ∧ IsShift C v D ((γ : O →+* O).comp τ₀) r ∧ Real.log r = N * κ₀ + ∑ᶠ σ, (D.lieRank ((γ : O →+* O).comp σ) : ℝ) * κ σ := by
  classical
  intro p _ C _ _ _ v O _ _ _ _ hv ε hε Λ _ _ _ _ _ _ τ₀
  obtain ⟨α, hα⟩ := GlobalTheory.MonoGen.exists_adjoin_eq_top_padicInt p Λ
  obtain ⟨κ₀, κ', hlin⟩ := GlobalTheory.T.psi_embedding_determinant_property p C v O hv ε hε Λ τ₀
  obtain ⟨hfin, -⟩ := GlobalTheory.card_ringHom_to_integers_eq_finrank p C v O hv Λ
  haveI := hfin
  letI := Fintype.ofFinite (Λ →+* O)
  let c : (Λ →+* O) → ℝ := fun σ => if σ = τ₀ then 0 else
    Real.log (v (algebraMap O C (τ₀ α) - algebraMap O C (σ α)))
  refine ⟨κ₀, fun σ => κ' σ - c σ, ?_⟩
  intro γ hγ N h hh D
  obtain ⟨γC, hγC, hvγ⟩ := hγ
  set τ : Λ →+* O := (γ : O →+* O).comp τ₀ with hτ
  obtain ⟨⟨ι, hι, -⟩, -⟩ := GlobalTheory.T.tilt_lattice_bound_second p C v O hv ε hε Λ N h hh D τ
  obtain ⟨lam, hlam, hlat⟩ := GlobalTheory.T.tilt_lattice_bound_third p C v O hv ε hε Λ N h hh D τ ι hι
  have hsh := GlobalTheory.T.dvr_alpha_determinant_valuation p C v O hv ε hε Λ α hα N h hh D τ ι lam hι hlat
  have hlog := hlin γ ⟨γC, hγC, hvγ⟩ N h hh D ι lam hι hlam hlat

  have hsep : ∀ σ : Λ →+* O, σ ≠ τ →
      v (algebraMap O C (τ α) - algebraMap O C (σ α)) ≠ 0 := by
    intro σ hσ
    refine (Valuation.ne_zero_iff v).mpr ?_
    rw [← map_sub]
    intro h0
    apply hσ
    refine (ringHom_eq_of_eq_on_generator hα σ τ ?_)
    have h1 : τ α - σ α = 0 := hv.hom_inj (by rw [h0, map_zero])
    exact (sub_eq_zero.1 h1).symm
  have hv0 : v lam ≠ 0 := (Valuation.ne_zero_iff v).mpr hlam
  set P : NNReal := ∏ᶠ σ : {σ : Λ →+* O // σ ≠ τ},
    v (algebraMap O C (τ α) - algebraMap O C (σ.1 α)) ^ D.lieRank σ.1 with hP
  have hPe : P = ∏ σ : {σ : Λ →+* O // σ ≠ τ},
      v (algebraMap O C (τ α) - algebraMap O C (σ.1 α)) ^ D.lieRank σ.1 :=
    finprod_eq_prod_of_fintype _
  have hP0 : P ≠ 0 := by
    rw [hPe]
    exact Finset.prod_ne_zero_iff.mpr fun σ _ => pow_ne_zero _ (hsep σ.1 σ.2)
  refine ⟨v lam * P⁻¹, mul_ne_zero hv0 (inv_ne_zero hP0), hsh, ?_⟩

  have hlogP : Real.log (P : ℝ) = ∑ σ : {σ : Λ →+* O // σ ≠ τ},
      (D.lieRank σ.1 : ℝ) * Real.log (v (algebraMap O C (τ α) - algebraMap O C (σ.1 α))) := by
    rw [hPe, NNReal.coe_prod, Real.log_prod]
    · refine Finset.sum_congr rfl fun σ _ => ?_
      rw [NNReal.coe_pow, Real.log_pow]
    · intro σ _
      exact_mod_cast pow_ne_zero _ (hsep σ.1 σ.2)
  have hlr : Real.log ((v lam * P⁻¹ : NNReal) : ℝ) = Real.log (v lam) - Real.log (P : ℝ) := by
    rw [NNReal.coe_mul, NNReal.coe_inv, Real.log_mul, Real.log_inv, sub_eq_add_neg]
    · exact_mod_cast hv0
    · exact inv_ne_zero (by exact_mod_cast hP0)

  let e : (Λ →+* O) ≃ (Λ →+* O) :=
    { toFun := fun σ => (γ : O →+* O).comp σ
      invFun := fun σ => (γ.symm : O →+* O).comp σ
      left_inv := fun σ => by ext x; simp
      right_inv := fun σ => by ext x; simp }
  have hsub : ∑ σ : {σ : Λ →+* O // σ ≠ τ},
      (D.lieRank σ.1 : ℝ) * Real.log (v (algebraMap O C (τ α) - algebraMap O C (σ.1 α))) =
      ∑ σ : Λ →+* O, (D.lieRank ((γ : O →+* O).comp σ) : ℝ) * c σ := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun σ => σ ≠ τ) (by simp)
      (fun σ => (D.lieRank σ : ℝ) * Real.log (v (algebraMap O C (τ α) - algebraMap O C (σ α)))),
      Finset.sum_filter]
    symm
    refine Fintype.sum_equiv e _ _ fun σ => ?_
    show (D.lieRank ((γ : O →+* O).comp σ) : ℝ) * c σ = if (γ : O →+* O).comp σ ≠ τ then _ else 0
    by_cases hσ : σ = τ₀
    · have heq : (γ : O →+* O).comp σ = τ := by rw [hσ]
      rw [if_neg (not_not.2 heq)]
      simp only [c, if_pos hσ, mul_zero]
    · have hne : (γ : O →+* O).comp σ ≠ τ := by
        intro heq
        apply hσ
        ext x
        exact γ.injective (congrArg (fun f : Λ →+* O => f x) heq)
      rw [if_pos hne]
      simp only [c, if_neg hσ]
      have hiso : v (algebraMap O C (τ₀ α) - algebraMap O C (σ α)) =
          v (algebraMap O C (γ (τ₀ α)) - algebraMap O C (γ (σ α))) := by
        rw [← hγC, ← hγC, ← map_sub γC, hvγ]
      rw [hiso]
      rfl
  rw [hlr, hlogP, hsub, hlog, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

end GlobalTheory.DetInv
