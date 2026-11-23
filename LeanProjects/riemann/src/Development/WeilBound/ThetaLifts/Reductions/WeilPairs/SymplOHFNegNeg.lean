import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.ImportsAlt
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.DoubledTargetWeilTransportRestrictFirstFactorImp
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.ThetaFunctionHeisenbergInvariant
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.WeilPairData.StandardTraceAddCharIsStandardCharOfAdmissibleCM
open scoped TensorProduct Matrix ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace PositivityTheory.ThKW.Dbl

open Formalism.IndefR.DatumF GlobalTheory.DblTargetDelta GlobalTheory.WeilSchrodinger.DblTargetF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {nS nT : ℕ}
  {σ : E →ₐ[F] E} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}

theorem topR_add (x y : WOF F E nS (nT + nT)) : topR (x + y) = topR x + topR y := rfl
theorem botR_add (x y : WOF F E nS (nT + nT)) : botR (x + y) = botR x + botR y := rfl
theorem topR_neg (x : WOF F E nS (nT + nT)) : topR (-x) = -topR x := rfl
theorem botR_neg (x : WOF F E nS (nT + nT)) : botR (-x) = -botR x := rfl
theorem topR_zero : topR (0 : WOF F E nS (nT + nT)) = 0 := rfl
theorem botR_zero : botR (0 : WOF F E nS (nT + nT)) = 0 := rfl

theorem continuous_topR : Continuous (topR : WOF F E nS (nT + nT) → WOF F E nS nT) :=
  continuous_id.matrix_submatrix _ _

theorem continuous_botR : Continuous (botR : WOF F E nS (nT + nT) → WOF F E nS nT) :=
  continuous_id.matrix_submatrix _ _

theorem hOF_dbl (x y : WOF F E nS (nT + nT)) :
    hOF σ JS (dblG JT) x y = hOF σ JS JT (topR x) (topR y) - hOF σ JS JT (botR x) (botR y) := by
  simp only [hOF, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [Finset.sum_sub_distrib]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1 <;> refine Finset.sum_congr rfl fun c _ => ?_ <;>
    rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type] <;>
    simp only [dblG, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, topR, botR,
      Function.comp_apply, id] <;> simp [dbl]

theorem symplOF_dbl (x y : WOF F E nS (nT + nT)) :
    symplOF σ JS (dblG JT) ξ₀ x y = symplOF σ JS JT ξ₀ (topR x) (topR y) - symplOF σ JS JT ξ₀ (botR x) (botR y) := by
  simp only [symplOF, hOF_dbl, mul_sub, map_sub]

theorem symplOHF_dbl (x y : WOF F E nS (nT + nT)) :
    symplOHF σ JS (dblG JT) ξ₀ x y = symplOHF σ JS JT ξ₀ (topR x) (topR y) - symplOHF σ JS JT ξ₀ (botR x) (botR y) := by
  simp only [symplOHF, symplOF_dbl, mul_sub]

theorem symplOHF_neg_neg (x y : WOF F E nS nT) : symplOHF σ JS JT ξ₀ (-x) (-y) = symplOHF σ JS JT ξ₀ x y := by
  simp [symplOHF, symplOF, hOF]

theorem conj_psi {ψ : AddChar (AF F) ℂ} (hψ : ∀ a, ‖ψ a‖ = 1) (t : AF F) : conj (ψ t) = ψ (-t) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ t)]

theorem heis_delta {ψ : AddChar (AF F) ℂ} (hψ : ∀ a, ‖ψ a‖ = 1) (w : WOF F E nS (nT + nT))
    (f₁ f₂ : WOF F E nS nT → ℂ) :
    heisOF σ JS (dblG JT) ξ₀ ψ w (deltaT f₁ f₂) =
      deltaT (heisOF σ JS JT ξ₀ ψ (topR w) f₁) (heisOF σ JS JT ξ₀ ψ (-botR w) f₂) := by
  funext x
  simp only [heisOF, deltaT_apply, symplOHF_dbl, symplOHF_neg_neg, map_mul, conj_psi hψ, topR_add, botR_add, neg_add,
    sub_eq_add_neg, AddChar.map_add_eq_mul]
  ring

theorem theta_delta {ψ : AddChar (AF F) ℂ} (hψ : ∀ a, ‖ψ a‖ = 1) {f₁ f₂ : WOF F E nS nT → ℂ}
    (h₁ : IsThetaFunOF σ JS JT ξ₀ ψ f₁) (h₂ : IsThetaFunOF σ JS JT ξ₀ ψ f₂) :
    IsThetaFunOF σ JS (dblG JT) ξ₀ ψ (deltaT f₁ f₂) := by
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  let tA : WOF F E nS (nT + nT) →+ WOF F E nS nT := ⟨⟨topR, rfl⟩, fun _ _ => rfl⟩
  let bA : WOF F E nS (nT + nT) →+ WOF F E nS nT := -⟨⟨botR, rfl⟩, fun _ _ => rfl⟩
  have htA : Continuous tA := continuous_topR
  have hbA : Continuous bA := continuous_botR.neg
  refine ⟨fun γ w => ?_, ?_, ?_, fun k L hL h0 w => ?_⟩
  · have e1 : topR (ratWF (F := F) γ) = ratWF (γ.submatrix (finSumFinEquiv ∘ Sum.inl) id) := rfl
    have e2 : -botR (ratWF (F := F) γ) = ratWF (-γ.submatrix (finSumFinEquiv ∘ Sum.inr) id) := by
      ext i j; simp [ratWF, botR]
    simp only [deltaT_apply, topR_add, botR_add, neg_add, symplOHF_dbl]
    rw [← symplOHF_neg_neg (botR _), e1, e2, h₁.quasi, h₂.quasi, map_mul, conj_psi hψ, neg_neg, neg_sub,
      sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  · obtain ⟨U₁, hU₁, hf₁⟩ := h₁.level
    obtain ⟨U₂, hU₂, hf₂⟩ := h₂.level
    refine ⟨U₁.comap tA ⊓ U₂.comap bA, (hU₁.preimage htA).inter (hU₂.preimage hbA), fun u hu h0 => ?_⟩
    rw [heis_delta hψ, hf₁ (topR u) hu.1, hf₂ (-botR u) hu.2]
    · ext i j
      have := congrFun (congrFun h0 (finSumFinEquiv (Sum.inr i))) j
      simp only [Matrix.map_apply, Matrix.zero_apply] at this
      show infPartF F E (-(u (finSumFinEquiv (Sum.inr i)) j)) = 0
      rw [map_neg, show infPartF F E (u (finSumFinEquiv (Sum.inr i)) j) = 0 from this, neg_zero]
    · ext i j
      exact congrFun (congrFun h0 (finSumFinEquiv (Sum.inl i))) j
  · exact (h₁.cont.comp htA).mul (Complex.continuous_conj.comp (h₂.cont.comp hbA))
  · have a1 := h₁.smooth k (tA.comp L) (htA.comp hL) (fun t => by
      ext i j
      exact congrFun (congrFun (h0 t) (finSumFinEquiv (Sum.inl i))) j) (topR w)
    have a2 := h₂.smooth k (bA.comp L) (hbA.comp hL) (fun t => by
      ext i j
      have := congrFun (congrFun (h0 t) (finSumFinEquiv (Sum.inr i))) j
      simp only [Matrix.map_apply, Matrix.zero_apply] at this
      show finPartF F E (-(L t (finSumFinEquiv (Sum.inr i)) j)) = 0
      rw [map_neg, this, neg_zero]) (-botR w)
    have a3 := a1.mul (Complex.conjCLE.contDiff.comp a2)
    refine (show (fun t => deltaT f₁ f₂ (w + L t)) = _ from funext fun t => ?_) ▸ a3
    simp only [deltaT_apply, topR_add, botR_add, neg_add]
    rfl

theorem psi_norm {B : Base F E} (hB : B.IsGood σ) : ∀ a, ‖B.ψ a‖ = 1 :=
  (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB).1.2.1

end PositivityTheory.ThKW.Dbl
