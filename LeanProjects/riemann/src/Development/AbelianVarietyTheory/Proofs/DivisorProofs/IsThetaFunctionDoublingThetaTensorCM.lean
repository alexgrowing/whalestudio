import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeltaTApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM

open scoped TensorProduct Matrix ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.DblTargetThetaF

open GlobalTheory.DblTargetDelta GlobalTheory.WeilSchrodinger.DblTargetF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def topH (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ) :
    WOF F E nS (nT + nT) →+ WOF F E nS nT where
  toFun := topR
  map_zero' := rfl
  map_add' _ _ := rfl

def sndH (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (nS nT : ℕ) :
    WOF F E nS (nT + nT) →+ WOF F E nS nT where
  toFun x := -botR x
  map_zero' := by ext; simp [botR]
  map_add' x y := by ext; simp [botR]; ring

theorem continuous_topH (nS nT : ℕ) : Continuous (topH F E nS nT) :=
  continuous_matrix fun i j => continuous_id.matrix_elem _ j

theorem continuous_sndH (nS nT : ℕ) : Continuous (sndH F E nS nT) := by
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  exact (continuous_matrix fun i j => continuous_id.matrix_elem (finSumFinEquiv (Sum.inr i)) j).neg

theorem map_topH {R : Type} [CommRing R] (φ : AEF F E →+* R) {nS nT : ℕ} {u : WOF F E nS (nT + nT)}
    (h : u.map φ = 0) : (topH F E nS nT u).map φ = 0 :=
  Matrix.ext fun i j => congrFun (congrFun h (finSumFinEquiv (Sum.inl i))) j

theorem map_sndH {R : Type} [CommRing R] (φ : AEF F E →+* R) {nS nT : ℕ} {u : WOF F E nS (nT + nT)}
    (h : u.map φ = 0) : (sndH F E nS nT u).map φ = 0 :=
  Matrix.ext fun i j => by
    have e : φ (u (finSumFinEquiv (Sum.inr i)) j) = 0 := congrFun (congrFun h (finSumFinEquiv (Sum.inr i))) j
    change φ (-(u (finSumFinEquiv (Sum.inr i)) j)) = 0
    rw [map_neg, e, neg_zero]

theorem hOF_neg (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (x y : WOF F E nS nT) : hOF σ JS JT (-x) (-y) = hOF σ JS JT x y := by
  simp [hOF]

theorem hOF_dbl (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (x y : WOF F E nS (nT + nT)) :
    hOF σ JS (dblG JT) x y = hOF σ JS JT (topH F E nS nT x) (topH F E nS nT y) -
      hOF σ JS JT (sndH F E nS nT x) (sndH F E nS nT y) := by
  change _ = hOF σ JS JT (topR x) (topR y) - hOF σ JS JT (-botR x) (-botR y)
  rw [hOF_neg]
  unfold hOF
  have hs : ∀ g : Fin (nT + nT) → AEF F E, ∑ a, g a =
      ∑ a, g (finSumFinEquiv (Sum.inl a)) + ∑ a, g (finSumFinEquiv (Sum.inr a)) := fun g => by
    rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [hs]
  simp [-finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right, dblG, GlobalTheory.WeilM.dbl, topH, topR, botR,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, sub_eq_add_neg]

theorem symplOHF_dbl (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E)
    (ξ₀ : E) (x y : WOF F E nS (nT + nT)) :
    symplOHF σ JS (dblG JT) ξ₀ x y = symplOHF σ JS JT ξ₀ (topH F E nS nT x) (topH F E nS nT y) -
      symplOHF σ JS JT ξ₀ (sndH F E nS nT x) (sndH F E nS nT y) := by
  unfold symplOHF symplOF
  rw [hOF_dbl, mul_sub, map_sub, mul_sub]

theorem conj_char {G : Type} [AddCommGroup G] (ψ : AddChar G ℂ) (h : ∀ x, ‖ψ x‖ = 1) (x : G) :
    conj (ψ x) = ψ (-x) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (h x)]

theorem deltaT_eq {nS nT : ℕ} (f₁ f₂ : WOF F E nS nT → ℂ) :
    deltaT f₁ f₂ = fun w => f₁ (topH F E nS nT w) * conj (f₂ (sndH F E nS nT w)) := rfl

theorem topH_ratWF {nS nT : ℕ} (γ : Matrix (Fin (nT + nT)) (Fin nS) E) :
    topH F E nS nT (ratWF γ) = ratWF (γ.submatrix (finSumFinEquiv ∘ Sum.inl) id) := rfl

theorem sndH_ratWF {nS nT : ℕ} (γ : Matrix (Fin (nT + nT)) (Fin nS) E) :
    sndH F E nS nT (ratWF γ) = ratWF (-γ.submatrix (finSumFinEquiv ∘ Sum.inr) id) := by
  ext i j
  change -((incAF F E) (γ _ j)) = (incAF F E) (-(γ _ j))
  rw [map_neg]

theorem isThetaFunOF_deltaT (σ : E →ₐ[F] E) {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E}
    {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E} {ψ : AddChar (AF F) ℂ} (hn : ∀ x, ‖ψ x‖ = 1)
    {f₁ f₂ : WOF F E nS nT → ℂ} (h₁ : IsThetaFunOF σ JS JT ξ₀ ψ f₁) (h₂ : IsThetaFunOF σ JS JT ξ₀ ψ f₂) :
    IsThetaFunOF σ JS (dblG JT) ξ₀ ψ (deltaT f₁ f₂) := by
  rw [deltaT_eq]
  refine ⟨fun γ w => ?_, ?_, ?_, fun k L hL h0 w => ?_⟩
  · rw [map_add, map_add, symplOHF_dbl, topH_ratWF, sndH_ratWF, h₁.quasi, h₂.quasi, map_mul, conj_char ψ hn,
      neg_neg, neg_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  · obtain ⟨U₁, hU₁, k₁⟩ := h₁.level
    obtain ⟨U₂, hU₂, k₂⟩ := h₂.level
    refine ⟨U₁.comap (topH F E nS nT) ⊓ U₂.comap (sndH F E nS nT),
      (hU₁.preimage (continuous_topH nS nT)).inter (hU₂.preimage (continuous_sndH nS nT)), fun u hu h0 => ?_⟩
    funext w
    have e₁ := congrFun (k₁ _ hu.1 (map_topH _ h0)) (topH F E nS nT w)
    have e₂ := congrFun (k₂ _ hu.2 (map_sndH _ h0)) (sndH F E nS nT w)
    simp only [heisOF] at e₁ e₂ ⊢
    rw [← e₁, ← e₂, symplOHF_dbl, sub_eq_add_neg, AddChar.map_add_eq_mul, map_add, map_add, map_mul, conj_char ψ hn]
    ring
  · exact (h₁.cont.comp (continuous_topH nS nT)).mul
      (Complex.continuous_conj.comp (h₂.cont.comp (continuous_sndH nS nT)))
  · simp only [map_add]
    exact (h₁.smooth k ((topH F E nS nT).comp L) ((continuous_topH nS nT).comp hL) (fun t => map_topH _ (h0 t)) _).mul
      (Complex.conjCLE.contDiff.comp (h₂.smooth k ((sndH F E nS nT).comp L) ((continuous_sndH nS nT).comp hL)
        (fun t => map_sndH _ (h0 t)) _))

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ,
        Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ → Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₂ →
        Formalism.IndefR.DatumF.IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ
          (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ f₁ f₂ h₁ h₂
  exact isThetaFunOF_deltaT σ (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB).1.2.1 h₁ h₂

end GlobalTheory.DblTargetThetaF

end
