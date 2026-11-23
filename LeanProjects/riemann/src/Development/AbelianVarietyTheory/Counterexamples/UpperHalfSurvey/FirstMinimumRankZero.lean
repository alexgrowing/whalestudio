import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowDomainCriterionHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsIntegralCc

namespace GlobalTheory.FlagFlowCheck

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem c_pos (τ : X.Ψ) : 0 < X.c τ := by
  have h : τ.1 X.ξ0 ≠ 0 := (map_ne_zero_iff τ.1 τ.1.injective).2 X.ξ0_ne
  unfold Data.c
  positivity

theorem tt_pos {x : Frame X.Ψ r} (hx : x ∈ X.dom) {ξ : Fin r → E} (hξ : ξ ≠ 0) (τ : X.Ψ) :
    0 < X.tt ξ x τ := by
  have hv : Data.emb τ.1 ξ ≠ 0 := by
    intro h
    apply hξ
    funext a
    exact (map_eq_zero_iff τ.1 τ.1.injective).1 (congrFun h a)
  have := X.maj_pos hx τ hv
  have := c_pos X τ
  unfold Data.tt
  positivity

theorem scaled_maj_flow {x : Frame X.Ψ r} (hx : x ∈ X.dom) {ξ : Fin r → E} (hξ : X.IsIso ξ)
    (s : X.Ψ → ℂ) (hs : X.flow ξ s x ∈ X.dom) (τ : X.Ψ) :
    X.c τ * X.maj (X.flow ξ s x) τ (Data.emb τ.1 ξ) = 1 / (X.tt ξ x τ + (s τ).im) := by
  have he : X.IsIsoV (fun τ => Data.emb τ.1 ξ) := by
    intro σ
    refine ⟨?_, fun h => hξ.2.2 ?_⟩
    · have h0 := congrArg σ.1 hξ.2.1
      simpa [herm, hermC, Data.emb, emb_cc] using h0
    · funext a
      exact (map_eq_zero_iff σ.1 σ.1.injective).1 (congrFun h a)
  have h := (flowDomainCriterion_holds r X _ he x hx s).2 hs τ
  have h' : X.tt ξ (X.flow ξ s x) τ = X.tt ξ x τ + (s τ).im := h
  rw [← h']
  simp [Data.tt]

theorem flowMat_eq_transv (ξ : Fin r → E) (τ : X.Ψ) (s : E) :
    X.flowMat ξ τ (τ.1 s) = (transvMat X.Gm ξ (s * X.κ0)).map τ.1 := by
  have hcc : cc X.κ0 = -X.κ0 := by
    rcases X.κ0_xi with h | h
    · rw [h, cc_mul, X.ξ0_im]; have : cc (2 : E) = 2 := map_ofNat _ 2
      rw [this]; ring
    · have e : -(2 * X.ξ0) = 0 - 2 * X.ξ0 := by ring
      rw [h, e, cc_sub, cc_zero, cc_mul, X.ξ0_im]; have : cc (2 : E) = 2 := map_ofNat _ 2
      rw [this]; ring
  have hre : (τ.1 X.κ0).re = 0 := by
    have h1 : conj (τ.1 X.κ0) = -(τ.1 X.κ0) := by rw [← emb_cc, hcc, map_neg]
    have h2 := congrArg Complex.re h1
    simp only [Complex.conj_re, Complex.neg_re] at h2
    linarith
  have hn : ‖τ.1 X.κ0‖ = X.c τ := by
    unfold Data.c
    rcases X.κ0_xi with h | h <;> simp [h, map_ofNat]
  have hk : τ.1 X.κ0 = -(I * X.c τ) := by
    have h3 : ‖τ.1 X.κ0‖ = |(τ.1 X.κ0).im| := (Complex.abs_im_eq_norm.2 hre).symm
    rw [abs_of_neg (X.κ0_sign τ)] at h3
    apply Complex.ext <;> simp [hre]
    linarith
  ext a b
  have h1 : τ.1 (if a = b then 1 else 0) = if a = b then 1 else 0 := by split_ifs <;> simp
  simp only [Data.flowMat, transvMat, Matrix.of_apply, Matrix.map_apply, map_add, map_mul, map_sum,
    h1, hk, emb_cc]
  ring

theorem first_minimum_rank_zero (Y : Data E 0) (x : Frame Y.Ψ 0) : Y.la1 x = 0 := by
  have : {t | ∃ v ∈ Y.Λ, v ≠ 0 ∧ t = ∑ τ, Y.c τ * Y.maj x τ (Data.emb τ.1 v)} = (∅ : Set ℝ) := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨v, -, hv, -⟩
    exact hv (Subsingleton.elim _ _)
  unfold Data.la1 Data.firstMinimumSq
  rw [this]
  simp

end GlobalTheory.FlagFlowCheck
