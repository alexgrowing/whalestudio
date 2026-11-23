import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsConstantShift
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsSemipositiveRelConstShift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDerived
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 Filter Topology MeasureTheory

noncomputable section

namespace ConstantShift

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [∀ k, Fintype (ι k)] in

theorem sheetDensity_add_const (P : Ideal (MRing ι)) {e : ℕ} {φ φ' : Fin e → ((Σ k, ι k) → ℂ) → ℝ}
    (h : ∀ j, ∃ c : ℝ, ∀ z ∈ mcPts P, φ' j z = φ j z + c)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ φ' g y w = sheetDensity P Ψ φ g y w := by
  unfold sheetDensity
  split_ifs with hγ
  · congr 1
    have hH : ∀ k, cxHessian (fun y' => φ' k (hγ.choose y')) y =
        cxHessian (fun y' => φ k (hγ.choose y')) y := by
      intro k
      obtain ⟨c, hc⟩ := h k
      have h1 : (fun y' => φ' k (hγ.choose y')) =ᶠ[𝓝 y] fun y' => φ k (hγ.choose y') + c := by
        filter_upwards [hγ.choose_spec.2] with y' hy'
        exact hc _ hy'.2.1
      have h2 : fderiv ℝ (fun y' => φ' k (hγ.choose y')) =ᶠ[𝓝 y]
          fderiv ℝ (fun y' => φ k (hγ.choose y')) := by
        filter_upwards [h1.eventuallyEq_nhds] with x hx
        rw [hx.fderiv_eq, fderiv_add_const]
      unfold cxHessian
      rw [h2.fderiv_eq]
    simp only [maDensity, hH]
  · rfl

omit [∀ k, Fintype (ι k)] in

theorem ptsIntegral_add_const (P : Ideal (MRing ι)) {e : ℕ} {φ φ' : Fin e → ((Σ k, ι k) → ℂ) → ℝ}
    (h : ∀ j, ∃ c : ℝ, ∀ z ∈ mcPts P, φ' j z = φ j z + c) (g : ((Σ k, ι k) → ℂ) → ℝ) :
    ptsIntegral P φ' g = ptsIntegral P φ g := by
  unfold ptsIntegral
  split_ifs
  · simp only [ptsIntegralAt, sheetDensity_add_const P h]
  · rfl

omit [∀ k, Fintype (ι k)] in

theorem ptsIntegral_const (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (r : ℝ) :
    ptsIntegral P φ (fun _ => r) = r * ptsIntegral P φ (fun _ => 1) := by
  have hs : ∀ Ψ y w, sheetDensity P Ψ φ (fun _ => r) y w = r * sheetDensity P Ψ φ (fun _ => 1) y w := by
    intro Ψ y w
    unfold sheetDensity
    split_ifs <;> simp
  unfold ptsIntegral
  split_ifs
  · simp only [ptsIntegralAt, hs]
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [mul_finsum_mem]
  · simp

theorem proof : ConstantShift.Statement := by
  intro K _ ι _ I P D A η hI hP hA
  have hS : IsSmoothHerm (HermLine.constShift A η) := isSmoothHerm_constShift hA η
  set g := geomDeg P A D with hg
  let L : ℕ → Fin (D + 1) → HermLine ι := fun n i =>
    if (i : ℕ) < n then HermLine.constShift A η else A
  have hLs : ∀ n i, IsSmoothHerm (L n i) := by
    intro n i
    dsimp only [L]
    split_ifs
    exacts [hS, hA]
  have hLpot : ∀ n i, ∃ c : ℝ, ∀ z ∈ mcPts P, Real.log ((L n i).h z) = Real.log (A.h z) + c := by
    intro n i
    dsimp only [L]
    split_ifs
    · refine ⟨-η, fun z hz => ?_⟩
      rw [constShift_h, Real.log_mul (A.pos z hz.1).ne' (Real.exp_pos _).ne', Real.log_exp]
    · exact ⟨0, fun z _ => by rw [add_zero]⟩
  have step : ∀ n, n < D + 1 → I P (D + 1) (L (n + 1)) = I P (D + 1) (L n) - η * g := by
    intro n hn
    set j : Fin (D + 1) := ⟨n, hn⟩ with hj
    set σ : Equiv.Perm (Fin (D + 1)) := Equiv.swap j (Fin.last D) with hσ
    set M : Fin D → HermLine ι := Fin.init (L n ∘ σ) with hMdef
    have hσl : σ (Fin.last D) = j := Equiv.swap_apply_right _ _
    have hne : ∀ i : Fin D, σ (Fin.castSucc i) ≠ j := by
      intro i h'
      rw [← hσl] at h'
      exact (Fin.castSucc_lt_last i).ne (σ.injective h')
    have hM : Fin.init (L (n + 1) ∘ σ) = M := by
      funext i
      have hv : ((σ (Fin.castSucc i) : Fin (D + 1)) : ℕ) ≠ n := fun h' => hne i (Fin.ext h')
      have hiff : ((σ (Fin.castSucc i) : Fin (D + 1)) : ℕ) < n + 1 ↔
          ((σ (Fin.castSucc i) : Fin (D + 1)) : ℕ) < n := by omega
      simp only [hMdef, Fin.init, Function.comp, L, hiff]
    have e0 : L n ∘ σ = Fin.snoc M A := by
      have h0 := Fin.snoc_init_self (q := L n ∘ σ)
      have hl : (L n ∘ σ) (Fin.last D) = A := by
        simp only [Function.comp, hσl, hj, L, lt_irrefl, if_false]
      rw [hl] at h0
      exact h0.symm
    have e1 : L (n + 1) ∘ σ = Fin.snoc M (HermLine.constShift A η) := by
      have h0 := Fin.snoc_init_self (q := L (n + 1) ∘ σ)
      have hl : (L (n + 1) ∘ σ) (Fin.last D) = HermLine.constShift A η := by
        simp only [Function.comp, hσl, hj, L, lt_add_one, if_true]
      rw [hl, hM] at h0
      exact h0.symm
    have hMs : ∀ i, IsSmoothHerm (M i) := fun i => hLs n _
    have hmc : I P (D + 1) (Fin.snoc M (HermLine.constShift A η)) =
        I P (D + 1) (Fin.snoc M A) - ptsIntegral P (pot M) (fun _ => η) :=
      metricChange K ι I hI P D M A (fun _ => η) (fun _ _ _ => rfl) hP hMs hA contDiffOn_const
    have hint : ptsIntegral P (pot M) (fun _ => η) = η * g := by
      rw [ptsIntegral_const, hg, geomDeg]
      congr 1
      exact ptsIntegral_add_const P (fun i => hLpot n _) _
    rw [← hI.1 P (D + 1) (L (n + 1)) σ hP (hLs (n + 1)), ← hI.1 P (D + 1) (L n) σ hP (hLs n), e0, e1,
      hmc, hint]
  have hall : ∀ n, n ≤ D + 1 → I P (D + 1) (L n) = I P (D + 1) (L 0) - n * η * g := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      rw [step n (by omega), ih (by omega)]
      push_cast
      ring
  have hL0 : L 0 = fun _ => A := by
    funext i
    simp [L]
  have hLD : L (D + 1) = fun _ => HermLine.constShift A η := by
    funext i
    simp [L, i.isLt]
  have := hall (D + 1) le_rfl
  rw [hL0, hLD] at this
  rw [this]
  push_cast
  ring

end ConstantShift

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
