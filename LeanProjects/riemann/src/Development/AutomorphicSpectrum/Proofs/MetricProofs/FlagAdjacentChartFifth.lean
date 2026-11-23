import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameMinorValueFormulaStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockLUFactorizationStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LUTwistRefactorizationStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartTenthStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameLUMinorValueStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedFrameValueFormulaStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Onto

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ z ∈ wO M Rb τ a k₀ ca cb F kb V r h, wRho M Rb τ k₀ ca cb F kb r h ε z ∈ wD ε V ∧ SameOrbit (wPhi M F bl h ε k₀ τ ca cb (wRho M Rb τ k₀ ca cb F kb r h ε z)) z := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hctx z hz
  have hctx' := hctx
  obtain ⟨hb, hab, hk, hca, hcb, hy, hF, hBC, hr, hrc, hh⟩ := hctx'
  obtain ⟨hmem, hsrc, hV, hden, hden2⟩ := hz
  obtain ⟨hzb, hG, horb, h', t', hh', Hf, Hs⟩ := GlobalTheory.T.flag_adjacent_chart_tenth K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h hctx z
    ⟨hmem, hsrc, hV, hden, hden2⟩
  have hS := Pts.same_summand hb hab hca hcb
  have hj := M.j_le
  set zb := baseOf M k₀ z with hzbdef
  set w := wRho M Rb τ k₀ ca cb F kb r h ε z with hw
  have hwB : wB ε w = Rb.A.chart kb (r zb) := by
    funext i
    simp [wB, hw, wRho, zb]
  have hwL : ∀ q, wL ε w q = lowRead M F zb h (fstPt k₀ z) q.1.1 q.1.2.1 q.1.2.2 := fun q => by
    simp [wL, hw, wRho, zb]
  have hwT : wT ε w = lowRead M F zb h (sndPt k₀ z) τ cb ca - lowRead M F zb h (fstPt k₀ z) τ cb ca := by
    simp [wT, hw, wRho, zb]
  refine ⟨show wB ε w ∈ V by rw [hwB]; exact hV, ?_⟩
  have hdu : ∀ τ', IsUnit (h τ').det := fun τ' => (hh τ').2.isUnit
  let G : Ψ → Matrix (Fin N) (Fin N) ℂ := fun τ' => (h τ')⁻¹ * h' τ'
  have hGb : ∀ τ', IsBlockDiag j (G τ') := fun τ' => ((hh τ').1.inv (hdu τ')).mul (hh' τ').1
  have hinvd : ∀ τ', ((h τ')⁻¹).det ≠ 0 := fun τ' h0 => by
    have h1 := Matrix.det_nonsing_inv_mul_det (h τ') (hdu τ')
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hGd : ∀ τ', (G τ').det ≠ 0 := fun τ' => by
    show ((h τ')⁻¹ * h' τ').det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (hinvd τ') (hh' τ').2
  have hmin : ∀ τ' i, IsProperStep N j i → minorIJ (G τ') (stepCols N j i) (stepCols N j i) ≠ 0 := by
    intro τ' i hi h0
    obtain ⟨k, hp⟩ : ∃ k, M.blk (τ', i) = some k := Option.ne_none_iff_exists'.1 fun e => (M.blk_none _).1 e hi
    obtain ⟨α, hα, hz₁⟩ := Hf (τ', i) k hp
    refine hden (τ', i) k hp ?_
    rw [GlobalTheory.T.frame_minor_value_formula K ι Φ y Ψ N j M F zb (τ', i) k (h' τ') (h τ')⁻¹ (fstPt k₀ z) α _ hF hzb hG hp (hh' τ').1 hz₁]
    show α * minorIJ (G τ') _ _ = 0
    rw [h0, mul_zero]
  choose L U hLb hLu hUb hUt hUd hLU using fun τ' => GlobalTheory.T.block_LU_factorization N j (G τ') hj (hGb τ') (hGd τ') (hmin τ')
  have hhL : ∀ τ', h τ' * (L τ' * U τ') = h' τ' := fun τ' => by
    rw [← hLU]
    exact Matrix.mul_nonsing_inv_cancel_left _ _ (hdu τ')
  have hlow : ∀ τ' (a' b' : Fin N), b' < a' → ((a' : ℕ) < N - j ↔ (b' : ℕ) < N - j) →
      lowRead M F zb h (fstPt k₀ z) τ' a' b' = L τ' a' b' := fun τ' a' b' e e' =>
    GlobalTheory.T.frame_LU_minor_value K ι Φ y Ψ N j M F zb h τ' a' b' (fstPt k₀ z) (h' τ') (L τ') (U τ') hF hzb hG (hh' τ').1 (hLU τ')
      (hLb τ') (hLu τ') (hUb τ') (hUt τ') (fun c _ => hUd τ' c) e e' (fun k hp => Hf (τ', stepOf N j b') k hp)
  have hlm : ∀ τ', lowMat (wL ε w) τ' = L τ' := fun τ' => by
    ext a' b'
    unfold lowMat
    split_ifs with e e'
    · rw [hwL]
      exact hlow τ' a' b' e.1 e.2
    · rw [e', (hLu τ').1]
    · rcases lt_or_gt_of_ne e' with e' | e'
      · exact ((hLu τ').2 _ _ e').symm
      · exact ((hLb τ') _ _ fun e'' => e ⟨e', e''⟩).symm
  obtain ⟨α₂, hα₂, hz₂⟩ := Hs
  have hne2 : minorIJ (L τ * U τ * (1 + Matrix.single cb ca t')) (stepCols N j a) (stepCols N j a) ≠ 0 := by
    intro h0
    refine hden2 ?_
    rw [GlobalTheory.T.frame_minor_value_formula K ι Φ y Ψ N j M F zb (τ, a) k₀ (h' τ * (1 + Matrix.single cb ca t')) (h τ)⁻¹ (sndPt k₀ z) α₂ _ hF hzb hG hk
      ((hh' τ).1.mul (Pts.transv_block hS t')) hz₂, ← Matrix.mul_assoc]
    show α₂ * minorIJ (G τ * _) _ _ = 0
    rw [hLU, h0, mul_zero]
  obtain ⟨t, Vm, hVb, hVt, hVd, hUV⟩ := GlobalTheory.T.LU_twist_refactorization N j a ca cb (L τ) (U τ) t' hj hca hcb hS (hLb τ) (hLu τ) (hUb τ) (hUt τ)
    (hUd τ) hne2
  have hlt : ca < cb := by rw [Fin.lt_def]; omega
  have hstep : stepOf N j ca = a := by
    have := a.2
    apply Fin.ext
    simp only [stepOf, hca, lastCol]
    split_ifs <;> omega
  have hcc : ∀ c, c ∈ stepCols N j (stepOf N j ca) → Vm c c ≠ 0 := fun c hc => hVd c (hstep ▸ hc)
  have hLe : ∀ r c, (L τ * (1 + Matrix.single cb ca t)) r c = L τ r c + if c = ca then L τ r cb * t else 0 := by
    intro r c
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
    congr 1
    by_cases e : c = ca
    · subst e
      simp [Matrix.mul_single_apply_same]
    · rw [if_neg e, Matrix.mul_single_apply_of_ne _ _ _ _ _ e]
  have hL2 : IsLowerUni (L τ * (1 + Matrix.single cb ca t)) := by
    refine ⟨fun r => ?_, fun r c e => ?_⟩
    · rw [hLe, (hLu τ).1]
      split_ifs with e
      · rw [e, (hLu τ).2 _ _ hlt, zero_mul, add_zero]
      · rw [add_zero]
    · rw [hLe, (hLu τ).2 _ _ e]
      split_ifs with e'
      · rw [(hLu τ).2 r cb (e.trans (e' ▸ hlt)), zero_mul, add_zero]
      · rw [add_zero]
  have hL2c : (L τ * (1 + Matrix.single cb ca t)) cb ca = L τ cb ca + t := by
    rw [hLe, if_pos rfl, (hLu τ).1, one_mul]
  have hsnd : lowRead M F zb h (sndPt k₀ z) τ cb ca = L τ cb ca + t := by
    rw [← hL2c]
    refine GlobalTheory.T.frame_LU_minor_value K ι Φ y Ψ N j M F zb h τ cb ca (sndPt k₀ z) (h' τ * (1 + Matrix.single cb ca t')) _ Vm hF hzb hG
      ((hh' τ).1.mul (Pts.transv_block hS t')) ?_ ((hLb τ).mul (Pts.transv_block hS t)) hL2 hVb hVt hcc hlt hS.symm ?_
    · rw [← Matrix.mul_assoc]
      show G τ * _ = _
      rw [hLU, Matrix.mul_assoc, hUV, Matrix.mul_assoc]
    · intro k hp
      rw [hstep, hk] at hp
      obtain rfl := Option.some.inj hp
      exact ⟨α₂, hα₂, by rw [hstep]; exact hz₂⟩
  have hwt : wT ε w = t := by
    rw [hwT, hsnd, hlow τ cb ca hlt hS.symm]
    ring
  have hHU : ∀ τ', (fun τ' => wH h ε τ' w) τ' * U τ' = h' τ' := fun τ' => by
    show h τ' * lowMat (wL ε w) τ' * U τ' = _
    rw [hlm, Matrix.mul_assoc, hhL]
  show SameOrbit (sqZ M F (bl (wB ε w)) (fun τ' => wH h ε τ' w) k₀ τ ca cb (wT ε w)) z
  rw [hwB, hwt]
  refine GlobalTheory.T.twisted_frame_value_formula K ι Φ y Ψ N j M τ a k₀ ca cb F _ z _ U Vm t hk hzb hG horb
    (fun τ' => ⟨hUb τ', hUt τ', hUd τ'⟩) hVb hVt hVd (fun p k hp => ?_) ⟨α₂, hα₂, fun m => ?_⟩
  · rw [hHU]
    exact Hf p k hp
  · have e : (fun τ' => wH h ε τ' w) τ * (1 + Matrix.single cb ca t) * Vm = h' τ * (1 + Matrix.single cb ca t') := by
      rw [← hHU τ, Matrix.mul_assoc, Matrix.mul_assoc, hUV]
    rw [e]
    exact hz₂ m

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Onto
