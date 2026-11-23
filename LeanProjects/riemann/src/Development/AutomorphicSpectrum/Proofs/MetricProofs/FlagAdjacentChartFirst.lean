import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Holo

section Gen

variable {e N : ℕ} {s : Set (Fin e → ℂ)}

theorem analytic_minorIJ (g : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (hg : ∀ a b, AnalyticOnNhd ℂ (fun w => g w a b) s) (I J : Finset (Fin N)) :
    AnalyticOnNhd ℂ (fun w => minorIJ (g w) I J) s := by
  by_cases e' : I.card = J.card
  · have hfun : (fun w => minorIJ (g w) I J) = fun w => ∑ σ : Equiv.Perm (Fin J.card),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, g w (I.orderEmbOfFin e' (σ i)) (J.orderEmbOfFin rfl i) := by
      funext w
      rw [minorIJ, dif_pos e', Matrix.det_apply']
      rfl
    rw [hfun]
    have H := Finset.analyticOnNhd_sum (𝕜 := ℂ) (s := s) (Finset.univ : Finset (Equiv.Perm (Fin J.card)))
      (f := fun σ w => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, g w (I.orderEmbOfFin e' (σ i)) (J.orderEmbOfFin rfl i))
      (fun σ _ => analyticOnNhd_const.mul (by
        have P := Finset.analyticOnNhd_prod (𝕜 := ℂ) (s := s) (Finset.univ : Finset (Fin J.card))
          (f := fun i w => g w (I.orderEmbOfFin e' (σ i)) (J.orderEmbOfFin rfl i)) (fun i _ => hg _ _)
        convert P using 1
        funext w
        rw [Finset.prod_apply]))
    convert H using 1
    funext w
    rw [Finset.sum_apply]
  · have hfun : (fun w => minorIJ (g w) I J) = fun _ => 0 := by
      funext w
      rw [minorIJ, dif_neg e']
    rw [hfun]
    exact analyticOnNhd_const

theorem analytic_mul_entry (g g' : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (hg : ∀ a b, AnalyticOnNhd ℂ (fun w => g w a b) s)
    (hg' : ∀ a b, AnalyticOnNhd ℂ (fun w => g' w a b) s) (a b : Fin N) :
    AnalyticOnNhd ℂ (fun w => (g w * g' w) a b) s := by
  simp only [Matrix.mul_apply]
  have H := Finset.analyticOnNhd_sum (𝕜 := ℂ) (s := s) (Finset.univ : Finset (Fin N))
    (f := fun c w => g w a c * g' w c b) (fun c _ => (hg a c).mul (hg' c b))
  convert H using 1
  funext w
  rw [Finset.sum_apply]

theorem analytic_coord (i : Fin e) : AnalyticOnNhd ℂ (fun w : Fin e → ℂ => w i) s := by
  exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) i).analyticOnNhd s

end Gen

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} {n e : ℕ}

theorem analytic_lowMat (s : Set (Fin e → ℂ)) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin e) (τ' : Ψ) (a b : Fin N) :
    AnalyticOnNhd ℂ (fun w => lowMat (wL ε w) τ' a b) s := by
  by_cases hc : b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)
  · have hfun : (fun w => lowMat (wL ε w) τ' a b) = fun w => w (ε (Sum.inr (Sum.inl ⟨(τ', a, b), hc⟩))) := by
      funext w
      simp only [lowMat]
      rw [dif_pos hc]
      rfl
    rw [hfun]
    exact analytic_coord _
  · have hfun : (fun w => lowMat (wL ε w) τ' a b) = fun _ => if a = b then (1 : ℂ) else 0 := by
      funext w
      simp only [lowMat]
      rw [dif_neg hc]
    rw [hfun]
    exact analyticOnNhd_const

theorem analytic_wH (s : Set (Fin e → ℂ)) (h : Ψ → Matrix (Fin N) (Fin N) ℂ)
    (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin e) (τ' : Ψ) (a b : Fin N) :
    AnalyticOnNhd ℂ (fun w => wH h ε τ' w a b) s := by
  exact analytic_mul_entry (s := s) (fun _ => h τ') (fun w => lowMat (wL ε w) τ') (fun _ _ => analyticOnNhd_const)
    (fun a b => analytic_lowMat s ε τ' a b) a b

theorem analytic_wH_snd (s : Set (Fin e → ℂ)) (h : Ψ → Matrix (Fin N) (Fin N) ℂ)
    (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin e) (τ : Ψ) (ca cb : Fin N) (a b : Fin N) :
    AnalyticOnNhd ℂ (fun w => (wH h ε τ w * (1 + Matrix.single cb ca (wT ε w))) a b) s := by
  refine analytic_mul_entry (s := s) (fun w => wH h ε τ w) (fun w => 1 + Matrix.single cb ca (wT ε w))
    (fun a b => analytic_wH s h ε τ a b) (fun a' b' => ?_) a b
  beta_reduce
  by_cases hc : cb = a' ∧ ca = b'
  · have hfun : (fun w => (1 + Matrix.single cb ca (wT ε w)) a' b') =
        fun w => (1 : Matrix (Fin N) (Fin N) ℂ) a' b' + w (ε (Sum.inr (Sum.inr ()))) := by
      funext w
      rw [Matrix.add_apply, Matrix.single_apply, if_pos hc]
      rfl
    rw [hfun]
    exact analyticOnNhd_const.add (analytic_coord _)
  · have hfun : (fun w => (1 + Matrix.single cb ca (wT ε w)) a' b') =
        fun _ => (1 : Matrix (Fin N) (Fin N) ℂ) a' b' + 0 := by
      funext w
      rw [Matrix.add_apply, Matrix.single_apply, if_neg hc]
    rw [hfun]
    exact analyticOnNhd_const

theorem analytic_flagZ (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {s : Set (Fin e → ℂ)}
    (zb : (Fin e → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (H : (Fin e → ℂ) → Ψ → Matrix (Fin N) (Fin N) ℂ)
    (hzb : ∀ q, AnalyticOnNhd ℂ (fun w => zb w q) s)
    (hval : ∀ q I, AnalyticOnNhd ℂ (fun w => valAt M.x (F.u q I) (zb w)) s)
    (hH : ∀ τ' a b, AnalyticOnNhd ℂ (fun w => H w τ' a b) s) (q : Σ k, ι k) :
    AnalyticOnNhd ℂ (fun w => flagZ M F (zb w) (H w) q) s := by
  by_cases e' : ∃ p, M.blk p = some q.1
  · have hfun : (fun w => flagZ M F (zb w) (H w) q) = fun w =>
        ∑ I, valAt M.x (F.u q I) (zb w) * minorIJ (H w e'.choose.1) I (stepCols N j e'.choose.2) := by
      funext w
      simp only [flagZ]
      rw [dif_pos e']
    rw [hfun]
    have S := Finset.analyticOnNhd_sum (𝕜 := ℂ) (s := s) Finset.univ
      (f := fun I w => valAt M.x (F.u q I) (zb w) * minorIJ (H w e'.choose.1) I (stepCols N j e'.choose.2))
      (fun I _ => (hval q I).mul (analytic_minorIJ (fun w => H w e'.choose.1) (fun a b => hH _ a b) I _))
    convert S using 1
    funext w
    rw [Finset.sum_apply]
  · have hfun : (fun w => flagZ M F (zb w) (H w) q) = fun w => zb w ⟨⟨q.1, fun p hp => e' ⟨p, hp⟩⟩, q.2⟩ := by
      funext w
      simp only [flagZ]
      rw [dif_neg e']
    rw [hfun]
    exact hzb _

theorem analytic_wB {Λ : Type} (ε : Fin n ⊕ Λ ⊕ Unit ≃ Fin e) (V : Set (Fin n → ℂ)) :
    AnalyticOnNhd ℂ (wB ε) (wD ε V) := by
  exact AnalyticOnNhd.pi (fun i => analytic_coord (s := wD ε V) (ε (Sum.inl i)))

end Flag

theorem wPhi_holo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ p, AnalyticOnNhd ℂ (fun w => wPhi M F bl h ε k₀ τ ca cb w p) (wD ε V) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hctx p
  obtain ⟨-, -, -, -, -, -, -, ⟨-, -, hbl, hvl, -⟩, -, -, -⟩ := hctx
  have hB : AnalyticOnNhd ℂ (wB ε) (wD ε V) := analytic_wB ε V
  have hmaps : Set.MapsTo (wB ε) (wD ε V) V := fun w hw => hw
  have hzb : ∀ q, AnalyticOnNhd ℂ (fun w => bl (wB ε w) q) (wD ε V) := fun q => (hbl q).comp hB hmaps
  have hval : ∀ q I, AnalyticOnNhd ℂ (fun w => valAt M.x (F.u q I) (bl (wB ε w))) (wD ε V) :=
    fun q I => (hvl q I).comp hB hmaps
  obtain ⟨o, m⟩ := p
  cases o with
  | some k =>
    exact analytic_flagZ M F (fun w => bl (wB ε w)) (fun w τ' => wH h ε τ' w) hzb hval
      (fun τ' a' b' => analytic_wH _ h ε τ' a' b') ⟨k, m⟩
  | none =>
    refine analytic_flagZ M F (fun w => bl (wB ε w))
      (fun w => Function.update (fun τ' => wH h ε τ' w) τ (wH h ε τ w * (1 + Matrix.single cb ca (wT ε w))))
      hzb hval ?_ ⟨k₀, m⟩
    intro τ' a' b'
    by_cases hτ : τ' = τ
    · have hfun : (fun w => Function.update (fun τ'' => wH h ε τ'' w) τ
          (wH h ε τ w * (1 + Matrix.single cb ca (wT ε w))) τ' a' b') =
          fun w => (wH h ε τ w * (1 + Matrix.single cb ca (wT ε w))) a' b' := by
        funext w
        rw [Function.update_apply, if_pos hτ]
      rw [hfun]
      exact analytic_wH_snd _ h ε τ ca cb a' b'
    · have hfun : (fun w => Function.update (fun τ'' => wH h ε τ'' w) τ
          (wH h ε τ w * (1 + Matrix.single cb ca (wT ε w))) τ' a' b') = fun w => wH h ε τ' w a' b' := by
        funext w
        rw [Function.update_apply, if_neg hτ]
      rw [hfun]
      exact analytic_wH _ h ε τ' a' b'

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Holo
