import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Exact

open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc

section Minor

variable {N : ℕ}

theorem minorIJ_mul_one_add_single (H : Matrix (Fin N) (Fin N) ℂ) (I C : Finset (Fin N)) {ca cb : Fin N} (hlt : ca < cb)
    (hiff : ca ∈ C ↔ cb ∈ C) (t : ℂ) :
    minorIJ (H * (1 + Matrix.single cb ca t)) I C = minorIJ H I C := by
  have hne : ∀ x, ¬ (x = cb ∧ x = ca) := fun x hx => hlt.ne (hx.2.symm.trans hx.1)
  have hent : ∀ x y, (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) x y =
      (if x = y then 1 else 0) + (if x = cb ∧ y = ca then t else 0) := by
    intro x y
    simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, eq_comm]
  rw [minorIJ_mul_of_support H _ I C]
  · have h1 : minorIJ (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) C C = 1 := by
      rw [minorIJ_eq_det _ C C _ rfl rfl, Matrix.det_of_lowerTriangular]
      · refine Finset.prod_eq_one fun x _ => ?_
        rw [Matrix.submatrix_apply, hent, if_pos rfl, if_neg, add_zero]
        rintro ⟨e1, e2⟩
        exact hne _ ⟨e1, e2⟩
      · intro x y hxy
        have hxy' : x < y := hxy
        have hs := (C.orderEmbOfFin rfl).strictMono hxy'
        rw [Matrix.submatrix_apply, hent, if_neg hs.ne, if_neg, add_zero]
        rintro ⟨e1, e2⟩
        rw [e1, e2] at hs
        exact absurd hs (not_lt.mpr hlt.le)
    rw [h1, mul_one]
  · intro k c hc hk
    have hkc : k ≠ c := by
      rintro rfl
      exact hk hc
    rw [hent, if_neg hkc, if_neg, add_zero]
    rintro ⟨e1, e2⟩
    rw [e1] at hk
    rw [e2] at hc
    exact hk (hiff.mp hc)

theorem mem_stepCols_iff {j : ℕ} {a b ca cb i : Fin N} (hb : (b : ℕ) = a + 1) (h2 : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) (hi : i ≠ a) :
    ca ∈ stepCols N j i ↔ cb ∈ stepCols N j i := by
  have h3 := i.2
  have h4 := b.2
  have h5 := ca.2
  have h6 := cb.2
  have hi' : (i : ℕ) ≠ a := fun e => hi (Fin.ext e)
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold lastCol at hca
  split_ifs at hca ⊢ <;> omega

end Minor

section Low

variable {Ψ : Type} {N j : ℕ}

theorem lowMat_isBlockDiag (c : LowIdx Ψ N j → ℂ) (τ : Ψ) : IsBlockDiag j (lowMat c τ) := by
  intro x y hxy
  unfold lowMat
  rw [dif_neg (fun e => hxy e.2), if_neg]
  rintro rfl
  exact hxy Iff.rfl

theorem lowMat_det (c : LowIdx Ψ N j → ℂ) (τ : Ψ) : (lowMat c τ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · refine Finset.prod_eq_one fun x _ => ?_
    unfold lowMat
    rw [dif_neg (fun e => lt_irrefl _ e.1), if_pos rfl]
  · intro x y hxy
    have hxy' : x < y := hxy
    unfold lowMat
    rw [dif_neg (fun e => lt_asymm hxy' e.1), if_neg hxy'.ne]

theorem analytic_wH {n e : ℕ} (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin e) (τ' : Ψ)
    (r s : Fin N) (S : Set (Fin e → ℂ)) : AnalyticOnNhd ℂ (fun w => wH h ε τ' w r s) S := by
  have hl : ∀ x, AnalyticOnNhd ℂ (fun w => lowMat (wL ε w) τ' x s) S := by
    intro x
    unfold lowMat
    by_cases hh : s < x ∧ ((x : ℕ) < N - j ↔ (s : ℕ) < N - j)
    · simp only [dif_pos hh, wL]
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ)
        (ε (Sum.inr (Sum.inl ⟨(τ', x, s), hh⟩)))).analyticOnNhd _
    · simp only [dif_neg hh]
      exact analyticOnNhd_const
  have : (fun w => wH h ε τ' w r s) = fun w => ∑ x, h τ' r x * lowMat (wL ε w) τ' x s := by
    funext w
    simp only [wH, Matrix.mul_apply]
  rw [this]
  exact Finset.analyticOnNhd_fun_sum _ fun x _ => analyticOnNhd_const.mul (hl x)

end Low

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} {M : FlagModel y Ψ N j} {F : FrameData ι Ψ N M.Ω M.blk}
  {zb : (Σ k, baseIdx ι M.blk k) → ℂ} {H : Ψ → Matrix (Fin N) (Fin N) ℂ}

theorem flagZ_base (k : NonPluckerBlocks M.blk) (m : ι k.1) : flagZ M F zb H ⟨k.1, m⟩ = zb ⟨k, m⟩ := by
  unfold flagZ
  rw [dif_neg (fun e => by obtain ⟨p, hp⟩ := e; exact k.2 p hp)]

theorem flagZ_step {p : Ψ × Fin N} {k : K} (hp : M.blk p = some k) (m : ι k) :
    flagZ M F zb H ⟨k, m⟩ = ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ (H p.1) I (stepCols N j p.2) := by
  have e : ∃ p, M.blk p = some k := ⟨p, hp⟩
  have hc : e.choose = p := M.blk_inj _ _ _ e.choose_spec hp
  unfold flagZ
  simp only [dif_pos e, hc]

variable {k₀ : K} {τ : Ψ} {ca cb : Fin N} {t : ℂ}

theorem fst_sqZ (k : K) (m : ι k) :
    fstPt k₀ (sqZ M F zb H k₀ τ ca cb t) ⟨k, m⟩ = flagZ M F zb H ⟨k, m⟩ := rfl

theorem snd_sqZ_ne {k : K} (hk : k ≠ k₀) (m : ι k) :
    sndPt k₀ (sqZ M F zb H k₀ τ ca cb t) ⟨k, m⟩ = flagZ M F zb H ⟨k, m⟩ := by
  show sqZ M F zb H k₀ τ ca cb t (v₁ k₀ ⟨k, m⟩) = _
  rw [v₁_ne (p := ⟨k, m⟩) hk]
  rfl

theorem snd_sqZ_self (m : ι k₀) :
    sndPt k₀ (sqZ M F zb H k₀ τ ca cb t) ⟨k₀, m⟩ =
      flagZ M F zb (Function.update H τ (H τ * (1 + Matrix.single cb ca t))) ⟨k₀, m⟩ := by
  show sqZ M F zb H k₀ τ ca cb t (v₁ k₀ ⟨k₀, m⟩) = _
  rw [v₁_self]
  rfl

theorem basePart_fst : basePart M.blk (fstPt k₀ (sqZ M F zb H k₀ τ ca cb t)) = zb := by
  funext q
  obtain ⟨k, m⟩ := q
  exact flagZ_base k m

theorem basePart_snd {a : Fin N} (hk₀ : M.blk (τ, a) = some k₀) :
    basePart M.blk (sndPt k₀ (sqZ M F zb H k₀ τ ca cb t)) = zb := by
  funext q
  obtain ⟨k, m⟩ := q
  have hne : k.1 ≠ k₀ := fun e => k.2 (τ, a) (by rw [hk₀, e])
  show sndPt k₀ (sqZ M F zb H k₀ τ ca cb t) ⟨k.1, m⟩ = _
  rw [snd_sqZ_ne hne]
  exact flagZ_base k m

theorem exact_fst (hn : ∀ k, zb ⟨k, F.c k⟩ = 1) (p : Ψ × Fin N) :
    M.ExactAt F p (fstPt k₀ (sqZ M F zb H k₀ τ ca cb t)) (H p.1) := by
  refine ⟨fun k => by rw [basePart_fst]; exact hn k, fun k hk m => ?_⟩
  rw [fst_sqZ, flagZ_step hk, basePart_fst]

theorem exact_snd {a : Fin N} (hk₀ : M.blk (τ, a) = some k₀) (hlt : ca < cb)
    (hiff : ∀ i, i ≠ a → (ca ∈ stepCols N j i ↔ cb ∈ stepCols N j i))
    (hn : ∀ k, zb ⟨k, F.c k⟩ = 1) (τ' : Ψ) (i : Fin N) :
    M.ExactAt F (τ', i) (sndPt k₀ (sqZ M F zb H k₀ τ ca cb t))
      (if τ' = τ then H τ * (1 + Matrix.single cb ca t) else H τ') := by
  refine ⟨fun k => by rw [basePart_snd hk₀]; exact hn k, fun k hk m => ?_⟩
  rw [basePart_snd hk₀]
  by_cases hkk : k = k₀
  · subst hkk
    have hp : (τ', i) = (τ, a) := M.blk_inj _ _ _ hk hk₀
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
    rw [snd_sqZ_self, flagZ_step hk₀, if_pos rfl, Function.update_self]
  · rw [snd_sqZ_ne hkk, flagZ_step hk]
    refine Finset.sum_congr rfl fun I _ => ?_
    by_cases hτ : τ' = τ
    · subst hτ
      have hia : i ≠ a := by
        rintro rfl
        exact hkk (Option.some_injective _ (hk.symm.trans hk₀))
      rw [if_pos rfl, minorIJ_mul_one_add_single _ _ _ hlt (hiff i hia)]
    · rw [if_neg hτ]

end Flag

theorem chart_exact : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → (∀ τ' r s, AnalyticOnNhd ℂ (fun w => wH h ε τ' w r s) (wD ε V)) ∧ ∀ w ∈ wD ε V, (∀ τ', IsBlockDiag j (wH h ε τ' w) ∧ (wH h ε τ' w).det ≠ 0) ∧ baseOf M k₀ (wPhi M F bl h ε k₀ τ ca cb w) = bl (wB ε w) ∧ ∀ τ' i, M.ExactAt F (τ', i) (fstPt k₀ (wPhi M F bl h ε k₀ τ ca cb w)) (wH h ε τ' w) ∧ M.ExactAt F (τ', i) (sndPt k₀ (wPhi M F bl h ε k₀ τ ca cb w)) (if τ' = τ then wH h ε τ w * (1 + Matrix.single cb ca (wT ε w)) else wH h ε τ' w) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hW
  obtain ⟨hb, h2, hk₀, hca, hcb, -, -, hB, -, -, hh⟩ := hW
  have hlt : ca < cb := by
    rw [Fin.lt_def]
    omega
  refine ⟨fun τ' r s => analytic_wH h ε τ' r s _, fun w hw => ⟨fun τ' => ⟨?_, ?_⟩, ?_, fun τ' i => ⟨?_, ?_⟩⟩⟩
  · exact isBlockDiag_mul (hh τ').1 (lowMat_isBlockDiag _ _)
  · rw [wH, Matrix.det_mul, lowMat_det, mul_one]
    exact (hh τ').2
  · exact basePart_fst
  · exact exact_fst (H := fun τ' => wH h ε τ' w) ((hB.2.2.2.2 _ hw).2.1) (τ', i)
  · exact exact_snd (H := fun τ' => wH h ε τ' w) hk₀ hlt
      (fun i hi => mem_stepCols_iff hb h2 hca hcb hi) ((hB.2.2.2.2 _ hw).2.1) τ' i

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Exact
