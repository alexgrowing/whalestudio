import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.StatementsMeanLogPlus
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

namespace FirstMinPos

section Lemmas

variable {Em : Type} [Field Em] [NumberField Em] [IsCMField Em] {Ψ : Type} [Fintype Ψ] {N j : ℕ}

theorem exists_cmType_one_le_norm (A : HermDatum Em Ψ N j) {x : Em} (hx : IsIntegral ℤ x) (hx0 : x ≠ 0) :
    ∃ τ, 1 ≤ ‖A.emb τ x‖ := by
  obtain ⟨σ, hσ⟩ := exists_conjugate_one_le_norm (K := Em) (α := ⟨x, hx⟩)
    (fun h => hx0 (congrArg (fun y : 𝓞 Em => (y : Em)) h))
  have hσ' : 1 ≤ ‖σ x‖ := hσ
  by_cases h : ∃ τ, A.emb τ = σ
  · obtain ⟨τ, rfl⟩ := h
    exact ⟨τ, hσ'⟩
  · obtain ⟨τ, hτ⟩ := not_not.mp (mt (A.cmType σ).mpr h)
    refine ⟨τ, ?_⟩
    rw [hτ, RingHom.comp_apply, Complex.norm_conj]
    exact hσ'

theorem exists_common_denom (A : HermDatum Em Ψ N j) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ v ∈ A.L, ∀ b, IsIntegral ℤ (d • v b) := by
  classical
  obtain ⟨S, hS⟩ := A.fg
  obtain ⟨d, hd0, hd⟩ := exists_integral_multiples ℤ ℚ (S.biUnion fun s => Finset.univ.image s)
  refine ⟨d, hd0, fun v hv => ?_⟩
  have key : ∀ w ∈ Submodule.span ℤ (S : Set (Fin N → Em)), ∀ b, IsIntegral ℤ (d • w b) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      intro b
      exact hd _ (Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image_of_mem _ (Finset.mem_univ b)⟩)
    | zero =>
      intro b
      simpa using (isIntegral_zero : IsIntegral ℤ (0 : Em))
    | add x y _ _ hx hy =>
      intro b
      simp only [Pi.add_apply, smul_add]
      exact (hx b).add (hy b)
    | smul a x _ hx =>
      intro b
      simp only [Pi.smul_apply]
      rw [smul_comm, zsmul_eq_mul]
      have hi := (isIntegral_algebraMap (R := ℤ) (A := Em) (x := a)).mul (hx b)
      rwa [algebraMap_int_eq, eq_intCast] at hi
  exact key v (by rw [hS]; exact hv)

theorem isUnit_det_of_eq_signMat {P A : Matrix (Fin N) (Fin N) ℂ} (h : Pᴴ * A * P = signMat N j) :
    IsUnit P.det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have hs : (signMat N j).det ≠ 0 := by
    rw [signMat, Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    intro a _
    split_ifs <;> norm_num
  apply hs
  rw [← h, Matrix.det_mul, h0, mul_zero]

theorem norm_sq_le_of_isUnit {P : Matrix (Fin N) (Fin N) ℂ} (hP : IsUnit P.det) (w : Fin N → ℂ) (b : Fin N) :
    ‖w b‖ ^ 2 ≤ (∑ a, ‖P b a‖ ^ 2) * ∑ a, ‖(P⁻¹ *ᵥ w) a‖ ^ 2 := by
  have hw : P *ᵥ (P⁻¹ *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hP, Matrix.one_mulVec]
  have h1 : ‖w b‖ ≤ ∑ a, ‖P b a‖ * ‖(P⁻¹ *ᵥ w) a‖ := by
    calc ‖w b‖ = ‖(P *ᵥ (P⁻¹ *ᵥ w)) b‖ := by rw [hw]
      _ = ‖∑ a, P b a * (P⁻¹ *ᵥ w) a‖ := by simp [Matrix.mulVec, dotProduct]
      _ ≤ ∑ a, ‖P b a * (P⁻¹ *ᵥ w) a‖ := norm_sum_le _ _
      _ = ∑ a, ‖P b a‖ * ‖(P⁻¹ *ᵥ w) a‖ := by simp
  calc ‖w b‖ ^ 2 ≤ (∑ a, ‖P b a‖ * ‖(P⁻¹ *ᵥ w) a‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

end Lemmas

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em]

theorem proof (D : FullerData II Ψ K ι Ω E Em) : FirstMinPos.Statement D := by
  intro z hz
  classical
  obtain ⟨d, hd0, hd⟩ := exists_common_denom D.herm
  have hP : ∀ τ, IsUnit (D.per z τ).det := fun τ => isUnit_det_of_eq_signMat (D.per_witt z hz τ)
  have hdR : (0 : ℝ) < (d : ℝ) ^ 2 := by
    have : (d : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hd0
    positivity
  set g : Ψ → ℝ := fun τ => 2 * ‖D.herm.emb τ D.herm.ξ‖ /
    ((d : ℝ) ^ 2 * (∑ b, ∑ a, ‖D.per z τ b a‖ ^ 2 + 1)) with hg
  have hgpos : ∀ τ, 0 < g τ := by
    intro τ
    have : D.herm.emb τ D.herm.ξ ≠ 0 := (map_ne_zero _).mpr D.herm.ξ_ne
    have : 0 < ‖D.herm.emb τ D.herm.ξ‖ := norm_pos_iff.mpr this
    positivity
  have hbound : ∀ v ∈ D.herm.L, v ≠ 0 → ∃ τ, g τ ≤ D.hodgeNormSq z v := by
    intro v hv hv0
    obtain ⟨b, hb⟩ : ∃ b, v b ≠ 0 := by
      by_contra! h
      exact hv0 (funext h)
    obtain ⟨τ, hτ⟩ := exists_cmType_one_le_norm D.herm (hd v hv b) (smul_ne_zero hd0 hb)
    refine ⟨τ, ?_⟩
    set w : Fin D.N → ℂ := fun b => D.herm.emb τ (v b) with hwdef
    have hw : 1 ≤ (d : ℝ) ^ 2 * ‖w b‖ ^ 2 := by
      have he : ‖D.herm.emb τ (d • v b)‖ = |(d : ℝ)| * ‖w b‖ := by
        simp [w, zsmul_eq_mul]
      rw [he] at hτ
      have := pow_le_pow_left₀ zero_le_one hτ 2
      rw [mul_pow, sq_abs, one_pow] at this
      exact this
    set Kτ : ℝ := ∑ b, ∑ a, ‖D.per z τ b a‖ ^ 2 + 1 with hK
    have hrow : ∑ a, ‖D.per z τ b a‖ ^ 2 ≤ Kτ := by
      have h := Finset.single_le_sum (s := Finset.univ) (f := fun b' => ∑ a, ‖D.per z τ b' a‖ ^ 2)
        (fun b' _ => Finset.sum_nonneg fun a _ => sq_nonneg ‖D.per z τ b' a‖) (Finset.mem_univ b)
      exact le_add_of_le_of_nonneg h zero_le_one
    set s : ℝ := ∑ a, ‖((D.per z τ)⁻¹ *ᵥ w) a‖ ^ 2 with hs
    have hs0 : 0 ≤ s := by positivity
    have hc := norm_sq_le_of_isUnit (hP τ) w b
    have h1 : 1 ≤ (d : ℝ) ^ 2 * Kτ * s := by
      calc (1 : ℝ) ≤ (d : ℝ) ^ 2 * ‖w b‖ ^ 2 := hw
        _ ≤ (d : ℝ) ^ 2 * ((∑ a, ‖D.per z τ b a‖ ^ 2) * s) := by gcongr
        _ ≤ (d : ℝ) ^ 2 * (Kτ * s) := by gcongr
        _ = (d : ℝ) ^ 2 * Kτ * s := by ring
    have hterm : 2 * ‖D.herm.emb τ D.herm.ξ‖ * s ≤ D.hodgeNormSq z v := by
      unfold FullerData.hodgeNormSq
      exact Finset.single_le_sum (f := fun τ' => 2 * ‖D.herm.emb τ' D.herm.ξ‖ *
          ∑ a, ‖((D.per z τ')⁻¹ *ᵥ fun b => D.herm.emb τ' (v b)) a‖ ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ τ)
    have hKτ : 0 < Kτ := by
      have : 0 ≤ ∑ b', ∑ a, ‖D.per z τ b' a‖ ^ 2 :=
        Finset.sum_nonneg fun b' _ => Finset.sum_nonneg fun a _ => sq_nonneg ‖D.per z τ b' a‖
      linarith
    have hKpos : 0 < (d : ℝ) ^ 2 * Kτ := mul_pos hdR hKτ
    have hc0 : 0 ≤ 2 * ‖D.herm.emb τ D.herm.ξ‖ := mul_nonneg zero_le_two (norm_nonneg _)
    have hmul := mul_le_mul_of_nonneg_left h1 hc0
    calc g τ = 2 * ‖D.herm.emb τ D.herm.ξ‖ / ((d : ℝ) ^ 2 * Kτ) := rfl
      _ ≤ 2 * ‖D.herm.emb τ D.herm.ξ‖ * s := by
        rw [div_le_iff₀ hKpos]
        nlinarith
      _ ≤ _ := hterm
  obtain ⟨v0, hv0L, hv0⟩ : ∃ v ∈ D.herm.L, v ≠ 0 := by
    by_contra! h
    have h2 : 2 ≤ D.N := D.two_le_N
    have : Nonempty (Fin D.N) := ⟨⟨0, by omega⟩⟩
    have hbot : Submodule.span ℚ (D.herm.L : Set (Fin D.N → Em)) = ⊥ :=
      Submodule.span_eq_bot.mpr fun x hx => h x hx
    rw [D.herm.span] at hbot
    exact top_ne_bot hbot
  obtain ⟨τ0, -⟩ := hbound v0 hv0L hv0
  set δ : ℝ := Finset.univ.inf' ⟨τ0, Finset.mem_univ τ0⟩ g with hδ
  have hδpos : 0 < δ := (Finset.lt_inf'_iff _).mpr fun τ _ => hgpos τ
  have hlow : Real.sqrt δ ≤ D.lam1 z := by
    unfold FullerData.lam1
    refine le_csInf ⟨_, v0, hv0L, hv0, rfl⟩ ?_
    rintro x ⟨v, hv, hvne, rfl⟩
    obtain ⟨τ, hτ⟩ := hbound v hv hvne
    exact Real.sqrt_le_sqrt ((Finset.inf'_le _ (Finset.mem_univ τ)).trans hτ)
  exact (Real.sqrt_pos.mpr hδpos).trans_le hlow

end FirstMinPos

end GroundTheory.Heights₂.Heights.NineStatements
