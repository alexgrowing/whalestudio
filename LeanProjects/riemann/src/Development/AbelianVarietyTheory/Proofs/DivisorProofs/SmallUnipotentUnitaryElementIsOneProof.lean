import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import ReciprocityTheory.SemistableReduction.ShareBallA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ModeHalfStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MajLactRmul
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.TraceMemPrimeOfPowMulVecMemSmul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsRadicalSpanPrimeOfNcardPrimesOverEqFinrank

open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped Matrix

noncomputable section

namespace GlobalTheory.SmallElement

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem span_L' {r : ℕ} (X : DataX E r) :
    Submodule.span E (X.L' : Set (Fin r → E)) = ⊤ := by
  rw [eq_top_iff, ← X.Λ_span, Submodule.span_le]
  intro x hx
  have h1 := X.NA_sub x hx
  have hNA : (X.NA : E) ≠ 0 := by exact_mod_cast X.NA_pos.ne'
  have e : x = (X.NA : E)⁻¹ • ((X.NA : E) • x) := by rw [smul_smul, inv_mul_cancel₀ hNA, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

theorem trace_sub_mem {r : ℕ} (X : DataX E r) (g : ℕ) (hg : IndefiniteRowSideFullHecke.SmallUnipotentElements.IsTotallySplitPrime E g)
    (δ : GL (Fin r) E) (hδ : IsUStab X.Gm X.L' δ)
    (hu : IndefiniteRowSideFullHecke.SmallUnipotentElements.IsUnipotentModOver X.L' g δ) :
    ∃ z : 𝓞 E, (δ : Matrix (Fin r) (Fin r) E).trace - r = (g : E) * z := by
  classical
  set N : Matrix (Fin r) (Fin r) E := (δ : Matrix (Fin r) (Fin r) E) - 1 with hNdef
  have htr : N.trace = (δ : Matrix (Fin r) (Fin r) E).trace - r := by
    simp [hNdef, Matrix.trace_sub]
  have hN : ∀ x ∈ X.L', N.mulVec x ∈ X.L' := fun x hx => by
    rw [hNdef, Matrix.sub_mulVec, Matrix.one_mulVec]
    exact X.L'.sub_mem ((hδ.2 x).1 hx) hx
  have hP : ∀ P ∈ (Ideal.span {(g : ℤ)}).primesOver (𝓞 E), ∃ z ∈ P, ((z : 𝓞 E) : E) = N.trace :=
    fun P hP => by
      obtain ⟨k, hk⟩ := hu P hP
      exact GlobalTheory.trace_mem_prime_of_pow_mulVec_mem_smul E r X.L' N P k X.L'_fg (span_L' X) hP.1 hN hk
  have hne : ((Ideal.span {(g : ℤ)}).primesOver (𝓞 E)).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [hg.2]
    exact (Module.finrank_pos (R := ℚ) (M := E)).ne'
  obtain ⟨P0, hP0⟩ := hne
  obtain ⟨t, -, ht⟩ := hP P0 hP0
  have hall : ∀ P ∈ (Ideal.span {(g : ℤ)}).primesOver (𝓞 E), t ∈ P := fun P hP' => by
    obtain ⟨z, hz, hzt⟩ := hP P hP'
    have : z = t := RingOfIntegers.ext (hzt.trans ht.symm)
    exact this ▸ hz
  have hpZ : Prime (g : ℤ) := Nat.prime_iff_prime_int.1 hg.1
  haveI hpr : (Ideal.span {(g : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  have hmax : (Ideal.span {(g : ℤ)}).IsMaximal :=
    hpr.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpZ.ne_zero)
  have hrad := GlobalTheory.SplitRadical.isRadical_span_of_ncard_primesOver E g hg.1 hg.2
  have hmem : t ∈ Ideal.span {(g : 𝓞 E)} := by
    apply hrad
    rw [Ideal.radical_eq_sInf]
    refine Submodule.mem_sInf.2 fun J hJ => ?_
    obtain ⟨hJle, hJp⟩ := hJ
    apply hall J
    refine ⟨hJp, ⟨?_⟩⟩
    have hle : Ideal.span {(g : ℤ)} ≤ Ideal.comap (algebraMap ℤ (𝓞 E)) J := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      show algebraMap ℤ (𝓞 E) (g : ℤ) ∈ J
      rw [map_natCast]
      exact hJle (Ideal.mem_span_singleton_self _)
    exact hmax.eq_of_le (Ideal.IsPrime.ne_top (Ideal.IsPrime.comap _)) hle
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨z, ?_⟩
  rw [← htr, ← ht, ← hz]
  push_cast
  ring

end GlobalTheory.SmallElement

namespace GlobalTheory.SmallElement

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem map_conj_mulVec {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) (u : Fin r → ℂ) :
    (M.map (starRingEnd ℂ)) *ᵥ u = star (M *ᵥ star u) := by
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum]

theorem normSq_star {r : ℕ} (u : Fin r → ℂ) : ReciprocityTheory.MultiplicativeHeights.normSq (star u) = ReciprocityTheory.MultiplicativeHeights.normSq u := by
  simp [ReciprocityTheory.MultiplicativeHeights.normSq]

theorem exp_sq (r : ℕ) : Real.exp (1 / (3 * (r : ℝ))) ^ 2 = Real.exp (2 / (3 * (r : ℝ))) := by
  rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

theorem det_ne_of_mul_eq_one {r : ℕ} {A B : Matrix (Fin r) (Fin r) ℂ} (h : A * B = 1) : A.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem map_conj_mul_eq_one {r : ℕ} {A : Matrix (Fin r) (Fin r) ℂ} (hA : IsUnit A.det) :
    (A⁻¹).map (starRingEnd ℂ) * A.map (starRingEnd ℂ) = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hA, Matrix.map_one _ (map_zero _) (map_one _)]

end GlobalTheory.SmallElement

namespace GlobalTheory.SmallElement

theorem smallElement : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    IndefiniteRowSideFullHecke.SmallUnipotentElements.SmallElementStatement E := by
  intro E _ _ _ r X g hg hgr Γo hstab hunip x hx hNC γ hγ hs
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact Units.ext (Matrix.ext fun i => i.elim0)
  obtain ⟨x1, h1, b, hb, rfl⟩ := ortho_holds r X.toData x hx
  have hx1 := ModeHalfA.dom_of_orth X.toData h1
  have hu : ∀ τ : X.Ψ, IsUnit (mat x1 τ).det :=
    fun τ => isUnit_iff_ne_zero.2 (LUPf.orthogonalFrame_det_ne_zero X.toData x1 h1 τ)
  have hmaj : ∀ (τ : X.Ψ) (v : Fin r → ℂ),
      X.maj (rmul x1 b) τ v = ReciprocityTheory.MultiplicativeHeights.normSq ((mat x1 τ)⁻¹ *ᵥ v) := fun τ v => by
    rw [GlobalTheory.MajInv.maj_rmul X.toData hx1 hb, ModeHalfA.maj_orth X.toData h1]
    rfl
  have hcΨ : ∀ σ : E →+* ℂ, σ ∉ X.Ψ → ComplexEmbedding.conjugate σ ∈ X.Ψ := fun σ hσ =>
    not_not.1 fun h' => hσ ((X.cmType σ).2 h')
  let Q : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ := fun σ =>
    if hσ : σ ∈ X.Ψ then (mat x1 ⟨σ, hσ⟩)⁻¹
    else ((mat x1 ⟨ComplexEmbedding.conjugate σ, hcΨ σ hσ⟩)⁻¹).map (starRingEnd ℂ)
  have hQpos : ∀ σ (hσ : σ ∈ X.Ψ), Q σ = (mat x1 ⟨σ, hσ⟩)⁻¹ := fun σ hσ => dif_pos hσ
  have hQneg : ∀ σ (hσ : σ ∉ X.Ψ),
      Q σ = ((mat x1 ⟨ComplexEmbedding.conjugate σ, hcΨ σ hσ⟩)⁻¹).map (starRingEnd ℂ) :=
    fun σ hσ => dif_neg hσ
  set G : Matrix (Fin r) (Fin r) E := (γ : Matrix (Fin r) (Fin r) E) with hG
  have hposB : ∀ (τ : X.Ψ) (u : Fin r → ℂ),
      ReciprocityTheory.MultiplicativeHeights.normSq (((mat x1 τ)⁻¹ * G.map τ.1 * ((mat x1 τ)⁻¹)⁻¹) *ᵥ u) ≤
        Real.exp (2 / (3 * (r : ℝ))) * ReciprocityTheory.MultiplicativeHeights.normSq u := by
    intro τ u
    have h := hs τ (mat x1 τ *ᵥ u)
    have e : (mat x1 τ)⁻¹ *ᵥ (mat x1 τ *ᵥ u) = u := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hu τ), Matrix.one_mulVec]
    rw [hmaj, hmaj, e, exp_sq] at h
    rw [Matrix.nonsing_inv_nonsing_inv _ (hu τ), ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact h
  have hQdet : ∀ σ, (Q σ).det ≠ 0 := by
    intro σ
    by_cases hσ : σ ∈ X.Ψ
    · rw [hQpos σ hσ]
      exact det_ne_of_mul_eq_one (Matrix.nonsing_inv_mul _ (hu _))
    · rw [hQneg σ hσ]
      exact det_ne_of_mul_eq_one (map_conj_mul_eq_one (hu _))
  have hop : ∀ σ (u : Fin r → ℂ), ReciprocityTheory.MultiplicativeHeights.normSq ((Q σ * G.map σ * (Q σ)⁻¹) *ᵥ u) ≤
      Real.exp (2 / (3 * (r : ℝ))) * ReciprocityTheory.MultiplicativeHeights.normSq u := by
    intro σ u
    by_cases hσ : σ ∈ X.Ψ
    · rw [hQpos σ hσ]
      exact hposB ⟨σ, hσ⟩ u
    · rw [hQneg σ hσ]
      set τ : X.Ψ := ⟨ComplexEmbedding.conjugate σ, hcΨ σ hσ⟩ with hτ
      have hinv : (((mat x1 τ)⁻¹).map (starRingEnd ℂ))⁻¹ = (mat x1 τ).map (starRingEnd ℂ) :=
        Matrix.inv_eq_right_inv (map_conj_mul_eq_one (hu τ))
      have hGm : G.map σ = (G.map τ.1).map (starRingEnd ℂ) := by
        ext i j
        simp [hτ, ComplexEmbedding.conjugate_coe_eq]
      have e : ((mat x1 τ)⁻¹).map (starRingEnd ℂ) * G.map σ *
          (((mat x1 τ)⁻¹).map (starRingEnd ℂ))⁻¹ =
          ((mat x1 τ)⁻¹ * G.map τ.1 * ((mat x1 τ)⁻¹)⁻¹).map (starRingEnd ℂ) := by
        rw [hinv, hGm, Matrix.nonsing_inv_nonsing_inv _ (hu τ), Matrix.map_mul, Matrix.map_mul]
      rw [e, map_conj_mulVec, normSq_star, ← normSq_star u]
      exact hposB τ (star u)
  have htr : ∀ n : ℕ, 1 ≤ n → n ≤ r → ∃ z : 𝓞 E, (G ^ n).trace - r = (g : E) * z := by
    intro n _ _
    have hm := Γo.pow_mem hγ n
    have := trace_sub_mem X g hg (γ ^ n) (hstab _ hm) (hunip _ hm)
    rwa [Units.val_pow_eq_pow_val] at this
  have hg' : (Real.exp (1 / 3) + 1) * r < g := by
    have h3 := ReciprocityTheory.MultiplicativeHeights.sb_exp_third_lt_two
    have hr' : (0 : ℝ) < r := by exact_mod_cast hr
    have hg3 : (3 * r : ℝ) < g := by exact_mod_cast hgr
    nlinarith
  have hU := ReciprocityTheory.MultiplicativeHeights.unipotent_holds E r g G Q htr hg' hQdet hop
  have hN : G - 1 = 0 := by
    refine hNC (G - 1) (fun v hv => ?_) (fun τ => ?_)
    · rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      exact X.L'.sub_mem (((hstab γ hγ).2 v).1 hv) hv
    · set S := ∑ a, ∑ b, ‖(Q τ.1 * (G.map τ.1 - 1) * (Q τ.1)⁻¹) a b‖ ^ 2 with hS
      have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hS1 : S < 1 := hU.2 τ.1
      refine ⟨Real.sqrt S, Real.sqrt_nonneg _, (Real.sqrt_lt' one_pos).2 (by rw [one_pow]; exact hS1),
        fun u => ?_⟩
      rw [Real.sq_sqrt hS0, hmaj, hmaj]
      have hmap : (G - 1).map τ.1 = G.map τ.1 - 1 := by
        rw [← RingHom.mapMatrix_apply, map_sub, map_one, RingHom.mapMatrix_apply]
      have hQτ : Q τ.1 = (mat x1 τ)⁻¹ := hQpos τ.1 τ.2
      have e2 : (mat x1 τ)⁻¹ *ᵥ ((G.map τ.1 - 1) *ᵥ u) =
          ((mat x1 τ)⁻¹ * (G.map τ.1 - 1) * ((mat x1 τ)⁻¹)⁻¹) *ᵥ ((mat x1 τ)⁻¹ *ᵥ u) := by
        rw [Matrix.nonsing_inv_nonsing_inv _ (hu τ)]
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hu τ),
          Matrix.mul_one]
      rw [hmap, e2, hS, hQτ]
      exact ReciprocityTheory.MultiplicativeHeights.sb_normSq_mulVec_le _ _
  exact Units.ext (sub_eq_zero.1 hN)

end GlobalTheory.SmallElement
