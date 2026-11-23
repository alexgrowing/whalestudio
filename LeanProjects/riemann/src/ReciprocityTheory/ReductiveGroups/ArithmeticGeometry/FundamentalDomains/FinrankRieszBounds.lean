import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.DiscreteLatticeMinimum

namespace ReciprocityTheory.ChartRestriction.G.FD

namespace FinrankRieszBounds

open NumberField Complex Module RealTangentSpace
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem maj_csmul {z : Frame X.Ψ r} (hz : z ∈ X.dom) (τ : X.Ψ) (c : ℂ) (v : Fin r → ℂ) :
    X.maj z τ (c • v) = ‖c‖ ^ 2 * X.maj z τ v := by
  have hl : ∀ w, hermC τ.1 X.Gm (c • v) w = c * hermC τ.1 X.Gm v w := by
    intro w
    simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hr : hermC τ.1 X.Gm v (c • v) = conj c * hermC τ.1 X.Gm v v := by
    simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hcc : c * conj c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hH : hermC τ.1 X.Gm (c • v) (c • v) = ((‖c‖ ^ 2 : ℝ) : ℂ) * hermC τ.1 X.Gm v v := by
    rw [hl, hr, ← mul_assoc, hcc]
  have hP : X.posPart z τ (c • v) = ‖c‖ ^ 2 * X.posPart z τ v := by
    simp only [Data.posPart, hl, map_mul]
    rw [← Complex.re_ofReal_mul]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← hcc]
    ring
  simp only [Data.maj, hP, hH, Complex.re_ofReal_mul]
  ring

variable (z : Frame X.Ψ r) (ξ : Fin r → E) [hz : Fact (z ∈ X.dom)]

theorem riesz (δ : X.Ψ → (Fin r → ℂ) →ₗ[ℂ] ℂ) :
    ∃ d : VT (X := X) z ξ, ∀ u ∈ X.Uz z ξ, ∀ τ : X.Ψ, δ τ (u τ) = X.Hf z τ (u τ) (d.val τ) := by
  classical
  let ℓ : VT (X := X) z ξ →ₗ[ℝ] ℝ :=
    { toFun := fun u => ∑ τ, (δ τ (u.val τ)).re
      map_add' := fun u v => by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [VT.val_add, Pi.add_apply, map_add, Complex.add_re]
      map_smul' := fun c u => by
        rw [RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [VT.val_smul, Pi.smul_apply, ← Complex.coe_smul, map_smul, smul_eq_mul,
          Complex.re_ofReal_mul] }
  let d := (InnerProductSpace.toDual ℝ (VT (X := X) z ξ)).symm (LinearMap.toContinuousLinearMap ℓ)
  refine ⟨d, fun u hu τ0 => ?_⟩
  have hd : ∀ v : VT (X := X) z ξ, inner ℝ d v = ℓ v := fun v => by
    rw [InnerProductSpace.toDual_symm_apply]
    rfl

  have key : ∀ w ∈ X.Uz z ξ, (δ τ0 (w τ0)).re = (X.Hf z τ0 (w τ0) (d.val τ0)).re := by
    intro w hw
    let s : X.Ψ → ℂ := fun τ => if τ = τ0 then 1 else 0
    have hw' := MajorantOperators.smul_fam_mem s hw
    have h := hd (VT.mk _ hw')
    rw [inner_eq] at h
    simp only [ℓ, LinearMap.coe_mk, AddHom.coe_mk, VT.val_mk, MajorantOperators.gI] at h
    rw [Finset.sum_eq_single τ0 (fun τ _ hτ => by simp [s, hτ, MajorantOperators.Hf_zero_right])
      (fun h => absurd (Finset.mem_univ τ0) h),
      Finset.sum_eq_single τ0 (fun τ _ hτ => by simp [s, hτ]) (fun h => absurd (Finset.mem_univ τ0) h)]
      at h
    simp only [s, if_true, one_smul] at h
    rw [← h, ← UnipotentCoefficientShift.Hf_conj hz.out, Complex.conj_re]
  have h1 := key u hu
  have h2 := key _ (MajorantOperators.smul_fam_mem (fun _ => Complex.I) hu)
  simp only [map_smul, smul_eq_mul, UnipotentCoefficientShift.Hf_smul_left, Complex.mul_re, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, zero_sub] at h2
  apply Complex.ext
  · exact h1
  · linarith

omit hz in

theorem finrank_le {ξ : Fin r → E} (hz : z ∈ X.dom) (hξ : X.IsIso ξ) :
    finrank ℝ (VT (X := X) z ξ) ≤ 2 * fdeg E * (r - 2) := by
  classical
  let Lm : (X.Ψ → Fin r → ℂ) →ₗ[ℝ] (X.Ψ → Fin 2 → ℂ) :=
    { toFun := fun u τ => ![hermC τ.1 X.Gm (u τ) (Data.emb τ.1 ξ),
        hermC τ.1 X.Gm (X.jp z τ (u τ)) (Data.emb τ.1 ξ)]
      map_add' := fun u v => by
        funext τ i
        fin_cases i <;> simp [hermC_add_left, Data.jp_add]
      map_smul' := fun c u => by
        funext τ i
        fin_cases i <;> simp [← Complex.coe_smul, hermC_smul_left, Data.jp_smul] }
  have hker : LinearMap.ker Lm = Usub (X := X) z ξ := by
    ext u
    rw [LinearMap.mem_ker]
    show Lm u = 0 ↔ u ∈ X.Uz z ξ
    rw [MajorantOperators.mem_Uz_iff, funext_iff]
    refine forall_congr' fun τ => ?_
    rw [funext_iff, Fin.forall_fin_two]
    simp [Lm]
  have hsurj : LinearMap.range Lm = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro t
    have hm : ∀ τ : X.Ψ, hermC τ.1 X.Gm (X.jp z τ (Data.emb τ.1 ξ)) (Data.emb τ.1 ξ) ≠ 0 := by
      intro τ
      rw [← Data.Hf_eq_jp, X.Hf_self hz]
      exact_mod_cast (X.maj_pos hz τ (emb_ne_zero τ.1 hξ.2.2)).ne'
    have hee : ∀ τ : X.Ψ, hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0 := fun τ => by
      rw [hermC_emb, hξ.2.1, map_zero]
    refine ⟨fun τ => (t τ 0 / hermC τ.1 X.Gm (X.jp z τ (Data.emb τ.1 ξ)) (Data.emb τ.1 ξ)) •
        X.jp z τ (Data.emb τ.1 ξ) +
      (t τ 1 / hermC τ.1 X.Gm (X.jp z τ (Data.emb τ.1 ξ)) (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ, ?_⟩
    funext τ i
    fin_cases i
    · simp [Lm, hermC_add_left, hermC_smul_left, hee, div_mul_cancel₀ _ (hm τ)]
    · simp [Lm, hermC_add_left, hermC_smul_left, Data.jp_add, Data.jp_smul, X.jp_jp hz, hee,
        div_mul_cancel₀ _ (hm τ)]
  have hrn := LinearMap.finrank_range_add_finrank_ker Lm
  rw [hsurj, finrank_top, hker] at hrn
  have hdom : finrank ℝ (X.Ψ → Fin r → ℂ) = Fintype.card X.Ψ * (r * 2) := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
  have hcod : finrank ℝ (X.Ψ → Fin 2 → ℂ) = Fintype.card X.Ψ * (2 * 2) := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
  rw [hdom, hcod] at hrn
  have hV : finrank ℝ (VT (X := X) z ξ) = finrank ℝ (Usub (X := X) z ξ) := rfl

  have hΨ : 2 * Fintype.card X.Ψ ≤ finrank ℚ E := by
    have hdisj : Disjoint X.Ψ (X.Ψ.image ComplexEmbedding.conjugate) := by
      rw [Finset.disjoint_left]
      intro σ hσ hσ'
      obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hσ'
      exact (X.cmType τ).mp hτ hσ
    have hinj : Function.Injective (ComplexEmbedding.conjugate : (E →+* ℂ) → (E →+* ℂ)) :=
      fun a b h => by
        have := congrArg ComplexEmbedding.conjugate h
        simpa using this
    have h1 := Finset.card_le_univ (X.Ψ ∪ X.Ψ.image ComplexEmbedding.conjugate)
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ hinj,
      NumberField.Embeddings.card] at h1
    rw [Fintype.card_coe]
    omega
  have hf : Fintype.card X.Ψ ≤ fdeg E := by
    unfold fdeg
    omega
  rw [hV]
  have hk : finrank ℝ (Usub (X := X) z ξ) = 2 * Fintype.card X.Ψ * (r - 2) := by
    rw [Nat.eq_sub_of_add_eq' hrn, Nat.mul_sub]
    ring_nf
  rw [hk]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hf)

end FinrankRieszBounds

end ReciprocityTheory.ChartRestriction.G.FD
