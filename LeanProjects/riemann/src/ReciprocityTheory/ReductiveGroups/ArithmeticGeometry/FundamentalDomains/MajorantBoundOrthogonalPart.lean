import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentSubOneMajorantBound

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace Data

variable {r : ℕ} (X : Data E r)

lemma Hf_unitary (x : Frame X.Ψ r) (τ : X.Ψ) (g : Matrix (Fin r) (Fin r) ℂ)
    (hg : ∀ u w, hermC τ.1 X.Gm (Matrix.mulVec g u) (Matrix.mulVec g w) = hermC τ.1 X.Gm u w)
    (hx : x ∈ X.dom) (y w : Fin r → ℂ) :
    X.Hf (X.lmulC (fun _ => g) x) τ (Matrix.mulVec g y) (Matrix.mulVec g w) = X.Hf x τ y w := by
  have hcol : ∀ a, col (mat (X.lmulC (fun _ => g) x) τ) a = g.mulVec (col (mat x τ) a) := by
    intro a
    funext k
    simp [col, mat, Data.lmulC, Matrix.of_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rfl
  have hgram : X.gramPos (X.lmulC (fun _ => g) x) τ = X.gramPos x τ := by
    ext a b
    simp only [Data.gramPos, gram, Matrix.submatrix_apply, Matrix.of_apply, hcol, hg]
  have hppos : X.ppos (X.lmulC (fun _ => g) x) τ (g.mulVec y) = g.mulVec (X.ppos x τ y) := by
    simp only [Data.ppos, hcol, hgram, hg, Matrix.mulVec_sum, Matrix.mulVec_smul]
  have hlin : (2 : ℂ) • g.mulVec (X.ppos x τ y) - g.mulVec y =
      g.mulVec ((2 : ℂ) • X.ppos x τ y - y) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul]
  simp only [Data.Hf]
  rw [hppos, hlin, hg]

lemma ppos_mat_eq {x x' : Frame X.Ψ r} {τ : X.Ψ} (h : mat x τ = mat x' τ) (v : Fin r → ℂ) :
    X.ppos x τ v = X.ppos x' τ v := by
  simp only [Data.ppos, Data.gramPos, h]

lemma Hf_mat_eq {x x' : Frame X.Ψ r} {τ : X.Ψ} (h : mat x τ = mat x' τ) (v w : Fin r → ℂ) :
    X.Hf x τ v w = X.Hf x' τ v w := by
  simp only [Data.Hf, ppos_mat_eq X h]

lemma mat_lmulC_at (n : X.Ψ → Matrix (Fin r) (Fin r) ℂ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    mat (X.lmulC n x) τ = mat (X.lmulC (fun _ => n τ) x) τ := rfl

lemma majorant_bound_orthogonal_part (ξ : Fin r → E) (x : Frame X.Ψ r) (hx : x ∈ X.dom)
    (δ : X.Ψ → (Fin r → ℂ) →ₗ[ℂ] ℂ) (κ : ℝ)
    (hδ : ∀ u ∈ X.Uz x ξ, ∀ τ, X.maj x τ (δ τ (u τ) • emb τ.1 ξ) ≤ κ ^ 2 * X.maj x τ (u τ))
    (τ : X.Ψ) (w : Fin r → ℂ) (hw1 : hermC τ.1 X.Gm w (emb τ.1 ξ) = 0)
    (hw2 : hermC τ.1 X.Gm w (X.Jp x τ (emb τ.1 ξ)) = 0) :
    X.maj x τ (δ τ w • emb τ.1 ξ) ≤ κ ^ 2 * X.maj x τ w := by
  classical
  let u : X.Ψ → Fin r → ℂ := fun τ' => if τ' = τ then w else 0
  have hu : u ∈ X.Uz x ξ := by
    refine ⟨fun τ' => ?_, fun τ' => ?_⟩
    · by_cases h : τ' = τ
      · subst h
        simp [u, hw1]
      · simp [u, h, hC_zero_left]
    · by_cases h : τ' = τ
      · subst h
        have hsm : hermC τ'.1 X.Gm (X.Jz x u τ') (emb τ'.1 ξ) =
            I * hermC τ'.1 X.Gm (X.Jp x τ' w) (emb τ'.1 ξ) := by
          simp [Data.Jz, Data.Jp, u, hermC, Finset.mul_sum, mul_assoc]
        rw [hsm, X.Jp_adj hx τ' w (emb τ'.1 ξ), hw2, mul_zero]
      · simp [Data.Jz, u, h, X.ppos_zero, hC_zero_left]
  have hmain := hδ u hu τ
  simpa [u] using hmain

set_option maxHeartbeats 1000000 in
theorem unipotent_majorant_bound_data : ReducedFrameDomainCovering (E := E) := by
  intro r X ξ hξ x hx δ κ hκ0 hκ1 hδ
  have hCsub : ∀ (τ : X.Ψ) (u v w : Fin r → ℂ) (c : ℂ),
      hermC τ.1 X.Gm (u - c • v) w = hermC τ.1 X.Gm u w - c * hermC τ.1 X.Gm v w := by
    intro τ u v w c
    simp only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
      Finset.mul_sum, mul_assoc]
  have hCsmul : ∀ (τ : X.Ψ) (u w : Fin r → ℂ) (c : ℂ),
      hermC τ.1 X.Gm (c • u) w = c * hermC τ.1 X.Gm u w := by
    intro τ u w c
    simp only [hermC, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  have hee : ∀ τ : X.Ψ, hermC τ.1 X.Gm (emb τ.1 ξ) (emb τ.1 ξ) = 0 := by
    intro τ
    have h : hermC τ.1 X.Gm (emb τ.1 ξ) (emb τ.1 ξ) = τ.1 (herm X.Gm ξ ξ) := by
      simp [hermC, herm, Data.emb, map_sum, map_mul, emb_cc]
    rw [h, hξ.2.1, map_zero]
  have he0 : ∀ τ : X.Ψ, emb τ.1 ξ ≠ 0 := by
    intro τ h
    apply hξ.2.2
    funext a
    have h1 := congrFun h a
    simpa [Data.emb] using h1
  have hq : ∀ τ : X.Ψ, X.Hf x τ (emb τ.1 ξ) (emb τ.1 ξ) = (X.maj x τ (emb τ.1 ξ) : ℂ) :=
    fun τ => X.Hf_self hx τ _
  have hqne : ∀ τ : X.Ψ, X.Hf x τ (emb τ.1 ξ) (emb τ.1 ξ) ≠ 0 := by
    intro τ
    rw [hq τ]
    exact_mod_cast (X.maj_pos hx τ (he0 τ)).ne'
  have hHfJ : ∀ τ v, X.Hf x τ v (emb τ.1 ξ) = hermC τ.1 X.Gm v (X.Jp x τ (emb τ.1 ξ)) :=
    fun τ v => by rw [X.Hf_eq x hx]; rfl
  set N : X.Ψ → Matrix (Fin r) (Fin r) ℂ := fun τ => X.d2n x τ (emb τ.1 ξ) (δ τ) with hN
  have hqr : ∀ τ : X.Ψ, conj (X.d2q x τ (emb τ.1 ξ)) = X.d2q x τ (emb τ.1 ξ) := by
    intro τ
    show conj (X.Hf x τ _ _) = X.Hf x τ _ _
    rw [hq τ]
    exact Complex.conj_ofReal _
  have hU : ∀ τ u w, hermC τ.1 X.Gm ((N τ).mulVec u) ((N τ).mulVec w) = hermC τ.1 X.Gm u w :=
    fun τ u w => X.unipotent_transform_unitary (x := x) (τ := τ) (e := emb τ.1 ξ) (δ := δ τ) hx (hee τ) (hqne τ) (hqr τ) u w
  have hNe : ∀ τ, (N τ).mulVec (emb τ.1 ξ) = emb τ.1 ξ :=
    fun τ => X.unipotent_fixes_e (x := x) (τ := τ) (e := emb τ.1 ξ) (δ := δ τ) hx (hee τ) (hqne τ)
  have hHfN : ∀ τ v w, X.Hf (X.lmulC N x) τ ((N τ).mulVec v) ((N τ).mulVec w) = X.Hf x τ v w :=
    fun τ v w => by
      rw [X.Hf_mat_eq (X.mat_lmulC_at N x τ)]
      exact X.Hf_unitary x τ (N τ) (hU τ) hx v w
  have hπsub : ∀ τ v (c : ℂ),
      X.d2pi x τ (emb τ.1 ξ) (v - c • emb τ.1 ξ) = X.d2pi x τ (emb τ.1 ξ) v := by
    intro τ v c
    have hJ : hermC τ.1 X.Gm (emb τ.1 ξ) (X.Jp x τ (emb τ.1 ξ)) = X.d2q x τ (emb τ.1 ξ) :=
      (hHfJ τ _).symm
    have hq0 : X.d2q x τ (emb τ.1 ξ) ≠ 0 := hqne τ
    rw [X.hyperbolic_projection_apply, X.hyperbolic_projection_apply, X.hyperbolic_coeff_a_apply, X.hyperbolic_coeff_a_apply, X.hyperbolic_coeff_b_apply, X.hyperbolic_coeff_b_apply,
      hCsub, hCsub, hee τ, hJ]
    ext a
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hπsmul : ∀ τ v (c : ℂ),
      X.d2pi x τ (emb τ.1 ξ) (c • v) = c • X.d2pi x τ (emb τ.1 ξ) v := by
    intro τ v c
    rw [X.hyperbolic_projection_apply, X.hyperbolic_projection_apply, X.hyperbolic_coeff_a_apply, X.hyperbolic_coeff_a_apply, X.hyperbolic_coeff_b_apply, X.hyperbolic_coeff_b_apply,
      hCsmul, hCsmul]
    ext a
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hNinv : ∀ τ v, hermC τ.1 X.Gm v (emb τ.1 ξ) = 0 →
      (N τ).mulVec (v - δ τ (X.d2pi x τ (emb τ.1 ξ) v) • emb τ.1 ξ) = v := by
    intro τ v hv
    have hperp : hermC τ.1 X.Gm (v - δ τ (X.d2pi x τ (emb τ.1 ξ) v) • emb τ.1 ξ) (emb τ.1 ξ) = 0 := by
      rw [hCsub, hv, hee τ, mul_zero, sub_zero]
    rw [X.unipotent_on_orthogonal_e (x := x) (τ := τ) (e := emb τ.1 ξ) (δ := δ τ) hx (hee τ) (hqne τ) hperp, hπsub]
    simp
  have hHfperp : ∀ τ v, hermC τ.1 X.Gm v (emb τ.1 ξ) = 0 →
      X.Hf (X.lmulC N x) τ v (emb τ.1 ξ) = X.Hf x τ v (emb τ.1 ξ) -
        δ τ (X.d2pi x τ (emb τ.1 ξ) v) * X.Hf x τ (emb τ.1 ξ) (emb τ.1 ξ) := by
    intro τ v hv
    have h1 := hHfN τ (v - δ τ (X.d2pi x τ (emb τ.1 ξ) v) • emb τ.1 ξ) (emb τ.1 ξ)
    rw [hNinv τ v hv, hNe τ] at h1
    rw [h1, X.Hf_eq x hx, X.Hf_eq x hx, X.Hf_eq x hx, hCsub]
  have hHfee : ∀ τ, X.Hf (X.lmulC N x) τ (emb τ.1 ξ) (emb τ.1 ξ) =
      X.Hf x τ (emb τ.1 ξ) (emb τ.1 ξ) := by
    intro τ
    have h1 := hHfN τ (emb τ.1 ξ) (emb τ.1 ξ)
    rwa [hNe τ] at h1
  have huz : ∀ u ∈ X.Uz x ξ, ∀ τ, hermC τ.1 X.Gm (u τ) (X.Jp x τ (emb τ.1 ξ)) = 0 := by
    intro u hu τ
    have h2 := hu.2 τ
    have hsm : X.Jz x u τ = I • X.Jp x τ (u τ) := rfl
    rw [hsm, hCsmul] at h2
    have h3 : hermC τ.1 X.Gm (X.Jp x τ (u τ)) (emb τ.1 ξ) = 0 :=
      (mul_eq_zero.1 h2).resolve_left Complex.I_ne_zero
    rwa [X.Jp_adj hx] at h3
  have hπperp : ∀ τ v, hermC τ.1 X.Gm v (emb τ.1 ξ) = 0 →
      X.d2pi x τ (emb τ.1 ξ) v = v - (X.Hf x τ v (emb τ.1 ξ) /
        X.Hf x τ (emb τ.1 ξ) (emb τ.1 ξ)) • emb τ.1 ξ := by
    intro τ v hv
    rw [X.hyperbolic_projection_apply, X.hyperbolic_coeff_a_apply, X.hyperbolic_coeff_b_apply, hv, mul_zero, zero_smul, sub_zero, hHfJ τ v,
      div_eq_inv_mul]
    rfl
  have hdom : X.lmulC N x ∈ X.dom := by
    show ∀ τ : X.Ψ, (mat (X.lmulC N x) τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (X.lmulC N x) τ i).re
    intro τ
    have hm : mat (X.lmulC N x) τ = N τ * mat x τ := rfl
    have hcol : ∀ c, col (N τ * mat x τ) c = (N τ).mulVec (col (mat x τ) c) := by
      intro c
      funext k
      simp [col, Matrix.mul_apply, Matrix.mulVec, dotProduct]
    have hgram : gram τ.1 X.Gm (N τ * mat x τ) = gram τ.1 X.Gm (mat x τ) := by
      ext a b
      simp only [gram, Matrix.of_apply, hcol, hU]
    refine ⟨?_, fun i => ?_⟩
    · rw [hm, Matrix.det_mul]
      refine mul_ne_zero ?_ (hx τ).1
      intro hdet
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
      apply hv0
      have horth : ∀ w, hermC τ.1 X.Gm v w = 0 := fun w => by
        rw [← hU τ v w, hv, hC_zero_left]
      have hvm : Matrix.vecMul v (X.Gm.map τ.1) = 0 := by
        funext b
        have h1 := horth (Pi.single b 1)
        simpa [hermC, Pi.single_apply, Matrix.vecMul, dotProduct] using h1
      exact Matrix.eq_zero_of_vecMul_eq_zero (map_det_ne τ.1 X.Gm X.Gm_det) hvm
    · simp only [dmin, hm, hgram]
      exact (hx τ).2 i
  refine ⟨N, hU, hNe, ?_, hdom, ?_, ?_, ?_, ?_⟩
  · intro u hu
    funext τ
    simp only [Data.applyV, Data.lineV, Pi.add_apply]
    exact X.unipotent_on_hyperbolic_complement (x := x) (τ := τ) (e := emb τ.1 ξ) (δ := δ τ) hx (hee τ) (hqne τ) (hu.1 τ) (huz u hu τ)
  · intro u hu
    funext τ
    simp only [Data.aproj, Data.lineV, Pi.sub_apply, Data.ucomp]
    rw [hHfperp τ (u τ) (hu τ), hHfee τ, hπperp τ (u τ) (hu τ), ← sub_smul]
    congr 1
    field_simp [hqne τ]
  · intro τ
    have h1 : (X.maj (X.lmulC N x) τ (emb τ.1 ξ) : ℂ) = X.maj x τ (emb τ.1 ξ) := by
      rw [← X.Hf_self hdom τ, ← X.Hf_self hx τ, hHfee τ]
    exact_mod_cast h1
  · intro u hu
    funext τ
    have hw1 : hermC τ.1 X.Gm (u τ) (emb τ.1 ξ) = 0 := hu.1 τ
    have hw2 := huz u hu τ
    have hJw : hermC τ.1 X.Gm (X.Jp x τ (u τ)) (emb τ.1 ξ) = 0 := by
      rw [X.Jp_adj hx]
      exact hw2
    have hIJw : hermC τ.1 X.Gm (I • X.Jp x τ (u τ)) (emb τ.1 ξ) = 0 := by
      rw [hCsmul, hJw, mul_zero]
    have hπw : X.d2pi x τ (emb τ.1 ξ) (u τ) = u τ :=
      X.hyperbolic_projection_of_perp (x := x) (τ := τ) (e := emb τ.1 ξ) hx (hee τ) (hqne τ) hw1 hw2
    have hHfw : X.Hf (X.lmulC N x) τ (u τ) (emb τ.1 ξ) =
        -(δ τ (u τ) * X.Hf x τ (emb τ.1 ξ) (emb τ.1 ξ)) := by
      rw [hHfperp τ (u τ) hw1, hHfJ τ (u τ), hw2, hπw, zero_sub]
    have hHfIJw : X.Hf (X.lmulC N x) τ (I • X.Jp x τ (u τ)) (emb τ.1 ξ) =
        -(δ τ (X.d2pi x τ (emb τ.1 ξ) (I • X.Jp x τ (u τ))) *
          X.Hf x τ (emb τ.1 ξ) (emb τ.1 ξ)) := by
      rw [hHfperp τ _ hIJw, hHfJ τ, hCsmul, X.Jp_adj hx, X.Jp_Jp hx, hw1, mul_zero, zero_sub]
    have hcol : ∀ c, col (mat (X.lmulC N x) τ) c = (N τ).mulVec (col (mat x τ) c) := by
      intro c
      funext k
      simp [col, mat, Data.lmulC, Matrix.of_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct]
      rfl
    have hgramP : X.gramPos (X.lmulC N x) τ = X.gramPos x τ := by
      ext a b
      simp only [Data.gramPos, gram, Matrix.submatrix_apply, Matrix.of_apply, hcol, hU]
    have hJpN : ∀ v, X.Jp (X.lmulC N x) τ ((N τ).mulVec v) = (N τ).mulVec (X.Jp x τ v) := by
      intro v
      have hp : X.ppos (X.lmulC N x) τ ((N τ).mulVec v) = (N τ).mulVec (X.ppos x τ v) := by
        simp only [Data.ppos, hcol, hgramP, hU, Matrix.mulVec_sum, Matrix.mulVec_smul]
      simp only [Data.Jp, hp, Matrix.mulVec_sub, Matrix.mulVec_smul]
    have hNw : (N τ).mulVec (u τ) = u τ + δ τ (u τ) • emb τ.1 ξ :=
      X.unipotent_on_hyperbolic_complement (x := x) (τ := τ) (e := emb τ.1 ξ) (δ := δ τ) hx (hee τ) (hqne τ) hw1 hw2
    have hNJw : (N τ).mulVec (X.Jp x τ (u τ)) = X.Jp x τ (u τ) +
        δ τ (X.d2pi x τ (emb τ.1 ξ) (X.Jp x τ (u τ))) • emb τ.1 ξ :=
      X.unipotent_on_orthogonal_e (x := x) (τ := τ) (e := emb τ.1 ξ) (δ := δ τ) hx (hee τ) (hqne τ) hJw
    have hJz : X.Jz x u τ = I • X.Jp x τ (u τ) := rfl
    have hq0 := hqne τ
    show X.Jz x u τ - (X.Hf (X.lmulC N x) τ (X.Jz x u τ) (emb τ.1 ξ) /
        X.Hf (X.lmulC N x) τ (emb τ.1 ξ) (emb τ.1 ξ)) • emb τ.1 ξ =
      I • X.Jp (X.lmulC N x) τ (u τ - (X.Hf (X.lmulC N x) τ (u τ) (emb τ.1 ξ) /
        X.Hf (X.lmulC N x) τ (emb τ.1 ξ) (emb τ.1 ξ)) • emb τ.1 ξ)
    rw [hJz, hHfIJw, hHfw, hHfee τ, neg_div, neg_div, mul_div_assoc, div_self hq0, mul_one,
      mul_div_assoc, div_self hq0, mul_one, neg_smul, neg_smul, sub_neg_eq_add, sub_neg_eq_add,
      ← hNw, hJpN, hNJw, hπsmul, map_smul, smul_eq_mul, smul_add, smul_smul]
  · intro τ v
    exact X.unipotent_sub_one_majorant_bound (x := x) (τ := τ) (e := emb τ.1 ξ) (δ := δ τ) hx (hee τ) (hqne τ)
      (fun v => X.Hf_self hx τ v) (fun v hv => X.maj_pos hx τ hv) κ hκ0 hκ1
      (fun w hw1 hw2 => X.majorant_bound_orthogonal_part ξ x hx δ κ hδ τ w hw1 hw2) v

end Data

theorem unipotent_majorant_bound : ReducedFrameDomainCovering (E := E) := Data.unipotent_majorant_bound_data

end ReciprocityTheory.ChartRestriction.G.FD
