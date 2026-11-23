import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajorantConjugateTransfer

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace FlowMatrixMajorants

open MajorantConjugateTransfer

variable {r : ℕ} (X : Data E r) (ξ : Fin r → E) (τ : X.Ψ)

theorem flowMat_add (hiso : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0) (a b : ℂ) :
    X.flowMat ξ τ (a + b) = X.flowMat ξ τ a * X.flowMat ξ τ b := by
  obtain ⟨V, hV⟩ : ∃ V : Matrix (Fin r) (Fin r) ℂ,
      V = Matrix.of fun a b => τ.1 (ξ a) * ∑ k, τ.1 (X.Gm b k) * conj (τ.1 (ξ k)) := ⟨_, rfl⟩
  have hM : ∀ s : ℂ, X.flowMat ξ τ s = 1 - (I * (X.c τ : ℂ) * s) • V := by
    intro s
    ext a b
    simp only [Data.flowMat, hV, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
      Matrix.of_apply, smul_eq_mul]
    ring
  have h0 : ∑ k, τ.1 (ξ k) * ∑ m, τ.1 (X.Gm k m) * conj (τ.1 (ξ m)) = 0 := by
    calc _ = hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) := by
          simp only [hermC, Data.emb, Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => by ring
      _ = 0 := hiso
  have hVV : V * V = 0 := by
    ext a b
    simp only [hV, Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
    calc ∑ k, τ.1 (ξ a) * (∑ m, τ.1 (X.Gm k m) * conj (τ.1 (ξ m))) *
          (τ.1 (ξ k) * ∑ m, τ.1 (X.Gm b m) * conj (τ.1 (ξ m)))
        = τ.1 (ξ a) * (∑ m, τ.1 (X.Gm b m) * conj (τ.1 (ξ m))) *
          ∑ k, τ.1 (ξ k) * ∑ m, τ.1 (X.Gm k m) * conj (τ.1 (ξ m)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = 0 := by rw [h0, mul_zero]
  simp only [hM, sub_mul, mul_sub, one_mul, mul_one, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    hVV, smul_zero, sub_zero, mul_add, add_smul]
  abel

theorem flowMat_zero : X.flowMat ξ τ 0 = 1 := by
  ext a b
  simp only [Data.flowMat, Matrix.of_apply, mul_zero, zero_mul, sub_zero, Matrix.one_apply]

theorem flow_split (hiso : ∀ τ : X.Ψ, hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0)
    (s : X.Ψ → ℂ) (x : Frame X.Ψ r) :
    X.flow ξ s x = X.flow ξ (fun τ => I * ((s τ).im : ℂ)) (X.flow ξ (fun τ => ((s τ).re : ℂ)) x) := by
  funext τ
  have hs : I * ((s τ).im : ℂ) + ((s τ).re : ℂ) = s τ := by
    rw [add_comm, mul_comm, Complex.re_add_im]
  show X.flowMat ξ τ (s τ) * mat x τ =
    X.flowMat ξ τ (I * ((s τ).im : ℂ)) * (X.flowMat ξ τ ((s τ).re : ℂ) * mat x τ)
  conv_lhs => rw [← hs]
  rw [flowMat_add X ξ τ (hiso τ), mul_assoc]

theorem flowMat_inv (hiso : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0) (a : ℂ)
    (w : Fin r → ℂ) : Matrix.mulVec (X.flowMat ξ τ a) (Matrix.mulVec (X.flowMat ξ τ (-a)) w) = w := by
  rw [Matrix.mulVec_mulVec, ← flowMat_add X ξ τ hiso, add_neg_cancel, flowMat_zero,
    Matrix.one_mulVec]

private lemma hermC_sub_smul_left_lemma_8 (σ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ)
    (p q y : Fin r → ℂ) : hermC σ G (p - a • q) y = hermC σ G p y - a * hermC σ G q y := by
  simp only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private lemma hermC_sub_smul_right_lemma_9 (σ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ)
    (y p q : Fin r → ℂ) :
    hermC σ G y (p - a • q) = hermC σ G y p - conj a * hermC σ G y q := by
  simp only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem flowMat_isom_real (hiso : hermC τ.1 X.Gm (Data.emb τ.1 ξ) (Data.emb τ.1 ξ) = 0) (t : ℝ)
    (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm (Matrix.mulVec (X.flowMat ξ τ t) u) (Matrix.mulVec (X.flowMat ξ τ t) v) =
      hermC τ.1 X.Gm u v := by
  have hMv : ∀ w : Fin r → ℂ, Matrix.mulVec (X.flowMat ξ τ t) w =
      w - (I * (X.c τ : ℂ) * (t : ℂ) * hermC τ.1 X.Gm w (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ := by
    intro w
    funext i
    show ∑ b, X.flowMat ξ τ t i b * w b = _
    simp only [Data.flowMat, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, hermC, Data.emb]
    congr 1
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring
  rw [hMv u, hMv v, hermC_sub_smul_left_lemma_8, hermC_sub_smul_right_lemma_9, hermC_sub_smul_right_lemma_9,
    hiso, ← hermC_conj τ.1 X.Gm_herm v (Data.emb τ.1 ξ)]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

theorem Hf_add_left (x : Frame X.Ψ r) (u u' w : Fin r → ℂ) :
    X.Hf x τ (u + u') w = X.Hf x τ u w + X.Hf x τ u' w := by
  unfold Data.Hf hermC
  rw [X.ppos_add x τ]
  simp only [smul_add, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem Hf_add_right (x : Frame X.Ψ r) (u w w' : Fin r → ℂ) :
    X.Hf x τ u (w + w') = X.Hf x τ u w + X.Hf x τ u w' := by
  unfold Data.Hf hermC
  simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

private lemma hermC_sum_left_lemma {ι : Type} [Fintype ι] (σ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (u : ι → ℂ) (v : ι → Fin r → ℂ) (y : Fin r → ℂ) :
    hermC σ G (∑ k, u k • v k) y = ∑ k, u k * hermC σ G (v k) y := by
  let f : (Fin r → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun x => hermC σ G x y
      map_add' := fun x x' => by
        simp only [hermC, Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp only [hermC, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring }
  have h := map_sum f (fun k => u k • v k) Finset.univ
  simp only [map_smul, smul_eq_mul] at h
  exact h

private lemma hermC_sum_right_lemma_2 {ι : Type} [Fintype ι] (σ : E →+* ℂ)
    (G : Matrix (Fin r) (Fin r) E) (x : Fin r → ℂ) (w : ι → ℂ) (z : ι → Fin r → ℂ) :
    hermC σ G x (∑ l, w l • z l) = ∑ l, conj (w l) * hermC σ G x (z l) := by
  let g : (Fin r → ℂ) →ₗ⋆[ℂ] ℂ :=
    { toFun := fun y => hermC σ G x y
      map_add' := fun y y' => by
        simp only [hermC, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]
      map_smul' := fun c y => by
        simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring }
  have h := map_sum g (fun l => w l • z l) Finset.univ
  simp only [map_smulₛₗ, smul_eq_mul] at h
  exact h

private lemma hermC_smul_sub_left_lemma_3 (σ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ)
    (p q y : Fin r → ℂ) : hermC σ G (a • p - q) y = a * hermC σ G p y - hermC σ G q y := by
  simp only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private lemma hermC_smul_sub_right_lemma_4 (σ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (a : ℂ)
    (y p q : Fin r → ℂ) :
    hermC σ G y (a • p - q) = conj a * hermC σ G y p - hermC σ G y q := by
  simp only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub, map_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private lemma hermC_ppos_lemma_5 (x : Frame X.Ψ r) (u w : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.ppos x τ u) w = hermC τ.1 X.Gm u (X.ppos x τ w) := by
  have hGp : Matrix.conjTranspose (X.gramPos x τ) = X.gramPos x τ := by
    ext a b
    exact hermC_conj τ.1 X.Gm_herm (col (mat x τ) (Fin.castLE X.p0_le b))
      (col (mat x τ) (Fin.castLE X.p0_le a))
  have hM : ∀ a b, conj ((X.gramPos x τ)⁻¹ b a) = (X.gramPos x τ)⁻¹ a b := by
    intro a b
    have h := congrFun (congrFun (show Matrix.conjTranspose ((X.gramPos x τ)⁻¹) = (X.gramPos x τ)⁻¹ by
      rw [Matrix.conjTranspose_nonsing_inv, hGp]) a) b
    exact h
  unfold Data.ppos
  rw [hermC_sum_left_lemma, hermC_sum_right_lemma_2]
  simp only [map_sum, map_mul, hM, hermC_conj τ.1 X.Gm_herm, Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

private lemma hermC_jp_lemma_6 {x : Frame X.Ψ r} (hx : x ∈ X.dom) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.jp x τ u) (X.jp x τ v) = hermC τ.1 X.Gm u v := by
  unfold Data.jp
  rw [hermC_smul_sub_left_lemma_3, hermC_smul_sub_right_lemma_4, hermC_smul_sub_right_lemma_4,
    hermC_ppos_lemma_5 X τ x u (X.ppos x τ v), X.ppos_ppos hx τ v, hermC_ppos_lemma_5 X τ x u v]
  have h2 : conj (2 : ℂ) = 2 := map_ofNat (starRingEnd ℂ) 2
  rw [h2]
  ring

private lemma maj_eq_lemma_7 (x : Frame X.Ψ r) (v : Fin r → ℂ) :
    X.maj x τ v = (hermC τ.1 X.Gm (X.jp x τ v) v).re := by
  have hP : hermC τ.1 X.Gm (X.ppos x τ v) v = ∑ a : Fin X.p0, ∑ b : Fin X.p0,
      hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le a)) * (X.gramPos x τ)⁻¹ a b *
        conj (hermC τ.1 X.Gm v (col (mat x τ) (Fin.castLE X.p0_le b))) := by
    unfold Data.ppos
    rw [hermC_sum_left_lemma]
    simp only [Finset.sum_mul, hermC_conj τ.1 X.Gm_herm]
    conv_lhs => rw [Finset.sum_comm]
  unfold Data.maj Data.posPart Data.jp
  rw [← hP, hermC_smul_sub_left_lemma_3, Complex.sub_re, Complex.mul_re]
  simp

theorem maj_jp {x : Frame X.Ψ r} (hx : x ∈ X.dom) (v : Fin r → ℂ) :
    X.maj x τ (X.jp x τ v) = X.maj x τ v := by
  rw [maj_eq_lemma_7 X τ x (X.jp x τ v), maj_eq_lemma_7 X τ x v, X.jp_jp hx τ v,
    ← hermC_conj τ.1 X.Gm_herm v (X.jp x τ v), Complex.conj_re]

theorem herm_eq_Hf_jp {x : Frame X.Ψ r} (hx : x ∈ X.dom) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm u v = X.Hf x τ u (X.jp x τ v) := by
  exact (hermC_jp_lemma_6 X τ hx u v).symm

private lemma flowMat_mulVec_lemma_10 (t : ℝ) (w : Fin r → ℂ) :
    Matrix.mulVec (X.flowMat ξ τ t) w =
      w - (I * (X.c τ : ℂ) * (t : ℂ) * hermC τ.1 X.Gm w (Data.emb τ.1 ξ)) • Data.emb τ.1 ξ := by
  funext i
  show ∑ b, X.flowMat ξ τ t i b * w b = _
  simp only [Data.flowMat, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, hermC, Data.emb]
  congr 1
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => by ring

theorem maj_flow_le {x : Frame X.Ψ r} (hx : x ∈ X.dom) (t : ℝ) (u : Fin r → ℂ) :
    X.maj x τ (Matrix.mulVec (X.flowMat ξ τ t) u) ≤
      (1 + X.c τ * |t| * X.maj x τ (Data.emb τ.1 ξ)) ^ 2 * X.maj x τ u := by
  have hHs : ∀ p q, conj (X.Hf x τ p q) = X.Hf x τ q p := by
    intro p q
    unfold Data.Hf
    rw [hermC_conj τ.1 X.Gm_herm, hermC_smul_sub_right_lemma_4, hermC_smul_sub_left_lemma_3,
      hermC_ppos_lemma_5 X τ x q p, map_ofNat]
  have hN : ∀ v, X.maj x τ v = (X.Hf x τ v v).re := fun v => maj_eq_lemma_7 X τ x v
  have hreal : ∀ v, X.Hf x τ v v = ((X.maj x τ v : ℝ) : ℂ) := by
    intro v
    rw [hN]
    exact (Complex.conj_eq_iff_re.mp (hHs v v)).symm
  have hnn : ∀ v, 0 ≤ X.maj x τ v := by
    intro v
    by_cases hv : v = 0
    · subst hv
      rw [hN]
      simp [Data.Hf, hermC]
    · exact (X.maj_pos hx τ hv).le
  have hsl : ∀ (a : ℂ) p q, X.Hf x τ (a • p) q = a * X.Hf x τ p q := by
    intro a p q
    unfold Data.Hf
    rw [X.ppos_smul_eq x τ]
    simp only [hermC, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hsr : ∀ (a : ℂ) p q, X.Hf x τ p (a • q) = conj a * X.Hf x τ p q := by
    intro a p q
    unfold Data.Hf
    simp only [hermC, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hexp : ∀ (α β : ℂ) p q, X.Hf x τ (α • p + β • q) (α • p + β • q) =
      α * conj α * X.Hf x τ p p + α * conj β * X.Hf x τ p q + β * conj α * X.Hf x τ q p +
        β * conj β * X.Hf x τ q q := by
    intro α β p q
    simp only [Hf_add_left X τ, Hf_add_right X τ, hsl, hsr]
    ring
  have hCS : ∀ p q, Complex.normSq (X.Hf x τ p q) ≤ X.maj x τ p * X.maj x τ q := by
    intro p q
    by_cases hq : q = 0
    · subst hq
      have h0 : X.Hf x τ p 0 = 0 := by simp [Data.Hf, hermC]
      rw [h0, map_zero]
      exact mul_nonneg (hnn p) (hnn 0)
    · have hn := X.maj_pos hx τ hq
      obtain ⟨z, hz⟩ : ∃ z, z = X.Hf x τ p q := ⟨_, rfl⟩
      have h0 := hnn (((X.maj x τ q : ℝ) : ℂ) • p + (-z) • q)
      rw [hN, hexp, hreal p, hreal q, ← hHs p q, ← hz] at h0
      simp only [Complex.add_re, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.conj_re,
        Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im, Complex.add_im,
        map_neg] at h0
      rw [← hz, Complex.normSq_apply]
      nlinarith [h0, hn]
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ, ℓ = hermC τ.1 X.Gm u (Data.emb τ.1 ξ) := ⟨_, rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℂ, β = I * (X.c τ : ℂ) * (t : ℂ) * ℓ := ⟨_, rfl⟩
  have hMu : Matrix.mulVec (X.flowMat ξ τ t) u = (1 : ℂ) • u + (-β) • Data.emb τ.1 ξ := by
    rw [flowMat_mulVec_lemma_10 X ξ τ t u, ← hℓ, ← hβ, one_smul, neg_smul, sub_eq_add_neg]
  obtain ⟨z, hz⟩ : ∃ z, z = X.Hf x τ u (Data.emb τ.1 ξ) := ⟨_, rfl⟩
  have hval : X.maj x τ (Matrix.mulVec (X.flowMat ξ τ t) u) = X.maj x τ u -
      2 * (conj β * z).re + Complex.normSq β * X.maj x τ (Data.emb τ.1 ξ) := by
    rw [hN, hMu, hexp, hreal u, hreal (Data.emb τ.1 ξ), ← hHs u (Data.emb τ.1 ξ), ← hz]
    have e1 : β * conj z = conj (conj β * z) := by
      rw [map_mul, Complex.conj_conj, mul_comm]
    have e2 : β * conj β = (Complex.normSq β : ℂ) := Complex.mul_conj β
    simp only [map_one, one_mul, mul_one, map_neg, neg_mul, mul_neg, neg_neg]
    rw [e1, e2]
    simp only [Complex.add_re, Complex.neg_re, Complex.conj_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    ring
  have hc0 : 0 ≤ X.c τ := by
    unfold Data.c
    positivity
  have hnβ : ‖β‖ = X.c τ * |t| * ‖ℓ‖ := by
    rw [hβ, norm_mul, norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hc0, one_mul]
  have hL : ‖ℓ‖ ^ 2 ≤ X.maj x τ u * X.maj x τ (Data.emb τ.1 ξ) := by
    rw [hℓ, herm_eq_Hf_jp X τ hx, ← Complex.normSq_eq_norm_sq, ← maj_jp X τ hx (Data.emb τ.1 ξ)]
    exact hCS _ _
  have hZ : ‖z‖ ^ 2 ≤ X.maj x τ u * X.maj x τ (Data.emb τ.1 ξ) := by
    rw [hz, ← Complex.normSq_eq_norm_sq]
    exact hCS _ _
  have hre : -(2 * (conj β * z).re) ≤ 2 * ‖β‖ * ‖z‖ := by
    have h1 := Complex.abs_re_le_norm (conj β * z)
    rw [norm_mul, Complex.norm_conj] at h1
    linarith [neg_abs_le (conj β * z).re]
  have hLZ : ‖ℓ‖ * ‖z‖ ≤ X.maj x τ u * X.maj x τ (Data.emb τ.1 ξ) := by
    nlinarith [sq_nonneg (‖ℓ‖ - ‖z‖), norm_nonneg ℓ, norm_nonneg z]
  have hk : 0 ≤ X.c τ * |t| := mul_nonneg hc0 (abs_nonneg t)
  have hb : 0 ≤ X.maj x τ (Data.emb τ.1 ξ) := hnn _
  have h1 := mul_le_mul_of_nonneg_left hLZ hk
  have h2 := mul_le_mul_of_nonneg_left hL (mul_nonneg (sq_nonneg (X.c τ * |t|)) hb)
  rw [hval, Complex.normSq_eq_norm_sq, hnβ]
  rw [hnβ] at hre
  nlinarith [h1, h2, hre]

end FlowMatrixMajorants

end ReciprocityTheory.ChartRestriction.G.FD
