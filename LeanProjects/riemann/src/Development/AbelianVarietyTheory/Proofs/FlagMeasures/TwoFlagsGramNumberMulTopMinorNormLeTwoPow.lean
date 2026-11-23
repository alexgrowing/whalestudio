import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
import Formalism.FormalDegreeBessel.FinalG
import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.Amp.LemA

section General
variable {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ}

theorem herm_add_l (u v w : Fin m → ℂ) : herm H (u + v) w = herm H u w + herm H v w := by
  simp [herm, Matrix.mulVec_add, dotProduct_add]

theorem herm_add_r (u v w : Fin m → ℂ) : herm H u (v + w) = herm H u v + herm H u w := by
  simp [herm, add_dotProduct]

theorem herm_smul_l (c : ℂ) (v w : Fin m → ℂ) : herm H (c • v) w = c * herm H v w := by
  simp [herm, Matrix.mulVec_smul, dotProduct_smul]

theorem herm_smul_r (c : ℂ) (v w : Fin m → ℂ) : herm H v (c • w) = star c * herm H v w := by
  simp [herm, smul_dotProduct]

theorem herm_sum_l {ι : Type*} (s : Finset ι) (v : ι → Fin m → ℂ) (w : Fin m → ℂ) :
    herm H (∑ i ∈ s, v i) w = ∑ i ∈ s, herm H (v i) w := by
  simp [herm, Matrix.mulVec_sum, dotProduct_sum]

theorem herm_sum_r {ι : Type*} (s : Finset ι) (v : ι → Fin m → ℂ) (w : Fin m → ℂ) :
    herm H w (∑ i ∈ s, v i) = ∑ i ∈ s, herm H w (v i) := by
  simp [herm, star_sum, sum_dotProduct]

theorem herm_conj (hH : Hᴴ = H) (v w : Fin m → ℂ) : star (herm H v w) = herm H w v := by
  unfold herm
  rw [← star_dotProduct_star, star_star, star_mulVec, hH, ← Matrix.dotProduct_mulVec]

theorem herm_isom {g : Matrix (Fin m) (Fin m) ℂ} (hg : g ∈ UH H) (v w : Fin m → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  unfold herm
  have : gᴴ * H * g = H := hg
  rw [star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, this]

theorem cs_real (A B : ℝ) (c : ℂ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h : ∀ s : ℝ, 0 ≤ A ^ 2 + 2 * s * ‖c‖ ^ 2 + s ^ 2 * ‖c‖ ^ 2 * B ^ 2) : ‖c‖ ≤ A * B := by
  have hd : discrim (‖c‖ ^ 2 * B ^ 2) (2 * ‖c‖ ^ 2) (A ^ 2) ≤ 0 :=
    discrim_le_zero fun s => by have := h s; nlinarith
  unfold discrim at hd
  rcases (norm_nonneg c).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · have h2 : 0 < ‖c‖ ^ 2 := by positivity
    have h3 : ‖c‖ ^ 2 ≤ (A * B) ^ 2 := by
      by_contra hh
      push Not at hh
      nlinarith
    exact (abs_le_of_sq_le_sq' h3 (by positivity)).2

theorem herm_cs (hH : Hᴴ = H) (u v : Fin m → ℂ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hu : herm H u u = ((A ^ 2 : ℝ) : ℂ)) (hv : herm H v v = ((B ^ 2 : ℝ) : ℂ))
    (h : ∀ t : ℂ, 0 ≤ (herm H (u + t • v) (u + t • v)).re) : ‖herm H u v‖ ≤ A * B := by
  refine cs_real A B _ hA hB fun s => ?_
  have h1 := h (s * herm H u v)
  rw [herm_add_l, herm_add_r, herm_add_r, herm_smul_l, herm_smul_l, herm_smul_r, herm_smul_r, hu, hv,
    ← herm_conj hH u v] at h1
  generalize herm H u v = c at *
  have e : ‖c‖ ^ 2 = c.re ^ 2 + c.im ^ 2 := by rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  rw [e]
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im] at h1
  nlinarith

theorem inner_eq_herm (p q : EuclideanSpace ℂ (Fin m)) (hp : H *ᵥ p.ofLp = p.ofLp) :
    ⟪q, p⟫_ℂ = herm H p.ofLp q.ofLp := by
  unfold herm
  rw [hp, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]

end General

variable {k r : ℕ}

theorem hpk_herm : (Hpk k r)ᴴ = Hpk k r := (Formalism.QuantumDeterminants.hpkFacts k r).1

theorem hpk_unit : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_left_inverse (Formalism.QuantumDeterminants.hpkFacts k r).2.1

theorem hpk_mulVec_e (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : (Hpk k r *ᵥ v) (eI k r a) = v (esI k r a) := by
  have ha := a.isLt
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (esI k r a)]
  · have : Hpk k r (eI k r a) (esI k r a) = 1 := by
      unfold Hpk; rw [if_pos]; simp only [eI, esI]; omega
    rw [this, one_mul]
  · intro j _ hj
    have hj' : j.val ≠ 2 * r + k - a.val := fun h => hj (Fin.ext h)
    have : Hpk k r (eI k r a) j = 0 := by
      unfold Hpk
      rw [if_neg, if_neg, if_neg] <;> simp only [eI] <;> omega
    rw [this, zero_mul]
  · simp

theorem herm_e (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : herm (Hpk k r) v (bvec (eI k r a)) = v (esI k r a) := by
  rw [← hpk_mulVec_e v a]
  simp [herm, bvec]

theorem herm_e_e (a b : Fin r) : herm (Hpk k r) (bvec (eI k r b)) (bvec (eI k r a)) = 0 := by
  rw [herm_e]
  have : esI k r a ≠ eI k r b := by
    intro h; have := congrArg Fin.val h; simp only [eI, esI] at this; omega
  simp [bvec, this]

theorem herm_low (v ξ : Fin (2 * r + k + 1) → ℂ) (hv : ∀ a, v (esI k r a) = 0) (hξ : ∀ i, r ≤ i.val → ξ i = 0) :
    herm (Hpk k r) v ξ = 0 := by
  unfold herm dotProduct
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i.val < r
  · have : i = eI k r ⟨i.val, hi⟩ := rfl
    rw [this, hpk_mulVec_e, hv, mul_zero]
  · simp [hξ i (by omega)]

theorem semidef (z y : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hy : ∀ a, herm (Hpk k r) y (fvec k r z a) = 0) : 0 ≤ (herm (Hpk k r) y y).re := by
  have hy1 : ∀ a, y (esI k r a) = 0 := fun a => by
    have := hy a.castSucc
    simp only [fvec, Fin.val_castSucc, a.isLt, dif_pos, Fin.eta] at this
    rwa [herm_e] at this
  have hy2 : herm (Hpk k r) y z = 0 := by
    have := hy (Fin.last r)
    simpa [fvec] using this
  set ξ : Fin (2 * r + k + 1) → ℂ := fun i => if i.val < r then -y i else 0 with hξ
  have hξ1 : ∀ i, r ≤ i.val → ξ i = 0 := fun i hi => by simp [hξ, not_lt.2 hi]
  have hξ2 : ∀ a, ξ (esI k r a) = 0 := fun a => hξ1 _ (by have := a.isLt; simp only [esI]; omega)
  have h1 : herm (Hpk k r) y ξ = 0 := herm_low _ _ hy1 hξ1
  have h2 : herm (Hpk k r) ξ y = 0 := by rw [← herm_conj hpk_herm, h1, star_zero]
  have h3 : herm (Hpk k r) ξ ξ = 0 := herm_low _ _ hξ2 hξ1
  have h4 : herm (Hpk k r) z ξ = 0 :=
    herm_low _ _ (fun a => hz _ (Or.inr (by have := a.isLt; simp only [esI]; omega))) hξ1
  have h5 : herm (Hpk k r) ξ z = 0 := by rw [← herm_conj hpk_herm, h4, star_zero]
  have hm : inWb k r (y + ξ) := by
    rintro i (hi | hi)
    · simp [hξ, hi]
    · have e : i = esI k r ⟨2 * r + k - i.val, by omega⟩ := Fin.ext (by simp only [esI]; omega)
      rw [Pi.add_apply, hξ1 i (by omega), e, hy1, add_zero]
  have h6 : herm (Hpk k r) (y + ξ) (y + ξ) = herm (Hpk k r) y y := by
    rw [herm_add_l, herm_add_r, herm_add_r, h1, h2, h3]; ring
  by_contra hneg
  push Not at hneg
  have hT' : (herm (Hpk k r) z z).re < 0 := by unfold Tz at hT; linarith
  have := Formalism.QuantumDeterminants.revCS k r z (y + ξ) hz hm hT' (by rwa [h6])
  rw [herm_add_l, hy2, h5, add_zero, map_zero] at this
  have h7 : 0 < Tz k r (y + ξ) := by unfold Tz; rw [h6]; linarith
  nlinarith [mul_pos hT h7]

def Zm (k r : ℕ) (γ : Mat k r) : Matrix (Fin r) (Fin r) ℂ := fun a b =>
  herm (Hpk k r) (γ *ᵥ bvec (eI k r b)) (bvec (eI k r a))

theorem Dr_eq (z z' : Fin (2 * r + k + 1) → ℂ) (γ : Mat k r) : Dr k r z z' γ = ‖(Zm k r γ).det‖ := by
  unfold Dr Dmin
  congr 2
  ext a b
  have ha : a.val < r := a.isLt
  have hb : b.val < r := b.isLt
  simp [Zhat, fvec, Zm, ha, hb]

theorem inv_cancel {g : Mat k r} (hg : g ∈ GG k r) (v : Fin (2 * r + k + 1) → ℂ) : g *ᵥ (g⁻¹ *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((uHGroup _ _ hpk_unit).2.2 g hg).1, Matrix.one_mulVec]

theorem herm_inv {g : Mat k r} (hg : g ∈ GG k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v (g⁻¹ *ᵥ w) = herm (Hpk k r) (g *ᵥ v) w := by
  rw [← herm_isom hg, inv_cancel hg]

theorem Zm_inv {γ : Mat k r} (hγ : γ ∈ GG k r) : Zm k r γ⁻¹ = (Zm k r γ)ᴴ := by
  ext a b
  simp only [Zm, conjTranspose_apply]
  rw [← herm_inv hγ, herm_conj hpk_herm]

theorem decomp {z z' : Fin (2 * r + k + 1) → ℂ} {γ x : Mat k r} (p : Ppos k r z z' γ x) :
    Hpk k r *ᵥ p.1.ofLp = p.1.ofLp ∧ ∃ w ∈ Hcom k r z z' γ, ∃ c : Fin r → ℂ,
      x *ᵥ p.1.ofLp = w + ∑ a, c a • bvec (eI k r a) := by
  obtain ⟨p, h1, h2⟩ := p
  refine ⟨?_, ?_⟩
  · have : (Hpk k r - 1) *ᵥ p.ofLp = 0 := h1
    rwa [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
  · have : x *ᵥ p.ofLp ∈ Hcom k r z z' γ ⊔ Xsp k r := h2
    obtain ⟨w, hw, ξ, hξ, e⟩ := Submodule.mem_sup.1 this
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hξ
    exact ⟨w, hw, c, e.symm⟩

theorem fvec_cast (z : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : fvec k r z a.castSucc = bvec (eI k r a) := by
  simp [fvec]

theorem alg (Z : Matrix (Fin r) (Fin r) ℂ) (hZ : IsUnit Z.det) (c d : Fin r → ℂ) :
    ∑ a, ∑ b, (Z *ᵥ c) a * (d ᵥ* Z) b * Z⁻¹ᵀ a b = d ⬝ᵥ (Z *ᵥ c) := by
  have : d = (d ᵥ* Z) ᵥ* Z⁻¹ := by rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hZ, Matrix.vecMul_one]
  conv_rhs => rw [this]
  generalize Z *ᵥ c = u
  generalize d ᵥ* Z = v
  simp only [dotProduct, Matrix.vecMul, transpose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem herm_self_norm {p : EuclideanSpace ℂ (Fin (2 * r + k + 1))} (hp : Hpk k r *ᵥ p.ofLp = p.ofLp) :
    herm (Hpk k r) p.ofLp p.ofLp = ((‖p‖ ^ 2 : ℝ) : ℂ) := by
  rw [← inner_eq_herm p p hp, inner_self_eq_norm_sq_to_K]; simp

theorem form_bound {z z' : Fin (2 * r + k + 1) → ℂ} {γ x : Mat k r} (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hγ : γ ∈ GG k r) (hx : x ∈ GG k r) (hZ : IsUnit (Zm k r γ).det)
    (p : Ppos k r z z' γ x) (q : Ppos k r z' z γ⁻¹ (γ * x)) :
    ‖∑ a, ∑ b, ⟪(WithLp.toLp 2 (x⁻¹ *ᵥ (γ⁻¹ *ᵥ bvec (eI k r a))) : EuclideanSpace ℂ _), p.1⟫_ℂ *
      starRingEnd ℂ ⟪(WithLp.toLp 2 ((γ * x)⁻¹ *ᵥ (γ⁻¹⁻¹ *ᵥ bvec (eI k r b))) : EuclideanSpace ℂ _), q.1⟫_ℂ *
      (Zm k r γ)⁻¹ᵀ a b‖ ≤ 2 * ‖p‖ * ‖q‖ := by
  have hγγ : γ⁻¹⁻¹ = γ := Matrix.nonsing_inv_nonsing_inv _ ((uHGroup _ _ hpk_unit).2.2 γ hγ).1
  have hγx : γ * x ∈ GG k r := (uHGroup _ _ hpk_unit).2.1 γ hγ x hx
  obtain ⟨hp, w, hw, c, ep⟩ := decomp p
  obtain ⟨hq, y₂, hy₂, d, eq⟩ := decomp q
  set y₁ := γ *ᵥ w with hy₁
  set ξ₁ := ∑ a, c a • γ *ᵥ bvec (eI k r a) with hξ₁
  set ξ₂ := ∑ a, d a • bvec (eI k r a) with hξ₂
  have ep' : (γ * x) *ᵥ p.1.ofLp = y₁ + ξ₁ := by
    rw [← Matrix.mulVec_mulVec, ep, Matrix.mulVec_add, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul, hy₁, hξ₁]
  have a1 : ∀ a, herm (Hpk k r) y₁ (fvec k r z a) = 0 := fun a => by rw [hy₁, ← herm_inv hγ]; exact (hw a).2
  have a2 : ∀ a, herm (Hpk k r) y₁ (γ *ᵥ fvec k r z' a) = 0 := fun a => by rw [hy₁, herm_isom hγ]; exact (hw a).1
  have b1 : ∀ a, herm (Hpk k r) y₂ (fvec k r z a) = 0 := fun a => (hy₂ a).1
  have b2 : ∀ a, herm (Hpk k r) y₂ (γ *ᵥ fvec k r z' a) = 0 := fun a => by have := (hy₂ a).2; rwa [hγγ] at this
  have a1' : ∀ a, herm (Hpk k r) y₁ (bvec (eI k r a)) = 0 := fun a => by rw [← fvec_cast z]; exact a1 _
  have a2' : ∀ a, herm (Hpk k r) y₁ (γ *ᵥ bvec (eI k r a)) = 0 := fun a => by rw [← fvec_cast z']; exact a2 _
  have b1' : ∀ a, herm (Hpk k r) y₂ (bvec (eI k r a)) = 0 := fun a => by rw [← fvec_cast z]; exact b1 _
  have b2' : ∀ a, herm (Hpk k r) y₂ (γ *ᵥ bvec (eI k r a)) = 0 := fun a => by rw [← fvec_cast z']; exact b2 _
  have c11 : herm (Hpk k r) y₁ ξ₁ = 0 := by simp [hξ₁, herm_sum_r, herm_smul_r, a2']
  have c12 : herm (Hpk k r) y₁ ξ₂ = 0 := by simp [hξ₂, herm_sum_r, herm_smul_r, a1']
  have c21 : herm (Hpk k r) y₂ ξ₁ = 0 := by simp [hξ₁, herm_sum_r, herm_smul_r, b2']
  have c22 : herm (Hpk k r) y₂ ξ₂ = 0 := by simp [hξ₂, herm_sum_r, herm_smul_r, b1']
  have d11 : herm (Hpk k r) ξ₁ y₁ = 0 := by rw [← herm_conj hpk_herm, c11, star_zero]
  have d21 : herm (Hpk k r) ξ₁ y₂ = 0 := by rw [← herm_conj hpk_herm, c21, star_zero]
  have d22 : herm (Hpk k r) ξ₂ y₂ = 0 := by rw [← herm_conj hpk_herm, c22, star_zero]
  have e1 : herm (Hpk k r) ξ₁ ξ₁ = 0 := by
    simp [hξ₁, herm_sum_r, herm_smul_r, herm_sum_l, herm_smul_l, herm_isom hγ, herm_e_e]
  have e2 : herm (Hpk k r) ξ₂ ξ₂ = 0 := by
    simp [hξ₂, herm_sum_r, herm_smul_r, herm_sum_l, herm_smul_l, herm_e_e]
  have n1 : herm (Hpk k r) y₁ y₁ = ((‖p.1‖ ^ 2 : ℝ) : ℂ) := by
    rw [← herm_self_norm hp, ← herm_isom hγx p.1.ofLp, ep', herm_add_l, herm_add_r, herm_add_r, c11, d11, e1]; ring
  have n2 : herm (Hpk k r) y₂ y₂ = ((‖q.1‖ ^ 2 : ℝ) : ℂ) := by
    rw [← herm_self_norm hq, ← herm_isom hγx q.1.ofLp, eq, herm_add_l, herm_add_r, herm_add_r, c22, d22, e2]; ring
  have cs : ‖herm (Hpk k r) y₁ y₂‖ ≤ ‖p.1‖ * ‖q.1‖ :=
    herm_cs hpk_herm _ _ _ _ (norm_nonneg _) (norm_nonneg _) n1 n2 fun t =>
      semidef z _ hz hT fun a => by rw [herm_add_l, herm_smul_l, a1, b1]; ring
  have m1 : ⟪q.1, p.1⟫_ℂ = herm (Hpk k r) y₁ y₂ + herm (Hpk k r) ξ₁ ξ₂ := by
    rw [inner_eq_herm _ _ hp, ← herm_isom hγx p.1.ofLp, ep', eq, herm_add_l, herm_add_r, herm_add_r, c12, d21]; ring
  have u1 : ∀ a, ⟪(WithLp.toLp 2 (x⁻¹ *ᵥ (γ⁻¹ *ᵥ bvec (eI k r a))) : EuclideanSpace ℂ _), p.1⟫_ℂ =
      (Zm k r γ *ᵥ c) a := fun a => by
    rw [inner_eq_herm _ _ hp, WithLp.ofLp_toLp, herm_inv hx, herm_inv hγ, Matrix.mulVec_mulVec, ep', herm_add_l, a1',
      zero_add, hξ₁, herm_sum_l]
    simp only [herm_smul_l]
    simp only [Zm, Matrix.mulVec, dotProduct, mul_comm]
  have u2 : ∀ b, starRingEnd ℂ
      ⟪(WithLp.toLp 2 ((γ * x)⁻¹ *ᵥ (γ⁻¹⁻¹ *ᵥ bvec (eI k r b))) : EuclideanSpace ℂ _), q.1⟫_ℂ =
      (star d ᵥ* Zm k r γ) b := fun b => by
    rw [inner_eq_herm _ _ hq, WithLp.ofLp_toLp, herm_inv hγx, eq, show γ⁻¹⁻¹ *ᵥ bvec (eI k r b) = γ *ᵥ bvec (eI k r b) by rw [hγγ],
      herm_add_l, b2', zero_add, starRingEnd_apply, herm_conj hpk_herm, hξ₂, herm_sum_r]
    simp only [herm_smul_r]
    rfl
  have u3 : star d ⬝ᵥ (Zm k r γ *ᵥ c) = herm (Hpk k r) ξ₁ ξ₂ := by
    rw [hξ₂, herm_sum_r]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [herm_smul_r, hξ₁, herm_sum_l]
    simp only [herm_smul_l]
    simp only [Zm, Matrix.mulVec, dotProduct, mul_comm, Pi.star_apply]
  simp only [u1, u2]
  rw [alg _ hZ, u3, show herm (Hpk k r) ξ₁ ξ₂ = ⟪q.1, p.1⟫_ℂ - herm (Hpk k r) y₁ y₂ by rw [m1]; ring]
  have := norm_inner_le_norm (𝕜 := ℂ) q.1 p.1
  have h2 := norm_sub_le ⟪q.1, p.1⟫_ℂ (herm (Hpk k r) y₁ y₂)
  change _ ≤ 2 * ‖p.1‖ * ‖q.1‖
  nlinarith

theorem gramProj_eq {n : ℕ} (P : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (v : Fin r → Fin n → ℂ) :
    gramProj P v = Real.sqrt ‖(Matrix.gram ℂ fun a => P.orthogonalProjectionOnto (WithLp.toLp 2 (v a))).det‖ := rfl

theorem Yv_mul_Yv_mul_Dr_le : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (γ : Mat k r), TwoFl k r z z' γ →
    ∀ x ∈ GG k r, Yv k r z z' γ x * Yv k r z' z γ⁻¹ (γ * x) * Dr k r z z' γ ≤ 2 ^ r := by
  intro k r z z' γ ⟨hz, _, hT, _, hγ, _, hD⟩ x hx
  have hD' : (Zm k r γ).det ≠ 0 := by rw [Dr_eq] at hD; exact norm_ne_zero_iff.1 hD
  have hZ : IsUnit (Zm k r γ).det := hD'.isUnit
  have h := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.absA (Ppos k r z z' γ x) (Ppos k r z' z γ⁻¹ (γ * x)) r
    (fun a => (Ppos k r z z' γ x).orthogonalProjectionOnto (WithLp.toLp 2 (x⁻¹ *ᵥ (γ⁻¹ *ᵥ bvec (eI k r a)))))
    (fun a => (Ppos k r z' z γ⁻¹ (γ * x)).orthogonalProjectionOnto
      (WithLp.toLp 2 ((γ * x)⁻¹ *ᵥ (γ⁻¹⁻¹ *ᵥ bvec (eI k r a))))) (Zm k r γ)⁻¹ᵀ (fun p q => by
        simp only [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right]
        exact form_bound hz hT hγ hx hZ p q)
  rw [← gramProj_eq, ← gramProj_eq, det_transpose, det_nonsing_inv, Ring.inverse_eq_inv', norm_inv] at h
  unfold Yv
  rw [Dr_eq, Dr_eq, Zm_inv hγ, det_conjTranspose, norm_star]
  have h0 : ‖(Zm k r γ).det‖ ≠ 0 := norm_ne_zero_iff.2 hD'
  refine le_of_eq_of_le ?_ h
  field_simp

end GlobalTheory.Amp.LemA
