import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods

open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.PeriodChart

section Abstract

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem symm_contraction (F F₀ : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (N : V →ₗ⋆[ℂ] V)
    (hF : ∀ z w, F z w = starRingEnd ℂ (F w z))
    (hp : ∀ z, z ≠ 0 → 0 < (F z z).re) (hp₀ : ∀ z, z ≠ 0 → 0 < (F₀ z z).re)
    (h : ∀ z w, (F (z + N z) (w + N w)).im = (F₀ z w).im) :
    (∀ z w, F₀ (N z) w = F₀ (N w) z) ∧ ∀ z, z ≠ 0 → (F₀ (N z) (N z)).re < (F₀ z z).re := by

  have expand : ∀ (s t : ℂ) (z w : V), F (s • z + N (s • z)) (t • w + N (t • w)) =
      s * starRingEnd ℂ t * F z w + starRingEnd ℂ s * t * F (N z) (N w) +
      starRingEnd ℂ s * starRingEnd ℂ t * F (N z) w + s * t * F z (N w) := by
    intro s t z w
    simp only [map_add, map_smul, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      Complex.conj_conj]
    ring
  have expand₀ : ∀ (s t : ℂ) (z w : V), F₀ (s • z) (t • w) = s * starRingEnd ℂ t * F₀ z w := by
    intro s t z w
    simp only [map_smul, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
    ring
  have key : ∀ z w, F z (N w) = F w (N z) ∧ F₀ z w = F z w - F (N w) (N z) := by
    intro z w
    have E : ∀ s t : ℂ, (s * starRingEnd ℂ t * F z w + starRingEnd ℂ s * t * F (N z) (N w) +
        starRingEnd ℂ s * starRingEnd ℂ t * F (N z) w + s * t * F z (N w)).im =
        (s * starRingEnd ℂ t * F₀ z w).im := by
      intro s t
      rw [← expand, ← expand₀]
      exact h _ _
    have E11 := E 1 1
    have EII := E Complex.I Complex.I
    have E1I := E 1 Complex.I
    have EI1 := E Complex.I 1
    simp only [map_one, Complex.conj_I, one_mul, mul_one, Complex.add_im, Complex.mul_im, Complex.mul_re,
      Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im] at E11 EII E1I EI1
    have hre : (F z (N w)).re = (F (N z) w).re := by linarith
    have him : (F z (N w)).im = -(F (N z) w).im := by linarith
    have hc : F z (N w) = starRingEnd ℂ (F (N z) w) := Complex.ext (by simp [hre]) (by simp [him])
    refine ⟨?_, ?_⟩
    · rw [hc, hF (N z) w, Complex.conj_conj]
    · rw [hF (N w) (N z)]
      apply Complex.ext
      · simp only [Complex.sub_re, Complex.conj_re]; linarith
      · simp only [Complex.sub_im, Complex.conj_im]; linarith
  refine ⟨fun z w => ?_, fun z hz => ?_⟩
  · rw [(key (N z) w).2, (key (N w) z).2]
    have h1 : F (N z) w = F (N w) z := by
      rw [hF (N z) w, (key w z).1, ← hF (N w) z]
    rw [h1, (key (N w) (N z)).1]
  · have hA : F₀ z z = F z z - F (N z) (N z) := (key z z).2
    have hB : F₀ (N z) (N z) = F (N z) (N z) - F (N (N z)) (N (N z)) := (key (N z) (N z)).2
    have hC : F z (N (N z)) = F (N z) (N z) := (key z (N z)).1
    have hC' : F (N (N z)) z = F (N z) (N z) := by
      rw [hF (N (N z)) z, hC, ← hF (N z) (N z)]
    by_cases hz2 : z - N (N z) = 0
    · have hNN : N (N z) = z := (sub_eq_zero.mp hz2).symm
      have hneg : F₀ (N z) (N z) = -F₀ z z := by rw [hB, hA, hNN]; ring
      rw [hneg, Complex.neg_re]
      have := hp₀ z hz
      linarith
    · have hpos := hp _ hz2
      have hD : F (z - N (N z)) (z - N (N z)) = F₀ z z - F₀ (N z) (N z) := by
        rw [hA, hB]
        simp only [map_sub, LinearMap.sub_apply]
        rw [hC, hC']
        try ring
      rw [hD, Complex.sub_re] at hpos
      linarith

theorem exists_lin_anti (T : V →+ V) (hT : ∀ (r : ℝ) z, T ((r : ℂ) • z) = (r : ℂ) • T z) :
    ∃ (A : V →ₗ[ℂ] V) (C : V →ₗ⋆[ℂ] V), ∀ z, T z = A z + C z := by
  have hTI : ∀ z, T (Complex.I • Complex.I • z) = -T z := by
    intro z
    rw [smul_smul, Complex.I_mul_I, neg_smul, one_smul, map_neg]
  have hTc : ∀ (c : ℂ) z, T (c • z) = (c.re : ℂ) • T z + (c.im : ℂ) • T (Complex.I • z) := by
    intro c z
    conv_lhs => rw [← Complex.re_add_im c, add_smul, mul_smul, map_add, hT, hT]
  refine ⟨{ toFun := fun z => (1 / 2 : ℂ) • (T z - Complex.I • T (Complex.I • z)),
            map_add' := ?_, map_smul' := ?_ },
          { toFun := fun z => (1 / 2 : ℂ) • (T z + Complex.I • T (Complex.I • z)),
            map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y
    simp only [smul_add, map_add]
    module
  · intro c z
    simp only [RingHom.id_apply]
    rw [hTc c z, smul_comm Complex.I c z, hTc c (Complex.I • z), hTI]
    conv_rhs => rw [← Complex.re_add_im c]
    match_scalars <;>
      first
      | ring1
      | linear_combination ((c.im : ℂ) / 2) * Complex.I_sq
  · intro x y
    simp only [smul_add, map_add]
    module
  · intro c z
    rw [hTc c z, smul_comm Complex.I c z, hTc c (Complex.I • z), hTI]
    conv_rhs => rw [← Complex.re_add_im c]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    match_scalars <;>
      first
      | ring1
      | linear_combination ((c.im : ℂ) / 2) * Complex.I_sq
  · intro z
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    module

theorem lin_anti_unique (A A' C C' : V → V) (hA : ∀ z, A (Complex.I • z) = Complex.I • A z)
    (hA' : ∀ z, A' (Complex.I • z) = Complex.I • A' z) (hC : ∀ z, C (Complex.I • z) = -Complex.I • C z)
    (hC' : ∀ z, C' (Complex.I • z) = -Complex.I • C' z) (h : ∀ z, A z + C z = A' z + C' z) (z : V) :
    A z = A' z ∧ C z = C' z := by
  have h1 := h z
  have h2 := h (Complex.I • z)
  rw [hA, hA', hC, hC'] at h2
  have h3 : Complex.I • (A z - A' z) = Complex.I • (C z - C' z) := by
    linear_combination (norm := module) h2
  have h4 : A z - A' z = C z - C' z := smul_right_injective V Complex.I_ne_zero h3
  have h5 : (2 : ℂ) • (C z - C' z) = 0 := by
    linear_combination (norm := module) h1 - h4
  have hC0 : C z = C' z := by
    rcases smul_eq_zero.mp h5 with h6 | h6
    · norm_num at h6
    · exact sub_eq_zero.mp h6
  refine ⟨?_, hC0⟩
  rw [hC0] at h1
  exact add_right_cancel h1

end Abstract

theorem exists_param {ι : Type} [Fintype ι] (R : ι → ι → Prop) (s : ι → Prop) (hR : ∀ i j, R i j → R j i)
    (hs : ∀ i j, R i j → (s i ↔ ¬ s j)) :
    ∃ (m : ℕ) (L : (Fin m → ℂ) →ₗ[ℂ] Matrix ι ι ℂ), 2 * m = Nat.card {x : ι × ι // R x.1 x.2} ∧
      Function.Injective L ∧ ∀ W : Matrix ι ι ℂ, (∃ b, L b = W) ↔ Wᵀ = W ∧ ∀ i j, ¬ R i j → W i j = 0 := by
  classical

  obtain ⟨e⟩ : Nonempty ({x : ι × ι // R x.1 x.2 ∧ s x.1} ≃ Fin (Nat.card {x : ι × ι // R x.1 x.2 ∧ s x.1})) :=
    ⟨Finite.equivFin _⟩
  have hflip : ∀ i j, R i j → ¬ s i → s j := fun i j hr hsi =>
    not_not.mp (mt (hs i j hr).mpr hsi)
  refine ⟨Nat.card {x : ι × ι // R x.1 x.2 ∧ s x.1},
    { toFun := fun b => Matrix.of fun i j =>
        if h : R i j ∧ s i then b (e ⟨(i, j), h⟩)
        else if h' : R j i ∧ s j then b (e ⟨(j, i), h'⟩) else 0
      map_add' := fun b b' => by
        ext i j
        simp only [Matrix.add_apply, Matrix.of_apply]
        split_ifs <;> simp
      map_smul' := fun c b => by
        ext i j
        simp only [Matrix.smul_apply, Matrix.of_apply, RingHom.id_apply]
        split_ifs <;> simp }, ?_, ?_, ?_⟩
  ·
    have eqv : {x : ι × ι // R x.1 x.2} ≃
        {x : ι × ι // R x.1 x.2 ∧ s x.1} ⊕ {x : ι × ι // R x.1 x.2 ∧ s x.1} :=
      { toFun := fun x => if h : s x.1.1 then Sum.inl ⟨x.1, x.2, h⟩
          else Sum.inr ⟨x.1.swap, hR _ _ x.2, hflip _ _ x.2 h⟩
        invFun := Sum.elim (fun k => ⟨k.1, k.2.1⟩) (fun k => ⟨k.1.swap, hR _ _ k.2.1⟩)
        left_inv := by
          rintro ⟨⟨i, j⟩, hr⟩
          by_cases h : s i <;> simp [h]
        right_inv := by
          rintro (⟨⟨i, j⟩, hr, hsi⟩ | ⟨⟨i, j⟩, hr, hsi⟩)
          · simp [hsi]
          · have : ¬ s j := (hs i j hr).mp hsi
            simp [this] }
    rw [Nat.card_congr eqv, Nat.card_sum]
    ring
  · intro b b' hbb
    funext n
    obtain ⟨⟨⟨i, j⟩, hr, hsi⟩, rfl⟩ := e.surjective n
    have := congrFun (congrFun hbb i) j
    simpa [Matrix.of_apply, hr, hsi] using this
  · intro W
    constructor
    · rintro ⟨b, rfl⟩
      refine ⟨?_, ?_⟩
      · ext i j
        simp only [Matrix.transpose_apply, LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
        by_cases h1 : R i j ∧ s i
        · have h2 : ¬ (R j i ∧ s j) := fun h => (hs _ _ h1.1).mp h1.2 h.2
          simp only [dif_pos h1, dif_neg h2]
        · by_cases h2 : R j i ∧ s j
          · simp only [dif_pos h2, dif_neg h1]
          · simp only [dif_neg h1, dif_neg h2]
      · intro i j hij
        simp only [LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
        rw [dif_neg (fun h : R i j ∧ s i => hij h.1), dif_neg (fun h : R j i ∧ s j => hij (hR _ _ h.1))]
    · rintro ⟨hW, hz⟩
      refine ⟨fun n => W (e.symm n).1.1 (e.symm n).1.2, ?_⟩
      ext i j
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Matrix.of_apply]
      by_cases h1 : R i j ∧ s i
      · rw [dif_pos h1, Equiv.symm_apply_apply]
      · by_cases h2 : R j i ∧ s j
        · rw [dif_neg h1, dif_pos h2, Equiv.symm_apply_apply]
          simpa using congrFun (congrFun hW i) j
        · rw [dif_neg h1, dif_neg h2]
          refine (hz i j fun hr => ?_).symm
          by_cases hsi : s i
          · exact h1 ⟨hr, hsi⟩
          · exact h2 ⟨hR _ _ hr, hflip _ _ hr hsi⟩

section Mat

variable {g : ℕ}

noncomputable def sesq (G : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (hermForm G)
    (fun x y z => by simp [hermForm]) (fun c x z => by simp [hermForm])
    (fun x y z => by simp [hermForm, mulVec_add]) (fun c x z => by simp [hermForm, mulVec_smul])

theorem sesq_apply (G : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) : sesq G z w = hermForm G z w := rfl

noncomputable def anti (Z : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ⋆[ℂ] (Fin g → ℂ) where
  toFun z := Z *ᵥ star z
  map_add' x y := by simp [mulVec_add]
  map_smul' c x := by simp [mulVec_smul]

theorem anti_apply (Z : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) : anti Z z = Z *ᵥ star z := rfl

theorem star_single (k : Fin g) : star (Pi.single k (1 : ℂ) : Fin g → ℂ) = Pi.single k 1 := by
  funext i
  by_cases h : i = k
  · subst h; simp
  · simp [h]

theorem star_mulVec' (B : Matrix (Fin g) (Fin g) ℂ) (w : Fin g → ℂ) :
    star (B *ᵥ w) = B.map (starRingEnd ℂ) *ᵥ star w := by
  funext i
  simp only [Pi.star_apply, mulVec, dotProduct, Matrix.map_apply, star_sum, star_mul', Complex.star_def]

theorem sesq_single (G : Matrix (Fin g) (Fin g) ℂ) (i j : Fin g) :
    sesq G (Pi.single i 1) (Pi.single j 1) = G i j := by
  rw [sesq_apply, hermForm, star_single]
  simp [mulVec, dotProduct, Pi.single_apply]

theorem sesq_mulVec_left (G A : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    sesq G (A *ᵥ z) w = sesq (Aᵀ * G) z w := by
  rw [sesq_apply, sesq_apply, hermForm, hermForm, ← mulVec_mulVec, dotProduct_mulVec z Aᵀ, vecMul_transpose]

theorem sesq_mulVec_right (G A : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    sesq G z (A *ᵥ w) = sesq (G * A.map (starRingEnd ℂ)) z w := by
  rw [sesq_apply, sesq_apply, hermForm, hermForm, star_mulVec', mulVec_mulVec]

theorem isHermitian_iff (G : Matrix (Fin g) (Fin g) ℂ) :
    G.IsHermitian ↔ ∀ z w, sesq G z w = starRingEnd ℂ (sesq G w z) := by
  constructor
  · intro hG z w
    rw [sesq_apply, sesq_apply, hermForm, hermForm]
    simp only [dotProduct, mulVec, map_sum, map_mul, Finset.mul_sum, Pi.star_apply, Complex.star_def,
      Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hij : starRingEnd ℂ (G i j) = G j i := by
      have := congrFun (congrFun hG j) i
      simpa [Matrix.conjTranspose_apply, Complex.star_def] using this
    rw [hij]
    ring
  · intro h
    ext i j
    have := h (Pi.single j 1) (Pi.single i 1)
    rw [sesq_single, sesq_single] at this
    simp [Matrix.conjTranspose_apply, this]

theorem exists_anti (N : (Fin g → ℂ) →ₗ⋆[ℂ] (Fin g → ℂ)) : ∃ Z, N = anti Z := by
  refine ⟨Matrix.of fun i j => N (Pi.single j 1) i, ?_⟩
  ext z i
  have hz : z = ∑ j, z j • (Pi.single j (1 : ℂ) : Fin g → ℂ) := by
    funext k
    simp [Pi.single_apply]
  rw [anti_apply]
  conv_lhs => rw [hz]
  simp only [map_sum, LinearMap.map_smulₛₗ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct,
    Matrix.of_apply, Pi.star_apply, Complex.star_def]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem anti_inj {Z Z' : Matrix (Fin g) (Fin g) ℂ} (h : ∀ z, anti Z z = anti Z' z) : Z = Z' := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [anti_apply, star_single, mulVec, dotProduct, Pi.single_apply] using this

theorem anti_symm_iff (G Z : Matrix (Fin g) (Fin g) ℂ) :
    (∀ z w, sesq G (anti Z z) w = sesq G (anti Z w) z) ↔ (Gᵀ * Z)ᵀ = Gᵀ * Z := by
  have key : ∀ z w, sesq G (anti Z z) w = star z ⬝ᵥ ((Zᵀ * G) *ᵥ star w) := by
    intro z w
    rw [anti_apply, sesq_mulVec_left, sesq_apply, hermForm]
  have tr : (Gᵀ * Z)ᵀ = Zᵀ * G := by rw [transpose_mul, transpose_transpose]
  constructor
  · intro h
    rw [tr]
    ext i j
    have := h (Pi.single i 1) (Pi.single j 1)
    rw [key, key, star_single, star_single] at this
    have e1 : (Pi.single i (1 : ℂ) : Fin g → ℂ) ⬝ᵥ ((Zᵀ * G) *ᵥ Pi.single j 1) = (Zᵀ * G) i j := by
      simp [mulVec, dotProduct, Pi.single_apply]
    have e2 : (Pi.single j (1 : ℂ) : Fin g → ℂ) ⬝ᵥ ((Zᵀ * G) *ᵥ Pi.single i 1) = (Zᵀ * G) j i := by
      simp [mulVec, dotProduct, Pi.single_apply]
    rw [e1, e2] at this
    rw [this, ← transpose_apply (Zᵀ * G) i j, transpose_mul, transpose_transpose]
  · intro h z w
    have e : Zᵀ * G = Gᵀ * Z := tr.symm.trans h
    have hM : (Zᵀ * G)ᵀ = Zᵀ * G := by rw [transpose_mul, transpose_transpose, e]
    rw [key, key, dotProduct_mulVec, ← mulVec_transpose, hM, dotProduct_comm]

theorem isUnit_det_of_ker (M : Matrix (Fin g) (Fin g) ℂ) (h : ∀ z, z ≠ 0 → M *ᵥ z ≠ 0) : IsUnit M.det := by
  rw [isUnit_iff_ne_zero]
  intro hd
  obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  exact h v hv h0

theorem exists_herm (G Z : Matrix (Fin g) (Fin g) ℂ) (hG : G.IsHermitian)
    (hs : ∀ z w, sesq G (anti Z z) w = sesq G (anti Z w) z)
    (hc : ∀ z, z ≠ 0 → (sesq G (anti Z z) (anti Z z)).re < (sesq G z z).re) :
    ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z, z ≠ 0 → 0 < (sesq Hm z z).re) ∧
      ∀ z w, (sesq Hm (z + anti Z z) (w + anti Z w)).im = (sesq G z w).im := by
  have hH := (isHermitian_iff G).1 hG
  set N := anti Z with hN
  set M : Matrix (Fin g) (Fin g) ℂ := 1 - Z * Z.map (starRingEnd ℂ) with hM

  have hMv : ∀ u, M *ᵥ u = u - N (N u) := by
    intro u
    simp only [hM, hN, Matrix.sub_mulVec, Matrix.one_mulVec, anti_apply, star_mulVec', star_star,
      Matrix.mulVec_mulVec]

  have hsq : ∀ a b, sesq G a (N (N b)) = sesq G (N (N a)) b := by
    intro a b
    rw [hH a, hs (N b) a, hs (N a) b, hH (N b) (N a)]

  have hinj : ∀ u, M *ᵥ u = 0 → u = 0 := by
    intro u hu
    rw [hMv, sub_eq_zero] at hu
    by_contra h0
    have hNu : N u ≠ 0 := by
      intro h1
      apply h0
      rw [hu, h1, map_zero]
    have h1 := hc u h0
    have h2 := hc (N u) hNu
    rw [← hu] at h2
    linarith
  have hdet : IsUnit M.det := isUnit_det_of_ker M (fun z hz h => hz (hinj z h))
  have hMMi : ∀ x, M *ᵥ (M⁻¹ *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hMiM : ∀ x, M⁻¹ *ᵥ (M *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

  have hcomm : ∀ z, M⁻¹ *ᵥ (z + N z) = M⁻¹ *ᵥ z + N (M⁻¹ *ᵥ z) := by
    intro z
    have e : z + N z = M *ᵥ (M⁻¹ *ᵥ z + N (M⁻¹ *ᵥ z)) := by
      conv_lhs => rw [← hMMi z]
      simp only [hMv, map_add, map_sub]
      abel
    rw [e, hMiM]
  have hF : ∀ x y, sesq ((M⁻¹)ᵀ * G) x y = sesq G (M⁻¹ *ᵥ x) y :=
    fun x y => (sesq_mulVec_left G M⁻¹ x y).symm
  refine ⟨(M⁻¹)ᵀ * G, ?_, ?_, ?_⟩
  · rw [isHermitian_iff]
    intro x y
    rw [hF, hF, ← hH]
    conv_lhs => rw [← hMMi y]
    conv_rhs => rw [← hMMi x]
    rw [hMv, hMv, map_sub, map_sub, LinearMap.sub_apply, hsq]
  · intro x hx
    have hu : M⁻¹ *ᵥ x ≠ 0 := by
      intro h
      apply hx
      rw [← hMMi x, h, Matrix.mulVec_zero]
    have e : sesq G (M⁻¹ *ᵥ x) x = sesq G (M⁻¹ *ᵥ x) (M *ᵥ (M⁻¹ *ᵥ x)) := by rw [hMMi]
    rw [hF, e, hMv, map_sub, hsq, hs (N (M⁻¹ *ᵥ x)) (M⁻¹ *ᵥ x), Complex.sub_re]
    have := hc _ hu
    linarith
  · intro z w
    obtain ⟨u, rfl⟩ : ∃ u, z = M *ᵥ u := ⟨M⁻¹ *ᵥ z, (hMMi z).symm⟩
    rw [hF, hcomm, hMiM, hMv]
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply, Complex.add_im, Complex.sub_im]
    rw [hs u w, hs (N u) w, hH (N w) u, hH (N w) (N u), Complex.conj_im, Complex.conj_im]
    ring

variable {M : Type} [AddCommGroup M]

theorem im_eq_of_span (P : M → (Fin g → ℂ)) (hs : Submodule.span ℝ (Set.range P) = ⊤)
    (F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) →ₗ⋆[ℂ] ℂ) (S T S' T' : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ))
    (h : ∀ a b, (F (S (P a)) (T (P b))).im = (F' (S' (P a)) (T' (P b))).im) (z w : Fin g → ℂ) :
    (F (S z) (T w)).im = (F' (S' z) (T' w)).im := by
  have hre : ∀ (r : ℝ) (v : Fin g → ℂ), r • v = (r : ℂ) • v := fun r v => (Complex.coe_smul r v).symm
  have hmem : ∀ v, v ∈ Submodule.span ℝ (Set.range P) := by
    intro v
    rw [hs]
    exact Submodule.mem_top

  have step : ∀ x b, (F (S x) (T (P b))).im = (F' (S' x) (T' (P b))).im := by
    intro x
    induction hmem x using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      exact fun b => h a b
    | zero => intro b; simp
    | add y y' _ _ hy hy' =>
      intro b
      simp only [map_add, LinearMap.add_apply, Complex.add_im, hy b, hy' b]
    | smul r y _ hy =>
      intro b
      simp only [map_smul]
      simp only [hre]
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Complex.im_ofReal_mul, hy b]

  induction hmem w using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    exact step z b
  | zero => simp
  | add y y' _ _ hy hy' =>
    simp only [map_add, Complex.add_im, hy, hy']
  | smul r y _ hy =>
    simp only [map_smul]
    simp only [hre]
    simp only [map_smulₛₗ, Complex.conj_ofReal, smul_eq_mul, Complex.im_ofReal_mul, hy]

private theorem discrete_range_toIntLinearMap_of_discrete_range (P : M →+ (Fin g → ℂ)) (hd : DiscreteTopology P.range) :
    DiscreteTopology (LinearMap.range P.toIntLinearMap) := by
  have hm : ∀ x : LinearMap.range P.toIntLinearMap, (x : Fin g → ℂ) ∈ P.range := by
    rintro ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hx
    exact AddMonoidHom.mem_range.mpr ⟨a, rfl⟩
  exact DiscreteTopology.of_continuous_injective
    (f := fun x => (⟨x, hm x⟩ : P.range)) (continuous_subtype_val.subtype_mk _)
    (fun x y hxy => Subtype.ext (congrArg Subtype.val hxy))

theorem finrank_of_lattice (P : M →+ (Fin g → ℂ)) (hi : Function.Injective P)
    (hd : DiscreteTopology P.range) (hs : Submodule.span ℝ (Set.range P) = ⊤) :
    finrank ℤ M = finrank ℝ (Fin g → ℂ) := by
  have : DiscreteTopology (LinearMap.range P.toIntLinearMap) := discrete_range_toIntLinearMap_of_discrete_range P hd
  have : IsZLattice ℝ (LinearMap.range P.toIntLinearMap) := ⟨by
    rw [LinearMap.coe_range]; exact hs⟩
  rw [(LinearEquiv.ofInjective P.toIntLinearMap hi).finrank_eq]
  exact ZLattice.rank ℝ _

private theorem module_free_int_of_injective_discrete (P : M →+ (Fin g → ℂ)) (hi : Function.Injective P)
    (hd : DiscreteTopology P.range) : Module.Free ℤ M := by
  have : DiscreteTopology (LinearMap.range P.toIntLinearMap) := discrete_range_toIntLinearMap_of_discrete_range P hd
  exact Module.Free.of_equiv (LinearEquiv.ofInjective P.toIntLinearMap hi).symm

theorem exists_extend [Module.Finite ℤ M] (P P' : M →+ (Fin g → ℂ)) (hi : Function.Injective P)
    (hd : DiscreteTopology P.range) (hs : Submodule.span ℝ (Set.range P) = ⊤) :
    ∃ T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ), ∀ a, T (P a) = P' a := by
  classical
  have := module_free_int_of_injective_discrete P hi hd
  let b := Module.Free.chooseBasis ℤ M
  let v : Module.Free.ChooseBasisIndex ℤ M → (Fin g → ℂ) := fun i => P (b i)
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range v) := by
    rw [← hs, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [SetLike.mem_coe, ← b.sum_repr a, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_zsmul]
    exact zsmul_mem (Submodule.subset_span (Set.mem_range_self i) : v i ∈ Submodule.span ℝ (Set.range v)) _
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ M) = finrank ℝ (Fin g → ℂ) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex ℤ M]
    exact finrank_of_lattice P hi hd hs
  let B := Basis.mk (linearIndependent_of_top_le_span_of_card_eq_finrank hsp hcard) hsp
  refine ⟨B.constr ℝ fun i => P' (b i), fun a => ?_⟩
  have key : ((B.constr ℝ fun i => P' (b i)).toAddMonoidHom.comp P).toIntLinearMap =
      P'.toIntLinearMap := by
    refine b.ext fun i => ?_
    have hB : B i = P (b i) := Basis.mk_apply _ _ _
    show (B.constr ℝ fun i => P' (b i)) (P (b i)) = P' (b i)
    rw [← hB, B.constr_basis]
  exact LinearMap.congr_fun key a

theorem lattice_map (P P' : M →+ (Fin g → ℂ)) (hi : Function.Injective P)
    (hd : DiscreteTopology P.range) (hs : Submodule.span ℝ (Set.range P) = ⊤)
    (T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ)) (hT : Function.Injective T) (h : ∀ a, P' a = T (P a)) :
    Function.Injective P' ∧ DiscreteTopology P'.range ∧ Submodule.span ℝ (Set.range P') = ⊤ := by
  have hTs : Function.Surjective T := LinearMap.injective_iff_surjective.mp hT
  have hP' : ⇑P' = T ∘ P := funext h
  refine ⟨?_, ?_, ?_⟩
  · rw [hP']; exact hT.comp hi
  · obtain ⟨G, hG⟩ := T.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hT)
    have hGT : ∀ z, G (T z) = z := fun z => by simpa using LinearMap.congr_fun hG z
    have hGc : Continuous G := LinearMap.continuous_of_finiteDimensional G
    have hmem : ∀ x : P'.range, G x ∈ P.range := by
      rintro ⟨x, hx⟩
      obtain ⟨a, rfl⟩ := AddMonoidHom.mem_range.mp hx
      exact AddMonoidHom.mem_range.mpr ⟨a, by show P a = G (P' a); rw [h, hGT]⟩
    have := hd
    refine DiscreteTopology.of_continuous_injective
      (f := fun x : P'.range => (⟨G x, hmem x⟩ : P.range)) ((hGc.comp continuous_subtype_val).subtype_mk _) ?_
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    obtain ⟨a, rfl⟩ := AddMonoidHom.mem_range.mp hx
    obtain ⟨c, rfl⟩ := AddMonoidHom.mem_range.mp hy
    have e1 := congrArg Subtype.val hxy
    simp only [h, hGT] at e1
    apply Subtype.ext
    simp only [h, e1]
  · have hr : Set.range P' = T '' Set.range P := by
      rw [hP', Set.range_comp]
    rw [hr, Submodule.span_image, hs, Submodule.map_top, LinearMap.range_eq_top.mpr hTs]

private lemma re_sesq_real_smul (G : Matrix (Fin g) (Fin g) ℂ) (r : ℝ) (x : Fin g → ℂ) :
    (sesq G ((r : ℂ) • x) ((r : ℂ) • x)).re = r ^ 2 * (sesq G x x).re := by
  simp only [map_smul, LinearMap.smul_apply, map_smulₛₗ, Complex.conj_ofReal, smul_eq_mul,
    Complex.re_ofReal_mul]
  ring

private lemma anti_real_smul (W : Matrix (Fin g) (Fin g) ℂ) (r : ℝ) (x : Fin g → ℂ) :
    anti W ((r : ℂ) • x) = (r : ℂ) • anti W x := by
  rw [map_smulₛₗ, Complex.conj_ofReal]

private lemma re_sesq_convex_of_pos_def (G : Matrix (Fin g) (Fin g) ℂ) (hp : ∀ z, z ≠ 0 → 0 < (sesq G z z).re)
    (x y : Fin g → ℂ) (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hac : a + c = 1) :
    (sesq G ((a : ℂ) • x + (c : ℂ) • y) ((a : ℂ) • x + (c : ℂ) • y)).re ≤
      a * (sesq G x x).re + c * (sesq G y y).re := by
  have hxy : 0 ≤ (sesq G (x - y) (x - y)).re := by
    by_cases h : x - y = 0
    · simp [h]
    · exact (hp _ h).le
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    map_smulₛₗ, Complex.conj_ofReal, smul_eq_mul, Complex.add_re, Complex.sub_re,
    Complex.re_ofReal_mul] at hxy ⊢
  have hc' : c = 1 - a := by linarith
  subst hc'
  nlinarith [mul_nonneg ha hc, mul_nonneg (mul_nonneg ha hc) hxy]

private lemma continuous_hermForm (G : Matrix (Fin g) (Fin g) ℂ) :
    Continuous fun p : (Fin g → ℂ) × (Fin g → ℂ) => hermForm G p.1 p.2 := by
  simp only [hermForm, dotProduct, Matrix.mulVec, Pi.star_apply]
  refine continuous_finsetSum _ fun i _ => ?_
  refine ((continuous_apply i).comp continuous_fst).mul ?_
  exact continuous_finsetSum _ fun j _ =>
    continuous_const.mul (continuous_star.comp ((continuous_apply j).comp continuous_snd))

theorem isOpen_convex {m : ℕ} (G : Matrix (Fin g) (Fin g) ℂ) (hp : ∀ z, z ≠ 0 → 0 < (sesq G z z).re)
    (Z : (Fin m → ℂ) →ₗ[ℂ] Matrix (Fin g) (Fin g) ℂ) :
    IsOpen {b | ∀ z, z ≠ 0 → (sesq G (anti (Z b) z) (anti (Z b) z)).re < (sesq G z z).re} ∧
    Convex ℝ {b | ∀ z, z ≠ 0 → (sesq G (anti (Z b) z) (anti (Z b) z)).re < (sesq G z z).re} := by
  have hA : ∀ (W : Matrix (Fin g) (Fin g) ℂ) z, anti W z = W *ᵥ star z := fun _ _ => rfl
  have hS : ∀ (G' : Matrix (Fin g) (Fin g) ℂ) z w, sesq G' z w = hermForm G' z w := fun _ _ _ => rfl
  constructor
  · rw [isOpen_iff_mem_nhds]
    intro b0 hb0
    have hZ : Continuous Z := LinearMap.continuous_of_finiteDimensional Z
    have hcont : Continuous fun p : (Fin m → ℂ) × (Fin g → ℂ) =>
        (sesq G p.2 p.2).re - (sesq G (anti (Z p.1) p.2) (anti (Z p.1) p.2)).re := by
      have hv : Continuous fun p : (Fin m → ℂ) × (Fin g → ℂ) => Z p.1 *ᵥ star p.2 :=
        (hZ.comp continuous_fst).matrix_mulVec continuous_snd.star
      exact (Complex.continuous_re.comp ((continuous_hermForm G).comp (continuous_snd.prodMk continuous_snd))).sub
        (Complex.continuous_re.comp ((continuous_hermForm G).comp (hv.prodMk hv)))
    have hev : ∀ᶠ b in nhds b0, ∀ z ∈ Metric.sphere (0 : Fin g → ℂ) 1,
        0 < (sesq G z z).re - (sesq G (anti (Z b) z) (anti (Z b) z)).re := by
      refine (isCompact_sphere (0 : Fin g → ℂ) 1).eventually_forall_of_forall_eventually ?_
      intro z hz
      have hz0 : z ≠ 0 := by
        rintro rfl
        simp at hz
      exact hcont.continuousAt.eventually (eventually_gt_nhds (sub_pos.mpr (hb0 z hz0)))
    filter_upwards [hev] with b hb
    intro z hz
    have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hu : ((‖z‖⁻¹ : ℝ) : ℂ) • z ∈ Metric.sphere (0 : Fin g → ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul]
      simp [hr.ne']
    have h1 := hb _ hu
    rw [anti_real_smul, re_sesq_real_smul, re_sesq_real_smul, ← mul_sub] at h1
    have hpos : 0 < (‖z‖⁻¹) ^ 2 := by positivity
    exact sub_pos.mp (pos_of_mul_pos_right h1 hpos.le)
  · intro b1 hb1 b2 hb2 a c ha hc hac z hz
    have hW : anti (Z (a • b1 + c • b2)) z = (a : ℂ) • anti (Z b1) z + (c : ℂ) • anti (Z b2) z := by
      rw [map_add, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, hA, hA, hA, Matrix.add_mulVec,
        Matrix.smul_mulVec, Matrix.smul_mulVec, Complex.coe_smul, Complex.coe_smul]
    have e1 := hb1 z hz
    have e2 := hb2 z hz
    show (sesq G (anti (Z (a • b1 + c • b2)) z) (anti (Z (a • b1 + c • b2)) z)).re < (sesq G z z).re
    rw [hW]
    refine lt_of_le_of_lt (re_sesq_convex_of_pos_def G hp _ _ a c ha hc hac) ?_
    rcases ha.eq_or_lt with h0 | h0
    · subst h0
      have : c = 1 := by linarith
      subst this
      linarith
    · have hQ : a * (sesq G z z).re + c * (sesq G z z).re = (sesq G z z).re := by
        rw [← add_mul, hac, one_mul]
      linarith [mul_lt_mul_of_pos_left e1 h0, mul_le_mul_of_nonneg_left e2.le hc]

end Mat

section Period

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}

noncomputable def dg (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) : Matrix (Fin g) (Fin g) ℂ :=
  diagonal fun i => ty i (a : E)

omit [IsCMField E] in
theorem comm_iff (ty ty' : Fin g → (E →+* ℂ)) (W : Matrix (Fin g) (Fin g) ℂ) :
    (∀ a, dg ty a * W = W * dg ty' a) ↔ ∀ i j, ¬ ty i = ty' j → W i j = 0 := by
  constructor
  · intro h i j hij
    by_contra hW
    apply hij
    have key : ∀ a : 𝓞 E, ty i (a : E) = ty' j (a : E) := by
      intro a
      have e := congrFun (congrFun (h a) i) j
      simp only [dg, Matrix.diagonal_mul, Matrix.mul_diagonal] at e
      rw [mul_comm (W i j)] at e
      exact mul_right_cancel₀ hW e
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => key a)
  · intro h a
    ext i j
    simp only [dg, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hij : ty i = ty' j
    · rw [hij, mul_comm]
    · rw [h i j hij]; simp

omit [NumberField E] [IsCMField E] in
theorem dg_map (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) :
    (dg ty a).map (starRingEnd ℂ) = dg (fun i => ComplexEmbedding.conjugate (ty i)) a := by
  unfold dg
  rw [Matrix.diagonal_map (map_zero _)]
  rfl

omit [NumberField E] [IsCMField E] in
theorem anti_comm_iff (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) (Z : Matrix (Fin g) (Fin g) ℂ) :
    (∀ z, anti Z (dg ty a *ᵥ z) = dg ty a *ᵥ anti Z z) ↔
      dg ty a * Z = Z * dg (fun i => ComplexEmbedding.conjugate (ty i)) a := by
  have hs : ∀ z : Fin g → ℂ,
      star (dg ty a *ᵥ z) = dg (fun i => ComplexEmbedding.conjugate (ty i)) a *ᵥ star z := by
    intro z
    funext k
    simp [dg, Matrix.mulVec_diagonal, ComplexEmbedding.conjugate_coe_eq, mul_comm]
  have key : ∀ z : Fin g → ℂ, anti Z (dg ty a *ᵥ z) =
      (Z * dg (fun i => ComplexEmbedding.conjugate (ty i)) a) *ᵥ star z := by
    intro z
    change Z *ᵥ star (dg ty a *ᵥ z) = _
    rw [hs, Matrix.mulVec_mulVec]
  have key2 : ∀ z : Fin g → ℂ, dg ty a *ᵥ anti Z z = (dg ty a * Z) *ᵥ star z := by
    intro z
    change dg ty a *ᵥ (Z *ᵥ star z) = _
    rw [Matrix.mulVec_mulVec]
  simp only [key, key2]
  constructor
  · intro h
    ext i j
    have hst : star (Pi.single j (1 : ℂ) : Fin g → ℂ) = Pi.single j 1 := by
      funext k
      by_cases hk : k = j
      · subst hk
        simp
      · simp [hk]
    have e := congrFun (h (Pi.single j 1)) i
    rw [hst, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at e
    exact e.symm
  · intro h z
    rw [h]

variable {D : Datum H} {ty : Fin g → (E →+* ℂ)}

theorem lin_iff (P : D.La →+ (Fin g → ℂ)) :
    (∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i) ↔ ∀ (a : 𝓞 E) x, P (a • x) = dg ty a *ᵥ P x := by
  constructor
  · intro h a x
    funext i
    rw [h]
    simp only [dg, Matrix.mulVec_diagonal]
  · intro h a x i
    rw [h]
    simp only [dg, Matrix.mulVec_diagonal]

theorem herm_comm (P : D.La →+ (Fin g → ℂ)) (hl : ∀ (a : 𝓞 E) x, P (a • x) = dg ty a *ᵥ P x)
    (hs : Submodule.span ℝ (Set.range P) = ⊤) (G : Matrix (Fin g) (Fin g) ℂ)
    (hE : ∀ x y, (sesq G (P x) (P y)).im = D.EF x y) (a : 𝓞 E) : dg ty a * Gᵀ = Gᵀ * dg ty a := by

  have hconjb : ∀ i, starRingEnd ℂ (ty i ((H.bar a : 𝓞 E) : E)) = ty i (a : E) := by
    intro i
    rw [H.bar_eq, IsCMField.complexEmbedding_complexConj, Complex.conj_conj]
  let S : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) := (Matrix.mulVecLin (dg ty a)).restrictScalars ℝ
  let T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) := (Matrix.mulVecLin (dg ty (H.bar a))).restrictScalars ℝ

  have h1 := im_eq_of_span (⇑P) hs (sesq G) (sesq G) S LinearMap.id LinearMap.id T (fun x y => by
    simp only [S, T, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, LinearMap.id_apply]
    rw [← hl, ← hl, hE, hE, D.adj])
  have h2 : ∀ z w, (sesq ((dg ty a)ᵀ * G) z w).im =
      (sesq (G * (dg ty (H.bar a)).map (starRingEnd ℂ)) z w).im := by
    intro z w
    have e := h1 z w
    simp only [S, T, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, LinearMap.id_apply] at e
    rwa [sesq_mulVec_left, sesq_mulVec_right] at e

  have h3 : ∀ z w, sesq ((dg ty a)ᵀ * G) z w = sesq (G * (dg ty (H.bar a)).map (starRingEnd ℂ)) z w := by
    intro z w
    apply Complex.ext
    · have e := h2 (Complex.I • z) w
      simpa using e
    · exact h2 z w
  have hX : (dg ty a)ᵀ * G = G * (dg ty (H.bar a)).map (starRingEnd ℂ) := by
    ext i j
    have e := h3 (Pi.single i 1) (Pi.single j 1)
    rwa [sesq_single, sesq_single] at e
  have hT : (dg ty a)ᵀ = dg ty a := Matrix.diagonal_transpose _
  have hM : (dg ty (H.bar a)).map (starRingEnd ℂ) = dg ty a := by
    unfold dg
    rw [Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    exact hconjb i
  rw [hT, hM] at hX
  have e := congrArg Matrix.transpose hX
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hT] at e
  exact e.symm

theorem isPeriod_add (P : D.La →+ (Fin g → ℂ)) (hl : ∀ (a : 𝓞 E) x, P (a • x) = dg ty a *ᵥ P x)
    (hi : Function.Injective P) (hd : DiscreteTopology P.range)
    (hs : Submodule.span ℝ (Set.range P) = ⊤) (G : Matrix (Fin g) (Fin g) ℂ) (hG : G.IsHermitian)
    (hE : ∀ x y, (sesq G (P x) (P y)).im = D.EF x y) (Z : Matrix (Fin g) (Fin g) ℂ)
    (h1 : ∀ a z, anti Z (dg ty a *ᵥ z) = dg ty a *ᵥ anti Z z)
    (h2 : ∀ z w, sesq G (anti Z z) w = sesq G (anti Z w) z)
    (h3 : ∀ z, z ≠ 0 → (sesq G (anti Z z) (anti Z z)).re < (sesq G z z).re) :
    IsPeriod D ty (P + (anti Z).toAddMonoidHom.comp P) := by

  let T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) :=
    { toFun := fun z => z + anti Z z
      map_add' := fun x y => by simp only [map_add]; abel
      map_smul' := fun r x => by
        simp only [RingHom.id_apply, smul_add, ← Complex.coe_smul, LinearMap.map_smulₛₗ,
          Complex.conj_ofReal] }
  have hT : ∀ z, T z = z + anti Z z := fun z => rfl

  have hTi : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    by_contra hne
    have hN : anti Z z = -z := eq_neg_of_add_eq_zero_right (by rw [← hT]; exact hz)
    have := h3 z hne
    simp only [hN, map_neg, LinearMap.neg_apply, neg_neg] at this
    exact lt_irrefl _ this
  obtain ⟨hi', hd', hs'⟩ := lattice_map P (P + (anti Z).toAddMonoidHom.comp P) hi hd hs T hTi
    (fun a => rfl)
  obtain ⟨Hm, hH, hpos, him⟩ := exists_herm G Z hG h2 h3
  refine ⟨fun a x i => ?_, hi', hd', hs', Hm, hH, fun z hz => ?_, fun x y => ?_⟩
  · change P (a • x) i + anti Z (P (a • x)) i = ty i (a : E) * (P x i + anti Z (P x) i)
    rw [hl, h1]
    simp only [dg, Matrix.mulVec_diagonal]
    ring
  · rw [← sesq_apply]; exact hpos z hz
  · rw [← sesq_apply]
    change (sesq Hm (P x + anti Z (P x)) (P y + anti Z (P y))).im = _
    rw [him, hE]

theorem exists_contraction (P : D.La →+ (Fin g → ℂ)) (hl : ∀ (a : 𝓞 E) x, P (a • x) = dg ty a *ᵥ P x)
    (hi : Function.Injective P) (hd : DiscreteTopology P.range)
    (hs : Submodule.span ℝ (Set.range P) = ⊤) (G : Matrix (Fin g) (Fin g) ℂ)
    (hp : ∀ z, z ≠ 0 → 0 < (sesq G z z).re)
    (hE : ∀ x y, (sesq G (P x) (P y)).im = D.EF x y) (P' : D.La →+ (Fin g → ℂ)) (hP' : IsPeriod D ty P') :
    ∃ (Z : Matrix (Fin g) (Fin g) ℂ) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ a z, anti Z (dg ty a *ᵥ z) = dg ty a *ᵥ anti Z z) ∧
      (∀ z w, sesq G (anti Z z) w = sesq G (anti Z w) z) ∧
      (∀ z, z ≠ 0 → (sesq G (anti Z z) (anti Z z)).re < (sesq G z z).re) ∧
      ∀ x, P' x = h (P x + anti Z (P x)) := by
  obtain ⟨hl'c, -, -, -, Hm', hH', hpos', hE'⟩ := hP'
  have hl' := (lin_iff P').1 hl'c
  have := D.fin
  have : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La

  obtain ⟨T, hTP⟩ := exists_extend P P' hi hd hs
  have hTr : ∀ (r : ℝ) z, T.toAddMonoidHom ((r : ℂ) • z) = (r : ℂ) • T.toAddMonoidHom z := by
    intro r z
    simp only [LinearMap.toAddMonoidHom_coe, Complex.coe_smul, map_smul]
  obtain ⟨A, C, hAC⟩ := exists_lin_anti T.toAddMonoidHom hTr
  have hAC' : ∀ z, T z = A z + C z := hAC

  have hkey : ∀ z w, (sesq Hm' (T z) (T w)).im = (sesq G z w).im := by
    intro z w
    have := im_eq_of_span P hs (sesq Hm') (sesq G) T T LinearMap.id LinearMap.id
      (fun a b => by rw [hTP, hTP, sesq_apply, hE', LinearMap.id_apply, LinearMap.id_apply, hE]) z w
    simpa using this

  have hAi : Function.Injective A := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    by_contra hne
    have e1 : T z = C z := by rw [hAC', hz, zero_add]
    have e2 : T (Complex.I • z) = (-Complex.I) • C z := by
      rw [hAC', map_smul, hz, smul_zero, zero_add, LinearMap.map_smulₛₗ, Complex.conj_I]
    have hq := hp z hne
    have hs0 : 0 ≤ (sesq Hm' (C z) (C z)).re := by
      by_cases h0 : C z = 0
      · simp [h0]
      · rw [sesq_apply]; exact (hpos' _ h0).le
    have := hkey z (Complex.I • z)
    rw [e1, e2] at this
    simp only [LinearMap.map_smulₛₗ, map_neg, Complex.conj_I, neg_neg, smul_eq_mul, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.neg_im, zero_mul, one_mul, zero_add,
      neg_mul] at this
    linarith
  let h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearEquiv.ofInjectiveEndo A hAi
  have hh : ∀ u, h u = A u := fun u => rfl
  have hA : ∀ u, A (h.symm u) = u := fun u => (hh _).symm.trans (h.apply_symm_apply u)
  let N : (Fin g → ℂ) →ₗ⋆[ℂ] (Fin g → ℂ) := (h.symm : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)).comp C
  have hN : ∀ z, N z = h.symm (C z) := fun z => rfl
  obtain ⟨Z, hZ⟩ := exists_anti N

  have hTD : ∀ (a : 𝓞 E) z, T (dg ty a *ᵥ z) = dg ty a *ᵥ T z := by
    intro a
    let Dr : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) := (Matrix.mulVecLin (dg ty a)).restrictScalars ℝ
    have hDr : T.comp Dr = Dr.comp T := by
      apply LinearMap.ext_on_range hs
      intro x
      change T (dg ty a *ᵥ P x) = dg ty a *ᵥ T (P x)
      rw [← hl, hTP, hTP, hl']
    intro z
    exact LinearMap.congr_fun hDr z
  have hDI : ∀ (a : 𝓞 E) (c : ℂ) z, dg ty a *ᵥ (c • z) = c • (dg ty a *ᵥ z) :=
    fun a c z => Matrix.mulVec_smul _ _ _
  have hcomm : ∀ (a : 𝓞 E) z,
      A (dg ty a *ᵥ z) = dg ty a *ᵥ A z ∧ C (dg ty a *ᵥ z) = dg ty a *ᵥ C z := by
    intro a z
    refine lin_anti_unique (fun z => A (dg ty a *ᵥ z)) (fun z => dg ty a *ᵥ A z)
      (fun z => C (dg ty a *ᵥ z)) (fun z => dg ty a *ᵥ C z) ?_ ?_ ?_ ?_ ?_ z
    · intro z; simp only [hDI, map_smul]
    · intro z; simp only [map_smul, hDI]
    · intro z; simp only [hDI, LinearMap.map_smulₛₗ, Complex.conj_I]
    · intro z; simp only [LinearMap.map_smulₛₗ, Complex.conj_I, hDI]
    · intro z
      show A (dg ty a *ᵥ z) + C (dg ty a *ᵥ z) = dg ty a *ᵥ A z + dg ty a *ᵥ C z
      rw [← hAC', hTD, hAC', Matrix.mulVec_add]

  let F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) →ₗ⋆[ℂ] ℂ := ((sesq Hm').comp A).compl₂ A
  have hFa : ∀ z w, F z w = sesq Hm' (A z) (A w) := fun z w => rfl
  have hFT : ∀ z w, F (z + N z) (w + N w) = sesq Hm' (T z) (T w) := by
    have e : ∀ u, A (u + N u) = T u := fun u => by rw [map_add, hN, hA, hAC']
    intro z w
    rw [hFa, e, e]
  obtain ⟨hsy, hct⟩ := symm_contraction F (sesq G) N
    (fun z w => by rw [hFa, hFa]; exact (isHermitian_iff Hm').1 hH' _ _)
    (fun z hz => by
      rw [hFa, sesq_apply]
      exact hpos' _ (fun h0 => hz (hAi (by rw [h0, map_zero]))))
    hp (fun z w => by rw [hFT, hkey])
  refine ⟨Z, h, ?_, ?_, ?_, ?_⟩ <;> rw [← hZ]
  · intro a z
    apply hAi
    rw [hN, hN, hA, (hcomm a _).1, hA, (hcomm a z).2]
  · exact hsy
  · exact hct
  · intro x
    rw [map_add, hh, hh, hN, hA, ← hAC', hTP]

theorem conj_rt (H : Host E) (τ : E →+* ℂ) :
    (τ (H.rt : E) = H.rt0 ↔ ¬ ComplexEmbedding.conjugate τ (H.rt : E) = H.rt0) := by
  have hd : (0 : ℝ) < H.d := Nat.cast_pos.2 H.d_prime.pos
  have hw : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    have e := congrArg (τ.comp (algebraMap (𝓞 E) E)) H.rt_sq
    rw [map_pow, map_neg, map_natCast] at e
    exact e
  have hre : H.rt0.re = 0 := by
    have e1 := congrArg Complex.re H.sqrt_neg_disc_sq
    have e2 := congrArg Complex.im H.sqrt_neg_disc_sq
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.natCast_re, Complex.natCast_im, neg_zero] at e1 e2
    have hri : H.rt0.re * H.rt0.im = 0 := by linarith
    rcases mul_eq_zero.1 hri with h | h
    · exact h
    · exfalso
      rw [h] at e1
      nlinarith [sq_nonneg H.rt0.re]
  have hconj : (starRingEnd ℂ) H.rt0 = -H.rt0 := by
    apply Complex.ext <;> simp [hre]
  have hne : H.rt0 ≠ -H.rt0 := by
    intro h
    have h0 : H.rt0 = 0 := by linear_combination h / 2
    have e := H.sqrt_neg_disc_sq
    rw [h0] at e
    have hd0 : (H.d : ℂ) = 0 := by linear_combination e
    exact H.d_prime.ne_zero (by exact_mod_cast hd0)
  have hroots : τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := by
    have e : (τ (H.rt : E) - H.rt0) * (τ (H.rt : E) + H.rt0) = 0 := by
      linear_combination hw - H.sqrt_neg_disc_sq
    rcases mul_eq_zero.1 e with h | h
    · left; linear_combination h
    · right; linear_combination h
  rw [ComplexEmbedding.conjugate_coe_eq]
  rcases hroots with h | h <;> rw [h]
  · rw [hconj]
    exact ⟨fun _ h' => hne h'.symm, fun _ => rfl⟩
  · rw [map_neg, hconj, neg_neg]
    exact ⟨fun h' => absurd h'.symm hne, fun h' => absurd rfl h'⟩

theorem card_pairs {p q : ℕ} (hty : IsTypeFn H p q ty) :
    Nat.card {x : Fin g × Fin g // ty x.1 = ComplexEmbedding.conjugate (ty x.2)} = finrank ℚ E * p * q := by
  classical
  have hN : ∀ τ : E →+* ℂ, (Finset.univ.filter (fun i : Fin g => ty i = τ)).card *
      (Finset.univ.filter (fun i : Fin g => ty i = ComplexEmbedding.conjugate τ)).card = p * q := by
    intro τ
    have h1 := hty τ
    have h2 := hty (ComplexEmbedding.conjugate τ)
    have hc := conj_rt H τ
    simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at h1 h2
    by_cases hτ : τ (H.rt : E) = H.rt0
    · rw [h1.1 hτ, h2.2 (hc.1 hτ)]
    · rw [h1.2 hτ, h2.1 (not_not.1 (mt hc.2 hτ)), mul_comm]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype,
    Finset.card_eq_sum_card_fiberwise (f := fun x : Fin g × Fin g => ty x.2) (t := Finset.univ)
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
  have hfib : ∀ τ : E →+* ℂ, ((Finset.univ.filter fun x : Fin g × Fin g =>
      ty x.1 = ComplexEmbedding.conjugate (ty x.2)).filter (fun x => ty x.2 = τ)).card = p * q := by
    intro τ
    rw [← hN τ, mul_comm, ← Finset.card_product]
    congr 1
    ext ⟨i, j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [h1, h2], h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [h1, h2], h2⟩
  rw [Finset.sum_congr rfl (fun τ _ => hfib τ), Finset.sum_const, Finset.card_univ,
    NumberField.Embeddings.card, smul_eq_mul]
  ring

end Period

theorem period_chart : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty → ∀ P₀, IsPeriod D ty P₀ → ∃ (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → (D.La →+ (Fin g → ℂ))), 2 * m = Module.finrank ℚ E * D.p * D.q ∧ IsOpen B ∧ Convex ℝ B ∧ 0 ∈ B ∧ P 0 = P₀ ∧ IsHolPeriods D ty B P ∧ ∀ P', IsPeriod D ty P' → ∃! b, b ∈ B ∧ ∃ h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ a, P' a = h (P b a)) := by
  intro E _ _ _ H D g ty hty P₀ hP₀
  obtain ⟨hl0, hi, hd, hs, G, hG, hpos, hEF⟩ := hP₀
  have hp : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (sesq G z z).re := fun z hz => by
    rw [sesq_apply]; exact hpos z hz
  have hE : ∀ x y, (sesq G (P₀ x) (P₀ y)).im = D.EF x y := fun x y => by
    rw [sesq_apply]; exact hEF x y
  have hl : ∀ (a : 𝓞 E) x, P₀ (a • x) = dg ty a *ᵥ P₀ x := (lin_iff P₀).1 hl0

  have hGu : IsUnit Gᵀ.det := by
    refine isUnit_det_of_ker Gᵀ fun z hz h0 => ?_
    have h1 := hpos z hz
    rw [hermForm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, h0] at h1
    simp at h1
  have hcancel : ∀ M N : Matrix (Fin g) (Fin g) ℂ, Gᵀ * M = Gᵀ * N → M = N := by
    intro M N h
    have h1 : Gᵀ⁻¹ * (Gᵀ * M) = Gᵀ⁻¹ * (Gᵀ * N) := by rw [h]
    rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hGu, Matrix.one_mul,
      Matrix.one_mul] at h1
  have hcc : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ :=
    fun φ => RingHom.ext fun x => by simp

  obtain ⟨m, L, hm, hLi, hLr⟩ := exists_param (fun i j : Fin g => ty i = ComplexEmbedding.conjugate (ty j))
      (fun i => ty i (H.rt : E) = H.rt0)
      (fun i j h => by
        show ty j = ComplexEmbedding.conjugate (ty i)
        rw [h, hcc])
      (fun i j h => by
        show ty i (H.rt : E) = H.rt0 ↔ ¬ ty j (H.rt : E) = H.rt0
        have h1 := conj_rt H (ty i)
        rw [h, hcc] at h1
        rw [h]
        exact h1)
  obtain ⟨Zl, hZl⟩ : ∃ Zl : (Fin m → ℂ) →ₗ[ℂ] Matrix (Fin g) (Fin g) ℂ, ∀ b, Zl b = Gᵀ⁻¹ * L b :=
    ⟨(LinearMap.mulLeft ℂ Gᵀ⁻¹).comp L, fun b => rfl⟩
  have hGc : ∀ a, dg ty a * Gᵀ = Gᵀ * dg ty a := herm_comm P₀ hl hs G hE

  have hchar : ∀ Z : Matrix (Fin g) (Fin g) ℂ,
      ((∀ (a : 𝓞 E) z, anti Z (dg ty a *ᵥ z) = dg ty a *ᵥ anti Z z) ∧
        ∀ z w, sesq G (anti Z z) w = sesq G (anti Z w) z) ↔ ∃ b, Zl b = Z := by
    intro Z
    have e0 : (∀ (a : 𝓞 E) z, anti Z (dg ty a *ᵥ z) = dg ty a *ᵥ anti Z z) ↔
        ∀ a, dg ty a * (Gᵀ * Z) = (Gᵀ * Z) * dg (fun i => ComplexEmbedding.conjugate (ty i)) a := by
      refine ⟨fun h a => ?_, fun h a => (anti_comm_iff ty a Z).2 ?_⟩
      · rw [← Matrix.mul_assoc, hGc, Matrix.mul_assoc, (anti_comm_iff ty a Z).1 (h a), Matrix.mul_assoc]
      · apply hcancel
        rw [← Matrix.mul_assoc, ← hGc, Matrix.mul_assoc, h a, Matrix.mul_assoc]
    have e1 := e0.trans (comm_iff ty (fun i => ComplexEmbedding.conjugate (ty i)) (Gᵀ * Z))
    have hex : (∃ b, L b = Gᵀ * Z) ↔ ∃ b, Zl b = Z := by
      constructor
      · rintro ⟨b, hb⟩
        refine ⟨b, ?_⟩
        rw [hZl, hb, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hGu, Matrix.one_mul]
      · rintro ⟨b, hb⟩
        refine ⟨b, ?_⟩
        rw [← hb, hZl, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hGu, Matrix.one_mul]
    exact (and_congr e1 (anti_symm_iff G Z)).trans (and_comm.trans ((hLr _).symm.trans hex))
  obtain ⟨hO, hC⟩ := isOpen_convex G hp Zl

  have hF : ∀ Z : Matrix (Fin g) (Fin g) ℂ, ∃ F : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ), ∀ z, F z = z + anti Z z := by
    intro Z
    refine ⟨⟨⟨fun z => z + anti Z z, fun x y => by simp only [map_add]; abel⟩, fun r z => ?_⟩, fun z => rfl⟩
    simp only [RingHom.id_apply, smul_add]
    congr 1
    rw [anti_apply, anti_apply, star_smul, star_trivial, Matrix.mulVec_smul]
  choose F hFz using hF
  refine ⟨m, {b | ∀ z, z ≠ 0 → (sesq G (anti (Zl b) z) (anti (Zl b) z)).re < (sesq G z z).re},
    fun b => P₀ + (anti (Zl b)).toAddMonoidHom.comp P₀, ?_, hO, hC, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · exact hm.trans (card_pairs hty)
  · simp only [Set.mem_ofPred_eq]
    intro z hz
    simpa [anti_apply] using hp z hz
  · ext x i
    simp [anti_apply]
  · intro b hb
    obtain ⟨h1, h2⟩ := (hchar (Zl b)).2 ⟨b, rfl⟩
    exact isPeriod_add P₀ hl hi hd hs G hG hE (Zl b) h1 h2 hb
  · intro x
    obtain ⟨T, hT⟩ : ∃ T : (Fin m → ℂ) →L[ℂ] (Fin g → ℂ), ∀ b, T b = Zl b *ᵥ star (P₀ x) :=
      ⟨LinearMap.toContinuousLinearMap
        (⟨⟨fun b => Zl b *ᵥ star (P₀ x), fun a b => by simp [Matrix.add_mulVec]⟩,
          fun c b => by simp [Matrix.smul_mulVec]⟩ : (Fin m → ℂ) →ₗ[ℂ] (Fin g → ℂ)), fun b => rfl⟩
    have hfun : (fun b => (P₀ + (anti (Zl b)).toAddMonoidHom.comp P₀) x) = fun b => P₀ x + T b := by
      funext b
      simp [hT, anti_apply]
    show DifferentiableOn ℂ (fun b => (P₀ + (anti (Zl b)).toAddMonoidHom.comp P₀) x) _
    rw [hfun]
    exact (differentiableOn_const _).add T.differentiable.differentiableOn
  · intro P' hP'
    obtain ⟨Z, h, h1, h2, h3, hPh⟩ := exists_contraction P₀ hl hi hd hs G hp hE P' hP'
    obtain ⟨b, rfl⟩ := (hchar Z).1 ⟨h1, h2⟩
    refine ⟨b, ⟨h3, h, fun a => by simpa using hPh a⟩, ?_⟩
    rintro b' ⟨-, h', hh'⟩
    obtain ⟨k, hk⟩ : ∃ k : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, k z = h'.symm (h z) :=
      ⟨h.trans h'.symm, fun z => rfl⟩

    have hext : F (Zl b') = (k.toLinearMap.restrictScalars ℝ).comp (F (Zl b)) := by
      refine LinearMap.ext_on_range hs fun a => ?_
      have e1 := hPh a
      have e2 := hh' a
      simp only [AddMonoidHom.add_apply, AddMonoidHom.coe_comp, Function.comp_apply,
        LinearMap.toAddMonoidHom_coe] at e2
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, hFz, LinearEquiv.coe_coe, hk]
      rw [← e1, e2, LinearEquiv.symm_apply_apply]
    have hkey : ∀ z, z + anti (Zl b') z = k z + k (anti (Zl b) z) := by
      intro z
      have e := LinearMap.congr_fun hext z
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, hFz, LinearEquiv.coe_coe,
        map_add] at e
      exact e
    have hu := fun z => lin_anti_unique (fun z => z) (fun z => k z) (fun z => anti (Zl b') z)
      (fun z => k (anti (Zl b) z)) (fun z => rfl) (fun z => by simp)
      (fun z => by rw [map_smulₛₗ, Complex.conj_I])
      (fun z => by rw [map_smulₛₗ, Complex.conj_I, map_smul]) hkey z
    have hZ : Zl b' = Zl b := by
      refine anti_inj fun z => ?_
      rw [(hu z).2]
      exact ((hu (anti (Zl b) z)).1).symm
    apply hLi
    rw [hZl, hZl] at hZ
    have h5 : Gᵀ * (Gᵀ⁻¹ * L b') = Gᵀ * (Gᵀ⁻¹ * L b) := by rw [hZ]
    rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hGu, Matrix.one_mul,
      Matrix.one_mul] at h5

end GlobalTheory.PeriodChart
