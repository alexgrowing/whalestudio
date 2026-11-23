import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.LineBasis
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo Polynomial
open scoped Matrix TensorProduct Classical
open UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2

section Lin

variable {n : ℕ}

private theorem hv_add_l (M : Matrix (Fin n) (Fin n) ℂ) (x x' y : Fin n → ℂ) :
    hv M (x + x') y = hv M x y + hv M x' y := by
  simp [hv, Matrix.mulVec_add, dotProduct_add]

private theorem hv_add_r (M : Matrix (Fin n) (Fin n) ℂ) (x y y' : Fin n → ℂ) :
    hv M x (y + y') = hv M x y + hv M x y' := by
  simp [hv, star_add, add_dotProduct]

private theorem hv_smul_l (M : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (x y : Fin n → ℂ) :
    hv M (c • x) y = c * hv M x y := by
  simp [hv, Matrix.mulVec_smul, dotProduct_smul]

private theorem hv_smul_r (M : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (x y : Fin n → ℂ) :
    hv M x (c • y) = (starRingEnd ℂ) c * hv M x y := by
  simp [hv, star_smul, smul_dotProduct]

private theorem hv_neg_l (M : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) : hv M (-x) y = -hv M x y := by
  simp [hv, Matrix.mulVec_neg, dotProduct_neg]

private theorem hv_neg_r (M : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) : hv M x (-y) = -hv M x y := by
  simp [hv, star_neg, neg_dotProduct]

private theorem hv_conj {M : Matrix (Fin n) (Fin n) ℂ} (h : M.IsHermitian) (x y : Fin n → ℂ) :
    hv M y x = (starRingEnd ℂ) (hv M x y) := by
  have e : (starRingEnd ℂ) (hv M x y) = star (star y ⬝ᵥ (M *ᵥ x)) := rfl
  rw [e, ← Matrix.star_dotProduct_star, star_star, Matrix.star_mulVec, h.eq, ← Matrix.dotProduct_mulVec]
  rfl

private theorem hv_self_im {M : Matrix (Fin n) (Fin n) ℂ} (h : M.IsHermitian) (x : Fin n → ℂ) :
    (hv M x x).im = 0 := by
  have := congrArg Complex.im (hv_conj h x x)
  simp only [Complex.conj_im] at this
  linarith

private theorem dec_place (M S : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ) (i₀ : Fin n) (hS : S.det ≠ 0)
    (hz : S *ᵥ Pi.single i₀ 1 = z) (hp : ∀ i, i ≠ i₀ → hv M (S *ᵥ Pi.single i 1) z = 0) (y : Fin n → ℂ) :
    ∃ (a : ℂ) (y' : Fin n → ℂ), y = a • z + y' ∧ hv M y' z = 0 ∧
      S *ᵥ (fun i => (if i = i₀ then (1 : ℂ) else -1) * (S⁻¹ *ᵥ y) i) = a • z - y' := by
  have hu : IsUnit S.det := hS.isUnit
  set c := S⁻¹ *ᵥ y with hc
  have hSc : S *ᵥ c = y := by rw [hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have e1 : c = c i₀ • (Pi.single i₀ 1 : Fin n → ℂ) + Function.update c i₀ 0 := by
    funext i
    by_cases h : i = i₀
    · subst h; simp
    · simp [h]
  have e2 : (fun i => (if i = i₀ then (1 : ℂ) else -1) * c i) =
      c i₀ • (Pi.single i₀ 1 : Fin n → ℂ) - Function.update c i₀ 0 := by
    funext i
    by_cases h : i = i₀
    · subst h; simp
    · simp [h]
  refine ⟨c i₀, S *ᵥ Function.update c i₀ 0, ?_, ?_, ?_⟩
  · conv_lhs => rw [← hSc, e1]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, hz]
  · have e3 : Function.update c i₀ 0 = ∑ i, (Function.update c i₀ 0 i) • (Pi.single i 1 : Fin n → ℂ) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [e3, Matrix.mulVec_sum]
    have : ∀ (t : Finset (Fin n)) (f : Fin n → Fin n → ℂ), hv M (∑ i ∈ t, f i) z = ∑ i ∈ t, hv M (f i) z := by
      intro t f
      induction t using Finset.induction_on with
      | empty => simp [hv]
      | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hv_add_l, ih]
    rw [this]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Matrix.mulVec_smul, hv_smul_l]
    by_cases h : i = i₀
    · subst h; simp
    · rw [hp i h, mul_zero]
  · rw [e2, Matrix.mulVec_sub, Matrix.mulVec_smul, hz]

end Lin

end UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2

section Place

variable {n : ℕ}

private theorem place_ne_inv (M : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) (hs : s = 1 ∨ s = -1) (x y : Fin n → ℂ) :
    hv M ((-(s * Complex.I)) • x) ((-(s * Complex.I)) • y) = hv M x y := by
  rw [hv_smul_l, hv_smul_r]
  rcases hs with rfl | rfl <;> simp only [map_neg, map_mul, map_one, Complex.conj_I] <;>
    linear_combination (-hv M x y) * Complex.I_sq

private theorem place_ne_pos (M : Matrix (Fin n) (Fin n) ℂ) (s : ℂ) (hs : s = 1 ∨ s = -1) (x : Fin n → ℂ) :
    (-s * Complex.I * hv M ((-(s * Complex.I)) • x) x).re = -(hv M x x).re := by
  rw [hv_smul_l]
  have : -s * Complex.I * (-(s * Complex.I) * hv M x x) = -hv M x x := by
    rcases hs with rfl | rfl <;> linear_combination (hv M x x) * Complex.I_sq
  rw [this, Complex.neg_re]

private theorem pair_form {M : Matrix (Fin n) (Fin n) ℂ} (h : M.IsHermitian) {z x' y' : Fin n → ℂ} (a b : ℂ)
    (hx : hv M x' z = 0) (hy : hv M y' z = 0) :
    hv M (a • z - x') (b • z - y') = hv M (a • z + x') (b • z + y') ∧
      hv M (a • z - x') (b • z + y') = a * (starRingEnd ℂ) b * hv M z z - hv M x' y' := by
  have hzy : hv M z y' = 0 := by rw [hv_conj h y' z, hy, map_zero]
  simp only [sub_eq_add_neg, hv_add_l, hv_add_r, hv_neg_l, hv_neg_r, hv_smul_l, hv_smul_r, hx, hzy]
  constructor <;> ring

private theorem place_eq_inv {M : Matrix (Fin n) (Fin n) ℂ} (h : M.IsHermitian) {z x' y' : Fin n → ℂ} (a b s : ℂ)
    (hs : s = 1 ∨ s = -1) (hx : hv M x' z = 0) (hy : hv M y' z = 0) :
    hv M ((s * Complex.I) • (a • z - x')) ((s * Complex.I) • (b • z - y')) = hv M (a • z + x') (b • z + y') := by
  rw [hv_smul_l, hv_smul_r, (pair_form h a b hx hy).1]
  rcases hs with rfl | rfl <;> simp only [map_neg, map_mul, map_one, Complex.conj_I] <;>
    linear_combination (-hv M (a • z + x') (b • z + y')) * Complex.I_sq

private theorem place_eq_pos {M : Matrix (Fin n) (Fin n) ℂ} (h : M.IsHermitian) {z x' : Fin n → ℂ} (a s : ℂ)
    (hs : s = 1 ∨ s = -1) (hx : hv M x' z = 0) (him : (hv M z z).im = 0) :
    (-s * Complex.I * hv M ((s * Complex.I) • (a • z - x')) (a • z + x')).re =
      Complex.normSq a * (hv M z z).re - (hv M x' x').re := by
  rw [hv_smul_l, (pair_form h a a hx hx).2, Complex.mul_conj]
  have : -s * Complex.I * (s * Complex.I * ((Complex.normSq a : ℂ) * hv M z z - hv M x' x')) =
      (Complex.normSq a : ℂ) * hv M z z - hv M x' x' := by
    rcases hs with rfl | rfl <;>
      linear_combination (-((Complex.normSq a : ℂ) * hv M z z - hv M x' x')) * Complex.I_sq
  rw [this, Complex.sub_re, Complex.re_ofReal_mul]

end Place

section Arch

variable {n : ℕ}

private noncomputable def Eb {P : Type} [Fintype P] (H : P → Matrix (Fin n) (Fin n) ℂ) (s : P → ℂ) (r : P → ℝ) :
    (P → Fin n → ℂ) →ₗ[ℝ] (P → Fin n → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ∑ v', r v' * (-(s v') * Complex.I * hv (H v') (x v') (y v')).re)
    (fun x x' y => by
      simp only [Pi.add_apply, hv_add_l, mul_add, Complex.add_re, Finset.sum_add_distrib])
    (fun c x y => by
      have e : ∀ v', (-(s v') * Complex.I * hv (H v') ((c • x) v') (y v')).re =
          c * (-(s v') * Complex.I * hv (H v') (x v') (y v')).re := by
        intro v'
        have e1 : (c • x) v' = (c : ℂ) • x v' := by
          funext i; simp
        rw [e1, hv_smul_l, show -(s v') * Complex.I * ((c : ℂ) * hv (H v') (x v') (y v')) =
          (c : ℂ) * (-(s v') * Complex.I * hv (H v') (x v') (y v')) by ring, Complex.re_ofReal_mul]
      simp only [e, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring)
    (fun x y y' => by
      simp only [Pi.add_apply, hv_add_r, mul_add, Complex.add_re, Finset.sum_add_distrib])
    (fun c x y => by
      have e : ∀ v', (-(s v') * Complex.I * hv (H v') (x v') ((c • y) v')).re =
          c * (-(s v') * Complex.I * hv (H v') (x v') (y v')).re := by
        intro v'
        have e1 : (c • y) v' = (c : ℂ) • y v' := by
          funext i; simp
        rw [e1, hv_smul_r, Complex.conj_ofReal, show -(s v') * Complex.I * ((c : ℂ) * hv (H v') (x v') (y v')) =
          (c : ℂ) * (-(s v') * Complex.I * hv (H v') (x v') (y v')) by ring, Complex.re_ofReal_mul]
      simp only [e, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring)

private theorem Eb_apply {P : Type} [Fintype P] (H : P → Matrix (Fin n) (Fin n) ℂ) (s : P → ℂ) (r : P → ℝ)
    (x y : P → Fin n → ℂ) :
    Eb H s r x y = ∑ v', r v' * (-(s v') * Complex.I * hv (H v') (x v') (y v')).re := rfl

private noncomputable def TT {P : Type} (v : P) (S : Matrix (Fin n) (Fin n) ℂ) (hS : S.det ≠ 0) :
    (P → Fin n → ℂ) ≃ₗ[ℝ] (P → Fin n → ℂ) where
  toFun x := Function.update x v (S⁻¹ *ᵥ x v)
  invFun x := Function.update x v (S *ᵥ x v)
  map_add' x y := by
    funext v'
    by_cases h : v' = v
    · subst h; simp [Matrix.mulVec_add]
    · simp [h]
  map_smul' c x := by
    funext v'
    by_cases h : v' = v
    · subst h; simp [Matrix.mulVec_smul]
    · simp [h]
  left_inv x := by
    funext v'
    by_cases h : v' = v
    · subst h
      simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hS.isUnit]
    · simp [h]
  right_inv x := by
    funext v'
    by_cases h : v' = v
    · subst h
      simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hS.isUnit]
    · simp [h]

private theorem TT_apply {P : Type} (v : P) (S : Matrix (Fin n) (Fin n) ℂ) (hS : S.det ≠ 0) (x : P → Fin n → ℂ) :
    TT v S hS x = Function.update x v (S⁻¹ *ᵥ x v) := rfl

private theorem TT_symm_apply {P : Type} (v : P) (S : Matrix (Fin n) (Fin n) ℂ) (hS : S.det ≠ 0)
    (x : P → Fin n → ℂ) : (TT v S hS).symm x = Function.update x v (S *ᵥ x v) := rfl

end Arch

end UpperTheory.Gal.W2

namespace UpperTheory.Gal.W2

private theorem core {P : Type} [Fintype P] {n g : ℕ} (hJ : HermOfJ) (H : P → Matrix (Fin n) (Fin n) ℂ)
    (s : P → ℂ) (r : P → ℝ) (v : P) (z : Fin n → ℂ) (i₀ : Fin n) (S : Matrix (Fin n) (Fin n) ℂ)
    (sg : P → Fin n → ℂ) (R₀ : (P → Fin n → ℂ) ≃ₗ[ℝ] (Fin g → ℂ))
    (hr : ∀ v', 0 < r v') (hs : ∀ v', s v' = 1 ∨ s v' = -1) (hH : ∀ v', (H v').IsHermitian)
    (hneg : ∀ v', v' ≠ v → ∀ x, x ≠ 0 → (hv (H v') x x).re < 0)
    (hz : 0 < (hv (H v) z z).re) (hperp : ∀ x, x ≠ 0 → hv (H v) x z = 0 → (hv (H v) x x).re < 0)
    (hS : S.det ≠ 0) (hSz : S *ᵥ Pi.single i₀ 1 = z)
    (hSp : ∀ i, i ≠ i₀ → hv (H v) (S *ᵥ Pi.single i 1) z = 0)
    (hsg : ∀ v', v' ≠ v → ∀ i, sg v' i = -1) (hsgv : ∀ i, sg v i = if i = i₀ then 1 else -1)
    (hR : ∀ x, R₀ (fun v' i => sg v' i * (s v' * Complex.I) * x v' i) = Complex.I • R₀ x) :
    ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ w : Fin g → ℂ, w ≠ 0 → 0 < (hermForm Hm w w).re) ∧
      ∀ x y, (hermForm Hm (R₀ (TT v S hS x)) (R₀ (TT v S hS y))).im = Eb H s r x y := by
  set R : (P → Fin n → ℂ) ≃ₗ[ℝ] (Fin g → ℂ) := (TT v S hS).trans R₀ with hRdef
  have hRa : ∀ x, R x = R₀ (TT v S hS x) := fun _ => rfl
  have hJ0 : ∀ x, R.symm (Complex.I • R x) = (TT v S hS).symm
      (fun v' i => sg v' i * (s v' * Complex.I) * (TT v S hS x) v' i) := by
    intro x
    rw [LinearEquiv.symm_apply_eq, hRa x, hRa, LinearEquiv.apply_symm_apply, hR]
  have hJne : ∀ x v', v' ≠ v → R.symm (Complex.I • R x) v' = (-(s v' * Complex.I)) • x v' := by
    intro x v' h
    rw [hJ0, TT_symm_apply, Function.update_of_ne h]
    funext i
    simp only [TT_apply, Function.update_of_ne h, hsg v' h i, Pi.smul_apply, smul_eq_mul]
    ring
  have hJv : ∀ x, ∃ (a : ℂ) (y' : Fin n → ℂ), x v = a • z + y' ∧ hv (H v) y' z = 0 ∧
      R.symm (Complex.I • R x) v = (s v * Complex.I) • (a • z - y') := by
    intro x
    obtain ⟨a, y', e1, e2, e3⟩ := dec_place (H v) S z i₀ hS hSz hSp (x v)
    refine ⟨a, y', e1, e2, ?_⟩
    rw [hJ0, TT_symm_apply, Function.update_self, ← e3, ← Matrix.mulVec_smul]
    congr 1
    funext i
    simp only [TT_apply, Function.update_self, hsgv i, Pi.smul_apply, smul_eq_mul]
    ring
  have hzim : (hv (H v) z z).im = 0 := hv_self_im (hH v) z
  have hterm : ∀ x v', 0 ≤ r v' * (-(s v') * Complex.I * hv (H v') (R.symm (Complex.I • R x) v') (x v')).re ∧
      (x v' ≠ 0 → 0 < r v' * (-(s v') * Complex.I * hv (H v') (R.symm (Complex.I • R x) v') (x v')).re) := by
    intro x v'
    rcases eq_or_ne v' v with rfl | h
    · obtain ⟨a, y', e1, e2, e3⟩ := hJv x
      rw [e3, e1, place_eq_pos (hH v') a (s v') (hs v') e2 hzim]
      have hy0 : (hv (H v') y' y').re ≤ 0 := by
        by_cases hy : y' = 0
        · subst hy; simp [hv]
        · exact (hperp y' hy e2).le
      have ha0 : 0 ≤ Complex.normSq a := Complex.normSq_nonneg a
      have hm : 0 ≤ Complex.normSq a * (hv (H v') z z).re := mul_nonneg ha0 hz.le
      refine ⟨mul_nonneg (hr v').le (by linarith), fun hx => mul_pos (hr v') ?_⟩
      by_cases hy : y' = 0
      · have ha : a ≠ 0 := by
          rintro rfl
          apply hx
          rw [hy]; simp
        have := mul_pos (Complex.normSq_pos.2 ha) hz
        linarith
      · have := hperp y' hy e2
        linarith
    · rw [hJne x v' h, place_ne_pos (H v') (s v') (hs v')]
      have hy0 : (hv (H v') (x v') (x v')).re ≤ 0 := by
        by_cases hy : x v' = 0
        · rw [hy]; simp [hv]
        · exact (hneg v' h _ hy).le
      refine ⟨mul_nonneg (hr v').le (by linarith), fun hx => mul_pos (hr v') ?_⟩
      have := hneg v' h _ hx
      linarith
  have hinv : ∀ x y v', hv (H v') (R.symm (Complex.I • R x) v') (R.symm (Complex.I • R y) v') =
      hv (H v') (x v') (y v') := by
    intro x y v'
    rcases eq_or_ne v' v with rfl | h
    · obtain ⟨a, x', e1, e2, e3⟩ := hJv x
      obtain ⟨b, y', f1, f2, f3⟩ := hJv y
      rw [e3, f3, e1, f1, place_eq_inv (hH v') a b (s v') (hs v') e2 f2]
    · rw [hJne x v' h, hJne y v' h, place_ne_inv (H v') (s v') (hs v')]
  obtain ⟨Hm, h1, h2, h3⟩ := hJ g ((Eb H s r).compl₁₂ R.symm.toLinearMap R.symm.toLinearMap)
    (by
      intro a
      simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, Eb_apply]
      refine Finset.sum_eq_zero fun v' _ => ?_
      have him := hv_self_im (hH v') (R.symm a v')
      rcases hs v' with e | e <;> simp [e, Complex.mul_re, him])
    (by
      intro a b
      simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, Eb_apply]
      refine Finset.sum_congr rfl fun v' _ => ?_
      have := hinv (R.symm a) (R.symm b) v'
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
      rw [this])
    (by
      intro a ha
      simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, Eb_apply]
      have hx : R.symm a ≠ 0 := fun h => ha (by simpa using congrArg R h)
      obtain ⟨v₁, hv₁⟩ := Function.ne_iff.1 hx
      have ht := hterm (R.symm a)
      rw [LinearEquiv.apply_symm_apply] at ht
      exact Finset.sum_pos' (fun v' _ => (ht v').1) ⟨v₁, Finset.mem_univ _, (ht v₁).2 hv₁⟩)
  refine ⟨Hm, h1, h2, fun x y => ?_⟩
  have := h3 (R x) (R y)
  simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at this
  exact this

end UpperTheory.Gal.W2

theorem UpperTheory.Gal.W2.rPer_of :
    UpperTheory.Gal.W2.SigB → UpperTheory.Gal.W2.LineBasis → UpperTheory.Gal.W2.TypeIso → UpperTheory.Gal.W2.HermOfJ → UpperTheory.Gal.W2.PlaceT → UpperTheory.Gal.W2.RPer := by
  intro hSig hLB hTI hHJ hPT p _ D G L ha v hv1 t₀ ht₀ ρ hρ A B z
  have hz : 0 < (hv (GlobalTheory.LKCx.herm G v B.β) z.1 z.1).re := z.2
  have hsig := fun v' => hSig p G B v'
  obtain ⟨i₀, S, hS, hSz, hSp⟩ := hLB G.n (GlobalTheory.LKCx.herm G v B.β) z.1 (hsig v).1 hz
  obtain ⟨R₀, hR₁, hR₂⟩ := hTI p D G L ha v hv1 t₀ ht₀ ρ hρ i₀
  have hPl := hPT p D G L ha v hv1 t₀ ht₀
  have hs : ∀ v', sgnV L v' = 1 ∨ sgnV L v' = -1 := fun v' => by
    unfold sgnV; split_ifs <;> simp
  obtain ⟨Hm, h1, h2, h3⟩ := core hHJ (fun v' => GlobalTheory.LKCx.herm G v' B.β) (sgnV L) A.r v z.1 i₀ S
    (fun v' i => if v' = v ∧ i = i₀ then 1 else -1) R₀ A.r_pos hs (fun v' => (hsig v').1)
    (fun v' hne x hx => (hsig v').2.2 (fun h => hne (hPl.1 v' h)) x hx) hz
    (fun x hx hxz => ((hsig v).2.1 hv1).2 z.1 x hz hx hxz) hS hSz hSp
    (fun v' h i => by simp [h]) (fun i => by simp) hR₁
  let R : Arch G ≃ₗ[ℝ] (Fin D.g → ℂ) := (TT v S hS).trans R₀
  have hRa : ∀ x, R x = R₀ (TT v S hS x) := fun _ => rfl
  let Q : VQ D →+ (Fin D.g → ℂ) := (R.toLinearMap.toAddMonoidHom).comp A.th
  have hQ : ∀ w, Q w = R (A.th w) := fun _ => rfl
  refine ⟨Q, R.toLinearMap, ⟨?_, ?_, Hm, h1, h2, ?_⟩, fun w => rfl, ?_⟩
  · intro c w
    obtain ⟨c', rfl⟩ := hρ.onto c
    have e1 : A.th (actQ D (algebraMap (𝓞 D.F) D.O c') w) =
        fun v' => v'.embedding (L.e (c' : D.F)) • A.th w v' := by
      funext v'
      rw [← L.rep_F c', A.act, G.psi_F]
      funext i
      simp [Matrix.mulVec, dotProduct, Matrix.scalar_apply, Matrix.diagonal_apply]
    have e2 : TT v S hS (fun v' => v'.embedding (L.e (c' : D.F)) • A.th w v') =
        fun v' => v'.embedding (L.e (c' : D.F)) • (TT v S hS (A.th w)) v' := by
      funext v'
      by_cases h : v' = v
      · subst h; simp [TT_apply, Matrix.mulVec_smul]
      · simp [TT_apply, h]
    rw [hQ, hQ, e1, hRa, hRa, e2, hR₂]
  · have e : Set.range Q = R '' Set.range A.th := by
      ext y
      constructor
      · rintro ⟨w, rfl⟩
        exact ⟨A.th w, ⟨w, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
        exact ⟨w, rfl⟩
    have e' : (R '' Set.range A.th) = (R.toLinearMap : Arch G →ₗ[ℝ] (Fin D.g → ℂ)) '' Set.range A.th := rfl
    rw [e, e', ← Submodule.map_span, A.span, Submodule.map_top]
    exact LinearEquiv.range R
  · intro u w
    rw [hQ, hQ, hRa, hRa, h3, Eb_apply, formB, A.form]
    refine Finset.sum_congr rfl fun v' _ => ?_
    rw [A.act]
    simp only [hv, GlobalTheory.LKCx.herm, Matrix.mulVec_mulVec]
  · have eS : S⁻¹ *ᵥ z.1 = Pi.single i₀ 1 := by
      rw [← hSz, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hS.isUnit, Matrix.one_mulVec]
    have eT : ∀ c : ℂ, TT v S hS (Pi.single v (c • z.1)) = Pi.single v (c • (Pi.single i₀ 1 : Fin G.n → ℂ)) := by
      intro c
      funext v'
      by_cases h : v' = v
      · subst h; simp [TT_apply, Matrix.mulVec_smul, eS]
      · simp [TT_apply, h]
    have e1 : TT v S hS (Pi.single v z.1) = Pi.single v (Pi.single i₀ 1 : Fin G.n → ℂ) := by
      simpa using eT 1
    have e2 := hR₁ (Pi.single v (Pi.single i₀ 1 : Fin G.n → ℂ))
    have e3 : (fun v' i => (if v' = v ∧ i = i₀ then (1 : ℂ) else -1) * (sgnV L v' * Complex.I) *
        (Pi.single v (Pi.single i₀ 1 : Fin G.n → ℂ) : Arch G) v' i) =
        (Pi.single v ((sgnV L v * Complex.I) • (Pi.single i₀ 1 : Fin G.n → ℂ)) : Arch G) := by
      funext v' i
      by_cases h : v' = v
      · subst h
        by_cases hi : i = i₀
        · subst hi; simp
        · simp [hi]
      · simp [h]
    rw [e3] at e2
    show R _ = _ • R _
    rw [hRa, hRa, eT, e1]
    rcases hs v with e | e
    · rw [e] at e2 ⊢
      simpa using e2
    · rw [e] at e2 ⊢
      have e4 : (Pi.single v (((-1 : ℂ) * Complex.I) • (Pi.single i₀ 1 : Fin G.n → ℂ)) : Arch G) =
          -(Pi.single v (Complex.I • (Pi.single i₀ 1 : Fin G.n → ℂ)) : Arch G) := by
        funext v'
        by_cases h : v' = v
        · subst h; simp
        · simp [h]
      rw [e4, map_neg] at e2
      rw [neg_one_mul, neg_smul, ← e2, neg_neg]
