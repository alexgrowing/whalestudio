import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

variable {ι : Type} {n : ι → ℕ}

def homogForm (g : Polynomial ℤ) (p q : Coord n) : MvPolynomial (Coord n) ℤ :=
  ∑ j ∈ Finset.range (g.natDegree + 1), C (g.coeff j) * X p ^ j * X q ^ (g.natDegree - j)

theorem eval_homogForm (g : Polynomial ℤ) (p q : Coord n) (z : Coord n → ℂ) :
    eval z (map (Int.castRingHom ℂ) (homogForm g p q)) =
      ∑ j ∈ Finset.range (g.natDegree + 1), (g.coeff j : ℂ) * z p ^ j * z q ^ (g.natDegree - j) := by
  simp [homogForm, map_sum]

theorem homog_sum_eq {F : Type*} [Field F] (g : Polynomial ℤ) (u v : F) (hv : v ≠ 0) :
    ∑ j ∈ Finset.range (g.natDegree + 1), (g.coeff j : F) * u ^ j * v ^ (g.natDegree - j) =
      v ^ g.natDegree * Polynomial.aeval (u / v) g := by
  rw [Polynomial.aeval_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj' : j ≤ g.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have e : v ^ g.natDegree = v ^ j * v ^ (g.natDegree - j) := by
    rw [← pow_add, Nat.add_sub_cancel' hj']
  rw [e, zsmul_eq_mul, div_pow]
  field_simp

theorem homog_sum_zero {F : Type*} [CommRing F] (g : Polynomial ℤ) (u : F) :
    ∑ j ∈ Finset.range (g.natDegree + 1), (g.coeff j : F) * u ^ j * (0 : F) ^ (g.natDegree - j) =
      (g.leadingCoeff : F) * u ^ g.natDegree := by
  rw [Finset.sum_eq_single g.natDegree]
  · rw [Nat.sub_self, pow_zero, mul_one]
    rfl
  · intro j hj hjN
    have : 0 < g.natDegree - j :=
      Nat.sub_pos_of_lt (lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hjN)
    rw [zero_pow this.ne', mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) h

theorem homogForm_mem_orbitIdeal [Fintype ι] [DecidableEq ι] (x : Cone n (AlgebraicClosure ℚ)) (g : Polynomial ℤ)
    (p q : Coord n) (hpq : p.1 = q.1) (hq : flatCone x q ≠ 0)
    (hg : Polynomial.aeval (flatCone x p / flatCone x q) g = 0) :
    homogForm g p q ∈ orbitIdeal x := by
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker]
  set y := flatCone x
  have key : ∀ j ∈ Finset.range (g.natDegree + 1),
      Geo.mConeMap (ι := blockIdx n) y (C (g.coeff j) * X p ^ j * X q ^ (g.natDegree - j)) =
        MvPolynomial.C ((g.coeff j : AlgebraicClosure ℚ) * y p ^ j * y q ^ (g.natDegree - j)) *
          MvPolynomial.X q.1 ^ g.natDegree := by
    intro j hj
    have hj' : j ≤ g.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have e : (MvPolynomial.X q.1 : MvPolynomial ι (AlgebraicClosure ℚ)) ^ g.natDegree =
        MvPolynomial.X q.1 ^ j * MvPolynomial.X q.1 ^ (g.natDegree - j) := by
      rw [← pow_add, Nat.add_sub_cancel' hj']
    simp only [Geo.mConeMap, map_mul, map_pow, aeval_X, e, hpq, eq_intCast, map_intCast]
    ring
  rw [homogForm, map_sum, Finset.sum_congr rfl key, ← Finset.sum_mul, ← map_sum,
    homog_sum_eq g _ _ hq]
  simp only [y] at hg ⊢
  simp only [map_mul, mul_eq_zero]
  exact Or.inl (Or.inr (MvPolynomial.C_eq_zero.mpr (by
    rw [Polynomial.aeval_def] at hg ⊢
    convert hg using 2
    exact RingHom.ext_int _ _)))

theorem exists_int_relation (r : AlgebraicClosure ℚ) :
    ∃ g : Polynomial ℤ, g ≠ 0 ∧ Polynomial.aeval r g = 0 :=
  (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic r)

theorem eval_conj_eq_zero [Fintype ι] [DecidableEq ι] (x : Cone n (AlgebraicClosure ℚ)) (σ : AlgebraicClosure ℚ →+* ℂ)
    {f : MvPolynomial (Coord n) ℤ} (hf : f ∈ orbitIdeal x) :
    eval (fun p ↦ σ (flatCone x p)) (map (Int.castRingHom ℂ) f) = 0 := by
  rw [orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker] at hf
  have h : ∀ f : MvPolynomial (Coord n) ℤ,
      eval (fun p ↦ σ (flatCone x p)) (map (Int.castRingHom ℂ) f) =
        σ (eval (fun _ : ι ↦ (1 : AlgebraicClosure ℚ))
          (Geo.mConeMap (ι := blockIdx n) (flatCone x) f)) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [Geo.mConeMap]
    | add f g hf hg => simp only [map_add, hf, hg]
    | mul_X f p hf => simp only [map_mul, hf, eval_X, map_X, Geo.mConeMap, aeval_X, eval_C, mul_one]
  rw [h, hf, map_zero, map_zero]

theorem OrbitDegree.full : OrbitDegree.Statement := by
  intro ι _ _ n x hx
  set W := orbitIdeal x
  set Q := Quot fun z z' : Geo.mcPts (ι := blockIdx n) W ↦
    ∃ c : ι → ℂ, (∀ k, c k ≠ 0) ∧ (z' : Coord n → ℂ) = fun p ↦ c p.1 * (z : Coord n → ℂ) p
  show 0 < Nat.card Q
  rw [Nat.card_pos_iff]

  let _ : Algebra.IsAlgebraic ℤ (AlgebraicClosure ℚ) := ⟨fun r ↦
    (IsFractionRing.isAlgebraic_iff ℤ ℚ (AlgebraicClosure ℚ)).mpr
      ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic r)⟩
  let σ : AlgebraicClosure ℚ →+* ℂ :=
    (IsAlgClosed.lift (R := ℤ) (S := AlgebraicClosure ℚ) (M := ℂ)).toRingHom
  have hσ : (fun p ↦ σ (flatCone x p)) ∈ Geo.mcPts (ι := blockIdx n) W := by
    refine ⟨fun k ↦ ?_, fun f hf ↦ eval_conj_eq_zero x σ hf⟩
    obtain ⟨i, hi⟩ := Function.ne_iff.mp (hx k)
    exact ⟨i, (map_ne_zero σ).mpr hi⟩
  refine ⟨⟨Quot.mk _ ⟨_, hσ⟩⟩, ?_⟩

  obtain ⟨c, hc⟩ := exists_chart hx
  let q : Coord n → Coord n := fun p ↦ ⟨p.1, c p.1⟩
  have hq : ∀ p, flatCone x (q p) ≠ 0 := fun p ↦ hc p.1
  choose g hg0 hg using fun p ↦ exists_int_relation (flatCone x p / flatCone x (q p))
  have hmem : ∀ p, homogForm (g p) p (q p) ∈ W := fun p ↦
    homogForm_mem_orbitIdeal x (g p) p (q p) rfl (hq p) (hg p)
  have hform : ∀ z ∈ Geo.mcPts (ι := blockIdx n) W, ∀ p,
      ∑ j ∈ Finset.range ((g p).natDegree + 1),
        ((g p).coeff j : ℂ) * z p ^ j * z (q p) ^ ((g p).natDegree - j) = 0 := fun z hz p ↦ by
    rw [← eval_homogForm]; exact hz.2 _ (hmem p)

  have hz0 : ∀ z ∈ Geo.mcPts (ι := blockIdx n) W, ∀ k, z ⟨k, c k⟩ ≠ 0 := by
    intro z hz k h0
    obtain ⟨i, hi⟩ := hz.1 k
    have := hform z hz ⟨k, i⟩
    simp only [q] at this
    rw [h0, homog_sum_zero] at this
    exact mul_ne_zero (Int.cast_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr (hg0 _)))
      (pow_ne_zero _ hi) this

  let T : Set (Coord n → ℂ) := Set.pi Set.univ fun p ↦ {t | ((g p).map (Int.castRingHom ℂ)).IsRoot t}
  have hT : T.Finite := Set.Finite.pi fun p ↦
    Polynomial.finite_setOfPred_isRoot ((Polynomial.map_ne_zero_iff (RingHom.injective_int _)).mpr (hg0 p))
  have hrat : ∀ z ∈ Geo.mcPts (ι := blockIdx n) W, (fun p ↦ z p / z (q p)) ∈ T := by
    intro z hz p _
    have h := hform z hz p
    rw [homog_sum_eq _ _ _ (hz0 z hz p.1)] at h
    have h' := (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ (hz0 z hz p.1))
    rw [Polynomial.aeval_def, algebraMap_int_eq] at h'
    simpa [Polynomial.IsRoot, Polynomial.eval_map] using h'
  let F : Q → T := Quot.lift (fun z ↦ ⟨_, hrat z.1 z.2⟩) (by
    rintro z z' ⟨a, ha, e⟩
    apply Subtype.ext
    funext p
    simp only [e, q]
    rw [mul_div_mul_left _ _ (ha p.1)])
  have hF : Function.Injective F := by
    rintro ⟨z, hz⟩ ⟨z', hz'⟩ h
    have h' := fun p ↦ congrFun (congrArg Subtype.val h) p
    simp only [F] at h'
    refine Quot.sound ⟨fun k ↦ z' ⟨k, c k⟩ / z ⟨k, c k⟩,
      fun k ↦ div_ne_zero (hz0 z' hz' k) (hz0 z hz k), ?_⟩
    funext p
    have hp := h' p
    simp only [q] at hp
    have h1 := hz0 z hz p.1
    have h2 := hz0 z' hz' p.1
    have e : z' p = z p / z ⟨p.1, c p.1⟩ * z' ⟨p.1, c p.1⟩ := by
      rw [hp, div_mul_cancel₀ _ h2]
    show z' p = z' ⟨p.1, c p.1⟩ / z ⟨p.1, c p.1⟩ * z p
    rw [e]
    field_simp
  have : Finite T := hT.to_subtype
  exact Finite.of_injective F hF

end

end GroundTheory.Heights₂.Heights
