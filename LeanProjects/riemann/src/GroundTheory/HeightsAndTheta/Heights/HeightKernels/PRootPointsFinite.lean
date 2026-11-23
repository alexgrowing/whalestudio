import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeight
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassHeightNE
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix

noncomputable section

namespace RootPointsFiniteAlt

variable {K : Type*} {ι : K → Type*}

def homog (q : Polynomial ℤ) (p a : Σ k, ι k) : MRing ι :=
  ∑ i ∈ Finset.range (q.natDegree + 1), C (q.coeff i) * X p ^ i * X a ^ (q.natDegree - i)

theorem homog_mem (y : (Σ k, ι k) → ℂ) (k : K) (i i₀ : ι k) (ha : y ⟨k, i₀⟩ = 1) (q : Polynomial ℤ)
    (hq : q.eval₂ (Int.castRingHom ℂ) (y ⟨k, i⟩) = 0) :
    homog q ⟨k, i⟩ ⟨k, i₀⟩ ∈ mCoordIdeal y := by
  show mConeMap y _ = 0
  have hterm : ∀ n ∈ Finset.range (q.natDegree + 1),
      mConeMap y (C (q.coeff n) * X ⟨k, i⟩ ^ n * X ⟨k, i₀⟩ ^ (q.natDegree - n)) =
        MvPolynomial.C ((q.coeff n : ℂ) * y ⟨k, i⟩ ^ n) * MvPolynomial.X k ^ q.natDegree := by
    intro n hn
    have hle : n ≤ q.natDegree := by simpa [Nat.lt_succ_iff] using hn
    simp only [mConeMap, map_mul, map_pow, map_intCast, aeval_X, ha, map_one, one_mul]
    conv_rhs => rw [← pow_mul_pow_sub (MvPolynomial.X k) hle]
    rw [aeval_C, eq_intCast (algebraMap ℤ (MvPolynomial K ℂ))]
    ring
  rw [homog, map_sum, Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← map_sum]
  have : ∑ n ∈ Finset.range (q.natDegree + 1), (q.coeff n : ℂ) * y ⟨k, i⟩ ^ n = 0 := by
    rw [← hq, Polynomial.eval₂_eq_sum_range]; rfl
  rw [this, map_zero, zero_mul]

theorem homog_eval (z : (Σ k, ι k) → ℂ) (p a : Σ k, ι k) (hza : z a ≠ 0) (q : Polynomial ℤ) :
    eval z (map (Int.castRingHom ℂ) (homog q p a)) =
      z a ^ q.natDegree * q.eval₂ (Int.castRingHom ℂ) (z p / z a) := by
  rw [Polynomial.eval₂_eq_sum_range, Finset.mul_sum, homog, map_sum, map_sum]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hle : n ≤ q.natDegree := by simpa [Nat.lt_succ_iff] using hn
  simp only [map_mul, map_pow, map_intCast, map_X, eval_X, eq_intCast]
  conv_rhs => rw [← pow_mul_pow_sub (z a) hle, div_pow]
  field_simp

theorem isIntegral_of_pow_eq_one {x : ℂ} {k : ℕ} (hk : 0 < k) (hx : x ^ k = 1) : IsIntegral ℤ x :=
  ⟨Polynomial.X ^ k - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hk.ne', by simp [hx]⟩

theorem rootCoord_isIntegral {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ) (hζ : IsRootMatrix ζ)
    (p : Σ _ : Fin f, PlIdx j m) : IsIntegral ℤ (rootCoord ζ p) := by
  refine IsIntegral.det fun a b => ?_
  simp only [colsOf, Matrix.submatrix_apply, id, onePipe, Matrix.of_apply]
  generalize (p.2.1.orderEmbOfFin p.2.2) b = c
  refine Fin.addCases (fun c => ?_) (fun c => ?_) c
  · rw [Fin.append_left, Matrix.one_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  · rw [Fin.append_right]
    obtain ⟨k, hk, hx⟩ := hζ p.1 a c
    exact isIntegral_of_pow_eq_one hk hx

end RootPointsFiniteAlt

open RootPointsFiniteAlt in

theorem RootPointsFinite.proof (h : RootAnchorNonzero.Statement) : RootPointsFinite.Statement := by
  intro f j m ζ hζ
  have hint : ∀ p, ∃ q : Polynomial ℤ, q.Monic ∧ q.eval₂ (Int.castRingHom ℂ) (rootCoord ζ p) = 0 := by
    intro p
    obtain ⟨q, hqm, hq⟩ := rootCoord_isIntegral ζ hζ p
    exact ⟨q, hqm, by rwa [← RingHom.ext_int (algebraMap ℤ ℂ) (Int.castRingHom ℂ)]⟩
  choose q hqm hq using hint
  let S : Set ((Σ _ : Fin f, PlIdx j m) → ℂ) :=
    Set.pi Set.univ fun p => {u | Polynomial.IsRoot ((q p).map (Int.castRingHom ℂ)) u}
  have hS : S.Finite := Set.Finite.pi fun p =>
    Polynomial.finite_setOfPred_isRoot ((hqm p).map _).ne_zero
  have hmem : ∀ z ∈ mcPts (rootPointIdeal ζ),
      (fun p : Σ _ : Fin f, PlIdx j m => z p / z ⟨p.1, plAnchor j m⟩) ∈ S := by
    intro z hz p _
    have hza := h f j m ζ hζ z hz p.1
    have h0 := hz.2 _ (homog_mem (rootCoord ζ) p.1 p.2 (plAnchor j m)
      (by simp [rootCoord, anchor_minor]) (q p) (hq p))
    rw [homog_eval z _ _ hza] at h0
    simpa [Polynomial.IsRoot, Polynomial.eval_map, hza] using h0
  let F : McClasses (rootPointIdeal ζ) → S := Quot.lift
    (fun z => ⟨fun p => z.1 p / z.1 ⟨p.1, plAnchor j m⟩, hmem z.1 z.2⟩) (by
      rintro z z' ⟨c, hc, hz'⟩
      apply Subtype.ext
      funext p
      simp only [hz']
      exact (mul_div_mul_left _ _ (hc p.1)).symm)
  have := hS.to_subtype
  refine Finite.of_injective F ?_
  intro x x'
  induction x using Quot.ind with | mk z => ?_
  induction x' using Quot.ind with | mk z' => ?_
  intro hF
  have hfun := fun p => congrFun (congrArg Subtype.val hF) p
  apply Quot.sound
  refine ⟨fun τ => z'.1 ⟨τ, plAnchor j m⟩ / z.1 ⟨τ, plAnchor j m⟩,
    fun τ => div_ne_zero (h f j m ζ hζ z'.1 z'.2 τ) (h f j m ζ hζ z.1 z.2 τ), ?_⟩
  funext p
  have hza := h f j m ζ hζ z.1 z.2 p.1
  have hza' := h f j m ζ hζ z'.1 z'.2 p.1
  have e : z.1 p / z.1 ⟨p.1, plAnchor j m⟩ = z'.1 p / z'.1 ⟨p.1, plAnchor j m⟩ := hfun p
  rw [div_eq_div_iff hza hza'] at e
  rw [div_mul_eq_mul_div, eq_div_iff hza]
  linear_combination -e

end

end GroundTheory.Heights₂.Heights
