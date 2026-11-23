import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLiftGraphPoints
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageInverse
import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmIUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.NatCardEqPowLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

namespace LiftGraphPoints

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem aeval_scale {S : Type} [CommRing S] {g : MRing ι} {a : K → ℕ} (hg : IsMultiHomog g a)
    (t : K → S) (x z : (Σ k, ι k) → S) (hz : ∀ p, z p = t p.1 * x p) :
    aeval z g = (∏ k, t k ^ a k) * aeval x g := by
  obtain rfl : z = fun p => t p.1 * x p := funext hz
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hprod : ∏ p, (t p.1 * x p) ^ m p = (∏ k, t k ^ a k) * ∏ p, x p ^ m p := by
    simp only [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, t k ^ m ⟨k, i⟩ = t k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  rw [hprod]
  ring

theorem eval_map_int {σ : Type} (z : σ → ℂ) (f : MvPolynomial σ ℤ) :
    eval z (map (Int.castRingHom ℂ) f) = aeval z f := by
  rw [eval_map, aeval_def, algebraMap_int_eq]

def homogAt (c : ∀ k, ι k) (M : ℕ) (F : MRing ι) : MRing ι :=
  ∑ m ∈ F.support, monomial m (coeff m F) * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (M - ∑ i, m ⟨k, i⟩)

theorem homogAt_isMultiHomog (c : ∀ k, ι k) (M : ℕ) (F : MRing ι)
    (hM : ∀ m ∈ F.support, ∀ k, ∑ i, m ⟨k, i⟩ ≤ M) : IsMultiHomog (homogAt c M F) (fun _ => M) := by
  classical
  intro m' hm' k
  obtain ⟨m, hm, hm'⟩ := Finset.mem_biUnion.mp (support_sum hm')
  have h := Inter.ThmIUnique.isMultiHomog_mul' (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_monomial m (coeff m F))
    (Inter.ThmIUnique.isMultiHomog_coordMonomial c (fun k => M - ∑ i, m ⟨k, i⟩)) m' hm' k
  simp only [Pi.add_apply] at h
  have := hM m hm k
  show _ = M
  omega

theorem aeval_homogAt {S : Type} [CommRing S] (c : ∀ k, ι k) (M : ℕ) (F : MRing ι)
    (x : (Σ k, ι k) → S) (hx : ∀ k, x ⟨k, c k⟩ = 1) : aeval x (homogAt c M F) = aeval x F := by
  conv_rhs => rw [F.as_sum]
  simp only [homogAt, map_sum, map_mul, map_prod, map_pow, aeval_X, hx, one_pow, Finset.prod_const_one, mul_one]

theorem aeval_ratio_eq_zero {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {w : (Σ k, ι k) → ℂ}
    (hw : w ∈ mcPts (mCoordIdeal y)) (c : ∀ k, ι k) (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (hwc : ∀ k, w ⟨k, c k⟩ ≠ 0) {F : MRing ι} (hF : aeval (fun p => y p / y ⟨p.1, c p.1⟩) F = 0) :
    aeval (fun p => w p / w ⟨p.1, c p.1⟩) F = 0 := by
  classical
  set M := ∑ m ∈ F.support, ∑ p, m p
  have hM : ∀ m ∈ F.support, ∀ k, ∑ i, m ⟨k, i⟩ ≤ M := by
    intro m hm k
    calc ∑ i, m ⟨k, i⟩ ≤ ∑ k, ∑ i, m ⟨k, i⟩ :=
          Finset.single_le_sum (f := fun k => ∑ i, m ⟨k, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
      _ = ∑ p, m p := (Fintype.sum_sigma _).symm
      _ ≤ M := Finset.single_le_sum (f := fun m : (Σ k, ι k) →₀ ℕ => ∑ p, m p) (fun _ _ => Nat.zero_le _) hm
  have hG := homogAt_isMultiHomog c M F hM
  have hyG : aeval y (homogAt c M F) = 0 := by
    rw [aeval_scale hG (fun k => y ⟨k, c k⟩) (fun p => y p / y ⟨p.1, c p.1⟩) y
      (fun p => by field_simp [hyc p.1]), aeval_homogAt c M F _ (fun k => div_self (hyc k)), hF, mul_zero]
  have hmem : homogAt c M F ∈ mCoordIdeal y := (BlockImageInverse.mem_mCoordIdeal_iff y hG).mpr hyG
  have hwG := hw.2 _ hmem
  rw [eval_map_int, aeval_scale hG (fun k => w ⟨k, c k⟩) (fun p => w p / w ⟨p.1, c p.1⟩) w
    (fun p => by field_simp [hwc p.1]), aeval_homogAt c M F _ (fun k => div_self (hwc k))] at hwG
  exact (mul_eq_zero.mp hwG).resolve_left (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hwc k))

end LiftGraphPoints

open LiftGraphPoints in

theorem LiftGraphPoints.proof : LiftGraphPoints.Statement := by
  classical
  intro K _ ι _ Ω _ y n r v hv hgen w hw
  choose c hwc using hw.1
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    apply hwc k
    have hX : (X ⟨k, c k⟩ : MRing ι) ∈ mCoordIdeal y := by
      rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul]
    simpa using hw.2 _ hX
  have hrange : chartRingZ y c = (aeval fun p => y p / y ⟨p.1, c p.1⟩).range := by
    rw [chartRingZ, Algebra.adjoin_range_eq_range_aeval]
  have hQ : ∀ j, ∃ Q : MRing ι, aeval (fun p => y p / y ⟨p.1, c p.1⟩) Q = v j * ∏ k, y ⟨k, c k⟩ ^ (-n k) := by
    intro j
    have h := hv j c hyc
    simp only [Nat.cast_one, one_mul] at h
    rw [hrange] at h
    exact (AlgHom.mem_range _).mp h
  choose Q hQ using hQ
  set σ : Fin r → ℂ := fun j => aeval (fun p => w p / w ⟨p.1, c p.1⟩) (Q j) with hσ
  refine ⟨addBlock w σ, ⟨fun k => ?_, fun f hf => ?_⟩, rfl⟩
  · cases k with
    | some k => exact ⟨c k, hwc k⟩
    | none =>
      obtain ⟨u, hu, hsum⟩ := hgen c hyc
      have hU : ∀ j, ∃ U : MRing ι, aeval (fun p => y p / y ⟨p.1, c p.1⟩) U = u j := fun j =>
        (AlgHom.mem_range _).mp (hrange ▸ hu j)
      choose U hU using hU
      by_contra hcon
      push Not at hcon
      have hF : aeval (fun p => y p / y ⟨p.1, c p.1⟩) (∑ j, U j * Q j - 1) = 0 := by
        simp only [map_sub, map_sum, map_mul, hU, hQ, map_one, hsum, sub_self]
      have h1 := aeval_ratio_eq_zero hw c hyc hwc hF
      have hσ0 : ∀ j, aeval (fun p => w p / w ⟨p.1, c p.1⟩) (Q j) = 0 := fun j => hcon j
      simp [hσ0] at h1
  · obtain ⟨S, hS, hspan⟩ := CoordinateConeArithVar.isMultiHomogIdeal (addBlock y v)
    rw [hspan] at hf
    induction hf using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨a, ha⟩ := hS g hg
      have hg0 : aeval (addBlock y v) g = 0 :=
        (BlockImageInverse.mem_mCoordIdeal_iff _ ha).mp (hspan ▸ Ideal.subset_span hg)
      have hP : (∏ k, y ⟨k, c k⟩ ^ (-n k)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hyc k)
      have hY : ∀ o : Option K, (o.elim (∏ k, y ⟨k, c k⟩ ^ (-n k))⁻¹ fun k => y ⟨k, c k⟩) ≠ 0 := by
        intro o
        cases o with
        | none => exact inv_ne_zero hP
        | some k => exact hyc k
      rw [aeval_scale ha (fun o => o.elim (∏ k, y ⟨k, c k⟩ ^ (-n k))⁻¹ fun k => y ⟨k, c k⟩)
        (addBlock (fun p => y p / y ⟨p.1, c p.1⟩) fun j => aeval (fun p => y p / y ⟨p.1, c p.1⟩) (Q j)) _
        (by
          rintro ⟨o, i⟩
          cases o with
          | none =>
            exact (show ∀ j : Fin r, v j = (∏ k, y ⟨k, c k⟩ ^ (-n k))⁻¹ *
                aeval (fun p => y p / y ⟨p.1, c p.1⟩) (Q j) from fun j => by rw [hQ]; field_simp) i
          | some k =>
            show y ⟨k, i⟩ = y ⟨k, c k⟩ * (y ⟨k, i⟩ / y ⟨k, c k⟩)
            field_simp [hyc k])] at hg0
      have hg1 := (mul_eq_zero.mp hg0).resolve_left (Finset.prod_ne_zero_iff.mpr fun o _ => pow_ne_zero _ (hY o))
      have hsub : ∀ (T : Type) [CommRing T] [Algebra ℤ T] (x : (Σ k, ι k) → T),
          aeval x (aeval (addBlock (fun p => (X p : MRing ι)) Q) g) =
            aeval (addBlock x fun j => aeval x (Q j)) g := by
        intro T _ _ x
        rw [comp_aeval_apply]
        have hfun : (fun q => aeval x (addBlock (fun p => (X p : MRing ι)) Q q)) =
            addBlock x fun j => aeval x (Q j) := by
          funext q
          obtain ⟨o, i⟩ := q
          cases o with
          | none => rfl
          | some k => exact aeval_X _ _
        rw [hfun]
      rw [← hsub] at hg1
      have h2 := aeval_ratio_eq_zero hw c hyc hwc hg1
      rw [hsub] at h2
      rw [eval_map_int, aeval_scale ha (fun o => o.elim 1 fun k => w ⟨k, c k⟩)
        (addBlock (fun p => w p / w ⟨p.1, c p.1⟩) σ) _
        (by
          rintro ⟨o, i⟩
          cases o with
          | none => exact (one_mul _).symm
          | some k =>
            show w ⟨k, i⟩ = w ⟨k, c k⟩ * (w ⟨k, i⟩ / w ⟨k, c k⟩)
            field_simp [hwc k]), h2, mul_zero]
    | zero => simp
    | add x₁ x₂ _ _ h₁ h₂ => simp [map_add, h₁, h₂]
    | smul a x _ hx => simp [smul_eq_mul, map_mul, hx]

end

end GroundTheory.Heights₂.Heights.Targets
