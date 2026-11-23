import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogXpow
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullSectionIntegralInt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullSectionIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace PullSectionIntegralInt

theorem aeval_mem_of_forall {σ Ω : Type} [Field Ω] (V : Subring Ω) (y' : σ → Ω) (hy : ∀ p, y' p ∈ V)
    (b : MvPolynomial σ ℤ) : aeval y' b ∈ V := by
  induction b using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add]; exact V.add_mem hp hq
  | mul_X p i hp => rw [map_mul, aeval_X]; exact V.mul_mem hp (hy i)

theorem proof : PullSectionIntegralInt.Statement := by
  intro K _ ι _ Ω _ y D e L q N M hrel he hL hM hdeg τ s hs j hj
  classical
  set ℓ := aeval y (L j)
  set B := Algebra.adjoin ℤ (insert ((M : Ω)⁻¹) (Set.range fun i => aeval y (L i) / ℓ))
  set R := (integralClosure B Ω).toSubring
  have : IsIntegrallyClosedIn R Ω := inferInstanceAs (IsIntegrallyClosedIn (integralClosure B Ω) Ω)
  show s / ℓ ^ (q * τ) ∈ R
  by_contra hnot
  obtain ⟨V, hRV, htV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hnot
  have hBV : ∀ x ∈ B, x ∈ V := fun x hx =>
    hRV (isIntegral_algebraMap (R := B) (A := Ω) (x := ⟨x, hx⟩))

  have hmax : ∀ k, ∃ c : ι k, ∀ i, V.valuation (y ⟨k, i⟩) ≤ V.valuation (y ⟨k, c⟩) := by
    intro k
    obtain ⟨i0, -⟩ := hrel k
    obtain ⟨c, -, hc⟩ := Finset.exists_max_image Finset.univ (fun i => V.valuation (y ⟨k, i⟩))
      ⟨i0, Finset.mem_univ _⟩
    exact ⟨c, fun i => hc i (Finset.mem_univ _)⟩
  choose c hc using hmax
  have hc0 : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    obtain ⟨i0, hi0⟩ := hrel k
    have := hc k i0
    rw [h0, map_zero, le_zero_iff, map_eq_zero] at this
    exact hi0 this
  have hratio : ∀ p : Σ k, ι k, y p / y ⟨p.1, c p.1⟩ ∈ V := by
    intro p
    rw [← V.valuation_le_one_iff, map_div₀]
    exact div_le_one_of_le₀ (hc p.1 p.2) zero_le

  set Mc : Ω := ∏ k, y ⟨k, c k⟩ ^ e k
  have hMc0 : Mc ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc0 k)
  have hchart : (chartRingZ y c : Set Ω) ⊆ V := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨p, rfl⟩ := hx; exact hratio p
    | algebraMap r => simp
    | add a b _ _ ha hb => exact add_mem ha hb
    | mul a b _ _ ha hb => exact mul_mem ha hb
  have : IsIntegrallyClosedIn V.toSubring Ω := inferInstanceAs (IsIntegrallyClosedIn V Ω)
  have hxV : s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * ((q * e k : ℕ) : ℤ))) ∈ V.toSubring :=
    (Subring.integralClosure_le_iff (R := chartRingZ y c) (T := V.toSubring)).mpr
      (fun r => hchart r.2) (hs c hc0)
  have hprod : ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * ((q * e k : ℕ) : ℤ))) = (Mc ^ (q * τ))⁻¹ := by
    rw [← Finset.prod_pow, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [show -((τ : ℤ) * ((q * e k : ℕ) : ℤ)) = -((e k * (q * τ) : ℕ) : ℤ) by push_cast; ring,
      zpow_neg, zpow_natCast, pow_mul]
  rw [hprod] at hxV

  set w := N * ∑ k, Fintype.card (ι k)
  have hd : ∀ k, e k + N * Fintype.card (ι k) ≤ ((w + 1) • e) k := by
    intro k
    have h1 : Fintype.card (ι k) ≤ ∑ k, Fintype.card (ι k) :=
      Finset.single_le_sum (f := fun k => Fintype.card (ι k)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ k)
    have h2 : N * Fintype.card (ι k) ≤ w := Nat.mul_le_mul_left N h1
    have h3 : w ≤ w * e k := Nat.le_mul_of_pos_right w (he k)
    simp only [Pi.smul_apply, smul_eq_mul]
    nlinarith
  obtain ⟨a, ha, hrelM⟩ := hdeg ((w + 1) • e) (xpow c ((w + 1) • e)) (isMultiHomog_xpow c _) hd
  have ha' : ∀ i, IsMultiHomog (a i) (fun k => w * e k) := by
    intro i
    convert ha i using 1
    funext k
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [add_mul, one_mul, Nat.add_sub_cancel]
  have hg : aeval y (xpow c ((w + 1) • e)) = Mc ^ (w + 1) := by
    simp only [xpow, map_prod, map_pow, aeval_X, Mc, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, ← pow_mul, mul_comm]
  set t : K → Ω := fun k => (y ⟨k, c k⟩)⁻¹
  have hscale : ∀ i, aeval (fun p => t p.1 * y p) (a i) = (Mc ^ w)⁻¹ * aeval y (a i) := by
    intro i
    rw [PullSectionIntegral.aeval_scale_of_isMultiHomog y t (ha' i)]
    congr 1
    simp only [Mc, t, ← Finset.prod_pow, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [inv_pow, ← pow_mul, mul_comm]

  have hsum : Mc / ℓ = (M : Ω)⁻¹ * ∑ i, aeval (fun p => t p.1 * y p) (a i) * (aeval y (L i) / ℓ) := by
    have : ∑ i, aeval (fun p => t p.1 * y p) (a i) * (aeval y (L i) / ℓ) =
        (Mc ^ w)⁻¹ * (∑ i, aeval y (a i) * aeval y (L i)) / ℓ := by
      simp only [hscale, Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [this, ← hrelM, hg]
    field_simp
    ring
  have hMV : Mc / ℓ ∈ V := by
    rw [hsum]
    refine mul_mem (hBV _ (Algebra.subset_adjoin (Set.mem_insert _ _))) (sum_mem fun i _ => mul_mem ?_ ?_)
    · exact aeval_mem_of_forall V.toSubring _ (fun p => by simpa [t, div_eq_inv_mul] using hratio p) (a i)
    · exact hBV _ (Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨i, rfl⟩))
  apply htV
  have hMn : Mc ^ (q * τ) ≠ 0 := pow_ne_zero _ hMc0
  have : s / ℓ ^ (q * τ) = s * (Mc ^ (q * τ))⁻¹ * (Mc / ℓ) ^ (q * τ) := by
    rw [div_pow, mul_assoc, ← mul_div_assoc, inv_mul_cancel₀ hMn, mul_one_div]
  rw [this]
  exact mul_mem hxV (pow_mem hMV _)

end PullSectionIntegralInt

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
