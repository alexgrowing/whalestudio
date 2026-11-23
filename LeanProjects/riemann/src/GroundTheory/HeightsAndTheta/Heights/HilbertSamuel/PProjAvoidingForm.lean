import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsProjAvoidingForm
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ExistsHomogeneousComponentNeZero
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PRatNoetherFrame
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ProjAvoidingForm

noncomputable section

theorem ProjAvoidingForm.constantCoeff_homogeneousComponent {σ : Type} {G : MvPolynomial σ ℚ} {d : ℕ}
    (hd : 0 < d) : constantCoeff (homogeneousComponent d G) = 0 := by
  show coeff 0 (homogeneousComponent d G) = 0
  rw [coeff_homogeneousComponent]
  split_ifs with h
  · simp at h
    omega
  · rfl

theorem ProjAvoidingForm.proof (hSeg : SegreArith.Statement) : ProjAvoidingForm.Statement := by
  intro K _ ι _ Ω _ y D df f hV hf hfP
  classical
  have hV' := hV
  obtain ⟨-, ⟨hprime, -, hrelv⟩, hhor, -⟩ := hV'

  have : CharZero Ω := by
    refine charZero_of_inj_zero fun n hn => ?_
    have h1 : ((n : ℤ) : MRing ι) ∈ mCoordIdeal y := by
      rw [mCoordIdeal, RingHom.mem_ker, map_intCast, Int.cast_natCast,
        ← map_natCast (C : Ω →+* MvPolynomial K Ω), hn, map_zero]
    have h2 : (n : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
      simpa using h1
    rw [hhor] at h2
    exact_mod_cast Ideal.mem_bot.mp h2

  have hx := hSeg K ι Ω y D hV
  set x := segreCoords y with hxdef
  obtain ⟨B, e, ⟨B', hB'⟩, hF⟩ := RatNoetherFrame.proof D Ω ((k : K) → ι k) x hx
  set x' := matAct B x with hx'def
  set w : Fin (D + 1) → Ω := x' ∘ e with hwdef
  set R₀ := coneRing ℚ w
  have hBB : ∀ p l, ∑ i, B' p i * B i l = if p = l then 1 else 0 := by
    intro p l
    have := congrFun (hB' (Pi.single l 1)).2 p
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite] using this
  have hxinv : ∀ p, x p = ∑ i, (B' p i : Ω) * x' i := by
    intro p
    simp only [hx'def, matAct, Finset.mul_sum, ← mul_assoc]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    have h1 : ∀ l, (∑ i, (B' p i : Ω) * (B i l : Ω)) = if p = l then 1 else 0 := fun l => by
      have := congrArg (fun q : ℚ => (q : Ω)) (hBB p l)
      push_cast at this
      rw [this]
      split_ifs <;> simp
    simp [h1]

  have hlin : ∀ c : Ix ((k : K) → ι k) → ℚ,
      (∑ i, C (c i) * X i : MvPolynomial (Ix ((k : K) → ι k)) ℚ).IsHomogeneous 1 :=
    fun c => IsHomogeneous.sum _ _ _ fun i _ => (isHomogeneous_X _ _).C_mul _
  have hint : ∀ p, IsIntegral R₀ (Polynomial.C (x p) * Polynomial.X) := by
    intro p
    have := isIntegral_coneMap x' R₀ hF.integral (∑ i, C (B' p i) * X i)
    rw [coneMap_of_isHomogeneous ℚ x' (hlin _), pow_one] at this
    convert this using 2
    rw [hxinv p]
    simp [map_sum]

  let ℓq : Fin (D + 1) → MvPolynomial (Ix ((k : K) → ι k)) ℚ := fun j => ∑ i, C (B (e j) i) * X i
  have hℓhom : ∀ j, (ℓq j).IsHomogeneous 1 := fun j => hlin _
  have hℓx : ∀ j, aeval x (ℓq j) = w j := fun j => by
    simp [ℓq, hwdef, hx'def, matAct]
  set N : ℕ := ∏ j, ∏ i, (B (e j) i).den with hNdef
  have hN : (N : ℚ) ≠ 0 := by
    rw [hNdef]
    exact_mod_cast Finset.prod_ne_zero_iff.mpr fun j _ =>
      Finset.prod_ne_zero_iff.mpr fun i _ => (B (e j) i).den_nz
  have hden : ∀ j i, ∃ n : ℤ, (n : ℚ) = (N : ℚ) * B (e j) i := by
    intro j i
    obtain ⟨r, hr⟩ : (B (e j) i).den ∣ N :=
      (Finset.dvd_prod_of_mem (fun i => (B (e j) i).den) (Finset.mem_univ i)).trans
        (Finset.dvd_prod_of_mem (fun j => ∏ i, (B (e j) i).den) (Finset.mem_univ j))
    refine ⟨r * (B (e j) i).num, ?_⟩
    rw [hr]
    have hq := Rat.num_div_den (B (e j) i)
    have hd : ((B (e j) i).den : ℚ) ≠ 0 := by exact_mod_cast (B (e j) i).den_nz
    have h3 : ((B (e j) i).num : ℚ) = B (e j) i * (B (e j) i).den := (div_eq_iff hd).mp hq
    push_cast
    rw [h3]
    ring
  choose n hn using hden
  let L : Fin (D + 1) → MRing ι := fun j => segreSub (∑ i, C (n j i) * X i)
  have hLhom : ∀ j, IsMultiHomog (L j) (fun _ => 1) := fun j => isMultiHomog_segreSub_linear (n j)
  have hLz : ∀ (z : (Σ k, ι k) → ℂ) j,
      eval z (map (Int.castRingHom ℂ) (L j)) = (N : ℂ) * aeval (segreCoords z) (ℓq j) := by
    intro z j
    simp only [L, ℓq, eval_segreSub, map_sum, map_mul, map_C, map_X, eval_X, eval_C, aeval_C, aeval_X,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := congrArg (fun q : ℚ => (q : ℂ)) (hn j i)
    push_cast at this
    simp [this, mul_assoc]
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN

  have hnz : ∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0 := by
    intro z hz
    by_contra hall
    push Not at hall
    have hℓ0 : (fun j => aeval (segreCoords z) (ℓq j)) = 0 := funext fun j => by
      have := hLz z j
      rw [hall j] at this
      exact (mul_eq_zero.mp this.symm).resolve_left hNC
    have hu0 : ∀ p, segreCoords z p = 0 := by
      intro p
      have hα : IsIntegral R₀ (coneMap ℚ x (X p)) := isIntegral_coneMap x R₀ hint (X p)
      have hg : ∀ k, ∃ g, coneMap ℚ w g = ((minpoly R₀ (coneMap ℚ x (X p))).coeff k : Polynomial Ω) :=
        fun k => (AlgHom.mem_range _).mp ((minpoly R₀ (coneMap ℚ x (X p))).coeff k).2
      choose g hg using hg
      have hrel := key_relation y w ℓq hℓhom hℓx (isHomogeneous_X ℚ p) _ (minpoly.aeval R₀ _) g hg
        (minpoly R₀ (coneMap ℚ x (X p))).natDegree hz
      simp only [← hxdef] at hrel
      rw [hℓ0, Finset.sum_range_succ, Finset.sum_eq_zero fun k hk => by
        rw [Finset.mem_range] at hk
        rw [if_pos (by omega), aeval_zero, constantCoeff_homogeneousComponent (by omega), map_zero, mul_zero],
        zero_add, if_pos (by omega), one_mul, Nat.sub_self, aeval_zero, homogeneousComponent_zero, constantCoeff_C] at hrel
      have htop : coeff 0 (g (minpoly R₀ (coneMap ℚ x (X p))).natDegree) = 1 := by
        have h1 := congrArg (fun q => Polynomial.coeff q 0) (hg (minpoly R₀ (coneMap ℚ x (X p))).natDegree)
        simp only [coeff_coneMap, homogeneousComponent_zero, aeval_C] at h1
        rw [(minpoly.monic hα).coeff_natDegree] at h1
        simp only [OneMemClass.coe_one, Polynomial.coeff_one_zero] at h1
        exact (algebraMap ℚ Ω).injective (h1.trans (map_one _).symm)
      rw [htop, map_one, mul_one] at hrel
      simpa using eq_zero_of_pow_eq_zero hrel
    obtain ⟨c, hc⟩ : ∃ c : (k : K) → ι k, ∀ k, z ⟨k, c k⟩ ≠ 0 :=
      ⟨fun k => (hz.1 k).choose, fun k => (hz.1 k).choose_spec⟩
    exact Finset.prod_ne_zero_iff.mpr (fun k _ => hc k) (hu0 ⟨(), c⟩)

  choose ic hic using hrelv
  obtain ⟨F, hFhom, hFeq⟩ := exists_segre_form hf ic
  have hW : (∏ k, (X ⟨k, ic k⟩ : MRing ι) ^ (∑ k', df k' - df k)) ∉ mCoordIdeal y := by
    intro h
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (p := mCoordIdeal y)).mp h
    exact hic k (hprime.mem_of_pow_mem _ hk)
  have hα0 : coneMap ℚ x (qmap F) ≠ 0 := by
    intro h
    rw [coneMap_qmap] at h
    have := segreSub_mem y (Q := F) (RingHom.mem_ker.mpr h)
    rw [hFeq] at this
    rcases hprime.mem_or_mem this with h1 | h1
    · exact hfP h1
    · exact hW h1
  have hαint : IsIntegral R₀ (coneMap ℚ x (qmap F)) := isIntegral_coneMap x R₀ hint (qmap F)
  have hg : ∀ k, ∃ g, coneMap ℚ w g = ((minpoly R₀ (coneMap ℚ x (qmap F))).coeff k : Polynomial Ω) :=
    fun k => (AlgHom.mem_range _).mp ((minpoly R₀ (coneMap ℚ x (qmap F))).coeff k).2
  choose g hg using hg
  have hg0 : g 0 ≠ 0 := by
    intro h
    have h1 := hg 0
    rw [h, map_zero] at h1
    exact minpoly_coeff_zero_ne hαint hα0 (Subtype.ext h1.symm)
  obtain ⟨d, hd⟩ := exists_homogeneousComponent_ne_zero hg0
  obtain ⟨M, hM, G, hG⟩ := exists_int_mul_eq_qmap (homogeneousComponent d (g 0))
  refine ⟨fun _ => 1, L, G, fun _ => le_rfl, hLhom, hnz, ?_, ?_⟩
  · rintro rfl
    rw [map_zero, mul_eq_zero] at hG
    rcases hG with h | h
    · exact hM (by exact_mod_cast h)
    · exact hd h
  · rintro ζ hGζ z hz ⟨t, ht⟩ hfz
    have hrel := key_relation y w ℓq hℓhom hℓx (hFhom.map (Int.castRingHom ℚ)) _ (minpoly.aeval R₀ _) g hg d hz
    simp only [← hxdef] at hrel
    have hFu : aeval (segreCoords z) (qmap F) = 0 := by
      rw [aeval_qmap, ← eval_segreSub, hFeq, map_mul, eval_mul, hfz, zero_mul]
    rw [Finset.sum_eq_single 0 (fun k _ hk => by rw [hFu, zero_pow hk]; simp) (by simp)] at hrel
    simp only [mul_zero, zero_le, if_true, pow_zero, one_mul, Nat.sub_zero] at hrel
    have hℓu : (fun j => aeval (segreCoords z) (ℓq j)) = fun j => (t / N) * ζ j := funext fun j => by
      have := hLz z j
      rw [ht j] at this
      field_simp
      linear_combination this.symm
    rw [hℓu, aeval_mul_of_isHomogeneous (homogeneousComponent_isHomogeneous d (g 0))] at hrel
    have hG1 : aeval ζ (homogeneousComponent d (g 0)) ≠ 0 := by
      intro h
      apply hGζ
      rw [← aeval_qmap, ← hG, map_mul, h, mul_zero]
    have ht0 : t ≠ 0 := by
      rintro rfl
      obtain ⟨j, hj⟩ := hnz z hz
      exact hj (by rw [ht j, zero_mul])
    rcases mul_eq_zero.mp hrel with h | h
    · exact pow_ne_zero _ (div_ne_zero ht0 hNC) h
    · exact hG1 h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
