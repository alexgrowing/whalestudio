import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IntToFracInjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

section Coordinates

variable {R : Type*} [CommRing R] {n e : ℕ}

theorem span_secCoord_eq_top (Q : Ideal (MvPolynomial (Fin n) R)) (y : Par e n → R) :
    Ideal.span (Set.range (secCoord Q y)) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h1 : Ideal.Quotient.mk (secIdeal Q y) (chartForm y - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _)))
  rw [map_sub, map_one, sub_eq_zero] at h1
  have h2 : (1 : SecAlg Q y) = ∑ j, Ideal.Quotient.mk _ (C (y (.inr j))) * secCoord Q y j := by
    rw [← h1, chartForm, linForm, map_sum]
    simp only [map_mul, secCoord]
  rw [h2]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

theorem eq_zero_of_secCoord_pow_mul (Q : Ideal (MvPolynomial (Fin n) R)) (y : Par e n → R)
    (b : SecAlg Q y) (h : ∀ j, ∃ N : ℕ, secCoord Q y j ^ N * b = 0) : b = 0 := by
  choose N hN using h
  have htop := Ideal.span_pow_eq_top _ (span_secCoord_eq_top Q y) (∑ j, N j)
  have hle : Ideal.span ((fun z => z ^ (∑ j, N j)) '' Set.range (secCoord Q y)) ≤
      LinearMap.ker (LinearMap.mulRight (SecAlg Q y) b) := by
    rw [Ideal.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.mulRight_apply]
    rw [← Nat.sub_add_cancel (Finset.single_le_sum (fun k _ => Nat.zero_le (N k)) (Finset.mem_univ j)),
      pow_add, mul_assoc, hN j, mul_zero]
  have h1 : (1 : SecAlg Q y) ∈ LinearMap.ker (LinearMap.mulRight (SecAlg Q y) b) :=
    hle (by rw [htop]; exact Submodule.mem_top)
  simpa using h1

end Coordinates

section Chart

variable {D : Type*} [CommRing D] {n : ℕ}

def chartCoordinate (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n) : MvPolynomial (Fin n) D ⧸ Q :=
  Ideal.Quotient.mk Q (X j)

abbrev ChartDj (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n) : Type _ :=
  Localization.Away (chartCoordinate Q j)

def chartCoord (e : ℕ) (Q : Ideal (MvPolynomial (Fin n) D)) (j k : Fin n) :
    MvPolynomial (Par e n) (ChartDj Q j) :=
  C (algebraMap _ _ (Ideal.Quotient.mk Q (X k)))

def chartInvC (e : ℕ) (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n) :
    MvPolynomial (Par e n) (ChartDj Q j) :=
  C (IsLocalization.Away.invSelf (chartCoordinate Q j))

theorem chartCoord_mul_inv (e : ℕ) (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n) :
    chartCoord e Q j j * chartInvC e Q j = 1 := by
  rw [chartCoord, chartInvC, ← C_mul]
  have : algebraMap (MvPolynomial (Fin n) D ⧸ Q) (ChartDj Q j) (Ideal.Quotient.mk Q (X j)) *
      IsLocalization.Away.invSelf (chartCoordinate Q j) = 1 := IsLocalization.Away.mul_invSelf (chartCoordinate Q j)
  rw [this, C_1]

def chartSub (e : ℕ) (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n) :
    Par e n → MvPolynomial (Par e n) (ChartDj Q j) :=
  Sum.elim
    (fun ik => X (.inl ik) -
      if ik.2 = j then (∑ k, X (.inl (ik.1, k)) * chartCoord e Q j k) * chartInvC e Q j else 0)
    (fun k => X (.inr k) -
      if k = j then (∑ k', X (.inr k') * chartCoord e Q j k' - 1) * chartInvC e Q j else 0)

theorem chartSub_rel_inl (e : ℕ) (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n) (i : Fin e) :
    ∑ k, chartSub e Q j (.inl (i, k)) * chartCoord e Q j k = 0 := by
  simp only [chartSub, Sum.elim_inl, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [mul_assoc, mul_comm (chartInvC e Q j) _, chartCoord_mul_inv, mul_one, sub_self]

theorem chartSub_rel_inr (e : ℕ) (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n) :
    ∑ k, chartSub e Q j (.inr k) * chartCoord e Q j k = 1 := by
  simp only [chartSub, Sum.elim_inr, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [mul_assoc, mul_comm (chartInvC e Q j) _, chartCoord_mul_inv, mul_one, sub_sub_cancel]
  rw [one_mul, mul_comm, chartCoord_mul_inv]

def chartHomA (e : ℕ) (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n) :
    MvPolynomial (Par e n) D →+* MvPolynomial (Par e n) (ChartDj Q j) :=
  eval₂Hom (C.comp ((algebraMap _ (ChartDj Q j)).comp ((Ideal.Quotient.mk Q).comp C))) (chartSub e Q j)

variable (e : ℕ) (R : Type*) [CommRing R] [Algebra (MvPolynomial (Par e n) D) R]

def chartModel (Q : Ideal (MvPolynomial (Fin n) D)) : Ideal (MvPolynomial (Fin n) R) :=
  Q.map (MvPolynomial.map ((algebraMap (MvPolynomial (Par e n) D) R).comp C))

variable (D) in

def chartPar : Par e n → R := fun p => algebraMap (MvPolynomial (Par e n) D) R (X p)

theorem chartModel_le (Q : Ideal (MvPolynomial (Fin n) D)) :
    chartModel e R Q ≤ secIdeal (chartModel e R Q) (chartPar D e R) :=
  le_sup_left.trans le_sup_left

abbrev ChartE' (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n) (S : Submonoid (MvPolynomial (Par e n) D)) :
    Type _ :=
  Localization (S.map (chartHomA e Q j))

variable (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n) (S : Submonoid (MvPolynomial (Par e n) D))

def chartHomR [IsLocalization S R] : R →+* ChartE' e Q j S :=
  IsLocalization.map (M := S) (ChartE' e Q j S) (chartHomA e Q j) (Submonoid.le_comap_map S)

theorem chartHomR_algebraMap [IsLocalization S R] (a : MvPolynomial (Par e n) D) :
    chartHomR e R Q j S (algebraMap _ R a) = algebraMap _ (ChartE' e Q j S) (chartHomA e Q j a) :=
  IsLocalization.map_eq _ _

def chartPhi0 [IsLocalization S R] : MvPolynomial (Fin n) R →+* ChartE' e Q j S :=
  eval₂Hom (chartHomR e R Q j S) fun k => algebraMap _ _ (chartCoord e Q j k)

theorem chartPhi0_map [IsLocalization S R] (q : MvPolynomial (Fin n) D) :
    chartPhi0 e R Q j S (MvPolynomial.map ((algebraMap (MvPolynomial (Par e n) D) R).comp C) q) =
      algebraMap (MvPolynomial (Par e n) (ChartDj Q j)) (ChartE' e Q j S)
        (C (algebraMap _ (ChartDj Q j) (Ideal.Quotient.mk Q q))) := by
  have : (chartPhi0 e R Q j S).comp (MvPolynomial.map ((algebraMap (MvPolynomial (Par e n) D) R).comp C)) =
      (algebraMap (MvPolynomial (Par e n) (ChartDj Q j)) (ChartE' e Q j S)).comp (C.comp ((algebraMap _ (ChartDj Q j)).comp
        (Ideal.Quotient.mk Q))) := by
    refine MvPolynomial.ringHom_ext (fun d => ?_) (fun k => ?_)
    · simp only [RingHom.comp_apply, map_C, chartPhi0, eval₂Hom_C, chartHomR_algebraMap, chartHomA]
    · simp only [RingHom.comp_apply, map_X, chartPhi0, eval₂Hom_X', chartCoord]
  exact RingHom.congr_fun this q

theorem secIdeal_le_ker_chartPhi0 [IsLocalization S R] :
    secIdeal (chartModel e R Q) (chartPar D e R) ≤ RingHom.ker (chartPhi0 e R Q j S) := by
  refine sup_le (sup_le ?_ ?_) ?_
  · rw [chartModel, Ideal.map_le_iff_le_comap]
    intro q hq
    rw [Ideal.mem_comap, RingHom.mem_ker, chartPhi0_map, Ideal.Quotient.eq_zero_iff_mem.mpr hq, map_zero,
      map_zero, map_zero]
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    have h := congrArg (algebraMap _ (ChartE' e Q j S)) (chartSub_rel_inl e Q j i)
    rw [map_zero] at h
    rw [← h]
    simp only [secForm, linForm, chartPar, map_sum, map_mul, chartPhi0, eval₂Hom_C, eval₂Hom_X',
      chartHomR_algebraMap, chartHomA]
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one,
      sub_eq_zero]
    have h := congrArg (algebraMap _ (ChartE' e Q j S)) (chartSub_rel_inr e Q j)
    rw [map_one] at h
    rw [← h]
    simp only [chartForm, linForm, chartPar, map_sum, map_mul, chartPhi0, eval₂Hom_C, eval₂Hom_X',
      chartHomR_algebraMap, chartHomA]

def chartPhi [IsLocalization S R] : SecAlg (chartModel e R Q) (chartPar D e R) →+* ChartE' e Q j S :=
  Ideal.Quotient.lift _ (chartPhi0 e R Q j S) fun _ ha => secIdeal_le_ker_chartPhi0 e R Q j S ha

abbrev ChartBj : Type _ :=
  Localization.Away (secCoord (chartModel e R Q) (chartPar D e R) j)

def chartKappa : MvPolynomial (Fin n) D →+* SecAlg (chartModel e R Q) (chartPar D e R) :=
  (Ideal.Quotient.mk _).comp (MvPolynomial.map ((algebraMap (MvPolynomial (Par e n) D) R).comp C))

theorem chartKappa_eq_zero {q : MvPolynomial (Fin n) D} (hq : q ∈ Q) : chartKappa e R Q q = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (chartModel_le e R Q (Ideal.mem_map_of_mem _ hq))

theorem chartKappa_X (k : Fin n) : chartKappa e R Q (X k) = secCoord (chartModel e R Q) (chartPar D e R) k := by
  simp only [chartKappa, RingHom.comp_apply, map_X, secCoord]

def chartChi : (MvPolynomial (Fin n) D ⧸ Q) →+* ChartBj e R Q j :=
  (algebraMap _ _).comp (Ideal.Quotient.lift Q (chartKappa e R Q) fun _ hq => chartKappa_eq_zero e R Q hq)

theorem chartChi_mk (q : MvPolynomial (Fin n) D) :
    chartChi e R Q j (Ideal.Quotient.mk Q q) = algebraMap _ (ChartBj e R Q j) (chartKappa e R Q q) := by
  simp only [chartChi, RingHom.comp_apply, Ideal.Quotient.lift_mk]

theorem chartChi_isUnit : IsUnit (chartChi e R Q j (chartCoordinate Q j)) := by
  rw [chartCoordinate, chartChi_mk, chartKappa_X]
  exact IsLocalization.Away.algebraMap_isUnit _

def chartPsiD : ChartDj Q j →+* ChartBj e R Q j :=
  IsLocalization.Away.lift (chartCoordinate Q j) (chartChi_isUnit e R Q j)

theorem chartPsiD_mk (q : MvPolynomial (Fin n) D) :
    chartPsiD e R Q j (algebraMap _ _ (Ideal.Quotient.mk Q q)) =
      algebraMap _ (ChartBj e R Q j) (chartKappa e R Q q) := by
  rw [chartPsiD, IsLocalization.Away.lift_eq, chartChi_mk]

def chartPsi0 : MvPolynomial (Par e n) (ChartDj Q j) →+* ChartBj e R Q j :=
  eval₂Hom (chartPsiD e R Q j) fun p =>
    algebraMap _ _ (algebraMap R (SecAlg (chartModel e R Q) (chartPar D e R)) (chartPar D e R p))

theorem chartPsi0_coord (k : Fin n) :
    chartPsi0 e R Q j (chartCoord e Q j k) =
      algebraMap _ (ChartBj e R Q j) (secCoord (chartModel e R Q) (chartPar D e R) k) := by
  rw [chartPsi0, chartCoord, eval₂Hom_C, chartPsiD_mk, chartKappa_X]

theorem chartPsi0_rel_inl (i : Fin e) :
    chartPsi0 e R Q j (∑ k, X (.inl (i, k)) * chartCoord e Q j k) = 0 := by
  have h0 : Ideal.Quotient.mk (secIdeal (chartModel e R Q) (chartPar D e R))
      (secForm (chartPar D e R) i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (Ideal.mem_sup_right
      (Ideal.subset_span ⟨i, rfl⟩)))
  have h1 := congrArg (algebraMap _ (ChartBj e R Q j)) h0
  rw [map_zero] at h1
  rw [← h1, map_sum, secForm, linForm, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_mul, map_mul, chartPsi0_coord, chartPsi0, eval₂Hom_X']
  rfl

theorem chartPsi0_rel_inr :
    chartPsi0 e R Q j (∑ k, X (.inr k) * chartCoord e Q j k - 1) = 0 := by
  have h0 : Ideal.Quotient.mk (secIdeal (chartModel e R Q) (chartPar D e R))
      (chartForm (chartPar D e R) - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _)))
  have h1 := congrArg (algebraMap _ (ChartBj e R Q j)) h0
  rw [map_zero] at h1
  rw [← h1]
  simp only [map_sub, map_one]
  rw [map_sum, chartForm, linForm, map_sum, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_mul, map_mul, chartPsi0_coord, chartPsi0, eval₂Hom_X']
  rfl

theorem chartPsi0_comp :
    (chartPsi0 e R Q j).comp (chartHomA e Q j) =
      (algebraMap _ (ChartBj e R Q j)).comp
        ((algebraMap R (SecAlg (chartModel e R Q) (chartPar D e R))).comp
          (algebraMap (MvPolynomial (Par e n) D) R)) := by
  refine MvPolynomial.ringHom_ext (fun d => ?_) (fun p => ?_)
  · simp only [RingHom.comp_apply, chartHomA, eval₂Hom_C]
    rw [chartPsi0, eval₂Hom_C, chartPsiD_mk]
    simp only [chartKappa, RingHom.comp_apply, map_C]
    rfl
  · simp only [RingHom.comp_apply, chartHomA, eval₂Hom_X']
    rcases p with ⟨i, k⟩ | k
    · simp only [chartSub, Sum.elim_inl, map_sub]
      split_ifs
      · rw [map_mul, chartPsi0_rel_inl, zero_mul, sub_zero, chartPsi0, eval₂Hom_X']
        rfl
      · rw [map_zero, sub_zero, chartPsi0, eval₂Hom_X']
        rfl
    · simp only [chartSub, Sum.elim_inr, map_sub]
      split_ifs
      · rw [map_mul, chartPsi0_rel_inr, zero_mul, sub_zero, chartPsi0, eval₂Hom_X']
        rfl
      · rw [map_zero, sub_zero, chartPsi0, eval₂Hom_X']
        rfl

def chartPsi [IsLocalization S R] : ChartE' e Q j S →+* ChartBj e R Q j :=
  IsLocalization.lift (M := S.map (chartHomA e Q j)) (g := chartPsi0 e R Q j) (by
    rintro ⟨_, s, hs, rfl⟩
    show IsUnit (chartPsi0 e R Q j (chartHomA e Q j s))
    have h := RingHom.congr_fun (chartPsi0_comp e R Q j) s
    simp only [RingHom.comp_apply] at h
    rw [h]
    exact ((IsLocalization.map_units R (⟨s, hs⟩ : S)).map _).map _)

theorem chartPsi_comp_homR [IsLocalization S R] :
    (chartPsi e R Q j S).comp (chartHomR e R Q j S) =
      (algebraMap _ (ChartBj e R Q j)).comp (algebraMap R (SecAlg (chartModel e R Q) (chartPar D e R))) := by
  refine IsLocalization.ringHom_ext S (RingHom.ext fun a => ?_)
  simp only [RingHom.comp_apply, chartHomR_algebraMap, chartPsi, IsLocalization.lift_eq]
  exact RingHom.congr_fun (chartPsi0_comp e R Q j) a

theorem chartPsi_comp_phi [IsLocalization S R] :
    (chartPsi e R Q j S).comp (chartPhi e R Q j S) = algebraMap _ (ChartBj e R Q j) := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r => ?_) (fun k => ?_))
  · have h := RingHom.congr_fun (chartPsi_comp_homR e R Q j S) r
    simp only [RingHom.comp_apply, chartPhi, Ideal.Quotient.lift_mk, chartPhi0, eval₂Hom_C] at h ⊢
    exact h
  · simp only [RingHom.comp_apply, chartPhi, Ideal.Quotient.lift_mk, chartPhi0, eval₂Hom_X', chartPsi,
      IsLocalization.lift_eq, chartPsi0_coord]
    rfl

theorem chart_pow_mul_eq_zero [IsDomain D] [Q.IsPrime] [IsLocalization S R]
    (hQ : ∀ c : D, C c ∈ Q → c = 0) (c : D) (hc : c ≠ 0)
    (b : SecAlg (chartModel e R Q) (chartPar D e R))
    (hb : algebraMap R _ (algebraMap (MvPolynomial (Par e n) D) R (C c)) * b = 0) :
    ∃ N : ℕ, secCoord (chartModel e R Q) (chartPar D e R) j ^ N * b = 0 := by
  by_cases hxj : (X j : MvPolynomial (Fin n) D) ∈ Q
  · refine ⟨1, ?_⟩
    have h0 : secCoord (chartModel e R Q) (chartPar D e R) j = 0 := by
      rw [← chartKappa_X, chartKappa_eq_zero e R Q hxj]
    rw [h0, pow_one, zero_mul]
  have hx0 : chartCoordinate Q j ≠ 0 := fun h => hxj (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have : IsDomain (ChartDj Q j) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hx0)
  have hΦ : chartPhi e R Q j S b = 0 := by
    have h := congrArg (chartPhi e R Q j S) hb
    rw [map_mul, map_zero] at h
    have hc' : chartPhi e R Q j S (algebraMap R _ (algebraMap (MvPolynomial (Par e n) D) R (C c))) =
        algebraMap (MvPolynomial (Par e n) (ChartDj Q j)) (ChartE' e Q j S)
          (C (algebraMap _ (ChartDj Q j) (Ideal.Quotient.mk Q (C c)))) := by
      show chartPhi0 e R Q j S (C (algebraMap (MvPolynomial (Par e n) D) R (C c))) = _
      rw [chartPhi0, eval₂Hom_C, chartHomR_algebraMap]
      simp only [chartHomA, eval₂Hom_C, RingHom.comp_apply]
    rw [hc'] at h
    have hcE : (C (algebraMap _ (ChartDj Q j) (Ideal.Quotient.mk Q (C c))) :
        MvPolynomial (Par e n) (ChartDj Q j)) ≠ 0 := by
      intro h0
      have h1 := C_injective (Par e n) (ChartDj Q j) (h0.trans (map_zero C).symm)
      have h2 := IsLocalization.injective (ChartDj Q j) (powers_le_nonZeroDivisors_of_noZeroDivisors hx0)
        (h1.trans (map_zero _).symm)
      exact hc (hQ c (Ideal.Quotient.eq_zero_iff_mem.mp h2))
    by_cases h0 : (0 : MvPolynomial (Par e n) (ChartDj Q j)) ∈ S.map (chartHomA e Q j)
    · have := IsLocalization.uniqueOfZeroMem (S := ChartE' e Q j S) h0
      exact Subsingleton.elim _ _
    · have hT := le_nonZeroDivisors_of_noZeroDivisors h0
      have : IsDomain (ChartE' e Q j S) := IsLocalization.isDomain_localization hT
      refine (mul_eq_zero.mp h).resolve_left fun h3 => hcE ?_
      exact IsLocalization.injective (ChartE' e Q j S) hT (h3.trans (map_zero _).symm)
  have hB : algebraMap _ (ChartBj e R Q j) b = 0 := by
    rw [← RingHom.congr_fun (chartPsi_comp_phi e R Q j S) b, RingHom.comp_apply, hΦ, map_zero]
  obtain ⟨⟨_, N, rfl⟩, hN⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (secCoord (chartModel e R Q) (chartPar D e R) j)) (ChartBj e R Q j) b).mp hB
  exact ⟨N, hN⟩

end Chart

theorem secAlg_const_mul_eq_zero {D : Type*} [CommRing D] [IsDomain D] {n : ℕ} (e : ℕ) (R : Type*)
    [CommRing R] [Algebra (MvPolynomial (Par e n) D) R] (Q : Ideal (MvPolynomial (Fin n) D)) [Q.IsPrime]
    (S : Submonoid (MvPolynomial (Par e n) D)) [IsLocalization S R] (hQ : ∀ c : D, C c ∈ Q → c = 0)
    (QR : Ideal (MvPolynomial (Fin n) R)) (hQR : QR = chartModel e R Q) (y : Par e n → R)
    (hy : y = chartPar D e R) (c : D) (hc : c ≠ 0) (b : SecAlg QR y)
    (hb : algebraMap R _ (algebraMap (MvPolynomial (Par e n) D) R (C c)) * b = 0) : b = 0 := by
  subst hQR hy
  exact eq_zero_of_secCoord_pow_mul _ _ b fun j => chart_pow_mul_eq_zero e R Q j S hQ c hc b hb

theorem dvd_pow_of_ne_zero_of_not_isUnit {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {r x : R} (hr : r ≠ 0) (hx : x ≠ 0) (hxu : ¬IsUnit x) :
    ∃ k : ℕ, r ∣ x ^ k := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.associated_pow_irreducible hr hϖ
  obtain ⟨b, hb⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx hϖ
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hxu (associated_one_iff_isUnit.mp (by simpa using hb))
  refine ⟨a, ha.dvd.trans ((pow_dvd_pow ϖ (Nat.le_mul_of_pos_left a (Nat.pos_of_ne_zero hb0))).trans ?_)⟩
  rw [pow_mul]
  exact (hb.pow_pow (n := a)).symm.dvd

theorem SecBTorsionFree.proof (h1 : ParDVRIsDVR.Statement) : SecBTorsionFree.Statement := by
  intro K _ _ n e I v hI r b hr hrb
  have := h1 K e n v
  have := hI.isPrime
  have hP : (integralModel I).IsPrime := by
    unfold integralModel
    infer_instance
  have hQ : ∀ a : 𝓞 K, C a ∈ integralModel I → a = 0 := by
    intro a ha
    by_contra h
    rw [integralModel, Ideal.mem_comap, map_C] at ha
    have hne : algebraMap (𝓞 K) K a ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr h
    exact hI.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ ha ((isUnit_iff_ne_zero.mpr hne).map C))
  obtain ⟨c, hcv, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hS0 : (parPrime e n v).primeCompl ≤ nonZeroDivisors (MvPolynomial (Par e n) (𝓞 K)) :=
    le_nonZeroDivisors_of_noZeroDivisors fun h => h (Ideal.zero_mem _)
  have hc'0 : algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (C c) ≠ 0 := by
    intro h0
    have h2 := IsLocalization.injective (ParDVR e n v) hS0 (h0.trans (map_zero _).symm)
    exact hc0 (C_injective (Par e n) (𝓞 K) (h2.trans (map_zero C).symm))
  have hc'u : ¬IsUnit (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (C c)) := fun hu =>
    ((IsLocalization.AtPrime.isUnit_to_map_iff (ParDVR e n v) (parPrime e n v) (C c)).mp hu)
      (Ideal.mem_map_of_mem C hcv)
  obtain ⟨k, q, hq⟩ := dvd_pow_of_ne_zero_of_not_isUnit hr hc'0 hc'u
  have hmodel : modelR e I v = chartModel e (ParDVR e n v) (integralModel I) := by
    rw [modelR, chartModel, IsScalarTower.algebraMap_eq (𝓞 K) (MvPolynomial (Par e n) (𝓞 K))
      (ParDVR e n v), MvPolynomial.algebraMap_eq]
  have hrb' : algebraMap (ParDVR e n v) (SecB e I v) r * b = 0 := (Algebra.smul_def r b).symm.trans hrb
  refine secAlg_const_mul_eq_zero e (ParDVR e n v) (integralModel I) (parPrime e n v).primeCompl hQ
    (modelR e I v) hmodel (parY e n v) rfl (c ^ k) (pow_ne_zero _ hc0) b ?_
  rw [map_pow, map_pow, hq, map_mul, mul_comm (algebraMap _ _ r), mul_assoc, hrb', mul_zero]

end

end GroundTheory.Heights₂.Heights.Vertical
