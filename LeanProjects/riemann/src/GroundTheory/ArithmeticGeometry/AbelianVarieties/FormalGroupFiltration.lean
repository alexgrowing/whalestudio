import Mathlib
import GroundTheory.ArithmeticGeometry.AbelianVarieties.FormalGroupIdeal

namespace GroundTheory.Arith.Abelian

noncomputable section

open IsLocalRing

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  [IsAdicComplete (maximalIdeal 𝒪) 𝒪]

section Values

variable (W : WeierstrassCurve 𝒪)

def wVal (z : 𝒪) : 𝒪 := psEvalAt (formalW W) (fun _ : Unit => z)

def vVal (z : 𝒪) : 𝒪 := psEvalAt (formalV W) (fun _ : Unit => z)

theorem evAlgHom_unit_X {z : 𝒪} (hz : z ∈ maximalIdeal 𝒪) :
    evAlgHom (fun _ : Unit => z) (fun _ => hz) PowerSeries.X = z := by
  rw [evAlgHom_apply]; exact psEvalAt_X _ ()

theorem evAlgHom_unit_C {z : 𝒪} (hz : z ∈ maximalIdeal 𝒪) (r : 𝒪) :
    evAlgHom (fun _ : Unit => z) (fun _ => hz) (PowerSeries.C r) = r := by
  rw [← PowerSeries.algebraMap_eq, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]

theorem map_C_evAlgHom {z : 𝒪} (hz : z ∈ maximalIdeal 𝒪) :
    (W.map PowerSeries.C).map (evAlgHom (fun _ : Unit => z) (fun _ => hz) : PowerSeries 𝒪 →+* 𝒪)
      = W := by
  rw [WeierstrassCurve.map_map]
  ext <;> simp [evAlgHom_unit_C]

theorem zwPoly_wVal {z : 𝒪} (hz : z ∈ maximalIdeal 𝒪) : zwPoly W z (wVal W z) = 0 := by
  have := congrArg (evAlgHom (fun _ : Unit => z) (fun _ => hz) : PowerSeries 𝒪 →+* 𝒪)
    (zwPoly_formalW W)
  rw [map_zwPoly, map_zero, map_C_evAlgHom] at this
  have h2 : zwPoly W (evAlgHom (fun _ : Unit => z) (fun _ => hz) PowerSeries.X)
      (evAlgHom (fun _ : Unit => z) (fun _ => hz) (formalW W)) = 0 := this
  rwa [evAlgHom_unit_X, evAlgHom_apply] at h2

theorem wVal_eq {z : 𝒪} (hz : z ∈ maximalIdeal 𝒪) : wVal W z = z ^ 3 * vVal W z := by
  rw [wVal, vVal, ← evAlgHom_apply _ (fun _ => hz), ← evAlgHom_apply _ (fun _ => hz), formalW,
    map_mul, map_pow, evAlgHom_unit_X]

theorem isUnit_vVal {z : 𝒪} (hz : z ∈ maximalIdeal 𝒪) : IsUnit (vVal W z) := by
  have h : vVal W z - 1 ∈ maximalIdeal 𝒪 := by
    have := psEvalAt_mem (f := formalV W - 1) (by
      rw [map_sub, map_one, show MvPowerSeries.constantCoeff (formalV W) = 1 from
        constantCoeff_formalV W, sub_self]; exact zero_mem _) (a := fun _ : Unit => z) (fun _ => hz)
    rwa [← evAlgHom_apply _ (fun _ => hz), map_sub, map_one, evAlgHom_apply] at this
  by_contra hu
  have h1 : vVal W z ∈ maximalIdeal 𝒪 := (mem_maximalIdeal _).2 hu
  have : (1 : 𝒪) ∈ maximalIdeal 𝒪 := by
    have := Ideal.sub_mem _ h1 h
    rwa [sub_sub_cancel] at this
  exact (maximalIdeal.isMaximal 𝒪).ne_top ((Ideal.eq_top_iff_one _).2 this)

theorem wVal_mem {z : 𝒪} (hz : z ∈ maximalIdeal 𝒪) : wVal W z ∈ maximalIdeal 𝒪 :=
  psEvalAt_mem (by rw [show MvPowerSeries.constantCoeff (formalW W) = 0 from
    constantCoeff_formalW W]; exact zero_mem _) (fun _ => hz)

theorem wVal_ne_zero {z : 𝒪} (hz : z ∈ maximalIdeal 𝒪) (hz0 : z ≠ 0) : wVal W z ≠ 0 := by
  rw [wVal_eq W hz]
  exact mul_ne_zero (pow_ne_zero _ hz0) (isUnit_vVal W hz).ne_zero

theorem eq_wVal {z w : 𝒪} (hz : z ∈ maximalIdeal 𝒪) (hw : w ∈ maximalIdeal 𝒪)
    (h : zwPoly W z w = 0) : w = wVal W z := by
  refine eq_of_zwPoly_eq_zero W h (zwPoly_wVal W hz) ?_
  have hm : W.a₁ * z + W.a₂ * z ^ 2 + W.a₃ * (w + wVal W z) + W.a₄ * z * (w + wVal W z) +
      W.a₆ * (w ^ 2 + w * wVal W z + wVal W z ^ 2) ∈ maximalIdeal 𝒪 := by
    have hw' := wVal_mem W hz
    refine Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_) ?_) ?_
    · exact Ideal.mul_mem_left _ _ hz
    · exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hz _ (by norm_num))
    · exact Ideal.mul_mem_left _ _ (Ideal.add_mem _ hw hw')
    · exact Ideal.mul_mem_left _ _ (Ideal.add_mem _ hw hw')
    · exact Ideal.mul_mem_left _ _ (Ideal.add_mem _ (Ideal.add_mem _
        (Ideal.pow_mem_of_mem _ hw _ (by norm_num)) (Ideal.mul_mem_right _ _ hw))
        (Ideal.pow_mem_of_mem _ hw' _ (by norm_num)))
  by_contra hu
  have h1 := (mem_maximalIdeal _).2 hu
  have := Ideal.add_mem _ h1 hm
  rw [sub_add_cancel] at this
  exact (maximalIdeal.isMaximal 𝒪).ne_top ((Ideal.eq_top_iff_one _).2 this)

end Values

section Points

variable (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W : WeierstrassCurve 𝒪)

omit [IsFractionRing 𝒪 K] in
theorem zwPoly_wVal_map {z : 𝒪} (hz : z ∈ maximalIdeal 𝒪) :
    zwPoly (W.map (algebraMap 𝒪 K)) (algebraMap 𝒪 K z) (algebraMap 𝒪 K (wVal W z)) = 0 := by
  rw [← map_zwPoly, zwPoly_wVal W hz, map_zero]

omit [IsAdicComplete (maximalIdeal 𝒪) 𝒪] in
theorem infinite_of_isDiscreteValuationRing : Infinite 𝒪 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪
  refine Infinite.of_injective (fun n : ℕ => ϖ ^ n) fun m n h => ?_
  exact pow_injective_of_not_isUnit hϖ.not_isUnit hϖ.ne_zero h

omit [IsAdicComplete (maximalIdeal 𝒪) 𝒪] in
theorem infinite_maximalIdeal : (maximalIdeal 𝒪 : Set 𝒪).Infinite := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪
  have hm : ∀ n : ℕ, ϖ ^ (n + 1) ∈ maximalIdeal 𝒪 := fun n =>
    Ideal.pow_mem_of_mem _ ((mem_maximalIdeal _).2 hϖ.not_isUnit) _ (Nat.succ_pos n)
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ϖ ^ (n + 1)) ?_ hm
  intro m n h
  have := pow_injective_of_not_isUnit hϖ.not_isUnit hϖ.ne_zero h
  simpa using this

include 𝒪 in
omit [IsAdicComplete (maximalIdeal 𝒪) 𝒪] in
theorem infinite_fraction : Infinite K :=
  haveI := infinite_of_isDiscreteValuationRing (𝒪 := 𝒪)
  Infinite.of_injective _ (IsFractionRing.injective 𝒪 K)

variable [(W.map (algebraMap 𝒪 K)).IsElliptic]

def pointE (x : MaxIdealPoint (formalGroup W)) : (W.map (algebraMap 𝒪 K)).toAffine.Point :=
  zwPoint (W.map (algebraMap 𝒪 K)) (algebraMap 𝒪 K x.val) (algebraMap 𝒪 K (wVal W x.val))

theorem wVal_zero : wVal W 0 = 0 := by
  rw [wVal_eq W (zero_mem _), zero_pow (by norm_num), zero_mul]

omit [IsFractionRing 𝒪 K] in
theorem pointE_zero : pointE K W 0 = 0 := by
  rw [pointE, zwPoint, dif_neg]
  rintro ⟨-, h⟩
  apply h
  rw [MaxIdealPoint.val_zero, wVal_zero, map_zero]

theorem pointE_of_ne_zero {x : MaxIdealPoint (formalGroup W)} (hx : x.val ≠ 0) :
    pointE K W x = WeierstrassCurve.Affine.Point.mk (equation_of_zwPoly _
      (zwPoly_wVal_map K W x.val_mem)
      ((map_ne_zero_iff _ (IsFractionRing.injective 𝒪 K)).2 (wVal_ne_zero W x.val_mem hx))) :=
  zwPoint_of _ (zwPoly_wVal_map K W x.val_mem)
    ((map_ne_zero_iff _ (IsFractionRing.injective 𝒪 K)).2 (wVal_ne_zero W x.val_mem hx))

theorem pointE_ne_zero {x : MaxIdealPoint (formalGroup W)} (hx : x.val ≠ 0) :
    pointE K W x ≠ 0 := by
  rw [pointE_of_ne_zero K W hx]
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

theorem pointE_eq_zero_iff {x : MaxIdealPoint (formalGroup W)} : pointE K W x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    exact pointE_ne_zero K W (fun h0 => hx (MaxIdealPoint.ext h0)) h
  · rintro rfl; exact pointE_zero K W

theorem pointE_injective : Function.Injective (pointE K W) := by
  intro x y h
  by_cases hx : x.val = 0
  · have hx' : x = 0 := MaxIdealPoint.ext hx
    rw [hx', pointE_zero, eq_comm, pointE_eq_zero_iff] at h
    rw [hx', h]
  by_cases hy : y.val = 0
  · have hy' : y = 0 := MaxIdealPoint.ext hy
    rw [hy', pointE_zero, pointE_eq_zero_iff] at h
    exact absurd h (fun h' => hx (by rw [h']; rfl))
  set ι := algebraMap 𝒪 K
  have hι : Function.Injective ι := IsFractionRing.injective 𝒪 K
  have hwx : ι (wVal W x.val) ≠ 0 := (map_ne_zero_iff _ hι).2 (wVal_ne_zero W x.val_mem hx)
  have hwy : ι (wVal W y.val) ≠ 0 := (map_ne_zero_iff _ hι).2 (wVal_ne_zero W y.val_mem hy)
  rw [pointE_of_ne_zero K W hx, pointE_of_ne_zero K W hy] at h
  simp only [WeierstrassCurve.Affine.Point.mk, WeierstrassCurve.Affine.Point.some.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have e : wVal W x.val = wVal W y.val := by
    have := congrArg (fun t => -t⁻¹) h2
    simpa [div_eq_mul_inv] using this
  rw [e, div_left_inj' hwy] at h1
  exact MaxIdealPoint.ext (hι h1)

theorem val_neg_eq (x : MaxIdealPoint (formalGroup W)) :
    (-x).val = psEvalAt (invSeries W) (fun _ : Unit => x.val) := by
  rw [MaxIdealPoint.val_neg, inv_formalGroup]

theorem pointE_neg (x : MaxIdealPoint (formalGroup W)) : pointE K W (-x) = -pointE K W x := by
  by_cases hx : x.val = 0
  · have hx' : x = 0 := MaxIdealPoint.ext hx
    rw [hx', neg_zero, pointE_zero]
    rfl
  set ι := algebraMap 𝒪 K
  have hι : Function.Injective ι := IsFractionRing.injective 𝒪 K
  set ψ := evAlgHom (fun _ : Unit => x.val) (fun _ => x.val_mem)
  set e := ψ (MvPowerSeries.invOfUnit (invDen W) 1) with he_def
  have ψX : ψ PowerSeries.X = x.val := evAlgHom_unit_X x.val_mem
  have ψC : ∀ r, ψ (PowerSeries.C r) = r := evAlgHom_unit_C x.val_mem
  have ψw : ψ (formalW W) = wVal W x.val := evAlgHom_apply _ _ _
  have he : (1 - W.a₁ * x.val - W.a₃ * wVal W x.val) * e = 1 := by
    have := congrArg ψ (mul_invOfUnit_one (constantCoeff_invDen W))
    rwa [map_mul, map_one, invDen, map_sub, map_sub, map_one, map_mul, map_mul, ψC, ψC, ψX,
      ψw] at this
  have hz : (-x).val = -x.val * e := by
    rw [val_neg_eq, ← evAlgHom_apply _ (fun _ => x.val_mem), invSeries, map_mul, map_neg, ψX]
  have hw : wVal W (-x).val = -wVal W x.val * e := by
    rw [wVal, val_neg_eq]
    rw [← psEvalAt_powerSeries_subst (PowerSeries.HasSubst.of_constantCoeff_zero
      (constantCoeff_invSeries W)) _ (fun _ => x.val_mem)]
    change psEvalAt (wAt W (invSeries W)) _ = _
    rw [wAt_invSeries, ← evAlgHom_apply _ (fun _ => x.val_mem), map_mul, map_neg, ψw]
  have hw0 : ι (wVal W x.val) ≠ 0 := (map_ne_zero_iff _ hι).2 (wVal_ne_zero W x.val_mem hx)
  have he' : (1 - (W.map ι).a₁ * ι x.val - (W.map ι).a₃ * ι (wVal W x.val)) * ι e = 1 := by
    have := congrArg ι he
    rwa [map_mul, map_sub, map_sub, map_one, map_mul, map_mul] at this
  obtain ⟨-, -, hneg⟩ := neg_zwPoint (W.map ι) (zwPoly_wVal_map K W x.val_mem) hw0 he'
  rw [pointE, pointE, hneg, hw, hz, map_mul, map_mul, map_neg, map_neg]

variable [DecidableEq K]

theorem pointE_add_of_ne {x y : MaxIdealPoint (formalGroup W)} (hx : x.val ≠ 0) (hy : y.val ≠ 0)
    (hxy : algebraMap 𝒪 K x.val / algebraMap 𝒪 K (wVal W x.val) ≠
      algebraMap 𝒪 K y.val / algebraMap 𝒪 K (wVal W y.val)) :
    pointE K W (x + y) = pointE K W x + pointE K W y := by
  have : Infinite K := infinite_fraction (𝒪 := 𝒪) K
  set ι := algebraMap 𝒪 K
  have hι : Function.Injective ι := IsFractionRing.injective 𝒪 K
  have hab := MaxIdealPoint.pair_mem x y
  set ψ := evAlgHom ![x.val, y.val] hab with hψdef
  have ψX0 : ψ (MvPowerSeries.X 0) = x.val := by rw [evAlgHom_apply, psEvalAt_X]; rfl
  have ψX1 : ψ (MvPowerSeries.X 1) = y.val := by rw [evAlgHom_apply, psEvalAt_X]; rfl
  have ψw : ∀ i, ψ (wAt W (MvPowerSeries.X i)) = wVal W (![x.val, y.val] i) := fun i => by
    rw [evAlgHom_apply, wAt, psEvalAt_powerSeries_subst (PowerSeries.HasSubst.X i) _ hab,
      psEvalAt_X, wVal]
  have hc0 : ∀ f : MvPowerSeries (Fin 2) 𝒪, MvPowerSeries.constantCoeff f = 0 →
      ψ f ∈ maximalIdeal 𝒪 := fun f hf => by
    rw [evAlgHom_apply]; exact psEvalAt_mem (by rw [hf]; exact zero_mem _) hab
  have hW : W.map (algebraMap 𝒪 𝒪) = W := by
    rw [Algebra.algebraMap_self]; exact WeierstrassCurve.map_id W
  set l := ψ (addSlope W)
  set n := ψ (addIntercept W)
  set b := ψ (MvPowerSeries.invOfUnit (secantB (W.map MvPowerSeries.C) (addSlope W)) 1)
  set z₃ := ψ (thirdZ W)
  set w₃ := ψ (thirdW W)
  set e := ψ (MvPowerSeries.invOfUnit (negDen W) 1)
  have rl₁ : wVal W x.val = l * x.val + n := by
    have := apply_wAt_X_zero W ψ; rwa [ψw, ψX0] at this
  have rl₂ : wVal W y.val = l * y.val + n := by
    have := apply_wAt_X_one W ψ; rwa [ψw, ψX1] at this
  have rb : secantB W l * b = 1 := by
    have := secantB_apply_mul W ψ; rwa [hW] at this
  have rz₃ : z₃ = -x.val - y.val - secantA W l n * b := by
    have := apply_thirdZ W ψ; rwa [ψX0, ψX1, hW] at this
  have rw₃ : w₃ = l * z₃ + n := apply_thirdW W ψ
  have re : (1 - W.a₁ * z₃ - W.a₃ * w₃) * e = 1 := by
    have := negDen_apply_mul W ψ; rwa [Algebra.algebraMap_self, RingHom.id_apply,
      RingHom.id_apply] at this
  have rF : (x + y).val = -z₃ * e := by
    rw [MaxIdealPoint.val_add, formalGroup_toPowerSeries, ← evAlgHom_apply _ hab, apply_addSeries]

  set V := W.map ι
  have hw₁ : ι (wVal W x.val) ≠ 0 := (map_ne_zero_iff ι hι).2 (wVal_ne_zero W x.val_mem hx)
  have hw₂ : ι (wVal W y.val) ≠ 0 := (map_ne_zero_iff ι hι).2 (wVal_ne_zero W y.val_mem hy)
  have hb' : secantB V (ι l) * ι b = 1 := by
    have := congrArg ι rb; rwa [map_mul, map_secantB, map_one] at this
  have hz₃' : ι z₃ = -ι x.val - ι y.val - secantA V (ι l) (ι n) * ι b := by
    rw [rz₃, map_sub, map_sub, map_neg, map_mul, map_secantA]
  have hw₃' : ι w₃ = ι l * ι z₃ + ι n := by rw [rw₃, map_add, map_mul]
  obtain ⟨h₃, hw₃0, hsum⟩ := secant_spec V (zwPoly_wVal_map K W x.val_mem)
    (zwPoly_wVal_map K W y.val_mem) hw₁ hw₂ (by rw [rl₁, map_add, map_mul])
    (by rw [rl₂, map_add, map_mul]) hb' hxy hz₃' hw₃'
  have he' : (1 - V.a₁ * ι z₃ - V.a₃ * ι w₃) * ι e = 1 := by
    have := congrArg ι re
    rwa [map_mul, map_sub, map_sub, map_mul, map_mul, map_one] at this
  obtain ⟨h', -, hneg⟩ := neg_zwPoint V h₃ hw₃0 he'
  have hF : (x + y).val ∈ maximalIdeal 𝒪 := (x + y).val_mem
  have hS : zwPoly W (x + y).val (-w₃ * e) = 0 := by
    apply hι
    rw [map_zwPoly, map_zero, rF, map_mul, map_mul, map_neg, map_neg]
    exact h'
  have hwF : -w₃ * e = wVal W (x + y).val := by
    refine eq_wVal W hF ?_ hS
    exact Ideal.mul_mem_right _ _ ((Ideal.neg_mem_iff _).2 (hc0 _ (constantCoeff_thirdW W)))
  rw [pointE, pointE, pointE, hsum, hneg, ← hwF, rF, map_mul, map_mul, map_neg, map_neg]

theorem pointE_add_of_ne' {x y : MaxIdealPoint (formalGroup W)} (hx : x ≠ 0) (hy : y ≠ 0)
    (h₁ : y ≠ x) (h₂ : y ≠ -x) : pointE K W (x + y) = pointE K W x + pointE K W y := by
  classical
  have hx' : x.val ≠ 0 := fun h => hx (MaxIdealPoint.ext h)
  have hy' : y.val ≠ 0 := fun h => hy (MaxIdealPoint.ext h)
  refine pointE_add_of_ne K W hx' hy' ?_
  intro hxy
  have hι := IsFractionRing.injective 𝒪 K
  have p₁ := WeierstrassCurve.Affine.equation_iff_nonsingular.mp (equation_of_zwPoly _
    (zwPoly_wVal_map K W x.val_mem) ((map_ne_zero_iff _ hι).2 (wVal_ne_zero W x.val_mem hx')))
  have p₂ := WeierstrassCurve.Affine.equation_iff_nonsingular.mp (equation_of_zwPoly _
    (zwPoly_wVal_map K W y.val_mem) ((map_ne_zero_iff _ hι).2 (wVal_ne_zero W y.val_mem hy')))
  have e₁ : pointE K W x = WeierstrassCurve.Affine.Point.some _ _ p₁ := pointE_of_ne_zero K W hx'
  have e₂ : pointE K W y = WeierstrassCurve.Affine.Point.some _ _ p₂ := pointE_of_ne_zero K W hy'
  rcases (WeierstrassCurve.Affine.Point.X_eq_iff (h₁ := p₁) (h₂ := p₂)).1 hxy with h | h
  · rw [← e₁, ← e₂] at h
    exact h₁ (pointE_injective K W h).symm
  · rw [← e₁, ← e₂, ← pointE_neg] at h
    exact h₂ (by rw [pointE_injective K W h, neg_neg])

theorem pointE_add_self (a : MaxIdealPoint (formalGroup W)) :
    pointE K W (a + a) = pointE K W a + pointE K W a := by
  classical
  by_cases ha : a = 0
  · rw [ha, add_zero, pointE_zero, add_zero]
  by_cases h2 : a + a = 0
  · have hna : -a = a := (eq_neg_of_add_eq_zero_left h2).symm
    have hP : pointE K W a = -pointE K W a := by rw [← pointE_neg, hna]
    rw [h2, pointE_zero]
    nth_rewrite 2 [hP]
    rw [add_neg_cancel]
  have : Infinite (MaxIdealPoint (formalGroup W)) := (infinite_maximalIdeal (𝒪 := 𝒪)).to_subtype
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset
    ({0, a, -a, a + a, -(a + a)} : Finset (MaxIdealPoint (formalGroup W)))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
  obtain ⟨ht0, hta, htna, ht2a, htn2a⟩ := ht
  have e₁ := pointE_add_of_ne' K W ha ht0 hta htna
  have hat : a + t ≠ 0 := fun h => htna (eq_neg_of_add_eq_zero_right h)
  have e₂ := pointE_add_of_ne' K W hat ha (fun h => ht0 (by
      have := congrArg (fun s => -a + s) h; simpa using this.symm))
    (fun h => htn2a (by
      have h' : -a = a + t := neg_eq_iff_eq_neg.mpr h
      rw [neg_add', h']; abel))
  have e₃ := pointE_add_of_ne' K W h2 ht0 ht2a htn2a
  have hsum : a + t + a = a + a + t := by abel
  rw [hsum, e₃, e₁] at e₂
  have : pointE K W (a + a) = pointE K W a + pointE K W t + pointE K W a - pointE K W t := by
    rw [← e₂]; abel
  rw [this]; abel

theorem pointE_add (x y : MaxIdealPoint (formalGroup W)) :
    pointE K W (x + y) = pointE K W x + pointE K W y := by
  by_cases hx : x = 0
  · rw [hx, zero_add, pointE_zero, zero_add]
  by_cases hy : y = 0
  · rw [hy, add_zero, pointE_zero, add_zero]
  by_cases h₁ : y = x
  · rw [h₁]; exact pointE_add_self K W x
  by_cases h₂ : y = -x
  · rw [h₂, add_neg_cancel, pointE_zero, pointE_neg, add_neg_cancel]
  exact pointE_add_of_ne' K W hx hy h₁ h₂

def pointEHom : MaxIdealPoint (formalGroup W) →+ (W.map (algebraMap 𝒪 K)).toAffine.Point where
  toFun := pointE K W
  map_zero' := pointE_zero K W
  map_add' := pointE_add K W

omit [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
  [IsFractionRing 𝒪 K] [(W.map (algebraMap 𝒪 K)).IsElliptic] [DecidableEq K] in
theorem zwPoly_of_equation {X Y : K} (h : (W.map (algebraMap 𝒪 K)).toAffine.Equation X Y)
    (hY : Y ≠ 0) : zwPoly (W.map (algebraMap 𝒪 K)) (-X / Y) (-1 / Y) = 0 := by
  rw [WeierstrassCurve.Affine.equation_iff] at h
  have key : zwPoly (W.map (algebraMap 𝒪 K)) (-X / Y) (-1 / Y) =
      (Y ^ 2 + (W.map (algebraMap 𝒪 K)).a₁ * X * Y + (W.map (algebraMap 𝒪 K)).a₃ * Y -
        (X ^ 3 + (W.map (algebraMap 𝒪 K)).a₂ * X ^ 2 + (W.map (algebraMap 𝒪 K)).a₄ * X +
          (W.map (algebraMap 𝒪 K)).a₆)) / Y ^ 3 := by
    unfold zwPoly; field_simp; ring
  rw [key, h, sub_self, zero_div]

omit [DecidableEq K] in

theorem mem_range_pointE_iff (P : (W.map (algebraMap 𝒪 K)).toAffine.Point) :
    P ∈ Set.range (pointE K W) ↔ ∀ (x y : K)
      (h : (W.map (algebraMap 𝒪 K)).toAffine.Nonsingular x y),
      P = .some x y h → x ∉ Set.range (algebraMap 𝒪 K) := by
  constructor
  · have hι : Function.Injective (algebraMap 𝒪 K) := IsFractionRing.injective 𝒪 K
    rintro ⟨z, rfl⟩ x y h hP ⟨r, hr⟩
    have hz : z.val ≠ 0 := by
      intro h0
      have : z = 0 := MaxIdealPoint.ext h0
      rw [this, pointE_zero] at hP
      exact WeierstrassCurve.Affine.Point.some_ne_zero h hP.symm
    rw [pointE_of_ne_zero K W hz] at hP
    simp only [WeierstrassCurve.Affine.Point.mk, WeierstrassCurve.Affine.Point.some.injEq] at hP
    obtain ⟨hx, -⟩ := hP
    have hw0 : (algebraMap 𝒪 K) (wVal W z.val) ≠ 0 :=
      (map_ne_zero_iff _ hι).2 (wVal_ne_zero W z.val_mem hz)
    rw [← hx, eq_div_iff hw0, ← map_mul] at hr
    have hr' := hι hr
    rw [wVal_eq W z.val_mem] at hr'
    have hu : IsUnit z.val := by
      refine isUnit_iff_exists_inv.2 ⟨r * z.val * vVal W z.val, ?_⟩
      have : z.val * (r * z.val ^ 2 * vVal W z.val - 1) = 0 := by linear_combination hr'
      have h1 := sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hz)
      linear_combination h1
    exact (mem_maximalIdeal _).1 z.val_mem hu
  · intro hP
    cases P with
    | zero => exact ⟨0, pointE_zero K W⟩
    | @some X Y hXY => ?_
    have hι : Function.Injective (algebraMap 𝒪 K) := IsFractionRing.injective 𝒪 K
    have hX := hP X Y hXY rfl
    have hXY' := hXY

    have hX0 : X ≠ 0 := fun h => hX ⟨0, by rw [h, map_zero]⟩
    obtain ⟨t, ht⟩ : ∃ t, (algebraMap 𝒪 K) t = X⁻¹ := by
      rcases ValuationRing.isInteger_or_isInteger 𝒪 X with h | h
      · exact absurd h hX
      · exact h
    have htm : t ∈ maximalIdeal 𝒪 := by
      refine (mem_maximalIdeal _).2 fun hu => hX ⟨↑hu.unit⁻¹, ?_⟩
      rw [← inv_inv X, ← ht]
      exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, hu.val_inv_mul, map_one])

    have hE := hXY.1
    rw [WeierstrassCurve.Affine.equation_iff] at hE
    have hU : Y / X ∉ Set.range (algebraMap 𝒪 K) := by
      rintro ⟨u, hu⟩
      have key : (algebraMap 𝒪 K) (u ^ 2 * t + W.a₁ * u * t + W.a₃ * u * t ^ 2 -
          (1 + W.a₂ * t + W.a₄ * t ^ 2 + W.a₆ * t ^ 3)) = 0 := by
        simp only [map_sub, map_add, map_mul, map_pow, map_one, hu, ht]
        simp only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
          WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at hE
        field_simp
        linear_combination hE
      have k2 := sub_eq_zero.1 (hι (key.trans (map_zero (algebraMap 𝒪 K)).symm))
      have hm : u ^ 2 * t + W.a₁ * u * t + W.a₃ * u * t ^ 2 - (W.a₂ * t + W.a₄ * t ^ 2 +
          W.a₆ * t ^ 3) ∈ maximalIdeal 𝒪 := by
        refine Ideal.sub_mem _ (Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_)
          (Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_) <;>
          first
          | exact Ideal.mul_mem_left _ _ htm
          | exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ htm _ (by norm_num))
      have : (1 : 𝒪) ∈ maximalIdeal 𝒪 := by
        have e : (1 : 𝒪) = u ^ 2 * t + W.a₁ * u * t + W.a₃ * u * t ^ 2 - (W.a₂ * t + W.a₄ * t ^ 2 +
            W.a₆ * t ^ 3) := by linear_combination -k2
        rw [e]; exact hm
      exact (maximalIdeal.isMaximal 𝒪).ne_top ((Ideal.eq_top_iff_one _).2 this)
    have hY0 : Y ≠ 0 := fun h => hU ⟨0, by rw [h, zero_div, map_zero]⟩
    obtain ⟨s, hs⟩ : ∃ s, (algebraMap 𝒪 K) s = (Y / X)⁻¹ := by
      rcases ValuationRing.isInteger_or_isInteger 𝒪 (Y / X) with h | h
      · exact absurd h hU
      · exact h
    have hsm : s ∈ maximalIdeal 𝒪 := by
      refine (mem_maximalIdeal _).2 fun hu => hU ⟨↑hu.unit⁻¹, ?_⟩
      rw [← inv_inv (Y / X), ← hs]
      exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, hu.val_inv_mul, map_one])
    have hz : -s ∈ maximalIdeal 𝒪 := (Ideal.neg_mem_iff _).2 hsm
    have hw : -(t * s) ∈ maximalIdeal 𝒪 := (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_right _ _ htm)
    have hzι : (algebraMap 𝒪 K) (-s) = -X / Y := by rw [map_neg, hs]; field_simp
    have hwι : (algebraMap 𝒪 K) (-(t * s)) = -1 / Y := by rw [map_neg, map_mul, hs, ht]; field_simp
    have hzw : zwPoly W (-s) (-(t * s)) = 0 := by
      apply hι
      rw [map_zwPoly, hzι, hwι, map_zero]
      exact zwPoly_of_equation K W hXY.1 hY0
    have hwv := eq_wVal W hz hw hzw
    refine ⟨MaxIdealPoint.mk (-s) hz, ?_⟩
    have hs0 : (MaxIdealPoint.mk (-s) hz : MaxIdealPoint (formalGroup W)).val ≠ 0 := by
      rw [MaxIdealPoint.val_mk, neg_ne_zero]
      intro h; apply hY0
      have : (algebraMap 𝒪 K) s = 0 := by rw [h, map_zero]
      rw [hs, inv_eq_zero, div_eq_zero_iff] at this
      exact this.resolve_right hX0
    rw [pointE_of_ne_zero K W hs0]
    simp only [WeierstrassCurve.Affine.Point.mk, WeierstrassCurve.Affine.Point.some.injEq,
      MaxIdealPoint.val_mk]
    rw [← hwv, hzι, hwι]
    constructor <;> field_simp

def E1 : AddSubgroup (W.map (algebraMap 𝒪 K)).toAffine.Point :=
  (pointEHom K W).range.copy {P | ∀ (x y : K)
    (h : (W.map (algebraMap 𝒪 K)).toAffine.Nonsingular x y),
    P = .some x y h → x ∉ Set.range (algebraMap 𝒪 K)}
    (by ext P; rw [Set.mem_ofPred_eq, ← mem_range_pointE_iff]; rfl)

theorem E1_eq_range : E1 K W = (pointEHom K W).range :=
  AddSubgroup.copy_eq _ _ _

def e1Equiv : MaxIdealPoint (formalGroup W) ≃+ E1 K W :=
  (AddMonoidHom.ofInjective (f := pointEHom K W) (pointE_injective K W)).trans
    (AddEquiv.addSubgroupCongr (E1_eq_range K W).symm)

end Points

end

end GroundTheory.Arith.Abelian
