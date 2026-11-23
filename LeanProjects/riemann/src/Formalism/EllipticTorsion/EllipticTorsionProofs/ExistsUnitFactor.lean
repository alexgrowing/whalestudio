import Formalism.EllipticTorsion.WChordSeries

open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL

namespace WeierstrassCoordinateSubstitution

variable {K : Type u} [Field K]

theorem exists_unit_factor {W : WeierstrassCurve K} {w : PowerSeries K} (hw : WFixed W w) :
    ∃ u : PowerSeries K, w = X ^ 3 * u ∧ constantCoeff u = 1 := by
  obtain ⟨h0, heq⟩ := hw
  have hX : (X : PowerSeries K) ≠ 0 := PowerSeries.X_ne_zero
  obtain ⟨v, rfl⟩ := PowerSeries.X_dvd_iff.mpr h0
  have hv : v = X ^ 2 + C W.a₁ * X * v + C W.a₂ * X ^ 2 * v + C W.a₃ * X * v ^ 2
      + C W.a₄ * X ^ 2 * v ^ 2 + C W.a₆ * X ^ 2 * v ^ 3 := by
    apply mul_left_cancel₀ hX
    linear_combination heq
  have hv0 : constantCoeff v = 0 := by simpa using congrArg constantCoeff hv
  obtain ⟨v₂, rfl⟩ := PowerSeries.X_dvd_iff.mpr hv0
  have hv₂ : v₂ = X + C W.a₁ * X * v₂ + C W.a₂ * X ^ 2 * v₂ + C W.a₃ * X ^ 2 * v₂ ^ 2
      + C W.a₄ * X ^ 3 * v₂ ^ 2 + C W.a₆ * X ^ 4 * v₂ ^ 3 := by
    apply mul_left_cancel₀ hX
    linear_combination hv
  have hv₂0 : constantCoeff v₂ = 0 := by simpa using congrArg constantCoeff hv₂
  obtain ⟨u, rfl⟩ := PowerSeries.X_dvd_iff.mpr hv₂0
  have hu : u = 1 + C W.a₁ * X * u + C W.a₂ * X ^ 2 * u + C W.a₃ * X ^ 3 * u ^ 2
      + C W.a₄ * X ^ 4 * u ^ 2 + C W.a₆ * X ^ 6 * u ^ 3 := by
    apply mul_left_cancel₀ hX
    linear_combination hv₂
  refine ⟨u, by ring, ?_⟩
  simpa using congrArg constantCoeff hu

theorem subst_w {u w : PowerSeries K} (hwu : w = X ^ 3 * u) {σ : Type}
    (s : MvPowerSeries σ K) (hs : MvPowerSeries.constantCoeff s = 0) :
    w.subst s = s ^ 3 * u.subst s := by
  have ha : PowerSeries.HasSubst s := PowerSeries.HasSubst.of_constantCoeff_zero hs
  rw [hwu, PowerSeries.subst_mul ha, PowerSeries.subst_pow ha, PowerSeries.subst_X ha]

theorem isUnit_subst {u : PowerSeries K} (hu : constantCoeff u = 1) {σ : Type}
    (s : MvPowerSeries σ K) (hs : MvPowerSeries.constantCoeff s = 0) :
    IsUnit (u.subst s) := by
  have ha : PowerSeries.HasSubst s := PowerSeries.HasSubst.of_constantCoeff_zero hs
  obtain ⟨u', hu'⟩ := PowerSeries.X_dvd_iff.mpr (show constantCoeff (u - 1) = 0 by simp [hu])
  have h1 : u = 1 + X * u' := by rw [← hu']; ring
  rw [MvPowerSeries.isUnit_iff_constantCoeff, h1, ← PowerSeries.coe_substAlgHom ha, map_add,
    map_one, map_mul, PowerSeries.coe_substAlgHom, PowerSeries.subst_X ha]
  simp [hs]

theorem xOf_eq {u w : PowerSeries K} (hwu : w = X ^ 3 * u) (hu : constantCoeff u = 1)
    {σ : Type} (s : MvPowerSeries σ K) (hs : MvPowerSeries.constantCoeff s = 0) (hne : s ≠ 0) :
    xOf w s = (algebraMap (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))
      (s ^ 2 * u.subst s))⁻¹ := by
  have hinj := IsFractionRing.injective (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))
  have hs' : algebraMap _ (FractionRing (MvPowerSeries σ K)) s ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hne
  have hu' : algebraMap _ (FractionRing (MvPowerSeries σ K)) (u.subst s) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (isUnit_subst hu s hs).ne_zero
  rw [xOf, subst_w hwu s hs, map_mul, map_mul, map_pow, map_pow]
  field_simp

theorem xOf_ne_of_hom {u w : PowerSeries K} (hwu : w = X ^ 3 * u) (hu : constantCoeff u = 1)
    {σ : Type} (φ : MvPowerSeries σ K →ₐ[K] MvPowerSeries σ K) (s t : MvPowerSeries σ K)
    (hs0 : MvPowerSeries.constantCoeff s = 0) (ht0 : MvPowerSeries.constantCoeff t = 0)
    (hs : s ≠ 0) (ht : t ≠ 0) (hφs : φ s = 0) (hφt : φ t ≠ 0) : xOf w s ≠ xOf w t := by
  intro h
  rw [xOf_eq hwu hu s hs0 hs, xOf_eq hwu hu t ht0 ht, inv_inj] at h
  have h2 := IsFractionRing.injective (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K)) h
  have h3 := congrArg φ h2
  rw [map_mul, map_mul, map_pow, map_pow, hφs] at h3
  have hut : IsUnit (φ (u.subst t)) := (isUnit_subst hu t ht0).map φ
  have h4 : φ t ^ 2 * φ (u.subst t) ≠ 0 := mul_ne_zero (pow_ne_zero _ hφt) hut.ne_zero
  apply h4
  rw [← h3]
  simp

theorem eq_of_xy {u w : PowerSeries K} (hwu : w = X ^ 3 * u) (hu : constantCoeff u = 1)
    {σ : Type} (A B : MvPowerSeries σ K) (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) (hx : xOf w A = xOf w B)
    (hy : yOf w A = yOf w B) : A = B := by
  have hinj := IsFractionRing.injective (MvPowerSeries σ K) (FractionRing (MvPowerSeries σ K))
  have key : ∀ s : MvPowerSeries σ K,
      xOf w s = -(algebraMap _ (FractionRing (MvPowerSeries σ K)) s) * yOf w s := by
    intro s
    simp only [xOf, yOf]
    ring
  have zero_of : ∀ s : MvPowerSeries σ K, MvPowerSeries.constantCoeff s = 0 →
      yOf w s = 0 → s = 0 := by
    intro s hs hys
    simp only [yOf, div_eq_zero_iff, neg_eq_zero, one_ne_zero, false_or] at hys
    have h1 : w.subst s = 0 := (map_eq_zero_iff _ hinj).mp hys
    rw [subst_w hwu s hs] at h1
    exact (pow_eq_zero_iff (by norm_num)).mp
      ((mul_eq_zero.mp h1).resolve_right (isUnit_subst hu s hs).ne_zero)
  by_cases hy0 : yOf w A = 0
  · rw [zero_of A hA hy0, zero_of B hB (by rw [← hy]; exact hy0)]
  · have hyB : yOf w B ≠ 0 := by rw [← hy]; exact hy0
    rw [key A, key B, hy] at hx
    exact hinj (neg_inj.mp (mul_right_cancel₀ hyB hx))

theorem some_congr {L : Type u} [Field L] {W' : WeierstrassCurve.Affine L} {x y x' y' : L}
    {h : W'.Nonsingular x y} (hx : x = x') (hy : y = y') :
    ∃ h' : W'.Nonsingular x' y', WeierstrassCurve.Affine.Point.some x y h =
      WeierstrassCurve.Affine.Point.some x' y' h' := by
  subst hx
  subst hy
  exact ⟨h, rfl⟩

end WeierstrassCoordinateSubstitution

end Formalism.ELL

namespace Formalism.ELL

namespace WeierstrassCoordinateSubstitution

variable {K : Type u} [Field K]

theorem chord_add {W : WeierstrassCurve K} {w : PowerSeries K} {σ : Type}
    [DecidableEq (FractionRing (MvPowerSeries σ K))] (s t r : MvPowerSeries σ K)
    (hs : (W.map (algebraMap K (FractionRing (MvPowerSeries σ K)))).toAffine.Nonsingular
      (xOf w s) (yOf w s))
    (ht : (W.map (algebraMap K (FractionRing (MvPowerSeries σ K)))).toAffine.Nonsingular
      (xOf w t) (yOf w t))
    (hne : xOf w s ≠ xOf w t) (hch : ChordAt W w s t r) :
    ∃ h : (W.map (algebraMap K (FractionRing (MvPowerSeries σ K)))).toAffine.Nonsingular
      (xOf w r) (yOf w r),
      WeierstrassCurve.Affine.Point.some _ _ hs + WeierstrassCurve.Affine.Point.some _ _ ht =
        WeierstrassCurve.Affine.Point.some _ _ h := by
  obtain ⟨hx, hy⟩ := hch
  rw [WeierstrassCurve.Affine.Point.add_some (fun h => hne h.1)]
  refine some_congr ?_ ?_
  · rw [WeierstrassCurve.Affine.slope_of_X_ne hne]
    exact hx.symm
  · rw [WeierstrassCurve.Affine.slope_of_X_ne hne]
    exact hy.symm

theorem X_ne_zero' {σ : Type} (i : σ) : (MvPowerSeries.X i : MvPowerSeries σ K) ≠ 0 := by
  intro h
  have h1 := congrArg (MvPowerSeries.coeff (Finsupp.single i 1)) h
  simp at h1

private theorem subst_subst_pair' {τ υ : Type} (F : MvPowerSeries (Fin 2) K)
    (a b : MvPowerSeries τ K) (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) (v : τ → MvPowerSeries υ K)
    (hv : MvPowerSeries.HasSubst v) :
    MvPowerSeries.subst v (F.subst ![a, b]) =
      F.subst ![MvPowerSeries.subst v a, MvPowerSeries.subst v b] := by
  have hab : MvPowerSeries.HasSubst ![a, b] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp [ha, hb])
  rw [MvPowerSeries.subst_comp_subst_apply hab hv]
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem subst_X_X_ne_zero (F : MvPowerSeries (Fin 2) K)
    (hF1 : MvPowerSeries.coeff (Finsupp.single 0 1) F = 1) (i j : Fin 3)
    (v : Fin 3 → MvPowerSeries (Fin 2) K) (hv0 : ∀ k, MvPowerSeries.constantCoeff (v k) = 0)
    (hi : v i = MvPowerSeries.X 0) (hj : v j = MvPowerSeries.X 1) :
    F.subst ![(MvPowerSeries.X i : MvPowerSeries (Fin 3) K), MvPowerSeries.X j] ≠ 0 := by
  intro h
  have hv := MvPowerSeries.hasSubst_of_constantCoeff_zero hv0
  have h1 := congrArg (MvPowerSeries.subst v) h
  rw [subst_subst_pair' F _ _ (by simp) (by simp) v hv, MvPowerSeries.subst_X hv,
    MvPowerSeries.subst_X hv, hi, hj] at h1
  have h0 : MvPowerSeries.subst v (0 : MvPowerSeries (Fin 3) K) = 0 := by
    rw [← MvPowerSeries.coe_substAlgHom hv, map_zero]
  have e : (![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 2) K) =
      MvPowerSeries.X := by
    funext k
    fin_cases k <;> rfl
  rw [h0, e, MvPowerSeries.subst_self, id_eq] at h1
  rw [h1] at hF1
  simp at hF1

theorem assoc_of (hS : WChordSubst.{u}) (hP : WPoint.{u}) {W : WeierstrassCurve K}
    {w : PowerSeries K} (hw : WFixed W w) {u : PowerSeries K} (hwu : w = X ^ 3 * u)
    (hu : constantCoeff u = 1) (F : MvPowerSeries (Fin 2) K)
    (hF0 : MvPowerSeries.constantCoeff F = 0)
    (hF1 : MvPowerSeries.coeff (Finsupp.single 0 1) F = 1)
    (hch : ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F) :
    F.subst ![F.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1],
        MvPowerSeries.X 2] =
      F.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K),
        F.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2]] := by
  classical
  have cX : ∀ i : Fin 3,
      MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) = 0 :=
    fun i => by simp
  have nX : ∀ i : Fin 3, (MvPowerSeries.X i : MvPowerSeries (Fin 3) K) ≠ 0 :=
    fun i => X_ne_zero' i
  have cSub : ∀ a b : MvPowerSeries (Fin 3) K, MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.constantCoeff b = 0 →
      MvPowerSeries.constantCoeff (F.subst ![a, b]) = 0 := by
    intro a b ha hb
    exact MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp [ha, hb]))
      (fun i => by fin_cases i <;> simp [ha, hb]) hF0
  have ne_of : ∀ (v : Fin 3 → MvPowerSeries (Fin 3) K),
      (∀ i, MvPowerSeries.constantCoeff (v i) = 0) →
      ∀ s t : MvPowerSeries (Fin 3) K, MvPowerSeries.constantCoeff s = 0 →
      MvPowerSeries.constantCoeff t = 0 → s ≠ 0 → t ≠ 0 → MvPowerSeries.subst v s = 0 →
      MvPowerSeries.subst v t ≠ 0 → xOf w s ≠ xOf w t := by
    intro v hv s t hs0 ht0 hs ht h1 h2
    have hv' := MvPowerSeries.hasSubst_of_constantCoeff_zero hv
    exact xOf_ne_of_hom hwu hu (MvPowerSeries.substAlgHom hv') s t hs0 ht0 hs ht
      (by rw [MvPowerSeries.coe_substAlgHom]; exact h1)
      (by rw [MvPowerSeries.coe_substAlgHom]; exact h2)
  have g01 : F.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] ≠ 0 :=
    subst_X_X_ne_zero F hF1 0 1 ![MvPowerSeries.X 0, MvPowerSeries.X 1, 0]
      (fun k => by fin_cases k <;> simp) rfl rfl
  have g12 : F.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] ≠ 0 :=
    subst_X_X_ne_zero F hF1 1 2 ![0, MvPowerSeries.X 0, MvPowerSeries.X 1]
      (fun k => by fin_cases k <;> simp) rfl rfl
  have c01 := cSub _ _ (cX 0) (cX 1)
  have c12 := cSub _ _ (cX 1) (cX 2)
  have hv1 : ∀ i, MvPowerSeries.constantCoeff
      ((![0, MvPowerSeries.X 1, MvPowerSeries.X 2] : Fin 3 → MvPowerSeries (Fin 3) K) i) = 0 :=
    fun i => by fin_cases i <;> simp
  have hv2 : ∀ i, MvPowerSeries.constantCoeff
      ((![MvPowerSeries.X 0, MvPowerSeries.X 1, 0] : Fin 3 → MvPowerSeries (Fin 3) K) i) = 0 :=
    fun i => by fin_cases i <;> simp
  have hv3 : ∀ i, MvPowerSeries.constantCoeff
      ((![MvPowerSeries.X 0, 0, MvPowerSeries.X 2] : Fin 3 → MvPowerSeries (Fin 3) K) i) = 0 :=
    fun i => by fin_cases i <;> simp
  have ne1 : xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) ≠ xOf w (MvPowerSeries.X 1) := by
    refine ne_of _ hv1 _ _ (cX 0) (cX 1) (nX 0) (nX 1) ?_ ?_
    · rw [MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hv1)]; rfl
    · rw [MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hv1)]; exact nX 1
  have ne2 : xOf w (F.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1]) ≠
      xOf w (MvPowerSeries.X 2) := by
    refine Ne.symm (ne_of _ hv2 _ _ (cX 2) c01 (nX 2) g01 ?_ ?_)
    · rw [MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hv2)]; rfl
    · rw [subst_subst_pair' F _ _ (cX 0) (cX 1) _ (MvPowerSeries.hasSubst_of_constantCoeff_zero hv2),
        MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hv2),
        MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hv2)]
      exact g01
  have ne3 : xOf w (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K) ≠ xOf w (MvPowerSeries.X 2) := by
    refine ne_of _ hv3 _ _ (cX 1) (cX 2) (nX 1) (nX 2) ?_ ?_
    · rw [MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hv3)]; rfl
    · rw [MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hv3)]; exact nX 2
  have ne4 : xOf w (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K) ≠
      xOf w (F.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2]) := by
    refine ne_of _ hv1 _ _ (cX 0) c12 (nX 0) g12 ?_ ?_
    · rw [MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hv1)]; rfl
    · rw [subst_subst_pair' F _ _ (cX 1) (cX 2) _ (MvPowerSeries.hasSubst_of_constantCoeff_zero hv1),
        MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hv1),
        MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hv1)]
      exact g12
  have ch1 := hS K W w hw F hF0 hch (Fin 3) _ _ (cX 0) (cX 1) (nX 0) (nX 1) ne1
  have ch2 := hS K W w hw F hF0 hch (Fin 3) _ _ c01 (cX 2) g01 (nX 2) ne2
  have ch3 := hS K W w hw F hF0 hch (Fin 3) _ _ (cX 1) (cX 2) (nX 1) (nX 2) ne3
  have ch4 := hS K W w hw F hF0 hch (Fin 3) _ _ (cX 0) c12 (nX 0) g12 ne4
  have p0 := hP K W w hw (Fin 3) _ (cX 0) (nX 0)
  have p1 := hP K W w hw (Fin 3) _ (cX 1) (nX 1)
  have p2 := hP K W w hw (Fin 3) _ (cX 2) (nX 2)
  have p01 := hP K W w hw (Fin 3) _ c01 g01
  have p12 := hP K W w hw (Fin 3) _ c12 g12
  obtain ⟨h01, e1⟩ := chord_add _ _ _ p0 p1 ne1 ch1
  obtain ⟨hL, e2⟩ := chord_add _ _ _ p01 p2 ne2 ch2
  obtain ⟨h12, e3⟩ := chord_add _ _ _ p1 p2 ne3 ch3
  obtain ⟨hR, e4⟩ := chord_add _ _ _ p0 p12 ne4 ch4
  have key := e2.symm.trans (((congrArg (· + _) e1).symm.trans
    ((add_assoc _ _ _).trans (congrArg (_ + ·) e3))).trans e4)
  simp only [WeierstrassCurve.Affine.Point.some.injEq] at key
  exact eq_of_xy hwu hu _ _ (cSub _ _ c01 (cX 2)) (cSub _ _ (cX 0) c12) key.1 key.2

end WeierstrassCoordinateSubstitution

theorem wFormalGroup_of (hC : Formalism.ELL.WChordSeries.{u}) (hS : Formalism.ELL.WChordSubst.{u})
    (hP : Formalism.ELL.WPoint.{u}) : Formalism.ELL.WFormalGroup.{u} := by
  intro K _ W w hw
  obtain ⟨F₂, hcoef, h0, h1, h2, hch⟩ := hC K W w hw
  obtain ⟨u, hwu, hu⟩ := WeierstrassCoordinateSubstitution.exists_unit_factor hw
  let F : FormalGroup K :=
    { toPowerSeries := F₂
      zero_constantCoeff := h0
      lin_coeff_X := h1
      lin_coeff_Y := h2
      assoc := WeierstrassCoordinateSubstitution.assoc_of hS hP hw hwu hu F₂ h0 h1 hch }
  exact ⟨F, hcoef, hch⟩

end Formalism.ELL
