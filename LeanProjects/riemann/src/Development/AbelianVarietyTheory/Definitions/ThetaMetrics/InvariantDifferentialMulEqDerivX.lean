import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FglInvariant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddXYZOrChordXYZOrOriginXYZNeZero

noncomputable section

open Formalism.L2.Th1.A ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

universe u v

namespace GlobalTheory.WeierstrassFormal

section Series

open PowerSeries

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : WeierstrassCurve R)

theorem w_eq : wSer W = X ^ 3 + C W.a₁ * X * wSer W + C W.a₂ * X ^ 2 * wSer W + C W.a₃ * wSer W ^ 2
    + C W.a₄ * X * wSer W ^ 2 + C W.a₆ * wSer W ^ 3 := (wSerSpec R W).1.2

theorem w_eq_X_pow_mul : wSer W = X ^ 3 * wU W ∧ constantCoeff (wU W) = 1 :=
  ⟨(wSerFactor R W).1, (wSerFactor R W).2.1⟩

theorem wU_eq : wU W = 1 + C W.a₁ * X * wU W + C W.a₂ * X ^ 2 * wU W + C W.a₃ * X ^ 3 * wU W ^ 2
    + C W.a₄ * X ^ 4 * wU W ^ 2 + C W.a₆ * X ^ 6 * wU W ^ 3 := by
  have h := w_eq W
  rw [(w_eq_X_pow_mul W).1] at h
  refine X_pow_mul_cancel (k := 3) ?_
  linear_combination h

theorem coeff_one_wU : coeff 1 (wU W) = W.a₁ := by
  have h : wU W = 1 + X * (C W.a₁ * wU W + X * (C W.a₂ * wU W + C W.a₃ * X * wU W ^ 2
      + C W.a₄ * X ^ 2 * wU W ^ 2 + C W.a₆ * X ^ 4 * wU W ^ 3)) := by
    linear_combination wU_eq W
  rw [h, map_add, coeff_succ_X_mul]
  simp [(w_eq_X_pow_mul W).2, coeff_one]

theorem fw_mul_om : fw W * om W = 1 := (unitSpec R W).2.1

theorem coeff_inv : constantCoeff (iSer W) = 0 ∧ coeff 1 (iSer W) = -1 :=
  ⟨(iSerSpec R W).1, (iSerSpec R W).2.1⟩

theorem inv_mul_den : iSer W * (-1 + C W.a₁ * X + C W.a₃ * wSer W) = X := by
  have h : iDen W * invOfUnit (iDen W) (-1) = 1 := (unitSpec R W).2.2.2.2.2.2
  change iSer W * iDen W = X
  rw [iSer]
  linear_combination X * h

theorem w_inv_mul_den :
    (wSer W).subst (iSer W) * (-1 + C W.a₁ * X + C W.a₃ * wSer W) = wSer W := by
  have h : iDen W * invOfUnit (iDen W) (-1) = 1 := (unitSpec R W).2.2.2.2.2.2
  change _ * iDen W = _
  rw [(iSerSpec R W).2.2.2.1]
  linear_combination wSer W * h

variable (φ : R →+* S)

theorem map_inv : PowerSeries.map φ (iSer W) = iSer (W.map φ) := (seriesMap R S φ W).2.2.2.2.2.2.2

end Series

section Group

open MvPowerSeries

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : WeierstrassCurve R)

def formalGroup : FormalGroup R where
  toPowerSeries := fgl W
  zero_constantCoeff := (fglChord R W).2.2.2.2.1
  lin_coeff_X := (fglChord R W).2.2.2.2.2.1
  lin_coeff_Y := (fglChord R W).2.2.2.2.2.2
  assoc := by
    obtain ⟨F, hF, -⟩ := fglGroup R W
    rw [← hF]
    exact F.assoc

@[simp] theorem formalGroup_toPowerSeries : (formalGroup W).toPowerSeries = fgl W := rfl

instance isComm_formalGroup : (formalGroup W).IsComm := ⟨Fgl2.fgl_symm W⟩

theorem chord (i : Fin 2) : (wSer W).subst (X i : MvPowerSeries (Fin 2) R) = lam W * X i + nu W := by
  have := Fgl2.nu_eq W i
  change _ = (wSer W).subst (X i : MvPowerSeries (Fin 2) R) - _ at this
  linear_combination -this

theorem third_point : constantCoeff (uThird W) = 0 ∧
    (wSer W).subst (uThird W) = lam W * uThird W + nu W ∧
    cThree W * (X 0 + X 1 + uThird W) + cTwo W = 0 ∧
    (formalGroup W).toPowerSeries = (iSer W).subst (uThird W) :=
  ⟨(fglChord R W).2.1, (fglChord R W).2.2.1.symm, Fgl2.third_rel W 0 1 (by decide),
    (fglChord R W).2.2.2.1⟩

theorem subst_X_inv :
    (formalGroup W).toPowerSeries.subst (![PowerSeries.X, iSer W] : Fin 2 → PowerSeries R) = 0 :=
  fglInv R W

variable {σ : Type*}

theorem subst_inv {s : MvPowerSeries σ R} (hs : PowerSeries.HasSubst s) :
    (formalGroup W).toPowerSeries.subst ![s, (iSer W).subst s] = 0 := by
  have h := congrArg (PowerSeries.subst s) (subst_X_inv W)
  rw [PowerSeries.subst, subst_comp_subst_apply (Fgl2.hasSubst_X_iSer W) hs.const,
    ← PowerSeries.coe_substAlgHom hs, map_zero] at h
  rw [← h]
  congr 1
  funext i
  fin_cases i
  · exact (PowerSeries.subst_X hs).symm
  · rfl

instance : Neg ((formalGroup W).Point σ) where
  neg s := ⟨(iSer W).subst s.val,
    IsNilpotent_subst s.prop.const (by
      have := (coeff_inv W).1
      rw [show MvPowerSeries.constantCoeff (iSer W) = 0 from this]
      exact IsNilpotent.zero)⟩

@[simp] theorem neg_val (s : (formalGroup W).Point σ) : (-s).val = (iSer W).subst s.val := rfl

instance addCommGroupPoint : AddCommGroup ((formalGroup W).Point σ) where
  __ := (inferInstance : AddCommMonoid ((formalGroup W).Point σ))
  zsmul := zsmulRec
  neg_add_cancel s := by
    rw [add_comm]
    exact Subtype.ext (subst_inv W s.prop)

theorem map_zsmul (φ : R →+* S) (n : ℤ) : PowerSeries.map φ (zSer W n) = zSer (W.map φ) n :=
  zSerMap R S φ W n

end Group

section Law

open MvPowerSeries

variable {R S : Type} [CommRing R] [CommRing S]

def toTwoPoints (F : MvPowerSeries (Fin 2) R) : PS R 2 1 :=
  F.subst (fun j : Fin 2 => (X (j, 0) : PS R 2 1))

theorem hasSubst_twoPoints : HasSubst (fun j : Fin 2 => (X (j, 0) : PS R 2 1)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem ev_toTwoPoints (F : MvPowerSeries (Fin 2) R) {n : ℕ} {a b : Pt R n 1}
    (ha : constantCoeff (a 0) = 0) (hb : constantCoeff (b 0) = 0) :
    ev ![a, b] (toTwoPoints F) = F.subst ![a 0, b 0] := by
  have h : HasSubst (fun p : Fin 2 × Fin 1 => ![a, b] p.1 p.2) :=
    hasSubst_of_constantCoeff_zero fun ⟨j, i⟩ => by
      obtain rfl := Subsingleton.elim i 0
      fin_cases j
      exacts [ha, hb]
  rw [ev, toTwoPoints, subst_comp_subst_apply hasSubst_twoPoints h]
  congr 1
  funext j
  rw [subst_X h]
  fin_cases j <;> rfl

def lawOfFormalGroup (F : FormalGroup R) [F.IsComm] : FGLaw R 1 where
  F _ := toTwoPoints F.toPowerSeries
  const _ := constantCoeff_subst_eq_zero hasSubst_twoPoints (fun _ => constantCoeff_X _)
    F.zero_constantCoeff
  unit i := by
    obtain rfl := Subsingleton.elim i 0
    rw [ev_toTwoPoints _ (by simp) (by simp [pt])]
    exact F.zero_add (PowerSeries.HasSubst.of_constantCoeff_zero (by simp [pt]))
  comm _ := by
    rw [ev_toTwoPoints _ (by simp [pt]) (by simp [pt]),
      F.comm' (PowerSeries.HasSubst.of_constantCoeff_zero (by simp [pt]))
        (PowerSeries.HasSubst.of_constantCoeff_zero (by simp [pt])), toTwoPoints]
    congr 1
    funext j
    fin_cases j <;> rfl
  assoc _ := by
    have hp : ∀ j : Fin 3, constantCoeff (pt R 1 j 0) = 0 := fun j => by simp [pt]
    have hF : ∀ i j : Fin 3, constantCoeff (F.toPowerSeries.subst ![pt R 1 i 0, pt R 1 j 0]) = 0 :=
      fun i j => constantCoeff_subst_eq_zero
        (hasSubst_of_constantCoeff_zero fun s => by fin_cases s <;> exact hp _)
        (fun s => by fin_cases s <;> exact hp _) F.zero_constantCoeff
    simp only [ev_toTwoPoints _ (hp _) (hp _)]
    rw [ev_toTwoPoints _ (hF 0 1) (hp 2), ev_toTwoPoints _ (hp 0) (hF 1 2)]
    exact F.assoc' (.of_constantCoeff_zero (hp 0)) (.of_constantCoeff_zero (hp 1))
      (.of_constantCoeff_zero (hp 2))

variable (W : WeierstrassCurve R)

def law : FGLaw R 1 := lawOfFormalGroup (formalGroup W)

end Law

section Points

open MvPowerSeries WeierstrassCurve WeierstrassCurve.Projective GlobalTheory.AddLaw

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) {σ : Type*}

abbrev seriesCurve (σ : Type*) : WeierstrassCurve.Projective (MvPowerSeries σ R) :=
  W.map (C : R →+* MvPowerSeries σ R)

def point (s : MvPowerSeries σ R) : Fin 3 → MvPowerSeries σ R := ![s, -1, (wSer W).subst s]

theorem map_substAlgHom {τ : Type*} {a : τ → MvPowerSeries σ R} (ha : HasSubst a) :
    (seriesCurve W τ).map (substAlgHom (R := R) ha : MvPowerSeries τ R →+* MvPowerSeries σ R) =
      seriesCurve W σ := by
  refine (WeierstrassCurve.map_map W _ _).trans ?_
  congr 1
  ext1 r
  simp [coe_substAlgHom, subst_C]

theorem substAlgHom_comp_point {τ : Type*} {a : τ → MvPowerSeries σ R} (ha : HasSubst a)
    {s : MvPowerSeries τ R} (hs : PowerSeries.HasSubst s) :
    (substAlgHom (R := R) ha : MvPowerSeries τ R →+* MvPowerSeries σ R) ∘ point W s =
      point W (s.subst a) := by
  rw [point, comp_fin3, point, map_neg, map_one]
  simp only [RingHom.coe_coe, coe_substAlgHom, Fgl2.mvsubst_psubst hs ha]

theorem equation_point {s : MvPowerSeries σ R} (hs : PowerSeries.HasSubst s) :
    (seriesCurve W σ).Equation (point W s) := by
  have h := congrArg (PowerSeries.substAlgHom (R := R) hs) (w_eq W)
  simp only [map_add, map_mul, map_pow, PowerSeries.substAlgHom_X] at h
  simp only [PowerSeries.coe_substAlgHom, PowerSeries.subst_C] at h
  rw [equation_iff]
  simp only [point, fin3_def_ext, WeierstrassCurve.map]
  linear_combination h

theorem neg_point {s : MvPowerSeries σ R} (hs : PowerSeries.HasSubst s) :
    (seriesCurve W σ).neg (point W s) =
      (-1 + C W.a₁ * s + C W.a₃ * (wSer W).subst s) • point W ((iSer W).subst s) := by
  have h₁ := congrArg (PowerSeries.substAlgHom (R := R) hs) (inv_mul_den W)
  have h₂ := congrArg (PowerSeries.substAlgHom (R := R) hs) (w_inv_mul_den W)
  simp only [map_add, map_mul, map_neg, map_one, PowerSeries.substAlgHom_X] at h₁ h₂
  simp only [PowerSeries.coe_substAlgHom, PowerSeries.subst_C, PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' (coeff_inv W).1) hs] at h₁ h₂
  ext1 i
  fin_cases i
  · simp [point, neg]
    linear_combination -h₁
  · simp [point, neg, negY]
    ring
  · simp [point, neg]
    linear_combination -h₂

theorem neg_eq_smul_point {A N Z : MvPowerSeries (Fin 2) R}
    (hZ : Z = lam W * A - nu W * N)
    (hA : (-cTwo W - cThree W * (X 0 + X 1)) * N + cThree W * A = 0) :
    ![A, (seriesCurve W (Fin 2)).negY ![A, N, Z], Z] =
      (-N * (-1 + C W.a₁ * uThird W + C W.a₃ * wThird W)) • point W (fgl W) := by
  obtain ⟨h0, hw, h3, hF⟩ := third_point W
  have hu : IsUnit (cThree W) := by
    rw [isUnit_iff_constantCoeff, Fgl1.cThree_cc W]
    exact isUnit_one
  have hA' : A = -N * uThird W := hu.mul_left_cancel (by linear_combination hA + N * h3)
  have e : ![A, N, Z] = -N • point W (uThird W) := by
    ext1 i
    fin_cases i
    · simp [point, hA']
    · simp [point]
    · simp [point, hw, hZ, hA']
      ring
  change (seriesCurve W (Fin 2)).neg ![A, N, Z] = _
  rw [e, Projective.neg_smul, neg_point W (.of_constantCoeff_zero h0), smul_smul, hw,
    ← hF]
  rfl

theorem originN_eq : originN (seriesCurve W (Fin 2)) (X 0)
      ((wSer W).subst (X 0 : MvPowerSeries (Fin 2) R)) (X 1) =
    lam W * originD (seriesCurve W (Fin 2)) ((wSer W).subst (X 0 : MvPowerSeries (Fin 2) R)) (X 1)
      ((wSer W).subst (X 0 : MvPowerSeries (Fin 2) R) + lam W * (X 1 - X 0)) := by
  have e : (wSer W).subst (X 0 : MvPowerSeries (Fin 2) R) + lam W * (X 1 - X 0) =
      (wSer W).subst (X 1 : MvPowerSeries (Fin 2) R) := by
    rw [chord W 0, chord W 1]; ring
  have h := sub_mul_originD (equation_point W (s := (X 0 : MvPowerSeries (Fin 2) R))
    (.of_constantCoeff_zero (by simp))) (equation_point W (s := (X 1 : MvPowerSeries (Fin 2) R))
    (.of_constantCoeff_zero (by simp)))
  rw [e]
  refine sub_eq_zero.mp (Fgl1.sub_cancel ?_)
  linear_combination h + originD (seriesCurve W (Fin 2))
    ((wSer W).subst (X 0 : MvPowerSeries (Fin 2) R)) (X 1)
    ((wSer W).subst (X 1 : MvPowerSeries (Fin 2) R)) * e

theorem addXYZ_diagXYZ_point_X :
    (∃ c : MvPowerSeries (Fin 2) R, (seriesCurve W (Fin 2)).addXYZ (point W (X 0)) (point W (X 1)) = c • point W (fgl W)) ∧
    ∃ c : MvPowerSeries (Fin 2) R, IsUnit c ∧
      diagXYZ (seriesCurve W (Fin 2)) (point W (X 0)) (point W (X 1)) = c • point W (fgl W) := by
  have e : (wSer W).subst (X 1 : MvPowerSeries (Fin 2) R) =
      (wSer W).subst (X 0 : MvPowerSeries (Fin 2) R) + lam W * (X 1 - X 0) := by
    rw [chord W 0, chord W 1]; ring
  have hn : (wSer W).subst (X 0 : MvPowerSeries (Fin 2) R) - lam W * X 0 = nu W := rfl
  have h₀ := equation_point W (s := (X 0 : MvPowerSeries (Fin 2) R))
    (.of_constantCoeff_zero (by simp))
  have h3 : lineCubicCoeff (seriesCurve W (Fin 2)) (lam W) 1 = cThree W := by
    simp [lineCubicCoeff, cThree]
  have h2 : lineQuadCoeff (seriesCurve W (Fin 2)) (lam W) (nu W) 1 = cTwo W := by
    simp [lineQuadCoeff, cTwo]
  have a₁ := addZ_line (W := seriesCurve W (Fin 2)) (X 0)
    ((wSer W).subst (X 0 : MvPowerSeries (Fin 2) R)) (X 1) (lam W)
  have a₂ := negAddY_line h₀ (originN_eq W)
  have d₁ := diagZ_line h₀ (originN_eq W)
  have d₂ := negDiagY_line h₀ (originN_eq W)
  rw [hn, ← e] at a₁ a₂ d₁ d₂
  rw [h2, h3] at a₂ d₂
  refine ⟨⟨_, neg_eq_smul_point W a₁ a₂⟩, _, ?_, neg_eq_smul_point W d₁ d₂⟩
  rw [isUnit_iff_constantCoeff, map_mul, map_neg, Fgl1.dd_cc W]
  have hN : constantCoeff (negDiagY (seriesCurve W (Fin 2))
      ![X 0, -1, (wSer W).subst (X 0 : MvPowerSeries (Fin 2) R)]
      ![X 1, -1, (wSer W).subst (X 1 : MvPowerSeries (Fin 2) R)]) = -1 := by
    rw [← map_negDiagY, comp_fin3, comp_fin3, Fgl1.Wi_cc W 0, Fgl1.Wi_cc W 1]
    simp [negDiagY]
  simp only [point, hN]
  simp

theorem addXYZ_diagXYZ_point {s t : MvPowerSeries σ R} (hs : PowerSeries.HasSubst s)
    (ht : PowerSeries.HasSubst t) :
    (∃ c : MvPowerSeries σ R, (seriesCurve W σ).addXYZ (point W s) (point W t) =
      c • point W ((formalGroup W).toPowerSeries.subst ![s, t])) ∧
    ∃ c : MvPowerSeries σ R, IsUnit c ∧ diagXYZ (seriesCurve W σ) (point W s) (point W t) =
      c • point W ((formalGroup W).toPowerSeries.subst ![s, t]) := by
  have h : HasSubst ![s, t] :=
    hasSubst_of_constantCoeff_nilpotent fun i => by fin_cases i <;> simpa
  obtain ⟨⟨c, hc⟩, d, hd, hd'⟩ := addXYZ_diagXYZ_point_X W
  set φ := (substAlgHom (R := R) h : MvPowerSeries (Fin 2) R →+* MvPowerSeries σ R) with hφ
  have hX : ∀ i, φ ∘ point W (X i) = point W (![s, t] i) := fun i => by
    rw [hφ, substAlgHom_comp_point W h (.of_constantCoeff_zero (by simp)), subst_X h]
  have hF : ∀ c : MvPowerSeries (Fin 2) R, φ ∘ (c • point W (fgl W)) = φ c • point W ((fgl W).subst ![s, t]) := fun c => by
    rw [← substAlgHom_comp_point W h (.of_constantCoeff_zero (Fgl1.fgl_cc W))]
    exact funext fun i => map_mul φ _ _
  have e₁ := map_addXYZ (W' := seriesCurve W (Fin 2)) φ (point W (X 0)) (point W (X 1))
  have e₂ := map_diagXYZ (W := seriesCurve W (Fin 2)) φ (point W (X 0)) (point W (X 1))
  rw [hc, hF, hX, hX] at e₁
  rw [hd', hF, hX, hX] at e₂
  rw [← map_substAlgHom W h]
  exact ⟨⟨_, e₁⟩, _, hd.map φ, e₂⟩

variable {K : Type v} [Field K] (φ : MvPowerSeries σ R →+* K)

theorem nonsingular_point {s : MvPowerSeries σ R} (hs : PowerSeries.HasSubst s) :
    ((seriesCurve W σ).map φ).Nonsingular (φ ∘ point W s) := by
  have h := congrArg (φ ∘ PowerSeries.substAlgHom (R := R) hs) (fw_mul_om W)
  simp only [Function.comp_apply, fw, map_sub, map_mul, map_pow, map_one, map_ofNat,
    PowerSeries.substAlgHom_X] at h
  simp only [PowerSeries.coe_substAlgHom, PowerSeries.subst_C] at h
  refine (nonsingular_iff _).mpr ⟨(equation_point W hs).map φ, Or.inr (Or.inr fun h' => ?_)⟩
  simp only [point, comp_fin3, fin3_def_ext, WeierstrassCurve.map, map_neg, map_one] at h'
  exact one_ne_zero (α := K) (by linear_combination -h + φ ((om W).subst s) * h')

theorem point_subst_equiv_add {s t : MvPowerSeries σ R} (hs : PowerSeries.HasSubst s)
    (ht : PowerSeries.HasSubst t) :
    φ ∘ point W ((formalGroup W).toPowerSeries.subst ![s, t]) ≈
      ((seriesCurve W σ).map φ).add (φ ∘ point W s) (φ ∘ point W t) := by
  obtain ⟨-, c, hc, e⟩ := addXYZ_diagXYZ_point W hs ht
  have e' : diagXYZ ((seriesCurve W σ).map φ) (φ ∘ point W s) (φ ∘ point W t) =
      φ c • φ ∘ point W ((formalGroup W).toPowerSeries.subst ![s, t]) := by
    rw [map_diagXYZ, e]
    ext1 i
    simp
  have h := diagXYZ_equiv_add (nonsingular_point W φ hs) (nonsingular_point W φ ht) (by
    rw [e']
    intro h0
    have := congrFun h0 1
    simp [point, (hc.map φ).ne_zero] at this)
  rw [e'] at h
  exact Setoid.trans (Setoid.symm (smul_equiv _ (hc.map φ))) h

def toPoint : (formalGroup W).Point σ →+ ((seriesCurve W σ).map φ).Point :=
  AddMonoidHom.mk' (fun s => ⟨(nonsingularLift_iff _).mpr (nonsingular_point W φ s.prop)⟩)
    fun s t => Point.ext (Quotient.sound (point_subst_equiv_add W φ s.prop t.prop))

end Points

section Examples

open MvPowerSeries

variable {R : Type u} [CommRing R]

theorem formalGroup_singular (a : R) :
    (formalGroup (⟨a, 0, 0, 0, 0⟩ : WeierstrassCurve R)).toPowerSeries =
      X 0 + X 1 - C a * X 0 * X 1 := by
  set W : WeierstrassCurve R := ⟨a, 0, 0, 0, 0⟩ with hW
  have hw : ∀ i : Fin 2, (lam W * X i + nu W) * (1 - C a * X i) = X i ^ 3 := fun i => by
    have h := (WeierstrassCurve.Projective.equation_iff _).mp
      (equation_point W (s := (X i : MvPowerSeries (Fin 2) R)) (.of_constantCoeff_zero (by simp)))
    simp only [point, WeierstrassCurve.Projective.fin3_def_ext, WeierstrassCurve.map, chord W i] at h
    simp only [hW, map_zero] at h ⊢
    linear_combination h
  have hl : lam W * ((1 - C a * X 0) * (1 - C a * X 1)) =
      X 0 ^ 2 + X 0 * X 1 + X 1 ^ 2 - C a * X 0 * X 1 * (X 0 + X 1) :=
    sub_eq_zero.mp (Fgl1.sub_cancel (by
      linear_combination (1 - C a * X 1) * hw 0 - (1 - C a * X 0) * hw 1))
  have h3 : X 0 + X 1 + uThird W + C a * lam W = 0 := by
    simpa [cThree, cTwo, hW] using (third_point W).2.2.1
  have hd : Fgl1.dd W * invOfUnit (Fgl1.dd W) (-1) = 1 :=
    mul_invOfUnit _ _ (by rw [Fgl1.dd_cc]; simp)
  have hd' : Fgl1.dd W = -1 + C a * uThird W := by simp [Fgl1.dd, hW]
  have key : uThird W = (X 0 + X 1 - C a * X 0 * X 1) * Fgl1.dd W := by
    rw [hd']
    linear_combination (1 - C a * X 0) * (1 - C a * X 1) * h3 - C a * hl
  change uThird W * invOfUnit (Fgl1.dd W) (-1) = _
  linear_combination invOfUnit (Fgl1.dd W) (-1) * key + (X 0 + X 1 - C a * X 0 * X 1) * hd

example : formalGroup (⟨0, 0, 0, 0, 0⟩ : WeierstrassCurve R) = FormalGroup.𝔾ₐ :=
  FormalGroup.ext (by simp [formalGroup_singular, -formalGroup_toPowerSeries])

example : formalGroup (⟨-1, 0, 0, 0, 0⟩ : WeierstrassCurve R) = FormalGroup.𝔾ₘ :=
  FormalGroup.ext (by simp [formalGroup_singular, -formalGroup_toPowerSeries])

example : PowerSeries.coeff 4 (wSer (⟨1, 0, 1, -1, 0⟩ : WeierstrassCurve ℤ)) = 1 := by
  rw [(w_eq_X_pow_mul _).1, PowerSeries.coeff_X_pow_mul' _ 3 4, if_pos (by norm_num), coeff_one_wU]

example (W : WeierstrassCurve R) : (xL W).coeff (-2) = 1 ∧ (yL W).coeff (-3) = -1 := by
  simp [xL, yL, uPow, HahnSeries.coeff_single_mul, PowerSeries.coeff_coe,
    (wSerFactor R W).2.2.2.1, (wSerFactor R W).2.2.2.2]

end Examples

end GlobalTheory.WeierstrassFormal
