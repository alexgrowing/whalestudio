import Formalism.EllipticTorsion.CoeffRing
import Formalism.EllipticTorsion.EllipticTorsionProofs.WChord
import Formalism.EllipticTorsion.EllipticTorsionProofs.ExistsUnitFactor
import Formalism.EllipticTorsion.EllipticTorsionProofs.WSubst
import Formalism.EllipticTorsion.EllipticTorsionProofs.WSeries
import Formalism.EllipticTorsion.EllipticTorsionProofs.WPoint
import Formalism.EllipticTorsion.EllipticTorsionProofs.FormalGroupPointsHomDef
import Formalism.EllipticTorsion.EllipticTorsionProofs.JetsTwo

open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL
namespace CubeTwoAlt

open WeierstrassChordSeries

variable {K : Type u} [Field K]

local notation "cc" => MvPowerSeries.constantCoeff

theorem coeff_subst_X0_zero (H : MvPowerSeries (Fin 2) K) (e : Fin 2 →₀ ℕ) (he : e 1 = 0) :
    MvPowerSeries.coeff e (H.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0]) =
      MvPowerSeries.coeff e H := by
  classical
  have hs : MvPowerSeries.HasSubst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] :=
    FormalGroupPointsHom.hasSubst2 (by simp) (by simp)
  have hprod : ∀ d : Fin 2 →₀ ℕ,
      (d.prod fun s n => (![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] s) ^ n)
        = MvPowerSeries.X 0 ^ d 0 * 0 ^ d 1 := by
    intro d
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two]
    simp
  rw [MvPowerSeries.coeff_subst hs, finsum_eq_single _ e]
  · rw [hprod, he, pow_zero, mul_one, MvPowerSeries.coeff_X_pow]
    have : e = Finsupp.single 0 (e 0) := ((eq_single_iff e).2).mpr he
    rw [if_pos this, smul_eq_mul, mul_one]
  · intro d hd
    rw [hprod]
    rcases Nat.eq_zero_or_pos (d 1) with h1 | h1
    · rw [h1, pow_zero, mul_one, MvPowerSeries.coeff_X_pow, if_neg, smul_zero]
      intro h
      apply hd
      have hd' : d = Finsupp.single 0 (d 0) := ((eq_single_iff d).2).mpr h1
      rw [hd']
      exact h.symm
    · rw [zero_pow h1.ne', mul_zero, map_zero, smul_zero]

theorem X_one_dvd_of_subst_X_zero_eq_zero (H : MvPowerSeries (Fin 2) K)
    (h : H.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] = 0) :
    (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ∣ H := by
  rw [MvPowerSeries.X_dvd_iff]
  intro m hm
  rw [← coeff_subst_X0_zero H m hm, h, map_zero]

theorem vec_mem {W : WeierstrassCurve K} {x y : MvPowerSeries (Fin 2) K} (hx : x ∈ T W)
    (hy : y ∈ T W) : ∀ i, ![x, y] i ∈ T W := by
  intro i; fin_cases i
  · exact hx
  · exact hy

theorem subst_mem_T_of_mem {W : WeierstrassCurve K} {f : MvPowerSeries (Fin 2) K} (hf : f ∈ T W)
    {a : Fin 2 → MvPowerSeries (Fin 2) K} (ha : ∀ i, a i ∈ T W) (h0 : ∀ i, cc (a i) = 0) :
    f.subst a ∈ T W := by
  obtain ⟨fS, rfl⟩ := hf
  have ha' : ∀ i, ∃ y, MvPowerSeries.map (algebraMap (Sadj W) K) y = a i := fun i => ha i
  choose aS haS using ha'
  have hinj : Function.Injective (algebraMap (Sadj W) K) := fun x y h => Subtype.ext h
  have hS : MvPowerSeries.HasSubst aS := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by
    apply hinj
    rw [map_zero]
    have := congrArg MvPowerSeries.constantCoeff (haS i)
    rw [MvPowerSeries.constantCoeff_map, h0 i] at this
    exact this)
  refine ⟨fS.subst aS, ?_⟩
  rw [MvPowerSeries.map_subst hS]
  congr 1
  funext i
  exact haS i

theorem div_diag {W : WeierstrassCurve K} (H : MvPowerSeries (Fin 2) K) (hT : H ∈ T W)
    (h : H.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 0] = 0) :
    ∃ Q ∈ T W, H = (MvPowerSeries.X 1 - MvPowerSeries.X 0) * Q := by
  have c0 : cc (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have c1 : cc (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have hτ : MvPowerSeries.HasSubst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      MvPowerSeries.X 1 + MvPowerSeries.X 0] := FormalGroupPointsHom.hasSubst2 c0 (by simp)
  have hτ' : MvPowerSeries.HasSubst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      MvPowerSeries.X 1 - MvPowerSeries.X 0] := FormalGroupPointsHom.hasSubst2 c0 (by simp)
  have hε : MvPowerSeries.HasSubst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] :=
    FormalGroupPointsHom.hasSubst2 c0 (by simp)
  obtain ⟨H', hH'⟩ : ∃ H', H' = H.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      MvPowerSeries.X 1 + MvPowerSeries.X 0] := ⟨_, rfl⟩
  have e1 : H'.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] = 0 := by
    rw [hH', MvPowerSeries.subst_comp_subst_apply hτ hε]
    have : (fun i => MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0]
        (![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1 + MvPowerSeries.X 0] i))
        = ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 0] := by
      funext i; fin_cases i
      · simp [MvPowerSeries.subst_X hε]
      · simp [MvPowerSeries.subst_add hε, MvPowerSeries.subst_X hε]
    rw [this]; exact h
  obtain ⟨Q', hQ'⟩ := X_one_dvd_of_subst_X_zero_eq_zero H' e1
  have hback : H'.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      MvPowerSeries.X 1 - MvPowerSeries.X 0] = H := by
    rw [hH', MvPowerSeries.subst_comp_subst_apply hτ hτ']
    have : (fun i => MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
        MvPowerSeries.X 1 - MvPowerSeries.X 0]
        (![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1 + MvPowerSeries.X 0] i))
        = ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] := by
      funext i; fin_cases i
      · simp [MvPowerSeries.subst_X hτ']
      · simp [MvPowerSeries.subst_add hτ', MvPowerSeries.subst_X hτ']
    rw [this]; exact FormalGroupPointsHom.subst_XX H
  refine ⟨Q'.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      MvPowerSeries.X 1 - MvPowerSeries.X 0], ?_, ?_⟩
  · have hH'T : H' ∈ T W := by
      rw [hH']
      exact subst_mem_T_of_mem hT (vec_mem (X_mem_T 0) ((T W).add_mem (X_mem_T 1) (X_mem_T 0)))
        (FormalGroupQuadraticJets.hv c0 (by simp))
    have hQ'T : Q' ∈ T W := by
      rw [mem_T]; intro e
      have := congrArg (MvPowerSeries.coeff (e + Finsupp.single 1 1)) hQ'
      rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul, if_pos le_add_self,
        add_tsub_cancel_right, one_mul] at this
      rw [← this]; exact mem_T.mp hH'T _
    exact subst_mem_T_of_mem hQ'T (vec_mem (X_mem_T 0) ((T W).sub_mem (X_mem_T 1) (X_mem_T 0)))
      (FormalGroupQuadraticJets.hv c0 (by simp))
  · conv_lhs => rw [← hback]
    rw [hQ', MvPowerSeries.subst_mul hτ', MvPowerSeries.subst_X hτ']
    simp

variable {W : WeierstrassCurve K} {w : PowerSeries K}

theorem w_eq_X_cube_mul_unit (hw : WFixed W w) : w = X ^ 3 * wU w := by
  obtain ⟨l0, l1, l2, _⟩ := w_low hw
  ext n
  rw [PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  · rw [wU, PowerSeries.coeff_mk, Nat.sub_add_cancel h]
  · interval_cases n <;> assumption

theorem wU_cc (hw : WFixed W w) : PowerSeries.constantCoeff (wU w) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, wU, PowerSeries.coeff_mk]
  exact (w_low hw).2.2.2

theorem subst_wU_X_mem_T_of_wFixed (hw : WFixed W w) (i : Fin 2) :
    (wU w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) ∈ T W := by
  classical
  rw [mem_T]; intro e
  rw [PowerSeries.coeff_subst_single]
  split_ifs
  · rw [wU, PowerSeries.coeff_mk]; exact w_coeff_mem hw _
  · exact Subalgebra.zero_mem _

theorem U_cc (hw : WFixed W w) (i : Fin 2) :
    cc ((wU w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K)) = 1 := by
  classical
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_subst_single]
  simp [wU, (w_low hw).2.2.2]

theorem Wi_eq (hw : WFixed W w) (i : Fin 2) :
    Wi w i = MvPowerSeries.X i ^ 3 * (wU w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) :=
  WeierstrassCoordinateSubstitution.subst_w (w_eq_X_cube_mul_unit hw) _ (by simp)

def dI (W : WeierstrassCurve K) (w : PowerSeries K) (i : Fin 2) : MvPowerSeries (Fin 2) K :=
  -1 + ca W.a₁ * MvPowerSeries.X i + ca W.a₃ * Wi w i

theorem dI_cc (hw : WFixed W w) (i : Fin 2) : cc (dI W w i) = -1 := by
  simp [dI, Wi_cc hw]

theorem dI_mem_T_of_wFixed (hw : WFixed W w) (i : Fin 2) : dI W w i ∈ T W :=
  (T W).add_mem ((T W).add_mem ((T W).neg_mem (T W).one_mem)
    ((T W).mul_mem (constSeries_mem_integralSeries (by simp)) (X_mem_T i))) ((T W).mul_mem (constSeries_mem_integralSeries (by simp)) (wVar_mem_integralSeries hw i))

theorem invSer_subst (hw : WFixed W w) (i : Fin 2) :
    (invSer W w).subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) =
      MvPowerSeries.X i * (dI W w i)⁻¹ := by
  have ha : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) :=
    PowerSeries.HasSubst.X i
  have hφc : PowerSeries.constantCoeff (-1 + C W.a₁ * X + C W.a₃ * w : PowerSeries K) ≠ 0 := by
    simp [hw.1]
  have e := congrArg (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K))
    (PowerSeries.mul_inv_cancel _ hφc)
  have hs : (-1 + C W.a₁ * X + C W.a₃ * w : PowerSeries K).subst
      (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = dI W w i := by
    rw [← PowerSeries.coe_substAlgHom ha]
    simp only [map_add, map_neg, map_one, map_mul]
    rw [PowerSeries.coe_substAlgHom ha, PowerSeries.subst_C, PowerSeries.subst_C,
      PowerSeries.subst_X ha]
    rfl
  have h1 : (1 : PowerSeries K).subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = 1 := by
    rw [← PowerSeries.coe_substAlgHom ha, map_one]
  rw [PowerSeries.subst_mul ha, hs, h1] at e
  have hinv : (-1 + C W.a₁ * X + C W.a₃ * w : PowerSeries K)⁻¹.subst
      (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = (dI W w i)⁻¹ :=
    (MvPowerSeries.eq_inv_iff_mul_eq_one (by rw [dI_cc hw]; exact neg_ne_zero.mpr one_ne_zero)).mpr
      (by rw [mul_comm]; exact e)
  rw [invSer, PowerSeries.subst_mul ha, PowerSeries.subst_X ha, hinv]

theorem ib_cc (hw : WFixed W w) :
    cc ((invSer W w).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)) = 0 := by
  rw [invSer_subst hw]; simp

theorem inverseSeries_subst_X1_mem (hw : WFixed W w) :
    (invSer W w).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ∈ T W := by
  rw [invSer_subst hw]
  exact (T W).mul_mem (X_mem_T 1) (inv_mem_integralSeries (dI_mem_T_of_wFixed hw 1)
    (by rw [dI_cc hw]; exact neg_ne_zero.mpr one_ne_zero)
    (by rw [dI_cc hw, inv_neg, inv_one]; exact Subalgebra.neg_mem _ (Subalgebra.one_mem _)))

theorem chord_series_eq_F2 (hw : WFixed W w) {F : MvPowerSeries (Fin 2) K} (hF0 : cc F = 0)
    (hch : ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) F) : F = WeierstrassChordSeries.F2 W w := by
  have h2 := chord wSeriesSubstUnique_holds.{u} hw
  dsimp only [ChordAt] at hch h2
  exact WeierstrassCoordinateSubstitution.eq_of_xy (w_eq_X_cube_mul_unit hw) (wU_cc hw) F (WeierstrassChordSeries.F2 W w) hF0 (constantCoeff_formalSum hw)
    (hch.1.trans h2.1.symm) (hch.2.trans h2.2.symm)

theorem Fp_diag (hw : WFixed W w) :
    ((WeierstrassChordSeries.F2 W w).subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      (invSer W w).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)]).subst
        ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 0] = 0 := by
  have hU := wSeriesSubstUnique_holds.{u}
  have hS := wChordSubst_of hU
  let FG : FormalGroup K := ⟨WeierstrassChordSeries.F2 W w, constantCoeff_formalSum hw, linearCoeff_formalSum hw 0, linearCoeff_formalSum hw 1,
    WeierstrassCoordinateSubstitution.assoc_of hS wSeriesNonsingularPoint_holds hw (w_eq_X_cube_mul_unit hw) (wU_cc hw) (WeierstrassChordSeries.F2 W w) (constantCoeff_formalSum hw) (linearCoeff_formalSum hw 0)
      (chord hU hw)⟩
  have hdA : dI W w 0 * (dI W w 0)⁻¹ = 1 :=
    MvPowerSeries.mul_inv_cancel _ (by rw [dI_cc hw]; exact neg_ne_zero.mpr one_ne_zero)
  have hψ : (1 - MvPowerSeries.C W.a₁ * MvPowerSeries.X 0 - MvPowerSeries.C W.a₃ *
      w.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K)) * (-(dI W w 0)⁻¹) = 1 := by
    simp only [dI, Wi] at hdA ⊢; linear_combination hdA
  have key := FormalGroupPointsHom.inv_formal hU hS hw FG (chord hU hw) _ hψ
  have hd : MvPowerSeries.HasSubst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      MvPowerSeries.X 0] := FormalGroupPointsHom.hasSubst2 (by simp) (by simp)
  rw [MvPowerSeries.subst_comp_subst_apply (FormalGroupPointsHom.hasSubst2 (by simp) (ib_cc hw)) hd]
  have : (fun i => MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      MvPowerSeries.X 0] (![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
        (invSer W w).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] i)) =
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), -MvPowerSeries.X 0 * -(dI W w 0)⁻¹] := by
    funext i; fin_cases i
    · simp [MvPowerSeries.subst_X hd]
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [WeierstrassSubstitution.mvsubst_psubst _ _ (by simp) _ hd, MvPowerSeries.subst_X hd]
      simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [invSer_subst hw 0]; ring
  rw [this]
  exact key

end CubeTwoAlt
end Formalism.ELL

namespace Formalism.ELL
namespace CubeTwoAlt

open WeierstrassChordSeries

variable {K : Type u} [Field K] {W : WeierstrassCurve K} {w : PowerSeries K}

local notation "cc" => MvPowerSeries.constantCoeff

theorem chord_subst_inverse_mem (hw : WFixed W w) :
    (WeierstrassChordSeries.F2 W w).subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
      (invSer W w).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] ∈ T W :=
  subst_mem_T_of_mem (formalSum_mem_integralSeries hw) (vec_mem (X_mem_T 0) (inverseSeries_subst_X1_mem hw))
    (FormalGroupQuadraticJets.hv (by simp) (ib_cc hw))

theorem Fp_lin (hw : WFixed W w) :
    MvPowerSeries.coeff (Finsupp.single 1 1) ((WeierstrassChordSeries.F2 W w).subst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
        (invSer W w).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)]) = -1 := by
  have h := FormalGroupQuadraticJets.ccd_F (WeierstrassChordSeries.F2 W w) (x := (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))
    (by simp) (ib_cc hw) 1
  simp only [FormalGroupQuadraticJets.ccd_single] at h
  rw [h, linearCoeff_formalSum hw 0, linearCoeff_formalSum hw 1, invSer_subst hw 1, WeierstrassChordSeries.L_mul]
  simp [WeierstrassChordSeries.L_X, MvPowerSeries.constantCoeff_inv, dI_cc hw]

theorem C3_mem_T_of_wFixed (hw : WFixed W w) : C3 W w ∈ T W :=
  lineCoeffCubic_mem _ (constSeries_mem_integralSeries (by simp)) (constSeries_mem_integralSeries (by simp)) (constSeries_mem_integralSeries (by simp)) (slope_mem_integralSeries hw)

theorem dd_mem_T_of_wFixed (hw : WFixed W w) : dd W w ∈ T W := by
  have h1 : ca W.a₁ ∈ T W := constSeries_mem_integralSeries (by simp)
  have h2 : ca W.a₂ ∈ T W := constSeries_mem_integralSeries (by simp)
  have h3 : ca W.a₃ ∈ T W := constSeries_mem_integralSeries (by simp)
  have h4 : ca W.a₄ ∈ T W := constSeries_mem_integralSeries (by simp)
  have h6 : ca W.a₆ ∈ T W := constSeries_mem_integralSeries (by simp)
  have hl := slope_mem_integralSeries hw
  have hn := intercept_mem_integralSeries hw
  have hC3 : C3 W w ∈ T W := lineCoeffCubic_mem _ h2 h4 h6 hl
  have hC2 : C2 W w ∈ T W := lineCoeffQuadratic_mem _ h1 h2 h3 h4 h6 hl hn
  have hC3i : (C3 W w)⁻¹ ∈ T W :=
    inv_mem_integralSeries hC3 (by rw [constantCoeff_chordCoeffCubic hw]; exact one_ne_zero)
      (by rw [constantCoeff_chordCoeffCubic hw, inv_one]; exact Subalgebra.one_mem _)
  have hz3 : z3 W w ∈ T W :=
    (T W).sub_mem ((T W).sub_mem ((T W).neg_mem (X_mem_T 0)) (X_mem_T 1)) ((T W).mul_mem hC2 hC3i)
  have hw3 : w3 W w ∈ T W := (T W).add_mem ((T W).mul_mem hl hz3) hn
  exact (T W).add_mem ((T W).add_mem ((T W).neg_mem (T W).one_mem) ((T W).mul_mem h1 hz3))
      ((T W).mul_mem h3 hw3)

theorem main (hw : WFixed W w) :
    ∃ c : MvPowerSeries (Fin 2) K, c ∈ T W ∧ cc c = -1 ∧
      (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ^ 2 *
          ((wU w).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K))⁻¹
        - (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ 2 *
          ((wU w).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K))⁻¹
        = c * WeierstrassChordSeries.F2 W w * MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K),
            (invSer W w).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] (WeierstrassChordSeries.F2 W w) := by
  have : IsDomain (MvPowerSeries (Fin 2) K) := NoZeroDivisors.to_isDomain _
  have hU := wSeriesSubstUnique_holds.{u}
  obtain ⟨Q, hQT, hQ⟩ := div_diag _ (chord_subst_inverse_mem hw) (Fp_diag hw)
  have hQc : cc Q = -1 := by
    have h := Fp_lin hw
    rw [hQ, WeierstrassChordSeries.L_mul] at h
    simpa [WeierstrassChordSeries.L_X] using h

  have hUs := fun (s : MvPowerSeries (Fin 2) K) (hs : cc s = 0) => hU K W w hw (Fin 2) s hs
  have h0 := (weq_iff W _ _).mp (hUs (MvPowerSeries.X 0) (by simp)).1
  have h1 := (weq_iff W _ _).mp (hUs (MvPowerSeries.X 1) (by simp)).1
  have hW0 : Wi w 0 = lam w * MvPowerSeries.X 0 + nu w := by unfold nu; ring
  have hW1 : Wi w 1 = lam w * MvPowerSeries.X 1 + nu w := by
    have := lam_mul w; unfold nu; linear_combination -this
  change WeierstrassChordSeries.G _ _ _ _ _ _ (Wi w 0) = 0 at h0
  change WeierstrassChordSeries.G _ _ _ _ _ _ (Wi w 1) = 0 at h1
  have hinv : C3 W w * (C3 W w)⁻¹ = 1 :=
    MvPowerSeries.mul_inv_cancel _ (by rw [constantCoeff_chordCoeffCubic hw]; exact one_ne_zero)
  have he1 : c3 (ca W.a₂) (ca W.a₄) (ca W.a₆) (lam w) *
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 + z3 W w) +
      c2 (ca W.a₁) (ca W.a₂) (ca W.a₃) (ca W.a₄) (ca W.a₆) (lam w) (nu w) = 0 := by
    change C3 W w * _ + C2 W w = 0
    rw [z3]
    linear_combination (-C2 W w) * hinv
  rw [hW0] at h0
  rw [hW1] at h1
  obtain ⟨-, -, he3⟩ := vieta X_ne h0 h1 he1
  change C3 W w * (MvPowerSeries.X 0 * MvPowerSeries.X 1 * z3 W w)
    + c0 (ca W.a₃) (ca W.a₆) (nu w) = 0 at he3
  simp only [c0] at he3
  obtain ⟨Ua, hUa⟩ : ∃ U, U = (wU w).subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) :=
    ⟨_, rfl⟩
  obtain ⟨Ub, hUb⟩ : ∃ U, U = (wU w).subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) :=
    ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : MvPowerSeries (Fin 2) K,
      E = 1 - ca W.a₃ * nu w - ca W.a₆ * nu w ^ 2 := ⟨_, rfl⟩
  have hUac : cc Ua = 1 := hUa ▸ U_cc hw 0
  have hUbc : cc Ub = 1 := hUb ▸ U_cc hw 1
  have hEc : cc E = 1 := by rw [hE]; simp [nu_cc hw]
  have hIa : Ua * Ua⁻¹ = 1 := MvPowerSeries.mul_inv_cancel _ (by rw [hUac]; exact one_ne_zero)
  have hIb : Ub * Ub⁻¹ = 1 := MvPowerSeries.mul_inv_cancel _ (by rw [hUbc]; exact one_ne_zero)
  have hIe : E * E⁻¹ = 1 := MvPowerSeries.mul_inv_cancel _ (by rw [hEc]; exact one_ne_zero)
  have hIq : Q * Q⁻¹ = 1 :=
    MvPowerSeries.mul_inv_cancel _ (by rw [hQc]; exact neg_ne_zero.mpr one_ne_zero)
  have hWa : Wi w 0 = MvPowerSeries.X 0 ^ 3 * Ua := hUa ▸ Wi_eq hw 0
  have hWb : Wi w 1 = MvPowerSeries.X 1 ^ 3 * Ub := hUb ▸ Wi_eq hw 1
  have hlam := lam_mul w
  have hν2 : (MvPowerSeries.X 1 - MvPowerSeries.X 0) * nu w =
      MvPowerSeries.X 1 * MvPowerSeries.X 0 ^ 3 * Ua
        - MvPowerSeries.X 0 * MvPowerSeries.X 1 ^ 3 * Ub := by
    unfold nu
    linear_combination (-MvPowerSeries.X 0) * hlam + MvPowerSeries.X 1 * hWa
      - MvPowerSeries.X 0 * hWb
  have key0 : MvPowerSeries.X 0 * MvPowerSeries.X 1 *
      ((MvPowerSeries.X 1 - MvPowerSeries.X 0) * C3 W w * z3 W w
        + (MvPowerSeries.X 1 ^ 2 * Ua⁻¹ - MvPowerSeries.X 0 ^ 2 * Ub⁻¹) * Ua * Ub * E) = 0 := by
    rw [hE]
    linear_combination (MvPowerSeries.X 1 - MvPowerSeries.X 0) * he3
      + (MvPowerSeries.X 0 * MvPowerSeries.X 1 * MvPowerSeries.X 1 ^ 2 * Ub
        * (1 - ca W.a₃ * nu w - ca W.a₆ * nu w ^ 2)) * hIa
      - (MvPowerSeries.X 0 * MvPowerSeries.X 1 * MvPowerSeries.X 0 ^ 2 * Ua
        * (1 - ca W.a₃ * nu w - ca W.a₆ * nu w ^ 2)) * hIb
      + (1 - ca W.a₃ * nu w - ca W.a₆ * nu w ^ 2) * hν2
  have key1 := (mul_eq_zero.mp key0).resolve_left
    (mul_ne_zero (WeierstrassCoordinateSubstitution.X_ne_zero' 0) (WeierstrassCoordinateSubstitution.X_ne_zero' 1))
  have hdc : cc (dd W w) ≠ 0 := by rw [dd_cc hw]; exact neg_ne_zero.mpr one_ne_zero
  have hF : WeierstrassChordSeries.F2 W w * dd W w = z3 W w := by
    rw [WeierstrassChordSeries.F2, mul_assoc, mul_comm _ (dd W w), MvPowerSeries.mul_inv_cancel _ hdc, mul_one]
  rw [← hF] at key1
  refine ⟨-(C3 W w * dd W w * Ua⁻¹ * Ub⁻¹ * E⁻¹ * Q⁻¹), ?_, ?_, ?_⟩
  · have hUaT : Ua⁻¹ ∈ T W := inv_mem_integralSeries (hUa ▸ subst_wU_X_mem_T_of_wFixed hw 0) (by rw [hUac]; exact one_ne_zero)
      (by rw [hUac, inv_one]; exact Subalgebra.one_mem _)
    have hUbT : Ub⁻¹ ∈ T W := inv_mem_integralSeries (hUb ▸ subst_wU_X_mem_T_of_wFixed hw 1) (by rw [hUbc]; exact one_ne_zero)
      (by rw [hUbc, inv_one]; exact Subalgebra.one_mem _)
    have hET : E ∈ T W := by
      rw [hE]
      exact (T W).sub_mem ((T W).sub_mem (T W).one_mem
        ((T W).mul_mem (constSeries_mem_integralSeries (by simp)) (intercept_mem_integralSeries hw)))
        ((T W).mul_mem (constSeries_mem_integralSeries (by simp)) ((T W).pow_mem (intercept_mem_integralSeries hw) 2))
    have hEiT : E⁻¹ ∈ T W := inv_mem_integralSeries hET (by rw [hEc]; exact one_ne_zero)
      (by rw [hEc, inv_one]; exact Subalgebra.one_mem _)
    have hQiT : Q⁻¹ ∈ T W := inv_mem_integralSeries hQT (by rw [hQc]; exact neg_ne_zero.mpr one_ne_zero)
      (by rw [hQc, inv_neg, inv_one]; exact Subalgebra.neg_mem _ (Subalgebra.one_mem _))
    exact (T W).neg_mem ((T W).mul_mem ((T W).mul_mem ((T W).mul_mem ((T W).mul_mem
      ((T W).mul_mem (C3_mem_T_of_wFixed hw) (dd_mem_T_of_wFixed hw)) hUaT) hUbT) hEiT) hQiT)
  · simp [MvPowerSeries.constantCoeff_inv, constantCoeff_chordCoeffCubic hw, dd_cc hw, hUac, hUbc, hEc, hQc]
  · rw [hQ, ← hUa, ← hUb]
    linear_combination (Ua⁻¹ * Ub⁻¹ * E⁻¹ * Q⁻¹ * Q) * key1
      - (MvPowerSeries.X 1 ^ 2 * Ua⁻¹ - MvPowerSeries.X 0 ^ 2 * Ub⁻¹) * (Ub * Ub⁻¹) * (E * E⁻¹)
        * (Q * Q⁻¹) * hIa
      - (MvPowerSeries.X 1 ^ 2 * Ua⁻¹ - MvPowerSeries.X 0 ^ 2 * Ub⁻¹) * (E * E⁻¹) * (Q * Q⁻¹) * hIb
      - (MvPowerSeries.X 1 ^ 2 * Ua⁻¹ - MvPowerSeries.X 0 ^ 2 * Ub⁻¹) * (Q * Q⁻¹) * hIe
      - (MvPowerSeries.X 1 ^ 2 * Ua⁻¹ - MvPowerSeries.X 0 ^ 2 * Ub⁻¹) * hIq

end CubeTwoAlt

theorem cube_two : Formalism.ELL.CubeTwo.{u} := by
  intro K _ W w F hw hF0 hch
  have hF := CubeTwoAlt.chord_series_eq_F2 hw hF0 hch
  subst hF
  obtain ⟨c, hcT, hcc, hc⟩ := CubeTwoAlt.main hw
  exact ⟨c, fun d => WeierstrassChordSeries.mem_T.mp hcT d, hcc, hc⟩

end Formalism.ELL
