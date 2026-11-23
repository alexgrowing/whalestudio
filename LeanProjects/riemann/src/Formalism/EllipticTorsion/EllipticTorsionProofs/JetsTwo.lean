import Formalism.EllipticTorsion.JetsCube
import Formalism.FormalGroupLog.FormalGroupLogProofs.ConstantCoeffSubstOfZero

universe u

noncomputable section

namespace Formalism.ELL.FormalGroupQuadraticJets

open Formalism.G.LogCR

variable {K : Type*} [CommRing K]

def ccd (i : Fin 2) (H : MvPowerSeries (Fin 2) K) : K :=
  MvPowerSeries.constantCoeff (MvPowerSeries.pderiv K i H)

def Q (H : MvPowerSeries (Fin 2) K) : K :=
  MvPowerSeries.constantCoeff (MvPowerSeries.pderiv K 1 (MvPowerSeries.pderiv K 0 H))

theorem Q_sub (f g : MvPowerSeries (Fin 2) K) : Q (f - g) = Q f - Q g := by
  simp [Q, map_sub]

theorem cc_psubst {τ : Type*} [Finite τ] {a : MvPowerSeries τ K}
    (ha : MvPowerSeries.constantCoeff a = 0) (f : PowerSeries K) :
    MvPowerSeries.constantCoeff (f.subst a) = PowerSeries.constantCoeff f := by
  exact Formalism.G.LogP.constantCoeff_subst_of_zero (f : MvPowerSeries Unit K) (b := fun _ => a) (fun _ => ha)

theorem cc_derivative (f : PowerSeries K) :
    PowerSeries.constantCoeff (PowerSeries.derivative K f) = PowerSeries.coeff 1 f := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
  simp

theorem pderiv_one_subst_X0 (g : PowerSeries K) :
    MvPowerSeries.pderiv K 1 (g.subst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K))
      = 0 := by
  rw [pderiv_psubst (MvPowerSeries.constantCoeff_X _)]
  simp [MvPowerSeries.pderiv_X]

theorem pderiv_zero_subst_X1 (g : PowerSeries K) :
    MvPowerSeries.pderiv K 0 (g.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K))
      = 0 := by
  rw [pderiv_psubst (MvPowerSeries.constantCoeff_X _)]
  simp [MvPowerSeries.pderiv_X]

theorem quadraticJet_subst_X0 (g : PowerSeries K) :
    Q (g.subst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K)) = 0 := by
  unfold Q
  rw [pderiv_psubst (MvPowerSeries.constantCoeff_X _)]
  simp [MvPowerSeries.pderiv_X, pderiv_one_subst_X0]

theorem quadraticJet_subst_X1 (g : PowerSeries K) :
    Q (g.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K)) = 0 := by
  unfold Q
  rw [pderiv_zero_subst_X1]
  simp

theorem linearCoeff_zero_subst_X0 (g : PowerSeries K) :
    ccd 0 (g.subst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K)) =
      PowerSeries.coeff 1 g := by
  unfold ccd
  rw [pderiv_psubst (MvPowerSeries.constantCoeff_X _)]
  simp [MvPowerSeries.pderiv_X, cc_psubst (MvPowerSeries.constantCoeff_X _), cc_derivative]

theorem linearCoeff_one_subst_X1 (g : PowerSeries K) :
    ccd 1 (g.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K)) =
      PowerSeries.coeff 1 g := by
  unfold ccd
  rw [pderiv_psubst (MvPowerSeries.constantCoeff_X _)]
  simp [MvPowerSeries.pderiv_X, cc_psubst (MvPowerSeries.constantCoeff_X _), cc_derivative]

theorem linearCoeff_one_subst_X0 (g : PowerSeries K) :
    ccd 1 (g.subst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K)) = 0 := by
  unfold ccd
  rw [pderiv_one_subst_X0]
  simp

theorem linearCoeff_zero_subst_X1 (g : PowerSeries K) :
    ccd 0 (g.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K)) = 0 := by
  unfold ccd
  rw [pderiv_zero_subst_X1]
  simp

theorem Q_phi (φ : PowerSeries K) {S : MvPowerSeries (Fin 2) K}
    (hS : MvPowerSeries.constantCoeff S = 0) :
    Q (φ.subst S) =
      PowerSeries.constantCoeff (PowerSeries.derivative K (PowerSeries.derivative K φ)) *
          ccd 1 S * ccd 0 S +
        PowerSeries.constantCoeff (PowerSeries.derivative K φ) * Q S := by
  unfold Q ccd
  rw [pderiv_psubst hS, Derivation.leibniz, pderiv_psubst hS]
  simp only [smul_eq_mul, map_add, map_mul, cc_psubst hS]
  ring

theorem hv {x y : MvPowerSeries (Fin 2) K} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) :
    ∀ j, MvPowerSeries.constantCoeff (![x, y] j) = 0 := by
  intro j
  fin_cases j <;> simp [hx, hy]

theorem ccd_F (F : MvPowerSeries (Fin 2) K) {x y : MvPowerSeries (Fin 2) K}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0)
    (i : Fin 2) :
    ccd i (F.subst ![x, y]) = ccd 0 F * ccd i x + ccd 1 F * ccd i y := by
  unfold ccd
  rw [pderiv_subst (hv hx hy), map_sum, Fin.sum_univ_two]
  simp only [map_mul, Formalism.G.LogP.constantCoeff_subst_of_zero _ (hv hx hy), Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]

theorem Q_F (F : MvPowerSeries (Fin 2) K) {x y : MvPowerSeries (Fin 2) K}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0) :
    Q (F.subst ![x, y]) =
      ccd 0 F * Q x + ccd 0 x * (ccd 0 (MvPowerSeries.pderiv K 0 F) * ccd 1 x +
          ccd 1 (MvPowerSeries.pderiv K 0 F) * ccd 1 y) +
        ccd 1 F * Q y + ccd 0 y * (ccd 0 (MvPowerSeries.pderiv K 1 F) * ccd 1 x +
          ccd 1 (MvPowerSeries.pderiv K 1 F) * ccd 1 y) := by
  unfold Q
  rw [pderiv_subst (hv hx hy), map_sum, Fin.sum_univ_two]
  simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul]
  rw [pderiv_subst (hv hx hy), pderiv_subst (hv hx hy)]
  simp only [Fin.sum_univ_two, map_add, map_mul, Formalism.G.LogP.constantCoeff_subst_of_zero _ (hv hx hy),
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, ccd]
  ring

theorem ccd_single (F : MvPowerSeries (Fin 2) K) (i : Fin 2) :
    ccd i F = MvPowerSeries.coeff (Finsupp.single i 1) F := by
  unfold ccd
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  simp

theorem ccd_mixed (F : MvPowerSeries (Fin 2) K) :
    ccd 1 (MvPowerSeries.pderiv K 0 F) = ccd 0 (MvPowerSeries.pderiv K 1 F) := by
  rw [ccd_single, ccd_single, MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv,
    add_comm (Finsupp.single (1 : Fin 2) 1)]
  simp

end Formalism.ELL.FormalGroupQuadraticJets

namespace Formalism.ELL.FormalGroupQuadraticJets

open Formalism.G.LogCR

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CharZero K]

theorem hb : ∀ j, MvPowerSeries.constantCoeff
    ((![PowerSeries.X, (0 : PowerSeries K)] : Fin 2 → PowerSeries K) j) = 0 := by
  intro j
  fin_cases j
  · exact MvPowerSeries.constantCoeff_X _
  · simp

theorem cc_omega (F : FormalGroup (Formalism.G.unitBall K)) :
    PowerSeries.constantCoeff (omegaF F) = ccd 1 (FK F).toPowerSeries := by
  unfold Formalism.ELL.omegaF
  exact Formalism.G.LogP.constantCoeff_subst_of_zero _ hb

theorem pd_unit_X : MvPowerSeries.pderiv K () (PowerSeries.X : PowerSeries K) = 1 := by
  show MvPowerSeries.pderiv K () (MvPowerSeries.X ()) = 1
  simp [MvPowerSeries.pderiv_X]

theorem cc_domega (F : FormalGroup (Formalism.G.unitBall K)) :
    PowerSeries.constantCoeff (PowerSeries.derivative K (omegaF F)) =
      ccd 0 (MvPowerSeries.pderiv K 1 (FK F).toPowerSeries) := by
  have hd : ∀ g : PowerSeries K, PowerSeries.derivative K g = MvPowerSeries.pderiv K () g := by
    intro g
    ext n
    rw [PowerSeries.coeff_derivative]
    show _ = MvPowerSeries.coeff (Finsupp.single () n) (MvPowerSeries.pderiv K () g)
    rw [MvPowerSeries.coeff_pderiv, ← Finsupp.single_add]
    simp only [Finsupp.single_eq_same]
    rfl
  rw [hd]
  change MvPowerSeries.constantCoeff (MvPowerSeries.pderiv K () (Formalism.ELL.omegaF F)) = _
  unfold Formalism.ELL.omegaF
  rw [pderiv_subst hb, Fin.sum_univ_two]
  simp only [map_add, map_mul, Formalism.G.LogP.constantCoeff_subst_of_zero _ hb, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, pd_unit_X, map_zero, mul_zero, add_zero, map_one, mul_one]
  rfl

theorem constantCoeff_second_derivative_law (F : FormalGroup (Formalism.G.unitBall K)) (φ : PowerSeries K) :
    PowerSeries.constantCoeff ((invD F)^[2] φ) =
      ccd 1 (FK F).toPowerSeries *
        (ccd 0 (MvPowerSeries.pderiv K 1 (FK F).toPowerSeries) *
            PowerSeries.constantCoeff (PowerSeries.derivative K φ) +
          ccd 1 (FK F).toPowerSeries *
            PowerSeries.constantCoeff (PowerSeries.derivative K (PowerSeries.derivative K φ))) := by
  unfold Formalism.ELL.invD
  show PowerSeries.constantCoeff (Formalism.ELL.omegaF F * PowerSeries.derivative K
      (Formalism.ELL.omegaF F * PowerSeries.derivative K φ)) = _
  rw [map_mul, Derivation.leibniz]
  simp only [map_add, map_mul, smul_eq_mul, cc_omega, cc_domega]
  ring

theorem linearCoeff_zero_formal_group_law (F : FormalGroup (Formalism.G.unitBall K)) : ccd 0 (FK F).toPowerSeries = 1 := by
  rw [ccd_single]
  simp [Formalism.ELL.FK, FormalGroup.map, MvPowerSeries.coeff_map, F.lin_coeff_X]

theorem linearCoeff_one_formal_group_law (F : FormalGroup (Formalism.G.unitBall K)) : ccd 1 (FK F).toPowerSeries = 1 := by
  rw [ccd_single]
  simp [Formalism.ELL.FK, FormalGroup.map, MvPowerSeries.coeff_map, F.lin_coeff_Y]

end Formalism.ELL.FormalGroupQuadraticJets

namespace Formalism.ELL

open Formalism.G Formalism.ELL.FormalGroupQuadraticJets Formalism.G.LogCR

theorem jetsTwo_of (hN : Formalism.ELL.NPderiv.{u}) : Formalism.ELL.JetsTwo.{u} := by
  intro K _ _ _ F φ a a' ha ha' hG
  have ha0 : PowerSeries.constantCoeff a = 0 := ha.1
  have ha0' : PowerSeries.constantCoeff a' = 0 := ha'.1
  have hβ : ∀ x y : MvPowerSeries (Fin 2) K, betaF F φ x y =
      φ.subst (MvPowerSeries.subst ![x, y] (FK F).toPowerSeries) - φ.subst x - φ.subst y :=
    fun x y => rfl
  have cX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K) = 0 :=
    MvPowerSeries.constantCoeff_X _
  have constantCoeff_threeGroupsFirstVariables_eq_zero : MvPowerSeries.constantCoeff (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) = 0 :=
    MvPowerSeries.constantCoeff_X _
  have cu : MvPowerSeries.constantCoeff
      (a.subst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K)) = 0 := by
    rw [cc_psubst cX0]; exact ha0
  have cv : MvPowerSeries.constantCoeff
      (a'.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K)) = 0 := by
    rw [cc_psubst constantCoeff_threeGroupsFirstVariables_eq_zero]; exact ha0'
  have hX00 : ccd 0 (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K) = 1 := by
    rw [ccd_single, MvPowerSeries.coeff_X, if_pos rfl]
  have hX10 : ccd 1 (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K) = 0 := by
    rw [ccd_single, MvPowerSeries.coeff_X, if_neg]
    rw [Finsupp.single_left_inj one_ne_zero]; decide
  have hX01 : ccd 0 (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) = 0 := by
    rw [ccd_single, MvPowerSeries.coeff_X, if_neg]
    rw [Finsupp.single_left_inj one_ne_zero]; decide
  have hX11 : ccd 1 (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) = 1 := by
    rw [ccd_single, MvPowerSeries.coeff_X, if_pos rfl]
  have hQX : ∀ j : Fin 2, Q (MvPowerSeries.X j : MvPowerSeries (Fin 2) K) = 0 := by
    intro j
    unfold Q
    rw [MvPowerSeries.pderiv_X]
    fin_cases j <;> simp [Pi.single_apply, Derivation.map_one_eq_zero]
  have cS : ∀ x y : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff x = 0 →
      MvPowerSeries.constantCoeff y = 0 →
      MvPowerSeries.constantCoeff (MvPowerSeries.subst ![x, y] (FK F).toPowerSeries) = 0 := by
    intro x y hx hy
    rw [Formalism.G.LogP.constantCoeff_subst_of_zero _ (hv hx hy)]
    exact (FK F).zero_constantCoeff
  have h1 : Q (betaF F φ (a.subst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K))
      (MvPowerSeries.X 1)) = PowerSeries.coeff 1 a *
        (PowerSeries.constantCoeff (PowerSeries.derivative K (PowerSeries.derivative K φ)) +
          PowerSeries.constantCoeff (PowerSeries.derivative K φ) *
            ccd 0 (MvPowerSeries.pderiv K 1 (FK F).toPowerSeries)) := by
    rw [hβ, Q_sub, Q_sub, Q_phi φ (cS _ _ cu constantCoeff_threeGroupsFirstVariables_eq_zero), Q_phi φ cu, Q_phi φ constantCoeff_threeGroupsFirstVariables_eq_zero,
      ccd_F _ cu constantCoeff_threeGroupsFirstVariables_eq_zero, ccd_F _ cu constantCoeff_threeGroupsFirstVariables_eq_zero, Q_F _ cu constantCoeff_threeGroupsFirstVariables_eq_zero]
    simp only [linearCoeff_zero_formal_group_law, linearCoeff_one_formal_group_law, linearCoeff_zero_subst_X0, linearCoeff_one_subst_X0, quadraticJet_subst_X0, hX01, hX11, hQX, ccd_mixed]
    ring
  have h2 : Q (betaF F φ (MvPowerSeries.X 0)
      (a'.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K))) = PowerSeries.coeff 1 a' *
        (PowerSeries.constantCoeff (PowerSeries.derivative K (PowerSeries.derivative K φ)) +
          PowerSeries.constantCoeff (PowerSeries.derivative K φ) *
            ccd 0 (MvPowerSeries.pderiv K 1 (FK F).toPowerSeries)) := by
    rw [hβ, Q_sub, Q_sub, Q_phi φ (cS _ _ cX0 cv), Q_phi φ cX0, Q_phi φ cv,
      ccd_F _ cX0 cv, ccd_F _ cX0 cv, Q_F _ cX0 cv]
    simp only [linearCoeff_zero_formal_group_law, linearCoeff_one_formal_group_law, linearCoeff_one_subst_X1, linearCoeff_zero_subst_X1, quadraticJet_subst_X1, hX00, hX10, hQX, ccd_mixed]
    ring
  have hQG := hN K (Fin 2) _ hG 0
  have key : Q (betaF F φ (a.subst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K))
        (MvPowerSeries.X 1) -
      betaF F φ (MvPowerSeries.X 0) (a'.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K))) =
      (PowerSeries.coeff 1 a - PowerSeries.coeff 1 a') * PowerSeries.constantCoeff ((invD F)^[2] φ) := by
    rw [Q_sub, h1, h2, constantCoeff_second_derivative_law, linearCoeff_one_formal_group_law]
    ring
  rw [← key]
  unfold Q
  rw [show ∀ Z : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff (MvPowerSeries.pderiv K 1 Z) =
      MvPowerSeries.coeff (Finsupp.single 1 1) Z from fun Z => ccd_single Z 1]
  exact hQG _

end Formalism.ELL
