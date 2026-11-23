import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMatrixOrderActionOnPowerStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBalAdd
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointBalancedPowerLiftStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MatDeg

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

variable {R : Type} [CommRing R] [IsDomain R]

theorem c_add' (D : DegPre R) (a b : D.X) : D.c (a + b) = D.c a * D.c b := D.c_add a b

theorem c_zero' (D : DegPre R) : D.c 0 = 1 := by
  have h := c_add' D 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem c_sum (D : DegPre R) {J : Type} (s : Finset J) (x : J → D.X) :
    D.c (∑ l ∈ s, x l) = ∏ l ∈ s, D.c (x l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using c_zero' D
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, c_add', ih]

theorem comp_prod {S : Scheme.{0}} {T T' A : Over S} [GrpObj A] [IsCommMonObj A] (f : T' ⟶ T)
    {J : Type} (s : Finset J) (x : J → (T ⟶ A)) :
    f ≫ ∏ l ∈ s, x l = ∏ l ∈ s, f ≫ x l := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, MonObj.comp_mul, ih]

theorem act_add {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {O : Type} [Ring O]
    (ρ : RingAct A O) (a b : O) : ρ.act (a + b) = ρ.act a * ρ.act b := ρ.map_add a b

theorem act_zero {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {O : Type} [Ring O]
    (ρ : RingAct A O) : ρ.act 0 = 1 := by
  have h := act_add ρ 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem tauBal_of_subsingleton (D : DegPre R) [Subsingleton D.X] (f g : D.P.A ⟶ D.P.A)
    (a b : D.X → D.X) : D.TauBal f g a b := by
  intro u hu h₀ y y'
  rw [Subsingleton.elim (a y) 0, Subsingleton.elim (b y') 0, Subsingleton.elim y 0,
    Subsingleton.elim y' 0]
  refine corr_of_val D.P.isLB fun z J hJ => ?_
  have e : D.pt2 0 0 = (toUnit (TK R)).left ≫ zero2 D.P.A := by
    rw [DegPre.pt2, c_zero', zero2, ← Over.comp_left, comp_lift]
    simp [Hom.one_def]
  have := val_corr hJ h₀ (toUnit (TK R)).left
  rw [val_pull hJ, val_one] at this
  rw [val_mul hJ, val_pull hJ, Category.id_comp, e, this, _root_.mul_one]

theorem exists_matrix_act : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j), D.TauBimult → D'.TauBimult → ∀ (O : Type) [Ring O] [StarRing O] [Module O D.X] (ιD : D.OAct O), ∃ (_ : Module (Matrix (Fin j) (Fin j) O) D'.X) (ι' : D'.OAct (Matrix (Fin j) (Fin j) O)), (∀ (m : (Matrix (Fin j) (Fin j) O)) (x : D'.X) (i : Fin j), pD.xe (m • x) i = ∑ l, m i l • pD.xe x l) ∧ (∀ (m : (Matrix (Fin j) (Fin j) O)) (i : Fin j), ι'.onB.act m ≫ pD.pw.pr i = ∏ l, pD.pw.pr l ≫ ιD.onB.act (m i l)) := by
  intro hG R _ _ j D D' pD hB hB' O _ _ _ ιD
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_matrix_order_action_on_power _ D.P D'.P j pD.pw pD.w pD.w_gen ⟨D'.P.L, D'.rig, D'.P.isLB, D'.rig_gen⟩ rfl
    ⟨D'.cub⟩ O ιD.onB
  letI : Module (Matrix (Fin j) (Fin j) O) (Fin j → D.X) := Matrix.Module.matrixModule
  letI mD : Module (Matrix (Fin j) (Fin j) O) D'.X := pD.xe.module _
  have hx : ∀ (m : Matrix (Fin j) (Fin j) O) (x : D'.X) (i : Fin j),
      pD.xe (m • x) i = ∑ l, m i l • pD.xe x l := fun m x i => by
    have : m • x = pD.xe.symm (m • pD.xe x) := rfl
    rw [this, AddEquiv.apply_symm_apply]; rfl
  have hc : ∀ (m : Matrix (Fin j) (Fin j) O) (x : D'.X), D'.c (m • x) = D'.c x ≫ ρ.act m := fun m x => by
    apply pD.pw.lim.hom_ext
    rintro ⟨i⟩
    show D'.c (m • x) ≫ pD.pw.pr i = (D'.c x ≫ ρ.act m) ≫ pD.pw.pr i
    rw [pD.c_pr, hx, c_sum, Category.assoc, hρ, comp_prod]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [ιD.c_lin, ← Category.assoc, pD.c_pr]
  have hs : ∀ (i l : Fin j) (a : O) (y : D'.X),
      Matrix.single i l a • y = pD.xe.symm (Pi.single i (a • pD.xe y l)) := fun i l a y => by
    apply pD.xe.injective
    rw [AddEquiv.apply_symm_apply]
    funext s
    rw [hx, Finset.sum_eq_single l (fun b _ hb => by rw [Matrix.single_apply_of_col_ne _ _ hb.symm, zero_smul])
      (fun h => absurd (Finset.mem_univ _) h)]
    by_cases h : s = i
    · subst h; simp
    · rw [Matrix.single_apply_of_row_ne (Ne.symm h), zero_smul, Pi.single_eq_of_ne h]
  have hp : ∀ (i l : Fin j) (a : O) (s : Fin j), ρ.act (Matrix.single i l a) ≫ pD.pw.pr s =
      if s = i then pD.pw.pr l ≫ ιD.onB.act a else 1 := fun i l a s => by
    rw [hρ, Finset.prod_eq_single l (fun b _ hb => by
      rw [Matrix.single_apply_of_col_ne _ _ hb.symm, act_zero, MonObj.comp_one])
      (fun h => absurd (Finset.mem_univ _) h)]
    by_cases h : s = i
    · subst h; simp
    · rw [Matrix.single_apply_of_row_ne (Ne.symm h), act_zero, MonObj.comp_one, if_neg h]
  have hel : ∀ (i l : Fin j) (a : O), D'.TauBal (ρ.act (Matrix.single i l a)) (ρ.act (star (Matrix.single i l a)))
      (fun y => Matrix.single i l a • y) (fun y => star (Matrix.single i l a) • y) := fun i l a => by
    have e : star (Matrix.single i l a) = Matrix.single l i (star a) := by
      rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_single]
    haveI := ιD.onB.hom a
    haveI := ιD.onB.hom (star a)
    rw [e, funext (hs i l a), funext (hs l i (star a))]
    exact GlobalTheory.T.rosati_adjoint_balanced_power_lift hG R j D D' pD hB (ιD.onB.act a) (ιD.onB.act (star a)) (fun y => a • y) (fun y => star a • y)
      (ιD.c_lin a) (ιD.c_lin (star a)) (ιD.onB.rosati a) (ιD.tau_bal a) _ _ i l (hp i l a) (hp l i (star a))
  refine ⟨mD, ⟨ρ, hc, fun m => ?_⟩, hx, hρ⟩
  induction m using Matrix.induction_on' with
  | h_zero =>
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · haveI : Subsingleton D'.X := pD.xe.toEquiv.subsingleton
      exact tauBal_of_subsingleton D' _ _ _ _
    · have := hel ⟨0, hj⟩ ⟨0, hj⟩ 0
      rwa [Matrix.single_zero] at this
  | h_add p q hp hq =>
    haveI := ρ.hom p
    haveI := ρ.hom q
    haveI := ρ.hom (star p)
    haveI := ρ.hom (star q)
    have := GlobalTheory.TauBalAdd.tauBal_add hG R D' hB' _ _ _ _ _ _ _ _ (hc p) (hc (star p)) (hc q) (hc (star q))
      (ρ.rosati p) (ρ.rosati q) hp hq
    rw [star_add, act_add, act_add, funext (add_smul p q), funext (add_smul (star p) (star q))]
    exact this
  | h_std_basis i l a => exact hel i l a

end GlobalTheory.MatDeg
