import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StGlob
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteBasisAlgebraicForms
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CompactSpaceDefiniteUnitaryInfinitePoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinUMulInfU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClozelCohomology.ContinuousEntryPairings.UnitaryCoordinateAlgebraDense
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open MeasureTheory GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

open MvPolynomial in

private theorem continuous_coeff_blockAct' {Y : Type} [TopologicalSpace Y] {T : Type} {k n : ℕ}
    (A : Y → T → Matrix (Fin k) (Fin k) ℂ) (hA : ∀ t a b, Continuous fun x => A x t a b)
    (F : MvPolynomial (T × Fin k × Fin n) ℂ) :
    ∀ m, Continuous fun x => coeff m (Formalism.GradedWeylDivisibility.blockAct ℂ (A x) F) := by
  classical
  induction F using MvPolynomial.induction_on with
  | C a =>
    intro m
    have e : ∀ x, Formalism.GradedWeylDivisibility.blockAct ℂ (n := n) (A x) (C a) = (C a : MvPolynomial (T × Fin k × Fin n) ℂ) :=
      fun x => (Formalism.GradedWeylDivisibility.blockAct ℂ (n := n) (A x)).commutes a
    simp only [e]
    exact continuous_const
  | add p q hp hq =>
    intro m
    simp only [map_add, coeff_add]
    exact (hp m).add (hq m)
  | mul_X p w hp =>
    intro m
    have e : ∀ x, Formalism.GradedWeylDivisibility.blockAct ℂ (A x) (X w) = ∑ b : Fin k, C (A x w.1 w.2.1 b) * X (w.1, (b, w.2.2)) :=
      fun x => aeval_X _ _
    simp only [map_mul, e, Finset.mul_sum, coeff_sum]
    refine continuous_finset_sum _ fun b _ => ?_
    simp only [mul_left_comm _ (C _), coeff_C_mul, coeff_mul_X']
    by_cases hw : ((w.1, (b, w.2.2)) : T × Fin k × Fin n) ∈ m.support
    · simp only [hw, if_true]
      exact (hA _ _ _).mul (hp _)
    · simp only [hw, if_false, mul_zero]
      exact continuous_const

private theorem continuous_detTwK' {Y : Type} [TopologicalSpace Y] {T : Type} [Fintype T] {n : ℕ}
    (lam : T → DomWeight n) (g : Y → (T → GL (Fin n) ℂ))
    (hg : ∀ v a b, Continuous fun x => ((g x v : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) a b) :
    Continuous fun x => Formalism.L2.DIV.detTwK lam (g x) := by
  simp only [Formalism.L2.DIV.detTwK]
  refine continuous_finset_prod _ fun τ _ => ?_
  have e : ∀ x, detPow ℂ n (g x τ) (lam τ).detShift =
      ((g x τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det ^ (lam τ).detShift := by
    intro x
    rw [detPow, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply]
  simp only [e]
  have hc : Continuous fun x => ((g x τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) :=
    continuous_pi fun a => continuous_pi fun b => hg τ a b
  refine hc.matrix_det.zpow₀ _ fun x => Or.inl ?_
  exact (Matrix.isUnit_iff_isUnit_det _).1 (g x τ).isUnit |>.ne_zero

open MvPolynomial in

private theorem continuous_rhoK_coeff' {Y : Type} [TopologicalSpace Y] {T : Type} [Fintype T] {n : ℕ}
    (lam : T → DomWeight n) {d : ℕ} (B : Module.Basis (Fin d) ℂ (Formalism.L2.DIV.VV ℂ lam)) (g : Y → (T → GL (Fin n) ℂ))
    (hg : ∀ v a b, Continuous fun x => ((g x v : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) a b) (i j : Fin d) :
    Continuous fun x => LinearMap.toMatrix B B (Formalism.L2.DIV.rhoK lam (g x)) i j := by
  classical
  obtain ⟨s, a, ha⟩ := GlobalTheory.IntStruct.exists_coord_eq_sum_coeff (Formalism.L2.DIV.VV ℂ lam) B i
  have e : ∀ x, LinearMap.toMatrix B B (Formalism.L2.DIV.rhoK lam (g x)) i j = ∑ m : s, a m *
      (Formalism.L2.DIV.detTwK lam (g x) * coeff m.1 (Formalism.GradedWeylDivisibility.blockAct ℂ
        (fun τ => Matrix.transpose ((g x τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))
        ((B j : Formalism.L2.DIV.VV ℂ lam) : Formalism.L2.DIV.Pol ℂ T n))) := by
    intro x
    rw [LinearMap.toMatrix_apply, ha]
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
  simp only [e]
  exact continuous_finset_sum _ fun m _ => continuous_const.mul ((continuous_detTwK' lam g hg).mul
    (continuous_coeff_blockAct' _ (fun t a b => hg t b a) _ m.1))

private theorem continuous_rep_coeff {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (W : Wt E a) {d : ℕ}
    (B : Module.Basis (Fin d) ℂ W.Sp) (i j : Fin d) :
    Continuous fun x : infU E a => B.repr (W.rep x (B i)) j := by
  have h := continuous_rhoK_coeff' (T := InfinitePlace E) W B (fun x : infU E a => cAll x.1)
    (fun v p q => GlobalTheory.PolyRealU.continuous_entry v.embedding p q) j i
  refine h.congr fun x => ?_
  rw [LinearMap.toMatrix_apply]
  rfl

theorem UpperTheory.Gal.Gen.wBound_pf :
    UpperTheory.Gal.Gen.WBound := by
  intro E _ _ _ a W d B
  haveI := GlobalTheory.InfUCompact.compactSpace_infU E a
  have hc : Continuous fun x : infU E a => fun (i j : Fin d) => B.repr (W.rep x (B i)) j :=
    continuous_pi fun i => continuous_pi fun j => continuous_rep_coeff W B i j
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨C, fun x i j => ?_⟩
  exact ((norm_le_pi_norm (fun j => B.repr (W.rep x (B i)) j) j).trans
    (norm_le_pi_norm (fun (i j : Fin d) => B.repr (W.rep x (B i)) j) i)).trans (hC x (Set.mem_univ _))
