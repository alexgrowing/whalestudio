import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RatioTrans
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PsiEvenBox

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily

theorem sym_box (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] {j : ℕ} {D D' : DegPre R}
    (pD : IsPowDeg D' D j) {Z : Scheme.{0}} (r : Z ⟶ D'.P.A.left) (y : Z) {J J'} (hJ : Good D.P.L y J)
    (hJ' : Good D'.P.L y J') :
    om pD.w y J J' (r ≫ (ι[D'.P.A]).left) * (om pD.w y J J' r)⁻¹ * val D'.sym r y J' =
      ∏ i, val D.sym (r ≫ (pD.pw.pr i).left) y J := by
  have hψ : ∀ (i : Fin j) (a : Fin 2), (![(ι[D'.P.A]).left, 𝟙 D'.P.A.left] : Fin 2 → _) a ≫ (pD.pw.pr i).left =
      (pD.pw.pr i).left ≫ (![(ι[D.P.A]).left, 𝟙 D.P.A.left] : Fin 2 → _) a := by
    intro i a
    have := pD.pw.hom i
    fin_cases a
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]
      rw [← Over.comp_left, ← Over.comp_left, GrpObj.inv_hom]
    · simp
  have he : eSec D'.P.A ≫ D'.P.A.hom = 𝟙 _ := Over.w η[D'.P.A]
  have hp : Function.Surjective D'.P.A.hom.appTop.hom := (hG _ D'.P.A D'.P.isAb).2
  have hinv : eSec D'.P.A ≫ (ι[D'.P.A]).left = eSec D'.P.A := by
    unfold eSec
    rw [← Over.comp_left, GrpObj.one_inv]
  have hpr : ∀ i, eSec D'.P.A ≫ (pD.pw.pr i).left = eSec D.P.A := fun i => by
    have := pD.pw.hom i
    unfold eSec
    rw [← Over.comp_left, IsMonHom.one_hom]
  have hone : ∀ (E : DegPre R) (z : ↥(𝟙_ (Over (Spec (CommRingCat.of R)))).left)
      (K : ((𝟙_ (Over (Spec (CommRingCat.of R)))).left ⟶ E.P.A.left) → E.P.L.ι), Good E.P.L z K →
      val E.sym (eSec E.P.A) z K = 1 := by
    intro E z K hK
    have h := val_corr hK E.sym_rig (𝟙 _)
    rw [val_pull hK, Category.id_comp, val_one] at h
    exact h
  have key := GlobalTheory.CubBox.box_unique (φ' := ![(ι[D'.P.A]).left, 𝟙 D'.P.A.left]) (φ := ![(ι[D.P.A]).left, 𝟙 D.P.A.left])
    (ε := ![1, -1]) (ρ := fun i => (pD.pw.pr i).left) D.P.isLB D'.P.isLB pD.w pD.w_gen hψ D'.sym_gen D.sym_gen
    D'.P.A.hom (eSec D'.P.A) he hp
  specialize key (by
    intro z K K' hK hK'
    rw [Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg_one,
      Category.comp_id, hinv, hpr, mul_inv_cancel]
    rw [hone D' z K' hK', hone D z K hK, Finset.prod_const_one, _root_.mul_one]) Z r y J J' hJ hJ'
  rw [Fin.prod_univ_two] at key
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg_one,
    Category.comp_id] at key
  exact key

private theorem mul_mul_eq_mul_mul_mul_inv_mul {G : Type*} [CommGroup G] (a b c s : G) :
    b * c * s = a * (c * (b * a⁻¹ * s)) := by
  rw [← mul_inv_cancel_left a (b * c * s)]
  ac_rfl

theorem main : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j), D.PsiEven → D'.PsiEven := by
  intro hG R _ _ j D D' pD hE χ
  refine corr_of_val D'.P.isLB (fun y J' hJ' => ?_)
  obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB y
  have ha : D'.xK (-χ) = D'.xK χ ≫ (ι[D'.P.A]).left := by
    show ptK (D'.c (-χ)) = ptK (D'.c χ) ≫ (ι[D'.P.A]).left
    rw [GlobalTheory.PsiEvenPull.c_neg]
    unfold ptK
    rw [← Over.comp_left, Category.assoc]
  have hb : ∀ i, D'.xK χ ≫ (pD.pw.pr i).left = D.xK (pD.xe χ i) := by
    intro i
    have h := cPoint_pr pD (TK R) χ i
    unfold cP at h
    show ptK (D'.c χ) ≫ (pD.pw.pr i).left = ptK (D.c (pD.xe χ i))
    unfold ptK
    rw [← Over.comp_left, h]
  have hc : ∀ i, pD.xe (-χ) i = -pD.xe χ i := fun i => by
    rw [map_neg, Pi.neg_apply]
  have h4 : ∀ i, val (D.psi (pD.xe (-χ) i)) (𝟙 _) y J * val D.sym (D'.xK χ ≫ (pD.pw.pr i).left) y J =
      val (D.psi (pD.xe χ i)) (𝟙 _) y J := fun i => by
    have h := val_corr hJ (hE (pD.xe χ i)) (𝟙 _)
    rw [val_mul hJ, val_pull hJ, Category.id_comp] at h
    rw [hc, hb]
    exact h
  have h1 := psi_val pD hJ hJ' χ (𝟙 _)
  have h2 := psi_val pD hJ hJ' (-χ) (𝟙 _)
  have h3 := sym_box hG pD (D'.xK χ) y hJ hJ'
  rw [Category.id_comp, inv_mul_eq_iff_eq_mul] at h1 h2
  rw [ha] at h2
  rw [val_mul hJ', val_pull hJ', Category.id_comp, h1, h2]
  simp only [← h4, Finset.prod_mul_distrib]
  rw [← h3]
  exact mul_mul_eq_mul_mul_mul_inv_mul _ _ _ _

end GlobalTheory.PsiEvenBox
