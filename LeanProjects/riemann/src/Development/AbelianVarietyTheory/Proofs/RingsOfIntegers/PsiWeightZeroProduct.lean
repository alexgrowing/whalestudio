import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TraceFormTwistIsoOfPullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PsiWZeroProd

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily

variable {R : Type} [CommRing R] [IsDomain R] {j : ℕ} {D D' : DegPre R}

theorem four_comm {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
    (p : A' ⟶ A) [IsMonHom p] (f : A ⟶ A) (f' : A' ⟶ A') (h : f' ≫ p = p ≫ f) (k : Fin 4) :
    (![(padd A' (𝟙 _) f').left, 𝟙 A'.left, f'.left, (toUnit A' ≫ η[A']).left] : Fin 4 → _) k ≫ p.left =
      p.left ≫ (![(padd A (𝟙 _) f).left, 𝟙 A.left, f.left, (toUnit A ≫ η[A]).left] : Fin 4 → _) k := by
  fin_cases k
  · show (padd A' (𝟙 _) f').left ≫ p.left = p.left ≫ (padd A (𝟙 _) f).left
    rw [← Over.comp_left, ← Over.comp_left]
    unfold padd
    congr 1
    rw [Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map, Category.id_comp, h, ← Category.assoc, comp_lift,
      Category.comp_id]
  · show 𝟙 A'.left ≫ p.left = p.left ≫ 𝟙 A.left
    simp
  · show f'.left ≫ p.left = p.left ≫ f.left
    rw [← Over.comp_left, ← Over.comp_left, h]
  · show (toUnit A' ≫ η[A']).left ≫ p.left = p.left ≫ (toUnit A ≫ η[A]).left
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    rw [Category.assoc, IsMonHom.one_hom, ← Category.assoc, toUnit_unique (p ≫ toUnit A) (toUnit A')]

set_option maxHeartbeats 1000000 in
theorem psi_weight_zero_product (pD : IsPowDeg D' D j) {O : Type} [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X]
    (hx : ∀ (a : O) (x : D'.X), pD.xe (a • x) = a • pD.xe x) (oa : D.OAct O) (oa' : D'.OAct O)
    (hact : ∀ a i, oa'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ oa.onB.act a) (w0 : O) (h : TraceFormTwistIso D oa w0) :
    TraceFormTwistIso D' oa' w0 := by
  obtain ⟨u, hu, h0, hy⟩ := h
  have := oa'.onB.hom w0
  have : ∀ i, IsMonHom (pD.pw.pr i) := pD.pw.hom
  obtain ⟨u', hu', hval⟩ := exists_boxPull_gen pD.w pD.w_gen D.P.isLB D'.P.isLB
    (fun i => (pD.pw.pr i).left) (fun i k => four_comm (pD.pw.pr i) _ _ (hact w0 i) k) (fun _ => u) (fun _ => hu)
  have hη : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) = η := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  refine ⟨u', hu', ?_, ?_⟩
  · apply corr_of_val D'.P.isLB
    intro z J' hJ'
    obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB z
    rw [val_pull hJ', val_one]
    have e1 := hval _ (𝟙 _ ≫ eSec D'.P.A) z J J' hJ hJ'
    have e2 : ∀ i, val u ((𝟙 _ ≫ eSec D'.P.A) ≫ (pD.pw.pr i).left) z J = 1 := by
      intro i
      have hc : (𝟙 _ ≫ eSec D'.P.A) ≫ (pD.pw.pr i).left = 𝟙 _ ≫ eSec D.P.A := by
        simp only [Category.id_comp, eSec, ← Over.comp_left, IsMonHom.one_hom]
      rw [hc, ← val_pull hJ, val_corr hJ h0, val_one]
    have e3 := GlobalTheory.PsiWZeroPull.prod_four (oa'.onB.act w0) (η[D'.P.A]) (fun m => om pD.w z J J' (𝟙 _ ≫ m))
    simp only [← hη] at e3
    rw [Finset.prod_eq_one (fun i _ => e2 i)] at e1
    simp only [Category.assoc] at e1
    have e4 : ∀ m : D'.P.A.left ⟶ D'.P.A.left, eSec D'.P.A ≫ m = (η[D'.P.A]).left ≫ m := fun m => rfl
    have h1f : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) ≫ oa'.onB.act w0 = 1 := by
      rw [hη, IsMonHom.one_hom]
    simp only [e4, ← hη, e3, h1f] at e1
    have alg : ∀ {G : Type} [CommGroup G] (a v : G), a * (a ^ 2)⁻¹ * a⁻¹ * a ^ 2 * v = v := by
      intros
      group
    have h11 : ((1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) * 1) = 1 := mul_one _
    erw [h11] at e1
    rwa [alg] at e1
  · intro y
    apply corr_of_val D'.P.isLB
    intro z J' hJ'
    obtain ⟨J, hJ⟩ := exists_good_at D.P.isLB z
    have hD : ∀ x : D.X, val (D.psi (x + w0 • x)) (𝟙 _) z J * (val (D.psi x) (𝟙 _) z J)⁻¹ *
        (val (D.psi (w0 • x)) (𝟙 _) z J)⁻¹ * (val D.rigK (𝟙 _) z J)⁻¹ * val u (𝟙 _ ≫ D.xK x) z J =
        val (D.psi x) (𝟙 _) z J * val D.rigK (𝟙 _) z J := by
      intro x
      have hc := val_corr hJ (hy x) (𝟙 _)
      simp only [DegPre.tau, val_mul hJ, val_inv, val_pull hJ] at hc
      exact hc
    rw [val_mul hJ', val_mul hJ', val_pull hJ']
    simp only [DegPre.tau, val_mul hJ', val_inv]
    have P := fun x => psi_val pD hJ hJ' x (𝟙 _)
    have Rg := rig_val pD hJ hJ' (𝟙 _)
    have U := hval _ (𝟙 _ ≫ D'.xK y) z J J' hJ hJ'
    have hpr : ∀ i, (𝟙 _ ≫ D'.xK y) ≫ (pD.pw.pr i).left = 𝟙 _ ≫ D.xK (pD.xe y i) := by
      intro i
      simp only [Category.id_comp, DegPre.xK, ptK, ← Over.comp_left, Category.assoc, pD.c_pr]
    simp only [hpr] at U
    have e3 := GlobalTheory.PsiWZeroPull.prod_four (oa'.onB.act w0) (toUnit (TK R) ≫ D'.c y)
      (fun m => om pD.w z J J' (𝟙 _ ≫ m))
    have e6 : (toUnit (TK R) ≫ D'.c y) ≫ oa'.onB.act w0 = toUnit (TK R) ≫ D'.c (w0 • y) := by
      rw [Category.assoc, ← oa'.c_lin]
    have e7 : (toUnit (TK R) ≫ D'.c y) * (toUnit (TK R) ≫ D'.c (w0 • y)) = toUnit (TK R) ≫ D'.c (y + w0 • y) := by
      rw [D'.c_add]
      unfold padd
      rw [← Category.assoc, comp_lift, Hom.mul_def]
    have e8 : ∀ x, (toUnit (TK R) ≫ D'.c x).left = D'.xK x := fun _ => rfl
    have e9 : (toUnit (TK R) ≫ η[D'.P.A]).left = (toUnit (TK R)).left ≫ eSec D'.P.A := rfl
    rw [e6, e7, Hom.one_def] at e3
    simp only [e8, e9] at e3
    simp only [Category.id_comp] at P Rg U e3 hD ⊢
    rw [e3] at U
    have hxe1 : ∀ i, pD.xe (y + w0 • y) i = pD.xe y i + w0 • pD.xe y i := by
      intro i
      rw [map_add, hx]
      rfl
    have hxe2 : ∀ i, pD.xe (w0 • y) i = w0 • pD.xe y i := by
      intro i
      rw [hx]
      rfl
    have Py := inv_mul_eq_iff_eq_mul.mp (P y)
    have Ps := inv_mul_eq_iff_eq_mul.mp (P (y + w0 • y))
    have Pw := inv_mul_eq_iff_eq_mul.mp (P (w0 • y))
    have key := Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) => (by rw [hxe1 i, hxe2 i]; exact hD (pD.xe y i) :
      val (D.psi (pD.xe (y + w0 • y) i)) (𝟙 _) z J * (val (D.psi (pD.xe y i)) (𝟙 _) z J)⁻¹ *
        (val (D.psi (pD.xe (w0 • y) i)) (𝟙 _) z J)⁻¹ * (val D.rigK (𝟙 _) z J)⁻¹ * val u (D.xK (pD.xe y i)) z J =
        val (D.psi (pD.xe y i)) (𝟙 _) z J * val D.rigK (𝟙 _) z J))
    simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib] at key
    rw [Py, Ps, Pw, eq_inv_mul_of_mul_eq Rg, eq_inv_mul_of_mul_eq U, eq_inv_mul_of_mul_eq key]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    abel

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (O : Type) [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X], (∀ (a : O) (x : D'.X), pD.xe (a • x) = a • pD.xe x) → ∀ (oa : D.OAct O) (oa' : D'.OAct O), (∀ a i, oa'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ oa.onB.act a) → ∀ w0 : O, Geo.Tor.TraceFormTwistIso D oa w0 → Geo.Tor.TraceFormTwistIso D' oa' w0 := by
  intro R _ _ j D D' pD O _ _ _ _ hx oa oa' hact w0 h
  exact psi_weight_zero_product pD hx oa oa' hact w0 h

end GlobalTheory.PsiWZeroProd
