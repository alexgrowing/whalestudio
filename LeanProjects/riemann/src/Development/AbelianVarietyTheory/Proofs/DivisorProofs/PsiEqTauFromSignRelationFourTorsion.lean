import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescalePsiW0
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiFunctionEqThetaOfPrimitiveLineBundle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FrameSqEqOfSymmetricThetaElement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LinearUniformisationTorsionMapIsLinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenMulPullPowUnif
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairing
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsThetaOfField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenProd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWFinal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RepsXSt
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.PsiSignRel

open GlobalTheory.UT.SymFrame

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X]

theorem act_zero' (o : D.OAct O) : o.onB.act (0 : O) = 1 := by
  have h := o.onB.map_add 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

theorem act_add' (o : D.OAct O) (a c : O) : o.onB.act a * o.onB.act c = o.onB.act (a + c) :=
  (o.onB.map_add a c).symm

theorem act_comp' (o : D.OAct O) (a c : O) : o.onB.act a ≫ o.onB.act c = o.onB.act (c * a) :=
  (o.onB.map_mul c a).symm

theorem act_natCast' (o : D.OAct O) (n : ℕ) : o.onB.act (n : O) = 𝟙 D.P.A ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, act_zero', pow_zero]
  | succ n ih => rw [Nat.cast_succ, ← act_add', ih, o.onB.map_one, pow_succ]

theorem act_pow' (o : D.OAct O) (a : O) (n : ℕ) : o.onB.act a ^ n = o.onB.act ((n : O) * a) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, zero_mul, act_zero']
  | succ n ih => rw [pow_succ, ih, act_add', Nat.cast_succ, add_one_mul]

theorem prod_gam {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] (x : T ⟶ A) {U : Type} [CommGroup U]
    (k : (T.left ⟶ A.left) → U) :
    ∏ i : Fin 4, k (x.left ≫ (![(𝟙 A ^ 5).left, (𝟙 A ^ 4).left, 𝟙 _, (1 : A ⟶ A).left] : Fin 4 → _) i) ^
      (![2, -3, -2, 3] : Fin 4 → ℤ) i =
      k (x ^ 5).left ^ 2 * (k (x ^ 4).left ^ 3)⁻¹ * (k x.left ^ 2)⁻¹ * k (1 : T ⟶ A).left ^ 3 := by
  rw [Fin.prod_univ_four]
  show k (x ≫ 𝟙 A ^ 5).left ^ (2 : ℤ) * k (x ≫ 𝟙 A ^ 4).left ^ (-3 : ℤ) * k (x ≫ 𝟙 A).left ^ (-2 : ℤ) *
    k (x ≫ 1).left ^ (3 : ℤ) = _
  rw [MonObj.comp_pow, MonObj.comp_pow, MonObj.comp_one, Category.comp_id, zpow_neg, zpow_neg, zpow_ofNat, zpow_ofNat,
    zpow_ofNat, zpow_ofNat]

set_option maxHeartbeats 1600000 in

theorem core_id (hG : GlobalFnsSt) (o : D.OAct O) (w : O) (u : GlobalTheory.PsiRescale.FourGen D.P.L (o.onB.act w)) (hu : Normd u)
    (gam : LB.Gen (LB.LinComb D.P.L (K := Fin 4) ![(𝟙 D.P.A ^ 5).left, (𝟙 D.P.A ^ 4).left, 𝟙 _, (1 : D.P.A ⟶ D.P.A).left] ![2, -3, -2, 3]))
    (hgam : Normd gam)
    (ra : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (o.onB.act (star (1 + w))) (o.onB.act (1 + w))) rosatiε))
    (hra : GlobalTheory.TorusExt.IsRos D.P.L (o.onB.act (star (1 + w))) (o.onB.act (1 + w)) ra)
    (rw' : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (o.onB.act (star w)) (o.onB.act w)) rosatiε))
    (hrw : GlobalTheory.TorusExt.IsRos D.P.L (o.onB.act (star w)) (o.onB.act w) rw')
    (hw : w + star w = 1) {T : Over (Spec (CommRingCat.of R))} (b : T ⟶ D.P.A) (z : T.left) {J} (hJ : Good D.P.L z J) :
    val u (b ^ 4).left z J * val₂ ra z J ((b ^ 4) ≫ o.onB.act (1 + w)) b ^ 2 * val gam (b ≫ o.onB.act (1 + w)).left z J =
      th D z J (b ^ 4 * b ^ 4) ((b ^ 4) ≫ o.onB.act (star w * w)) b ^ 2 * th D z J (b ^ 4) (b ^ 4) b ^ 2 *
        val gam b.left z J ^ 2 * val₂ rw' z J ((b ^ 4) ≫ o.onB.act w) b ^ 2 * val gam (b ≫ o.onB.act w).left z J := by
  have hm : ∀ t : O, IsMonHom (o.onB.act t) := o.onB.hom
  have Gu := (grep_gen (Y := D.P.A) u hu.1 (o.onB.act 4).left).congr (P' := fun _ _ h =>
      h (o.onB.act 4 * (o.onB.act 4 ≫ o.onB.act w)).left * (h (o.onB.act 4).left ^ 2)⁻¹ *
        (h (o.onB.act 4 ≫ o.onB.act w).left)⁻¹ * h (1 : D.P.A ⟶ D.P.A).left ^ 2)
    (fun _ _ h => GlobalTheory.PsiWZeroPull.prod_four _ _ h) (fun _ _ _ _ _ => rfl)
  have Gra := (grep_gen (Y := D.P.A) ra hra.1 (lift (o.onB.act 4 ≫ o.onB.act (1 + w)) (𝟙 D.P.A)).left).congr
    (fun _ _ h => prod_ros _ _ _ _ h) (fun _ _ _ _ _ => rfl)
  have Grw := (grep_gen (Y := D.P.A) rw' hrw.1 (lift (o.onB.act 4 ≫ o.onB.act w) (𝟙 D.P.A)).left).congr
    (fun _ _ h => prod_ros _ _ _ _ h) (fun _ _ _ _ _ => rfl)
  have Gga := (grep_gen (Y := D.P.A) gam hgam.1 (o.onB.act (1 + w)).left).congr (fun _ _ h => prod_gam _ h)
    (fun _ _ _ _ _ => rfl)
  have Ggw := (grep_gen (Y := D.P.A) gam hgam.1 (o.onB.act w).left).congr (fun _ _ h => prod_gam _ h)
    (fun _ _ _ _ _ => rfl)
  have Ggb := (grep_gen (Y := D.P.A) gam hgam.1 (Over.Hom.left (𝟙 D.P.A))).congr (fun _ _ h => prod_gam _ h)
    (fun _ _ _ _ _ => rfl)
  have Gt2 := grep_cub (D := D) (Y := D.P.A) (o.onB.act 4 * o.onB.act 4) (o.onB.act 4 ≫ o.onB.act (star w * w)) (𝟙 D.P.A)
  have Gt1 := grep_cub (D := D) (Y := D.P.A) (o.onB.act 4) (o.onB.act 4) (𝟙 D.P.A)
  have key := (((Gu.mul (Gra.pow 2)).mul Gga).mul (((((Gt2.pow 2).mul (Gt1.pow 2)).mul (Ggb.pow 2)).mul
    (Grw.pow 2)).mul Ggw).inv).triv hG (fun U _ h => by
      clear Gu Gra Grw Gga Ggw Ggb Gt2 Gt1
      have e1 : 𝟙 D.P.A = o.onB.act 1 := o.onB.map_one.symm
      have e0 : (1 : D.P.A ⟶ D.P.A) = o.onB.act 0 := (act_zero' o).symm
      have hsw : star w = 1 - w := eq_sub_of_add_eq' hw
      simp only [e1, e0, act_add', act_comp', act_pow', star_add, star_one, hsw]
      ring_nf
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one]
      abel) (fun y I hI => by
      clear Gu Gra Grw Gga Ggw Ggb Gt2 Gt1
      have C : IsCub (cubV D.cub (T := 𝟙_ _) y I) := isCub_cubV D.cub hI
      have o1 : ∀ t : O, (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left ≫ (o.onB.act t).left =
          (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left := fun t => by
        rw [← Over.comp_left, MonObj.one_comp]
      have l1 : ∀ t t' : O, (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left ≫
          (lift (o.onB.act t ≫ o.onB.act t') (𝟙 D.P.A)).left =
          (lift (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) 1).left := fun t t' => by
        rw [← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc, MonObj.one_comp, MonObj.one_comp]
      beta_reduce
      rw [o1, l1, l1, o1, o1, Over.id_left, Category.comp_id, normd_one hu hI, normd_one hgam hI]
      have r1 := hra.val_origin hI
      have r2 := hrw.val_origin hI
      unfold val₂ at r1 r2
      rw [r1, r2]
      simp only [MonObj.comp_mul, MonObj.one_comp, Category.comp_id, _root_.mul_one, C.face, one_pow, inv_one, normd_one hgam hI]) T b z J hJ
  have c4 : b ≫ o.onB.act 4 = b ^ 4 := by
    have := act_natCast' o 4
    rw [Nat.cast_ofNat] at this
    rw [this, comp_id_pow]
  beta_reduce at key
  simp only [← Over.comp_left, comp_lift, ← Category.assoc, c4, MonObj.comp_mul, Category.comp_id] at key
  exact mul_inv_eq_one.1 key

set_option maxHeartbeats 800000 in

theorem sign_rel : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (O : Type) [CommRing O] [StarRing O] [Module O D.X] (o : D.OAct O) (w : O), w + star w = 1 → ∀ u : GlobalTheory.PsiRescale.FourGen D.P.L (o.onB.act w), Normd u → ∀ gam : LB.Gen (LB.LinComb D.P.L (K := Fin 4) ![(𝟙 D.P.A ^ 5).left, (𝟙 D.P.A ^ 4).left, 𝟙 _, (1 : D.P.A ⟶ D.P.A).left] ![2, -3, -2, 3]), Normd gam → ∀ p q r : QkPt D F 4, q.y = w • p.y → r.y = (1 + w) • p.y → GtAct o w p.g q.g → GtAct o (1 + w) p.g r.g → ∀ (z : (TF (R := R) F).left) J, Good D.P.L z J → ∀ s s' s'' : ((TF (R := R) F).left.presheaf.stalk z)ˣ, s * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (p.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J) = val (p.g.s p.y) (𝟙 _) z J ^ 2 * val gam p.g.b.left z J → s' * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (q.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J) = val (q.g.s q.y) (𝟙 _) z J ^ 2 * val gam q.g.b.left z J → s'' * (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (r.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J) = val (r.g.s r.y) (𝟙 _) z J ^ 2 * val gam r.g.b.left z J → s'' = s ^ 2 * s' → @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.tau p.y (w • p.y)) (jFK (R := R) F) z J) * val u (cP D (TF (R := R) F) p.y).left z J = @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (p.y)) (jFK (R := R) F) z J) * rigV D (TF (R := R) F).hom z J := by
  intro R _ _ D F _ _ O _ _ _ o w hw u hu gam hgam p q r hq hr hgq hgr z J hJ s s' s'' hs hs' hs'' hss
  have hG : GlobalFnsSt := GlobalTheory.firstFiveLaws.1.globalFns
  have hb4 : cP D (TF (R := R) F) p.y = p.g.b ^ 4 := cPoint_y p
  obtain ⟨qb, qv⟩ := (GlobalTheory.TorusExt.gtAct_iff_val hG o w p.g q.g).1 hgq
  obtain ⟨rb, rv⟩ := (GlobalTheory.TorusExt.gtAct_iff_val hG o (1 + w) p.g r.g).1 hgr
  have eq1 := qv (w • p.y) z J hJ
  have eq2 := rv ((1 + w) • p.y) z J hJ
  have sm1 : star w • w • p.y = (star w * w) • p.y := smul_smul _ _ _
  have sm2 : star (1 + w) • (1 + w) • p.y = (p.y + p.y) + (star w * w) • p.y := by
    rw [smul_smul, show star (1 + w) * (1 + w) = 1 + 1 + star w * w by
      rw [star_add, star_one]; linear_combination hw, add_smul, add_smul, one_smul]
  have e3 : (1 + w) • p.y = p.y + w • p.y := by rw [add_smul, one_smul]
  rw [sm1, GlobalTheory.TorusExt.cPoint_smul o, hb4] at eq1
  rw [sm2, GlobalTheory.TorusExt.cPoint_smul o, hb4] at eq2
  have g1 := GlobalTheory.TorusExt.charVal_add p.g hJ p.y p.y
  have g2 := GlobalTheory.TorusExt.charVal_add p.g hJ (p.y + p.y) ((star w * w) • p.y)
  rw [cPoint_add, GlobalTheory.TorusExt.cPoint_smul o, hb4] at g2
  rw [hb4] at g1
  have cid := core_id hG o w u hu gam hgam (GlobalTheory.TorusExt.rosGen hG o (1 + w)) (GlobalTheory.TorusExt.rosGen_isRos hG o (1 + w))
    (GlobalTheory.TorusExt.rosGen hG o w) (GlobalTheory.TorusExt.rosGen_isRos hG o w) hw p.g.b z hJ
  have vτ : @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.tau p.y (w • p.y)) (jFK (R := R) F) z J) =
      @id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi ((1 + w) • p.y)) (jFK (R := R) F) z J) *
        (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi p.y) (jFK (R := R) F) z J))⁻¹ *
        (@id ((TF (R := R) F).left.presheaf.stalk z)ˣ (val (D.psi (w • p.y)) (jFK (R := R) F) z J))⁻¹ *
        (rigV D (TF (R := R) F).hom z J)⁻¹ := by
    rw [e3]
    exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) ((val_inv _ _).trans
        (congrArg (·⁻¹) ((val_pull hJ _ _ _).trans rfl))))
  have gq : val gam q.g.b.left z J = val gam (p.g.b ≫ o.onB.act w).left z J := by rw [qb]
  have gr : val gam r.g.b.left z J = val gam (p.g.b ≫ o.onB.act (1 + w)).left z J := by rw [rb]
  rw [hq, gq] at hs'
  rw [hr, gr] at hs''
  rw [vτ, hb4]
  simp only [id_eq] at hs hs' hs'' ⊢
  apply Additive.ofMul.injective
  have E := fun {a c : ((TF (R := R) F).left.presheaf.stalk z)ˣ} (e : a = c) => congrArg Additive.ofMul e
  have hs := E hs; have hs' := E hs'; have hs'' := E hs''; have hss := E hss
  have eq1 := E eq1; have eq2 := E eq2; have g1 := E g1; have g2 := E g2; have cid := E cid
  simp only [ofMul_mul, ofMul_inv, ofMul_pow] at hs hs' hs'' hss eq1 eq2 g1 g2 cid ⊢
  linear_combination (norm := module) hs'' - 2 • hs - hs' - hss + 2 • eq2 - 2 • eq1 + 2 • g2 + 2 • g1 + cid

end GlobalTheory.PsiSignRel
