import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationDegenerationDataUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordLambdaBilinearIntegralCombinations
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoPullbackOfCoprodJoinStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorValEqOneOfGenericSpecDomainStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

namespace GlobalTheory.PrimPull

theorem lamF {S : Scheme.{0}} {B T : Over S} [GrpObj B] [IsCommMonObj B] {X Y : Scheme.{0}} (x y : T ⟶ B)
    (f₁ : T.left ⟶ Y) (f₂ : Y ⟶ (G2 B).left) (hf : f₁ ≫ f₂ = (lift x y).left) (e : B.left ⟶ X)
    {U : Type} [CommGroup U] (h : (T.left ⟶ X) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h (f₁ ≫ f₂ ≫ (psum B (x2 B) I.down).left ≫ e) ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      h ((x * y).left ≫ e) * (h (x.left ≫ e))⁻¹ * (h (y.left ≫ e))⁻¹ * h ((1 : T ⟶ B).left ≫ e) := by
  refine Eq.trans (Finset.prod_congr rfl fun I _ => ?_) (GlobalTheory.PrimCocycle.prod_lam x y (fun q => h (q ≫ e)))
  rw [← Category.assoc f₁, hf]
  simp only [Category.assoc]

theorem lamFneg {S : Scheme.{0}} {B T : Over S} [GrpObj B] [IsCommMonObj B] {X : Scheme.{0}} (x y : T ⟶ B)
    (e : B.left ⟶ X) {U : Type} [CommGroup U] (h : (T.left ⟶ X) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h ((lift x y).left ≫ (psum B (x2 B) I.down).left ≫ e) ^ (-((-1 : ℤ) ^ (2 - I.down.card))) =
      (h ((x * y).left ≫ e) * (h (x.left ≫ e))⁻¹ * (h (y.left ≫ e))⁻¹ * h ((1 : T ⟶ B).left ≫ e))⁻¹ :=
  (GlobalTheory.MumBil.prodNeg (fun I : ULift.{0} (Finset (Fin 2)) => h ((lift x y).left ≫ (psum B (x2 B) I.down).left ≫ e))
    (fun I => (-1 : ℤ) ^ (2 - I.down.card))).trans
    (congrArg (·⁻¹) (lamF x y (lift x y).left (𝟙 _) (Category.comp_id _) e h |>.symm.trans (Finset.prod_congr rfl fun I _ => by rw [Category.id_comp])).symm)

theorem isPullDeg_of_primitive : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X] (o : D.toPre.OAct O) (o' : D'.toPre.OAct O) (w : O), TraceFormTwistIso D.toPre o w → TraceFormTwistIso D'.toPre o' w → ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (xe : D'.toPre.X ≃+ D.toPre.X), IsMonHom Φ.hom → ((∀ a, o'.onB.act a ≫ Φ.hom = Φ.hom ≫ o.onB.act a) ∧ (∀ (a : O) x, xe (a • x) = a • xe x) ∧ (∀ x, D'.toPre.c x ≫ Φ.hom = D.toPre.c (xe x))) → (∃ wΛ : (letI := D.toPre.P.isAb.comm; letI := D'.toPre.P.isAb.comm; LB.Iso (abelian₂ D'.toPre.P.A D'.toPre.P.L) ((abelian₂ D.toPre.P.A D.toPre.P.L).pull (lift (fst D'.toPre.P.A D'.toPre.P.A ≫ Φ.hom) (snd D'.toPre.P.A D'.toPre.P.A ≫ Φ.hom) : G2 D'.toPre.P.A ⟶ G2 D.toPre.P.A).left)), wΛ.IsGen ∧ ∀ a b z J J', Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → val (D'.toPre.tau a b) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal wΛ (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left z J J' * val (D.toPre.tau (xe a) (xe b)) (𝟙 _) z J) → ∃ hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre, hD.xe = xe ∧ hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) = Φ.hom.left := by
  intro R _ _ _ hR D D' O _ _ _ _ o o' w hw hw' Φ xe hΦ hlin hwΛ
  obtain ⟨hact, hxe, hc⟩ := hlin
  obtain ⟨wΛ, gΛ, vΛ⟩ := hwΛ
  obtain ⟨u, hu, hu0, hup⟩ := hw
  obtain ⟨u', hu', hu0', hup'⟩ := hw'
  have hM := D.toPre.P.isLB
  have hM' := D'.toPre.P.isLB
  have P₁ := isPart_inl D'.toPre.P.L D.toPre.P.L
  have P₂ := isPart_inr D'.toPre.P.L D.toPre.P.L
  have hN := join_isLB hM' hM
  obtain ⟨t₁, ht₁, vt₁⟩ := exists_gen_of_iso P₂ P₁ wΛ gΛ
  have g₁ := DVR.pullGen_isGen _ _ _ t₁ ht₁ (lift (𝟙 D'.toPre.P.A) (o'.onB.act w)).left
  have g₂ := P₁.gen_isGen hu'
  have g₃ := P₂.gen_isGen (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ u hu Φ.hom.left))
  have g₄ := P₂.gen_isGen (DVR.pullGen_isGen _ _ _ D.toPre.rig D.toPre.rig_gen (toUnit D'.toPre.P.A).left)
  have g₅ := P₁.gen_isGen (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ D'.toPre.rig D'.toPre.rig_gen (toUnit D'.toPre.P.A).left))
  have g := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ g₁ g₂) g₃) g₄) g₅
  have E1 : (lift (𝟙 D'.toPre.P.A) (o'.onB.act w)).left ≫ (lift (fst D'.toPre.P.A D'.toPre.P.A ≫ Φ.hom) (snd D'.toPre.P.A D'.toPre.P.A ≫ Φ.hom)).left = (lift Φ.hom (o'.onB.act w ≫ Φ.hom)).left := by
    rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, Category.id_comp]
  have q1 : (Φ.hom * (o'.onB.act w ≫ Φ.hom)).left = Φ.hom.left ≫ (padd D.toPre.P.A (𝟙 _) (o.onB.act w)).left := by
    rw [← Over.comp_left]
    refine congrArg Over.Hom.left ?_
    show _ = Φ.hom ≫ (𝟙 _ * o.onB.act w)
    rw [MonObj.comp_mul, Category.comp_id, hact]
  have q2 : (o'.onB.act w ≫ Φ.hom).left = Φ.hom.left ≫ (o.onB.act w).left := by
    rw [← Over.comp_left, hact]
  have q3 : (1 : D'.toPre.P.A ⟶ D.toPre.P.A).left = (toUnit D'.toPre.P.A).left ≫ eSec D.toPre.P.A := rfl
  have q4 : Φ.hom.left ≫ (toUnit D.toPre.P.A ≫ η).left = (toUnit D'.toPre.P.A).left ≫ eSec D.toPre.P.A := by
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]; rfl
  have q6 : (𝟙 D'.toPre.P.A * o'.onB.act w).left = (padd D'.toPre.P.A (𝟙 _) (o'.onB.act w)).left := rfl
  have q8 : (1 : D'.toPre.P.A ⟶ D'.toPre.P.A).left = (toUnit D'.toPre.P.A).left ≫ eSec D'.toPre.P.A := rfl
  have q9 : (toUnit D'.toPre.P.A ≫ η).left = (toUnit D'.toPre.P.A).left ≫ eSec D'.toPre.P.A := rfl
  obtain ⟨t, ht, vt⟩ := exists_gen hN (φ' := Sum.elim (fun _ : PUnit => Φ.hom.left ≫ coprod.inr) (fun _ : PUnit => coprod.inl)) (ε' := Sum.elim (fun _ => (1:ℤ)) (fun _ => (-1:ℤ))) (by
      intro U _ h
      clear vΛ vt₁ hu0 hup hu0' hup' hxe hc g g₁ g₂ g₃ g₄ g₅ gΛ ht₁ hM hM' hN hu hu'
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
      rw [lamF Φ.hom (o'.onB.act w ≫ Φ.hom) _ _ E1, lamFneg, q1, q2, q3, q4, Category.comp_id, q8, q9, q6]
      simp only [Category.id_comp, Over.id_left]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, zpow_one]
      clear q1 q2 q3 q4 q6 q8 q9 E1 t₁ u u' P₁ P₂ wΛ xe hΦ hact
      abel) _ g
  obtain ⟨w₀, hw₀, vw₀⟩ := GlobalTheory.T.exists_lineBundleIso_pullback_of_coprodJoin D.toPre.P.L D'.toPre.P.L hM hM' inferInstance inferInstance Φ.hom.left t ht
  have vw : ∀ (Z : Scheme.{0}) (f : Z ⟶ D'.toPre.P.A.left) (z : Z)
      (J : (Z ⟶ D'.toPre.P.A.left ⨿ D.toPre.P.A.left) → (join D'.toPre.P.L D.toPre.P.L).ι),
      Good (join D'.toPre.P.L D.toPre.P.L) z J →
      gw w₀ f z (rr J (f ≫ Φ.hom.left)) (rl J f) =
        GlobalTheory.PolDeg.lamVal wΛ (f ≫ (lift (𝟙 D'.toPre.P.A) (o'.onB.act w)).left) z (rr J) (rl J) * val u' f z (rl J) *
          (val u (f ≫ Φ.hom.left) z (rr J))⁻¹ * val D.toPre.rig (f ≫ (toUnit D'.toPre.P.A).left) z (rr J) *
          (val D'.toPre.rig (f ≫ (toUnit D'.toPre.P.A).left) z (rl J))⁻¹ := by
    intro Z f z J hJ
    rw [vw₀ Z f z J hJ, vt Z f z J hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_pull hJ, vt₁ _ _ z J hJ,
      P₁.val_gen _ _ _ hJ, P₂.val_gen _ _ _ hJ, P₂.val_gen _ _ _ hJ, P₁.val_gen _ _ _ hJ, val_inv, val_inv,
      val_pull (P₂.good hJ), val_pull (P₂.good hJ), val_pull (P₁.good hJ)]
    rfl
  haveI := hΦ
  have c0' : D'.toPre.c 0 = 1 := by
    have h := D'.toPre.c_add 0 0
    rw [add_zero] at h
    exact mul_eq_left.1 (h.symm : D'.toPre.c 0 * D'.toPre.c 0 = D'.toPre.c 0)
  have hone : ∀ {T : Over (Spec (CommRingCat.of R))} (s : T ⟶ 𝟙_ (Over (Spec (CommRingCat.of R)))),
      s ≫ η[D'.toPre.P.A] ≫ lift (𝟙 D'.toPre.P.A) (o'.onB.act w) = lift (1 : T ⟶ D'.toPre.P.A) 1 := by
    intro T s
    have e1 : (η[D'.toPre.P.A] : 𝟙_ _ ⟶ D'.toPre.P.A) ≫ o'.onB.act w = η := by
      haveI := o'.onB.hom w; exact IsMonHom.one_hom _
    rw [comp_lift, comp_lift, Category.comp_id, e1, Hom.one_def, toUnit_unique s (toUnit T)]
  have hjK : (toUnit (TK R)).left = jK R := by simpa using Over.w (toUnit (TK R))
  have Z0 : ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of R)) (z : Z)
      (J : (Z ⟶ D'.toPre.P.A.left ⨿ D.toPre.P.A.left) → (join D'.toPre.P.L D.toPre.P.L).ι),
      Good (join D'.toPre.P.L D.toPre.P.L) z J →
      GlobalTheory.PolDeg.lamVal wΛ (r ≫ eSec D'.toPre.P.A ≫ (lift (𝟙 D'.toPre.P.A) (o'.onB.act w)).left) z (rr J) (rl J) = 1 := by
    have E0 : eSec D'.toPre.P.A ≫ (lift (𝟙 D'.toPre.P.A) (o'.onB.act w)).left =
        (lift (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.toPre.P.A) 1).left := by
      rw [eSec, ← Over.comp_left, ← hone (𝟙 _), Category.id_comp]
    have E0' : (lift (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.toPre.P.A) 1).left ≫
        (lift (fst D'.toPre.P.A D'.toPre.P.A ≫ Φ.hom) (snd D'.toPre.P.A D'.toPre.P.A ≫ Φ.hom)).left =
        (lift (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.toPre.P.A) 1).left := by
      rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, MonObj.one_comp]
    intro Z r z J hJ
    have key := GlobalTheory.T.generator_val_eq_one_of_generic_spec_domain R (join D'.toPre.P.L D.toPre.P.L) hN _ _ (by
        intro U _ h
        simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_empty, E0]
        rw [lamF 1 1 _ _ E0', lamFneg, _root_.mul_one, _root_.mul_one]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_one]
        abel)
      (LB.pullGen _ _ _ t₁ (eSec D'.toPre.P.A ≫ (lift (𝟙 D'.toPre.P.A) (o'.onB.act w)).left))
      (DVR.pullGen_isGen _ _ _ _ ht₁ _) (by
        intro y J hJ
        rw [val_pull hJ, vt₁ _ _ y J hJ]
        have E1g : jK R ≫ eSec D'.toPre.P.A ≫ (lift (𝟙 D'.toPre.P.A) (o'.onB.act w)).left =
            (lift (toUnit (TK R) ≫ D'.toPre.c 0) (toUnit (TK R) ≫ D'.toPre.c 0)).left := by
          rw [c0', MonObj.comp_one, ← hone (toUnit (TK R)), Over.comp_left, Over.comp_left, hjK]; rfl
        have v := vΛ 0 0 y (rr J) (rl J) (P₂.good hJ) (P₁.good hJ)
        rw [GlobalTheory.MumBil.tau_zero D'.tau_bimult (P₁.good hJ), map_zero, GlobalTheory.MumBil.tau_zero D.tau_bimult (P₂.good hJ),
          _root_.mul_one] at v
        rw [E1g]; exact v.symm) Z r z J hJ
    rw [val_pull hJ, vt₁ _ _ z J hJ] at key
    exact key
  have hE : eSec D'.toPre.P.A ≫ Φ.hom.left = eSec D.toPre.P.A := by
    rw [eSec, eSec, ← Over.comp_left, IsMonHom.one_hom]
  have hT : eSec D'.toPre.P.A ≫ (toUnit D'.toPre.P.A).left = 𝟙 _ := by
    rw [eSec, ← Over.comp_left, toUnit_unique (η ≫ toUnit D'.toPre.P.A) (𝟙 _)]; rfl
  have exJ : ∀ (Z : Scheme.{0}) (z : Z) (f : Z ⟶ D'.toPre.P.A.left) (p : D.toPre.P.L.ι) (q : D'.toPre.P.L.ι),
      Φ.hom.left (f z) ∈ D.toPre.P.L.U p → f z ∈ D'.toPre.P.L.U q →
      ∃ J, Good (join D'.toPre.P.L D.toPre.P.L) z J ∧ rr J (f ≫ Φ.hom.left) = p ∧ rl J f = q := by
    intro Z z f p q hp hq
    obtain ⟨J, hJ, e⟩ := exists_good (join D'.toPre.P.L D.toPre.P.L) hN z (K := Bool)
      (fun b => if b then (f ≫ Φ.hom.left) ≫ coprod.inr else f ≫ coprod.inl) (fun _ => (q, p)) (fun _ _ _ => rfl) (by
        rintro (_ | _)
        · exact (P₁.mem (q, p) (f z)).2 hq
        · exact (P₂.mem (q, p) _).2 hp)
    exact ⟨J, hJ, congrArg Prod.snd (e true), congrArg Prod.fst (e false)⟩
  have hr : PMaps w₀ (K := PUnit) (fun _ => eSec D'.toPre.P.A) (fun _ => eSec D.toPre.P.A) (fun _ => 1)
      D'.toPre.rig D.toPre.rig (𝟙 _) := by
    intro Z r z p q hp hq
    obtain ⟨J, hJ, ep, eq⟩ := exJ Z z (r ≫ eSec D'.toPre.P.A) (p PUnit.unit) (q PUnit.unit) (hp PUnit.unit) (hq PUnit.unit)
    have v := vw Z (r ≫ eSec D'.toPre.P.A) z J hJ
    rw [ep, eq] at v
    have a1 : GlobalTheory.PolDeg.lamVal wΛ ((r ≫ eSec D'.toPre.P.A) ≫ (lift (𝟙 D'.toPre.P.A) (o'.onB.act w)).left) z
        (rr J) (rl J) = 1 := by
      rw [Category.assoc]; exact Z0 Z r z J hJ
    have a2 : val u' (r ≫ eSec D'.toPre.P.A) z (rl J) = 1 := by
      rw [← val_pull (P₁.good hJ), val_corr (P₁.good hJ) hu0' r, val_one]
    have a3 : val u ((r ≫ eSec D'.toPre.P.A) ≫ Φ.hom.left) z (rr J) = 1 := by
      rw [Category.assoc, hE, ← val_pull (P₂.good hJ), val_corr (P₂.good hJ) hu0 r, val_one]
    have a4 : (r ≫ eSec D'.toPre.P.A) ≫ (toUnit D'.toPre.P.A).left = r := by
      rw [Category.assoc, hT, Category.comp_id]
    have a5 : gm r z (LB.wchart D.toPre.P.L (fun _ => eSec D.toPre.P.A) p) (D.toPre.rig.s p) =
        val D.toPre.rig r z (rr J) := by
      refine (val_of _ _ _ _ p fun k => ?_).symm
      rw [← ep, ← hE, ← Category.assoc]
    have a6 : gm r z (LB.wchart D'.toPre.P.L (fun _ => eSec D'.toPre.P.A) q) (D'.toPre.rig.s q) =
        val D'.toPre.rig r z (rl J) := by
      refine (val_of _ _ _ _ q fun k => ?_).symm
      rw [← eq]
    simp only [Fintype.prod_unique, zpow_one, Category.comp_id]
    rw [v, a1, a2, a3, a4, a5, a6]
    group
  have hx : ∀ x, D'.toPre.xK x ≫ Φ.hom.left = D.toPre.xK (xe x) := fun x => by
    show (toUnit (TK R) ≫ D'.toPre.c x).left ≫ Φ.hom.left = (toUnit (TK R) ≫ D.toPre.c (xe x)).left
    rw [← Over.comp_left, Category.assoc, hc]
  have vΛr : ∀ (a b : D'.toPre.X) (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z)
      (J : (Z ⟶ D'.toPre.P.A.left ⨿ D.toPre.P.A.left) → (join D'.toPre.P.L D.toPre.P.L).ι),
      Good (join D'.toPre.P.L D.toPre.P.L) z J →
      val (D'.toPre.tau a b) r z (rl J) = GlobalTheory.PolDeg.lamVal wΛ
        (r ≫ (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left) z (rr J) (rl J) *
        val (D.toPre.tau (xe a) (xe b)) r z (rr J) := by
    intro a b Z r z J hJ
    have C := corr_of_val hN (t := P₁.gen (D'.toPre.tau a b))
      (t' := LB.mulGen _ _ _ _ _ (LB.pullGen _ _ _ t₁
        (lift (toUnit (TK R) ≫ D'.toPre.c a) (toUnit (TK R) ≫ D'.toPre.c b)).left) (P₂.gen (D.toPre.tau (xe a) (xe b))))
      (fun y J hJ => by
        rw [P₁.val_gen _ _ _ hJ, val_mul hJ, val_pull hJ, vt₁ _ _ _ _ hJ, P₂.val_gen _ _ _ hJ, Category.id_comp]
        exact vΛ a b y (rr J) (rl J) (P₂.good hJ) (P₁.good hJ))
    have := val_corr hJ C r
    rw [P₁.val_gen _ _ _ hJ, val_mul hJ, val_pull hJ, vt₁ _ _ _ _ hJ, P₂.val_gen _ _ _ hJ] at this
    exact this
  have hψ : ∀ x, PMaps w₀ (K := PUnit) (fun _ => D'.toPre.xK x) (fun _ => D.toPre.xK (xe x)) (fun _ => -1)
      (D'.toPre.psi x) (D.toPre.psi (xe x)) (𝟙 _) := by
    intro x Z r z p q hp hq
    obtain ⟨J, hJ, ep, eq⟩ := exJ Z z (r ≫ D'.toPre.xK x) (p PUnit.unit) (q PUnit.unit) (hp PUnit.unit) (hq PUnit.unit)
    have v := vw Z (r ≫ D'.toPre.xK x) z J hJ
    rw [ep, eq] at v
    have m1 : (r ≫ D'.toPre.xK x) ≫ (lift (𝟙 D'.toPre.P.A) (o'.onB.act w)).left =
        r ≫ (lift (toUnit (TK R) ≫ D'.toPre.c x) (toUnit (TK R) ≫ D'.toPre.c (w • x))).left := by
      rw [Category.assoc, o'.c_lin]
      congr 1
      show (toUnit (TK R) ≫ D'.toPre.c x).left ≫ _ = _
      rw [← Over.comp_left, comp_lift, Category.comp_id, Category.assoc]
    have m2 : (r ≫ D'.toPre.xK x) ≫ Φ.hom.left = r ≫ D.toPre.xK (xe x) := by rw [Category.assoc, hx]
    have m3 : (r ≫ D'.toPre.xK x) ≫ (toUnit D'.toPre.P.A).left = r ≫ (toUnit (TK R)).left := by
      rw [Category.assoc]; congr 1
      show (toUnit (TK R) ≫ D'.toPre.c x).left ≫ _ = _
      rw [← Over.comp_left, Category.assoc, toUnit_unique (D'.toPre.c x ≫ toUnit _) (𝟙 _), Category.comp_id]
    rw [m1, m2, m3] at v
    have A := val_corr (P₁.good hJ) (hup' x) r
    rw [val_mul (P₁.good hJ), val_mul (P₁.good hJ), val_pull (P₁.good hJ), DegPre.rigK, val_pull (P₁.good hJ)] at A
    have B := val_corr (P₂.good hJ) (hup (xe x)) r
    rw [val_mul (P₂.good hJ), val_mul (P₂.good hJ), val_pull (P₂.good hJ), DegPre.rigK, val_pull (P₂.good hJ)] at B
    have Cc := vΛr x (w • x) Z r z J hJ
    rw [hxe] at Cc
    have a5 : gm (r ≫ 𝟙 _) z (LB.wchart D.toPre.P.L (fun _ => D.toPre.xK (xe x)) p) ((D.toPre.psi (xe x)).s p) =
        val (D.toPre.psi (xe x)) r z (rr J) := by
      rw [Category.comp_id]
      refine (val_of _ _ _ _ p fun k => ?_).symm
      rw [← ep, ← hx, ← Category.assoc]
    have a6 : gm r z (LB.wchart D'.toPre.P.L (fun _ => D'.toPre.xK x) q) ((D'.toPre.psi x).s q) =
        val (D'.toPre.psi x) r z (rl J) := by
      refine (val_of _ _ _ _ q fun k => ?_).symm
      rw [← eq]
    simp only [Fintype.prod_unique]
    rw [a5, a6, v, eq_mul_inv_of_mul_eq B.symm, eq_mul_inv_of_mul_eq A.symm, Cc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    abel
  have hs := specOf_id R
  have gp : IsGrpPullback D'.toPre.P.A D.toPre.P.A (specOf (RingHom.id R)) Φ.hom.left :=
    (isGrpPullback_of_iso Φ).congr hs.symm rfl
  obtain ⟨e, me, hF⟩ := grpPullback_iso gp (isGrpPullback_pullback D.toPre.P.A (specOf (RingHom.id R)))
  obtain ⟨w', g', r', ψ'⟩ := GlobalTheory.UnifUniq.exists_transport hF
    (fun (F : D'.toPre.P.A.left ⟶ D.toPre.P.A.left) (w : LB.Iso D'.toPre.P.L (D.toPre.P.L.pull F)) => w.IsGen ∧
      PMaps w (K := PUnit) (fun _ => eSec D'.toPre.P.A) (fun _ => eSec D.toPre.P.A) (fun _ => 1)
        D'.toPre.rig D.toPre.rig (𝟙 _) ∧
      ∀ x, PMaps w (K := PUnit) (fun _ => D'.toPre.xK x) (fun _ => D.toPre.xK (xe x)) (fun _ => -1)
        (D'.toPre.psi x) (D.toPre.psi (xe x)) (𝟙 _)) w₀ ⟨hw₀, hr, hψ⟩
  obtain ⟨W, hW, ⟨ψW⟩⟩ := GlobalTheory.PsiSpread.exists_psiOn D.toPre D.tau_bimult
  have hc₁' : ∀ x, (D'.toPre.c x).left ≫ Φ.hom.left = (D.toPre.c (xe x)).left := fun x => by
    rw [← Over.comp_left, hc]
  obtain ⟨hD, e₁, -, e₃⟩ := GlobalTheory.UnifUniq.exists_isPullDeg_id D.toPre D'.toPre W hW ψW e me w' g'
    ((congrArg (_ ≫ ·) hF).trans hE) r' xe (fun x => (congrArg (_ ≫ ·) hF).trans (hc₁' x)) ψ'
  exact ⟨hD, e₃, by rw [e₁]; exact hF⟩

end GlobalTheory.PrimPull
