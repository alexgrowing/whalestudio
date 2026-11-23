import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8LB
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.ToATotal
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SharpGen
open GlobalTheory.PowE8

theorem exists_gen {S T : Scheme.{0}} (f : T ⟶ S) (G₀ : Over S) [GrpObj G₀] [IsCommMonObj G₀] {B C : Over T}
    [GrpObj B] [GrpObj C] (pr : Fin 8 → (B ⟶ C)) (hpr : ∀ a, IsMonHom (pr a))
    (huniq : ∀ (T' : Over T) (y : Fin 8 → (T' ⟶ C)), ∃! x : T' ⟶ B, ∀ a, x ≫ pr a = y a)
    (u : (Over.pullback f).obj G₀ ≅ C) [IsMonHom u.hom] :
    ∃ gen : (Over.pullback f).obj (powObj G₀ 8) ≅ B, IsMonHom gen.hom ∧
      ∀ a, gen.hom ≫ pr a = (Over.pullback f).map (powPr G₀ a) ≫ u.hom := by
  let hl := isLimitOfPreserves (Over.pullback f) (powIsLimit G₀ 8)
  let ρ : Fin 8 → ((Over.pullback f).obj (powObj G₀ 8) ⟶ (Over.pullback f).obj G₀) :=
    fun a => (Over.pullback f).map (powPr G₀ a)
  choose x hx hxu using fun (T' : Over T) (y : Fin 8 → (T' ⟶ C)) => huniq T' y
  let inv : B ⟶ (Over.pullback f).obj (powObj G₀ 8) :=
    hl.lift ⟨B, Discrete.natTrans fun a => pr a.as ≫ u.inv⟩
  have hinv : ∀ a, inv ≫ ρ a = pr a ≫ u.inv := fun a => hl.fac ⟨B, Discrete.natTrans fun a => pr a.as ≫ u.inv⟩ ⟨a⟩
  let hom := x _ (fun a => ρ a ≫ u.hom)
  have hhom : ∀ a, hom ≫ pr a = ρ a ≫ u.hom := hx _ _
  refine ⟨⟨hom, inv, ?_, ?_⟩, ?_, hhom⟩
  · refine hl.hom_ext fun ⟨a⟩ => ?_
    show (hom ≫ inv) ≫ ρ a = 𝟙 _ ≫ ρ a
    rw [Category.assoc, hinv, ← Category.assoc, hhom, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Category.id_comp]
  · have h1 := hxu B (fun a => pr a) (inv ≫ hom) (fun a => by
      rw [Category.assoc, hhom, ← Category.assoc, hinv, Category.assoc, Iso.inv_hom_id, Category.comp_id])
    have h2 := hxu B (fun a => pr a) (𝟙 B) (fun a => Category.id_comp _)
    exact h1.trans h2.symm
  · have hm : ∀ a, IsMonHom (hom ≫ pr a) := fun a => by rw [hhom]; infer_instance
    constructor
    · have h1 := hxu _ (fun a => η[C]) (η ≫ hom) (fun a => by
        haveI := hm a; rw [Category.assoc]; exact IsMonHom.one_hom (hom ≫ pr a))
      have h2 := hxu _ (fun a => η[C]) η (fun a => by haveI := hpr a; exact IsMonHom.one_hom (pr a))
      exact h1.trans h2.symm
    · have h1 := hxu _ (fun a => ((hom ≫ pr a) ⊗ₘ (hom ≫ pr a)) ≫ μ[C]) (μ ≫ hom) (fun a => by
        haveI := hm a; rw [Category.assoc]; exact IsMonHom.mul_hom (hom ≫ pr a))
      have h2 := hxu _ (fun a => ((hom ≫ pr a) ⊗ₘ (hom ≫ pr a)) ≫ μ[C]) ((hom ⊗ₘ hom) ≫ μ) (fun a => by
        haveI := hpr a; rw [Category.assoc, IsMonHom.mul_hom (pr a), ← Category.assoc, tensorHom_comp_tensorHom])
      exact h1.trans h2.symm

theorem lift_lamφ {S : Scheme.{0}} {B T : Over S} [GrpObj B] [IsCommMonObj B] (x y : T ⟶ B)
    (I : ULift.{0} (Finset (Fin 2))) :
    (lift x y).left ≫ GlobalTheory.PrimCocycle.lamφ B I = (psum B ![x, y] I.down).left :=
  congrArg (fun q => q.left) ((psum_hom (preHom (lift x y)) (x2 B) I.down).trans
    (congrArg (fun q => psum B q I.down) (funext fun i => by fin_cases i <;> simp [preHom, x2])))

theorem psum_comp_hom {S : Scheme.{0}} {B C T : Over S} [GrpObj B] [IsCommMonObj B] [GrpObj C] [IsCommMonObj C]
    (u : B ⟶ C) [IsMonHom u] (x y : T ⟶ B) (I : Finset (Fin 2)) :
    psum C ![x ≫ u, y ≫ u] I = psum B ![x, y] I ≫ u :=
  ((congrArg (fun q => psum C q I) (funext fun i => by fin_cases i <;> rfl)).trans
    (psum_hom (MonoidHom.mk' (fun z : T ⟶ B => z ≫ u) fun a b => MonObj.mul_comp a b u) ![x, y] I).symm)

theorem zpow_lam {U : Type} [CommGroup U] (a b c d : U) (w : ℤ) :
    (a * b⁻¹ * c⁻¹ * d) ^ w = a ^ (-(w * negε 0)) * b ^ (-(w * negε 1)) * c ^ (-(w * negε 2)) * d ^ (-(w * negε 3)) := by
  simp only [negε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, mul_zpow, inv_zpow', mul_neg, mul_one, neg_neg]
  norm_num

theorem gen_eighthPower : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (D₀ : DegData V₁ (maximalIdeal V₁)) (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ P : PolAV (Sp (FractionRing V₁)), SharpOver F W P y → ∃ gen : (Over.pullback (jK V₁)).obj (powObj G₀ 8) ≅ P.A, IsMonHom gen.hom ∧ LBIso (P.L.pull gen.hom.left) ((GlobalTheory.PowE8.e8LB G₀ U₀.LG.L W).pull (pullback.fst (powObj G₀ 8).hom (jK V₁))) := by
  intro g n o _ ζ F W V₁ _ _ _ D₀ G₀ _ _ A₀ U₀ y α α₂ hcart hsq hlb P hP
  obtain ⟨c, ⟨φ, φ₂, hφ, hφsq, hφlb, -⟩, pr, prh, prl, hPL⟩ := hP
  obtain ⟨e, he, heα⟩ := grpPullback_iso hcart hφ
  haveI := he
  haveI := U₀.gen_hom
  haveI : IsMonHom (U₀.gen ≪≫ e).hom := by rw [Iso.trans_hom]; infer_instance
  obtain ⟨gen, hgen, hcoord⟩ := exists_gen (jK V₁) G₀ pr prh prl (U₀.gen ≪≫ e)
  refine ⟨gen, hgen, ?_⟩
  have hA0 := A₀.isLB
  have hc := c.isLB
  have hLG := U₀.LG.isLB
  have hPl := P.isLB
  have hU := F.univ.isLB
  let ρ : Fin 8 → ((Over.pullback (jK V₁)).obj (powObj G₀ 8) ⟶ (Over.pullback (jK V₁)).obj G₀) :=
    fun a => (Over.pullback (jK V₁)).map (powPr G₀ a)
  let e₂ : (G2 A₀.A).left ⟶ (G2 c.A).left := (lift (fst _ _ ≫ e.hom) (snd _ _ ≫ e.hom)).left
  let mAB : Fin 8 × Fin 8 → (((Over.pullback (jK V₁)).obj (powObj G₀ 8)).left ⟶ (G2 A₀.A).left) :=
    fun ab => (lift (ρ ab.1 ≫ U₀.gen.hom) (ρ ab.2 ≫ U₀.gen.hom)).left
  have hm : ∀ ab : Fin 8 × Fin 8, mAB ab ≫ e₂ = gen.hom.left ≫ (lift (pr ab.1) (pr ab.2)).left := fun ab => by
    simp only [mAB, e₂, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, hcoord, Iso.trans_hom,
      Category.assoc]
    rfl
  have he₂ : e₂ ≫ φ₂ = α₂ := by
    apply pullback.hom_ext
    · have h1 : (fst F.univ.A F.univ.A).left = pullback.fst _ _ := rfl
      rw [← h1, Category.assoc, hφsq.1, hsq.1, ← heα]
      simp only [e₂, ← Category.assoc, ← Over.comp_left, lift_fst]
    · have h1 : (snd F.univ.A F.univ.A).left = pullback.snd _ _ := rfl
      rw [← h1, Category.assoc, hφsq.2, hsq.2, ← heα]
      simp only [e₂, ← Category.assoc, ← Over.comp_left, lift_snd]
  have Q1 : LBIso (c.P.pull e₂) (abelian₂ A₀.A A₀.L) := by
    refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
      (GlobalTheory.PowPrimitive.lbIso_linComb hφlb (fun _ : PUnit => e₂) (fun _ => 1)) ?_
    refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
      (GlobalTheory.PrimNorm.lbIso_nested hU (fun _ : PUnit => φ₂) (fun _ => 1) (fun _ : PUnit => e₂) (fun _ => 1)
        (fun _ : PUnit => α₂) (fun _ => 1) (by simp [he₂])) ?_
    exact hlb.symm
  let q := pullback.fst (powObj G₀ 8).hom (jK V₁)
  let q0 := pullback.fst G₀.hom (jK V₁)
  let n : (Fin 8 × Fin 8) × ULift.{0} (Finset (Fin 2)) →
      (((Over.pullback (jK V₁)).obj (powObj G₀ 8)).left ⟶ ((Over.pullback (jK V₁)).obj G₀).left) :=
    fun p => (psum _ ![ρ p.1.1, ρ p.1.2] p.2.down).left
  let κ : (Fin 8 × Fin 8) × ULift.{0} (Finset (Fin 2)) → ℤ := fun p => GlobalTheory.PrimCocycle.lamε p.2 * W p.1.1 p.1.2
  have hn : ∀ ab I, mAB ab ≫ GlobalTheory.PrimCocycle.lamφ A₀.A I = n (ab, I) ≫ U₀.gen.hom.left := fun ab I => by
    rw [lift_lamφ, psum_comp_hom]; rfl
  let Uq : Over.mk (((Over.pullback (jK V₁)).obj (powObj G₀ 8)).hom ≫ jK V₁) ⟶ powObj G₀ 8 :=
    Over.homMk q pullback.condition
  have hq : ∀ ab I, n (ab, I) ≫ q0 = q ≫ (lift (powPr G₀ ab.1) (powPr G₀ ab.2)).left ≫ GlobalTheory.PrimCocycle.lamφ G₀ I :=
    fun ab I => by
      rw [lift_lamφ]
      refine psum_push (isGrpPullback_pullback G₀ (jK V₁)) _ _ Uq (fun i => ?_) I.down
      apply Over.OverMorphism.ext
      fin_cases i
      · exact pullback.lift_fst _ _ _
      · exact pullback.lift_fst _ _ _
  refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
    (GlobalTheory.PowPrimitive.lbIso_linComb hPL (fun _ : PUnit => gen.hom.left) (fun _ => 1)) ?_
  refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
    (GlobalTheory.PrimNorm.lbIso_nested hc _ _ (fun _ : PUnit => gen.hom.left) (fun _ => 1) (fun ab => mAB ab ≫ e₂)
      (fun ab => W ab.1 ab.2) (by simp [hm])) ?_
  refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
    (GlobalTheory.PrimNorm.lbIso_nested hc (fun _ : PUnit => e₂) (fun _ => 1) mAB (fun ab => W ab.1 ab.2)
      (fun ab => mAB ab ≫ e₂) (fun ab => W ab.1 ab.2) (by simp)).symm ?_
  refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
    (GlobalTheory.PowPrimitive.lbIso_linComb Q1 mAB (fun ab => W ab.1 ab.2)) ?_
  refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
    (GlobalTheory.PrimNorm.lbIso_nested hA0 (GlobalTheory.PrimCocycle.lamφ A₀.A) GlobalTheory.PrimCocycle.lamε mAB (fun ab => W ab.1 ab.2)
      (fun p => n p ≫ U₀.gen.hom.left) κ ?_) ?_
  · refine Eq.trans ?_ (Fintype.prod_prod_type _).symm
    refine Fintype.prod_congr _ _ fun ab => ?_
    rw [← Finset.prod_zpow]
    refine Fintype.prod_congr _ _ fun I => ?_
    rw [← zpow_mul, hn]
  refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
    (GlobalTheory.PrimNorm.lbIso_nested hA0 (fun _ : PUnit => U₀.gen.hom.left) (fun _ => 1) n κ
      (fun p => n p ≫ U₀.gen.hom.left) κ (by simp)).symm ?_
  obtain ⟨w, hw⟩ := U₀.ext
  refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (GlobalTheory.PowPrimitive.lbIso_linComb ⟨w, hw⟩ n κ) ?_
  refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
    (GlobalTheory.PrimNorm.lbIso_nested hLG (fun _ : PUnit => q0) (fun _ => 1) n κ (fun p => n p ≫ q0) κ (by simp)) ?_
  refine LBIso.trans (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _) (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by first | assumption | exact DVR.linComb_isLB _ (by assumption) _ _) _ _) _ _)
    ((GlobalTheory.PrimNorm.lbIso_iff hLG (fun p => n p ≫ q0) κ
      (fun k : (Fin 8 × Fin 8) × Fin 4 => q ≫ lamPts (powPr G₀ k.1.1) (powPr G₀ k.1.2) k.2)
      (fun k => -(W k.1.1 k.1.2 * negε k.2))).2 ?_) ?_
  · refine ((Fintype.prod_prod_type _).trans ?_).trans (Fintype.prod_prod_type _).symm
    refine Fintype.prod_congr _ _ fun ab => ?_
    have e1 : ∏ I, GlobalTheory.PrimNorm.cls U₀.LG.L (n (ab, I) ≫ q0) ^ κ (ab, I) =
        (∏ I, (fun m => GlobalTheory.PrimNorm.cls U₀.LG.L (q ≫ m))
          ((lift (powPr G₀ ab.1) (powPr G₀ ab.2)).left ≫ GlobalTheory.PrimCocycle.lamφ G₀ I) ^ GlobalTheory.PrimCocycle.lamε I) ^
          W ab.1 ab.2 := by
      rw [← Finset.prod_zpow]
      refine Fintype.prod_congr _ _ fun I => ?_
      rw [← zpow_mul, hq]
    rw [e1]
    refine (congrArg (· ^ W ab.1 ab.2) (GlobalTheory.PrimCocycle.prod_lam (powPr G₀ ab.1) (powPr G₀ ab.2)
      (fun m => GlobalTheory.PrimNorm.cls U₀.LG.L (q ≫ m)))).trans ?_
    rw [Fin.prod_univ_four]
    exact zpow_lam _ _ _ _ _
  exact (GlobalTheory.PrimNorm.lbIso_nested hLG
    (fun k : (Fin 8 × Fin 8) × Fin 4 => lamPts (powPr G₀ k.1.1) (powPr G₀ k.1.2) k.2)
    (fun k => -(W k.1.1 k.1.2 * negε k.2)) (fun _ : PUnit => q) (fun _ => 1) _ _ (by simp)).symm

end GlobalTheory.SharpGen
