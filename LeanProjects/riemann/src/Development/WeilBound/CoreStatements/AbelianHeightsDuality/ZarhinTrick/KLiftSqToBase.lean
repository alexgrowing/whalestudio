import Mathlib
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.IsLBZb
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibLam
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.EightfoldProjection

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]

section Points

variable {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S)

def kLiftPt (G : Over S) {Y : Over (Sp Ω)} (v : Over.mk (Y.hom ≫ s) ⟶ G) : Y ⟶ (Over.pullback s).obj G :=
  Over.homMk (pullback.lift v.left Y.hom (Over.w v)) (pullback.lift_snd _ _ _)

theorem kToBase_liftPt (G : Over S) {Y : Over (Sp Ω)} (v : Over.mk (Y.hom ≫ s) ⟶ G) :
    toBase G s (kLiftPt s G v) = v :=
  Over.OverMorphism.ext (pullback.lift_fst _ _ _)

theorem kToBase_inj (G : Over S) {Y : Over (Sp Ω)} {a b : Y ⟶ (Over.pullback s).obj G}
    (h : toBase G s a = toBase G s b) : a = b := by
  ext1
  apply pullback.hom_ext
  · simpa [toBase] using congrArg Over.Hom.left h
  · exact (Over.w a).trans (Over.w b).symm

theorem kToBase_comp (G : Over S) {Y Y' : Over (Sp Ω)} (h : Y' ⟶ Y) (a : Y ⟶ (Over.pullback s).obj G) :
    toBase G s (h ≫ a) = (Over.homMk h.left (by simp only [Over.mk_hom]; rw [← Category.assoc, Over.w h]) :
      Over.mk (Y'.hom ≫ s) ⟶ Over.mk (Y.hom ≫ s)) ≫ toBase G s a :=
  Over.OverMorphism.ext (Category.assoc _ _ _)

theorem kToBase_one (G : Over S) [GrpObj G] {Y : Over (Sp Ω)} :
    toBase G s (1 : Y ⟶ (Over.pullback s).obj G) = 1 := by
  apply Over.OverMorphism.ext
  simp only [toBase, Hom.one_def]
  simp
  erw [pullback.lift_fst]
  have hc : pullback.fst (𝟙 S) s = pullback.snd (𝟙 S) s ≫ s := by
    simpa using (pullback.condition (f := 𝟙 S) (g := s))
  erw [reassoc_of% hc]
  simp

theorem kLift_sqToBase (G : Over S) {Y : Over (Sp Ω)} (a u : Y ⟶ (Over.pullback s).obj G) :
    (lift a u).left ≫ sqToBase G s = (lift (toBase G s a) (toBase G s u)).left := by
  have key : (Over.homMk (lift a u).left (by simp only [Over.mk_hom]; rw [← Category.assoc, Over.w (lift a u)]) :
      Over.mk (Y.hom ≫ s) ⟶ Over.mk (((Over.pullback s).obj G ⊗ (Over.pullback s).obj G).hom ≫ s)) ≫
        lift (toBase G s (fst _ _)) (toBase G s (snd _ _)) = lift (toBase G s a) (toBase G s u) := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, ← kToBase_comp, lift_fst, lift_fst]
    · rw [Category.assoc, lift_snd, ← kToBase_comp, lift_snd, lift_snd]
  unfold sqToBase
  rw [← key]
  rfl

end Points

variable {Ω : Type} [Field Ω]

theorem kLam_zb_pt (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {P : LB (A ⊗ B).left} (hD : IsDual A B P)
    (hD' : IsDual B A (swap P)) (l : A ⟶ B) [IsMonHom l] (mu : B ⟶ A) [IsMonHom mu] (α : Matrix (Fin 4) (Fin 4) ℤ)
    [IsAlgClosed Ω] (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB)
    (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
    {Y : Over (Sp Ω)} (a u : Y ⟶ (Over.pullback s).obj (G4 (A ⊗ B))) :
    lam (cls (zb mu α s P L) (isLB_zb mu α s hD.isLB hL)) a u =
      zcPair hD.isLB l mu α (toBase _ s a) (toBase _ s u) := by
  have k := lam_zb hA hB hD hD' l mu α Ω s L hL e
  have k2 := congrArg (pull (lift a u).left) k
  rw [pull_lam, lift_fst, lift_snd] at k2
  rw [← k2, ← pull_comp, kLift_sqToBase]
  unfold zc
  rw [zcPair_pull, lift_fst, lift_snd]

theorem kEvc_sym (hA : IsAbelianScheme A) {P : LB (A ⊗ B).left} (hP : P.IsLB) (l : A ⟶ B) (s : Sp Ω ⟶ S)
    (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB)
    (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
    {Y : Over (Sp Ω)} (x y : Over.mk (Y.hom ≫ s) ⟶ A) :
    evc hP x (y ≫ l) = evc hP y (x ≫ l) := by
  haveI := hA.comm
  haveI : IsCommMonObj ((Over.pullback s).obj A) := inferInstance
  have h1 := lam_cL_pt s hP l L hL e (kLiftPt s A x) (kLiftPt s A y)
  have h2 := lam_cL_pt s hP l L hL e (kLiftPt s A y) (kLiftPt s A x)
  rw [kToBase_liftPt, kToBase_liftPt] at h1 h2
  rw [← h1, ← h2]
  unfold lam
  rw [mul_comm (kLiftPt s A x) (kLiftPt s A y)]
  abel

private theorem evc_comp_left_eq_pull {S' : Scheme} {G H Y0 Y1 : Over S'} {P : LB (G ⊗ H).left} (hP : P.IsLB)
    (h : Y1 ⟶ Y0) (a : Y0 ⟶ G) (b : Y0 ⟶ H) : evc hP (h ≫ a) (h ≫ b) = pull h.left (evc hP a b) := by
  unfold evc
  rw [← pull_comp, ← Over.comp_left, comp_lift]

private theorem lam_comp_eq_pull_lift_sub_pull_lift_one {S' : Scheme} {G T0 Y0 : Over S'} [GrpObj G] {L : LB G.left} (hL : L.IsLB)
    (x : T0 ⟶ G) (g : Y0 ⟶ T0) (u : Y0 ⟶ G) :
    lam (cls L hL) (g ≫ x) u =
      pull (lift g u).left (cls (Out.translDiff G L x) (LB.isLB_linComb hL _ _)) -
        pull (lift g (1 : Y0 ⟶ G)).left (cls (Out.translDiff G L x) (LB.isLB_linComb hL _ _)) := by
  rw [GlobalTheory.TripleProd.cls_translDiff hL x]
  simp only [map_sub, ← pull_comp, ← Over.comp_left, comp_mul, lift_fst_assoc, lift_snd]
  rw [_root_.mul_one]
  unfold lam
  abel

private theorem pull_lift_cls_translDiff_eq_zero_of_gen {S' : Scheme} {G T0 Y0 : Over S'} [GrpObj G] {L : LB G.left} (hL : L.IsLB)
    (x : T0 ⟶ G) (W : T0.left.Opens)
    (hW : ∃ c : ((Out.translDiff G L x).pull ((fst T0 G).left ⁻¹ᵁ W).ι).Gen, c.IsGen)
    (g : Y0 ⟶ T0) (hg : Set.range g.left.base ⊆ W) (u : Y0 ⟶ G) :
    pull (lift g u).left (cls (Out.translDiff G L x) (LB.isLB_linComb hL _ _)) = 0 := by
  have hD : (Out.translDiff G L x).IsLB := LB.isLB_linComb hL _ _
  have h0 := (cls_eq_zero_iff (LB.isLB_pull hD ((fst T0 G).left ⁻¹ᵁ W).ι)).2 hW
  rw [cls_pull hD _ (LB.isLB_pull hD _)] at h0
  have hr : Set.range (lift g u).left.base ⊆ Set.range ((fst T0 G).left ⁻¹ᵁ W).ι.base := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    show (fst T0 G).left.base ((lift g u).left.base y) ∈ W
    have e1 : (fst T0 G).left.base ((lift g u).left.base y) = g.left.base y := by
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, lift_fst]
    rw [e1]
    exact hg ⟨y, rfl⟩
  rw [← IsOpenImmersion.lift_fac _ _ hr, pull_comp, h0, map_zero]

theorem kTriv_zb' (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {P : LB (A ⊗ B).left} (hD : IsDual A B P)
    (hD' : IsDual B A (swap P)) (l : A ⟶ B) [IsMonHom l] (mu : B ⟶ A) [IsMonHom mu] (α : Matrix (Fin 4) (Fin 4) ℤ)
    [IsAlgClosed Ω] (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB)
    (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
    (m : ℕ) (hm : 1 ≤ m) (h₁ : l ≫ mu = 𝟙 A ^ m) (h₂ : mu ≫ l = 𝟙 B ^ m)
    (hα : α.transpose * α = ((4 * m ^ 2 - 1 : ℕ) : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (hα' : α * α.transpose = ((4 * m ^ 2 - 1 : ℕ) : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) :
    Out.KTriv ((Over.pullback s).obj (G4 (A ⊗ B))) (zb mu α s P L) := by
  intro R _ t x hloc
  have core : ∀ V : (Spec (CommRingCat.of R)).Opens,
      (∃ c : ((Out.translDiff _ (zb mu α s P L) x).pull
        ((fst (Over.mk t) ((Over.pullback s).obj (G4 (A ⊗ B)))).left ⁻¹ᵁ V).ι).Gen, c.IsGen) →
      V.ι ≫ x.left = V.ι ≫ (toUnit (Over.mk t) ≫ η).left := by
    intro V hV
    let Z : Over (Sp Ω) := Over.mk (V.ι ≫ t)
    let j : Z ⟶ Over.mk t := Over.homMk V.ι rfl
    have hxV : j ≫ x = 1 := by
      apply kToBase_inj s
      rw [kToBase_one]
      refine zcPair_eq_one hA hB hD hD' l mu α m hm h₁ h₂ hα hα' (toBase _ s (j ≫ x)) ?_ ?_
      · intro Y w a b
        let Z' : Over (Sp Ω) := Over.mk (w.left ≫ Z.hom)
        let ε : Y ≅ Over.mk (Z'.hom ≫ s) := Over.isoMk (Iso.refl _) (by simpa [Z'] using Over.w w)
        calc evc _ a (b ≫ l) = evc hD.isLB (ε.hom ≫ (ε.inv ≫ a)) (ε.hom ≫ (ε.inv ≫ b ≫ l)) := by simp
          _ = pull ε.hom.left (evc hD.isLB (ε.inv ≫ a) (ε.inv ≫ b ≫ l)) := evc_comp_left_eq_pull _ _ _ _
          _ = pull ε.hom.left (evc hD.isLB (ε.inv ≫ b) ((ε.inv ≫ a) ≫ l)) := by
            rw [← Category.assoc ε.inv b l, kEvc_sym hA hD.isLB l s L hL e (ε.inv ≫ a) (ε.inv ≫ b)]
          _ = evc _ b (a ≫ l) := by
            rw [← evc_comp_left_eq_pull]
            simp
      · intro Y w v
        let Z' : Over (Sp Ω) := Over.mk (w.left ≫ Z.hom)
        let ε : Y ≅ Over.mk (Z'.hom ≫ s) := Over.isoMk (Iso.refl _) (by simpa [Z'] using Over.w w)
        let k : Z' ⟶ Z := Over.homMk w.left rfl
        have hk : ε.inv ≫ w = (Over.homMk k.left
            (by simp only [Over.mk_hom]; rw [← Category.assoc, Over.w k]) :
              Over.mk (Z'.hom ≫ s) ⟶ Over.mk (Z.hom ≫ s)) := by
          ext
          simp [ε, k]
          try exact Category.id_comp _
        have hg : Set.range (k ≫ j).left.base ⊆ (V : Set (Spec (CommRingCat.of R))) := by
          rintro _ ⟨y, rfl⟩
          have e2 : (k ≫ j).left = k.left ≫ V.ι := by simp [j]
          rw [e2, Scheme.Hom.comp_apply]
          have hm := Set.mem_range_self (f := V.ι.base) (k.left.base y)
          rwa [Scheme.Opens.range_ι] at hm
        calc zcPair _ l mu α (w ≫ toBase _ s (j ≫ x)) v
            = zcPair hD.isLB l mu α (ε.hom ≫ (ε.inv ≫ w ≫ toBase _ s (j ≫ x))) (ε.hom ≫ (ε.inv ≫ v)) := by
              simp
          _ = pull ε.hom.left (zcPair hD.isLB l mu α (ε.inv ≫ w ≫ toBase _ s (j ≫ x)) (ε.inv ≫ v)) :=
              (zcPair_pull _ _ _ _ _ _ _).symm
          _ = 0 := by
            rw [← Category.assoc, hk, ← kToBase_comp, ← kToBase_liftPt s _ (ε.inv ≫ v),
              ← kLam_zb_pt hA hB hD hD' l mu α s L hL e, ← Category.assoc,
              lam_comp_eq_pull_lift_sub_pull_lift_one (isLB_zb mu α s hD.isLB hL) x (k ≫ j),
              pull_lift_cls_translDiff_eq_zero_of_gen (isLB_zb mu α s hD.isLB hL) x V hV (k ≫ j) hg,
              pull_lift_cls_translDiff_eq_zero_of_gen (isLB_zb mu α s hD.isLB hL) x V hV (k ≫ j) hg, sub_zero, map_zero]
    have h2 : j ≫ (toUnit (Over.mk t) ≫ η[(Over.pullback s).obj (G4 (A ⊗ B))]) =
        (1 : Z ⟶ (Over.pullback s).obj (G4 (A ⊗ B))) := by
      rw [Hom.one_def, ← Category.assoc, comp_toUnit]
    have h3 := congrArg Over.Hom.left (hxV.trans h2.symm)
    exact h3
  choose V hpV hV using hloc
  apply Over.OverMorphism.ext
  refine Scheme.Cover.hom_ext ((Spec (CommRingCat.of R)).openCoverOfIsOpenCover V ?_) _ _ (fun p => ?_)
  · exact eq_top_iff.2 (fun p _ => TopologicalSpace.Opens.mem_iSup.2 ⟨p, hpV p⟩)
  · exact core (V p) (hV p)

theorem kTriv_zb (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {P : LB (A ⊗ B).left} (hD : IsDual A B P)
    (hD' : IsDual B A (swap P)) (l : A ⟶ B) [IsMonHom l] (mu : B ⟶ A) [IsMonHom mu] (α : Matrix (Fin 4) (Fin 4) ℤ)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB)
    (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
    (m : ℕ) (hm : 1 ≤ m) (h₁ : l ≫ mu = 𝟙 A ^ m) (h₂ : mu ≫ l = 𝟙 B ^ m)
    (hα : α.transpose * α = ((4 * m ^ 2 - 1 : ℕ) : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (hα' : α * α.transpose = ((4 * m ^ 2 - 1 : ℕ) : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) :
    Out.KTriv ((Over.pullback s).obj (G4 (A ⊗ B))) (zb mu α s P L) :=
  kTriv_zb' hA hB hD hD' l mu α s L hL e m hm h₁ h₂ hα hα'

end PositivityTheory.PrwZar
