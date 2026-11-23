import Mathlib
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.FibAmpleD
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.IsFiniteMapG4map

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

set_option maxHeartbeats 400000 in

theorem relAmple_lPart (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (mu : B ⟶ A) [IsMonHom mu]
    (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB)
    (ha : Out.RelAmple ((Over.pullback s).obj A) L) (hmu : IsFinite ((Over.pullback s).map mu).left) :
    Out.RelAmple ((Over.pullback s).obj (G4 (A ⊗ B))) (lPart mu s L) := by
  have hGA : IsAbelianScheme ((Over.pullback s).obj A) := GlobalTheory.isAbelianScheme_pullback_obj s A hA
  haveI : IsProper ((Over.pullback s).obj A).hom := hGA.proper
  have hAA : IsAbelianScheme (A ⊗ A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hAB : IsAbelianScheme (A ⊗ B) := AbelianSchemeGerms.isAbelianScheme_tensor A B hA hB
  have h4A : IsAbelianScheme (G4 (A ⊗ A)) :=
    AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAA
      (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAA (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAA hAA))
  have h4B : IsAbelianScheme (G4 (A ⊗ B)) :=
    AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAB
      (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAB (AbelianSchemeGerms.isAbelianScheme_tensor _ _ hAB hAB))
  have hY : IsAbelianScheme ((Over.pullback s).obj (G4 (A ⊗ A))) := GlobalTheory.isAbelianScheme_pullback_obj s _ h4A
  have hG : IsAbelianScheme ((Over.pullback s).obj (G4 (A ⊗ B))) := GlobalTheory.isAbelianScheme_pullback_obj s _ h4B
  haveI : IsProper ((Over.pullback s).obj (G4 (A ⊗ A))).hom := hY.proper
  haveI : IsProper ((Over.pullback s).obj (G4 (A ⊗ B))).hom := hG.proper
  have hL' : (L.LinComb ![𝟙 _, Over.Hom.left (𝟙 ((Over.pullback s).obj A))⁻¹] ![1, 1]).IsLB :=
    LB.isLB_linComb hL _ _
  have ha' := XB.relAmple_sym hL ha
  haveI hpr : ∀ j, IsMonHom (XB.pr8 A j) := by
    intro j
    fin_cases j <;> simp only [XB.pr8] <;> infer_instance
  let p : Out.IsPowGrp ((Over.pullback s).obj (G4 (A ⊗ A))) ((Over.pullback s).obj A) 8 :=
    { pr := fun j => (Over.pullback s).map (XB.pr8 A j)
      hom := fun j => inferInstance
      lim := (isLimitMapConeFanMkEquiv (Over.pullback s) _ _).1 (isLimitOfPreserves _ (XB.lim8 A)) }
  have hbox := GlobalTheory.relAmple_boxLB _ _ _ 8 p _ hL' ha'
  have hboxLB : (Out.boxLB (L.LinComb ![𝟙 _, Over.Hom.left (𝟙 ((Over.pullback s).obj A))⁻¹] ![1, 1])
      p.pr).IsLB := LB.isLB_linComb hL' _ _
  have hid : IsFinite ((Over.pullback s).map (𝟙 A)).left := by
    have e1 : (Over.pullback s).map (𝟙 A) = 𝟙 _ := (Over.pullback s).map_id A
    rw [e1, Over.id_left]
    infer_instance
  have hΦ : IsFinite ((Over.pullback s).map (XB.fourfoldProductMap (𝟙 A ⊗ₘ mu))).left :=
    XB.isFinite_map_g4map s _ (XB.isFinite_map_tensorHom s _ _ hid hmu)
  haveI := hΦ
  have h2 := GlobalTheory.PosDefAmple.relAmple_pull_of_isAffineHom ((Over.pullback s).map (XB.fourfoldProductMap (𝟙 A ⊗ₘ mu)))
    hboxLB hbox
  have hlpLB : (lPart mu s L).IsLB := LB.isLB_linComb hL _ _
  have hq : ∀ i : Fin 4, XB.fourfoldProductMap (𝟙 A ⊗ₘ mu) ≫ prj (A ⊗ A) i = prj (A ⊗ B) i ≫ (𝟙 A ⊗ₘ mu) := by
    intro i
    fin_cases i <;> simp [XB.fourfoldProductMap, prj]
  have hinv : ∀ {X : Over (Sp Ω)} (f : X ⟶ (Over.pullback s).obj A),
      (pull (Over.Hom.left f⁻¹)) (cls L hL) =
        (pull (Over.Hom.left f)) ((pull (Over.Hom.left (𝟙 ((Over.pullback s).obj A))⁻¹)) (cls L hL)) := by
    intro X f
    rw [← pull_comp, ← Over.comp_left, GrpObj.comp_inv, Category.comp_id]
  refine GlobalTheory.PosDefAmple.relAmple_of_nsmul hlpLB (LB.isLB_pull hboxLB _) le_rfl ?_ h2
  rw [one_smul, cls_pull hboxLB, GlobalTheory.PosDefAmple.pull_cls_boxLB p.pr hL']
  simp only [lPart]
  simp only [cls_linComb hL, Fintype.sum_prod_type, Fin.sum_univ_four, Fin.sum_univ_eight, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_smul, map_add, Over.id_left, pull_id]
  simp only [p, ← Functor.map_comp, XB.pr8]
  simp only [← Category.assoc, hq]
  simp only [Category.assoc, tensorHom_fst, tensorHom_snd, Category.comp_id, phiL]
  simp only [hinv (pA s 0), hinv (pA s 1), hinv (pA s 2), hinv (pA s 3), hinv (pM mu s 0), hinv (pM mu s 1),
    hinv (pM mu s 2), hinv (pM mu s 3)]
  simp only [pA, pM]
  abel

end PositivityTheory.PrwZar
