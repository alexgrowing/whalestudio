import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamExt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnivIdentity
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Desc

noncomputable section

namespace GlobalTheory.Mum.Desc

open GlobalTheory.FieldBaseChange

theorem phiRel_famExt : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), Odd N → ∀ (p : QkPt D.toPre (Kb R) N) (w : GlobalTheory.UT.Frm D.toPre (Kb R) N p.g.b) (p' : QkPt D.toPre F N) (w' : GlobalTheory.UT.Frm D.toPre F N p'.g.b), GlobalTheory.UT.TXFrame N p w → GlobalTheory.UT.TXFrame N p' w' → QkExt em.toRingHom p p' → ∀ s s₁, PhiRel D.toPre (Kb R) N p w s s₁ → PhiRel D.toPre F N p' w' (famExt D.toPre em N s) (famExt D.toPre em N s₁) := by
  intro R _ _ _ I hI D F _ _ _ em N hN p w p' w' hw hw' hp s s₁ H
  letI : Algebra (Kb R) F := em.toRingHom.toAlgebra
  haveI : IsScalarTower (FractionRing R) (Kb R) F := IsScalarTower.of_algebraMap_eq fun r => (em.commutes r).symm
  have hL : GlobalTheory.UT.LL := ⟨GlobalTheory.allSixLaws.1, GlobalTheory.allSixLaws.2.1, GlobalTheory.allSixLaws.2.2.1, GlobalTheory.allSixLaws.2.2.2.1,
    GlobalTheory.allSixLaws.2.2.2.2.1⟩
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  obtain ⟨hy, hb, hs⟩ := hp
  have hb' : p'.g.b = baseMap (R := R) (Kb R) F ≫ p.g.b := Over.OverMorphism.ext hb
  have hb2 : (baseMap (R := R) (Kb R) F).left ≫ p.g.b.left = p'.g.b.left := hb.symm
  have h0 : (baseMap (R := R) (Kb R) F).left ≫ (DegPre.zeroF D.toPre (Kb R)).left = (DegPre.zeroF D.toPre F).left :=
    congrArg (fun q : TF (R := R) F ⟶ D.toPre.P.A => q.left) (MonObj.comp_one (M := D.toPre.P.A) (baseMap (R := R) (Kb R) F))
  have j1 : (baseMap (R := R) (Kb R) F).left ≫ jFK (R := R) (Kb R) = jFK (R := R) F := specMap_jFK (R := R) (Kb R) F
  have j2 : (baseMap (R := R) (Kb R) F).left ≫ (TF (R := R) (Kb R)).hom = (TF (R := R) F).hom := Over.w _
  obtain ⟨w'', hw'', hv⟩ := exists_gen D.toPre.P.isLB (φ' := DegPre.lineφ D.toPre F p'.g.b) (ε' := DegPre.lineε N)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by
      fin_cases i
      · exact congrArg (fun q => h q ^ _) h0
      · exact congrArg (fun q => h q ^ _) hb.symm)
    (LB.pullGen D.toPre.P.L _ _ w (baseMap (R := R) (Kb R) F).left) (pullGen_isGen _ _ _ _ hw.1 _)
  have hX : GlobalTheory.UT.TXFrame N p' w'' := by
    refine ⟨hw'', fun ν hν z J hJ => ?_, fun κ hκ z J hJ => ?_⟩
    · have C : LB.Gen.Corr D.toPre.P.L _ _ _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ w 2)
          (LB.mulGen D.toPre.P.L _ _ _ _ (p.g.s p.y) (LB.pullGen D.toPre.P.L _ _ ν p.g.b.left)) :=
        corr_of_val D.toPre.P.isLB fun y J hJ => by
          rw [val_mul hJ, val_pull hJ, Category.id_comp]
          exact (map_pow _ _ _).trans (hw.2.1 ν hν y J hJ)
      have e := val_corr hJ C (baseMap (R := R) (Kb R) F).left
      rw [val_mul hJ, val_pull hJ, hb2] at e
      rw [hv _ _ z J hJ, val_pull hJ, val_corr hJ (hs p'.y), val_pull hJ, hy, Category.id_comp, Category.id_comp]
      exact (map_pow _ _ _).symm.trans e
    · have C : LB.Gen.Corr D.toPre.P.L _ _ _ _
          (LB.mulGen D.toPre.P.L _ _ _ _ (GeneratorPullback.powGen D.toPre.P.L _ _ w N) (LB.pullGen D.toPre.P.L _ _ κ p.g.b.left))
          (LB.mulGen D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ (D.toPre.psi p.y) (jFK (R := R) (Kb R)))
            (LB.pullGen D.toPre.P.L (fun _ : PUnit => eSec D.toPre.P.A) (fun _ => 1) D.toPre.rig
              (TF (R := R) (Kb R)).hom)) :=
        corr_of_val D.toPre.P.isLB fun y J hJ => by
          rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp,
            Category.id_comp]
          exact (congrArg₂ (· * ·) (map_pow _ _ _) rfl).trans (hw.2.2 κ hκ y J hJ)
      have e := val_corr hJ C (baseMap (R := R) (Kb R) F).left
      rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, val_pull hJ, hb2, j1, j2] at e
      rw [hv _ _ z J hJ, val_pull hJ, Category.id_comp, hy]
      exact (congrArg₂ (· * ·) (map_pow _ _ _).symm rfl).trans e
  have Cw : LB.Gen.Corr D.toPre.P.L _ _ _ _ w' (LB.pullGen D.toPre.P.L _ _ w (baseMap (R := R) (Kb R) F).left) :=
    corr_of_val D.toPre.P.isLB fun y J hJ =>
      ((GlobalTheory.UT.SymFrame.main hL R I hI D F N hN p').2 w'' w' hX hw' y J hJ).symm.trans (hv _ _ y J hJ)
  rw [phiRel_iff hG p w hw.1] at H
  refine (phiRel_iff hG p' w' hw'.1 _ _).2 ?_
  intro α β hβ T ρ z J hJ
  have e₁ : DegPre.trPt D.toPre F p'.g.b ≫ famMap D.toPre (Kb R) F =
      famMap D.toPre (Kb R) F ≫ DegPre.trPt D.toPre (Kb R) p.g.b := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, Category.assoc, famMap_fst, tr_fst, ← Category.assoc, tr_fst, famMap_fst]
    · refine ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (famMap_snd D.toPre (Kb R) F)).trans (tr_pr D.toPre F _))).trans
        (Eq.symm ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (tr_pr D.toPre (Kb R) _)).trans ?_)))
      rw [MonObj.comp_mul, famMap_snd, ← Category.assoc, famMap_fst, hb', Category.assoc]
  have e₂ : ((ρ ≫ famMap D.toPre (Kb R) F) ≫ fst _ _).left = (ρ ≫ fst _ _).left ≫ (baseMap (R := R) (Kb R) F).left := by
    rw [Category.assoc, famMap_fst, ← Category.assoc]; rfl
  have e₃ : uVal D.toPre (Kb R) N α p.g.b (ρ ≫ famMap D.toPre (Kb R) F) z J = uVal D.toPre F N α p'.g.b ρ z J := by
    have : famMap D.toPre (Kb R) F ≫ fst _ _ ≫ p.g.b = fst _ _ ≫ p'.g.b := by
      rw [← Category.assoc, famMap_fst, hb', Category.assoc]
    simp only [uVal, Category.assoc, famMap_snd, this]
  refine (sval_pullOver _ _ _ _ hJ).trans ((H α β (hy ▸ hβ) T (ρ ≫ famMap D.toPre (Kb R) F) z J hJ).trans
    (congrArg₂ (· * ·) (Eq.trans ?_ (sval_pullOver _ _ _ _ hJ).symm) (congrArg Units.val ?_)))
  · rw [Category.assoc, ← e₁, ← Category.assoc]; rfl
  · rw [e₃, val_mul hJ, val_mul hJ, val_corr hJ Cw, val_pull hJ, val_corr hJ (hs α), val_pull hJ, e₂]
    rfl

end GlobalTheory.Mum.Desc
