import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjPullG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentStabilizerActsByLevelChange
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsTransitionUnique
import Formalism.LocalToGlobal.ProjectiveLattices.GenSpecSep
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevelMoveRestr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_frPt_ptF {K : Type} [Field K] [Algebra c.F K] (t : Sp K ⟶ Xo.XF c)
    (ht : t ≫ pullback.snd _ _ = spMap (algebraMap c.F K)) : ∃ y : FrPt Xo c K, ptF y = t := by
  obtain ⟨y, hy⟩ := GlobalTheory.FlagTan.exists_frPt (Xo := Xo) (c := c) (S := K) (t ≫ pullback.fst _ _) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ht, sOf, ← Spec.map_comp]; rfl)
  refine ⟨y, pullback.hom_ext ?_ ?_⟩
  · simp only [ptF, pullback.lift_fst]; exact hy
  · simp only [ptF, pullback.lift_snd]; exact ht.symm

theorem restr_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Γ : Type) [Group Γ] (ι : Γ →* LevelAut Dw l) (ρ : Γ →* Aut (V₀ TF.Y Z)), ActsBy ι ρ → ∀ γ : Γ, (ρ γ).hom ≫ i₀ TF.Y Z = i₀ TF.Y Z ≫ GlobalTheory.CompLevelStab.mvF hpq hA Xo c (ι γ)⁻¹ := by
  intro E _ _ _ H Dw l Xo c TF Z hpq hA Γ _ ι ρ hρ γ
  haveI : IsSeparated Xo.s := Formalism.L2.Pj.sepX Xo
  haveI : IsReduced (Xo.XF c) := GlobalTheory.TransitionUnique.isReduced_XF Xo c
  refine ext_of_fromSpecResidueField_eq _ _ (pullback.snd _ _) Set.univ dense_univ (fun x _ => ?_) ?_
  · let t : Spec ((V₀ TF.Y Z).residueField x) ⟶ Sp c.F :=
      (V₀ TF.Y Z).fromSpecResidueField x ≫ i₀ TF.Y Z ≫ pullback.snd _ _
    letI : Algebra c.F ((V₀ TF.Y Z).residueField x) := (Spec.preimage t).hom.toAlgebra
    obtain ⟨y, hy⟩ := exists_frPt_ptF (K := (V₀ TF.Y Z).residueField x)
      ((V₀ TF.Y Z).fromSpecResidueField x ≫ i₀ TF.Y Z) (by
        rw [Category.assoc]
        exact (Spec.map_preimage t).symm)
    have h1 := hρ.2 γ ((V₀ TF.Y Z).residueField x) y ((V₀ TF.Y Z).fromSpecResidueField x) hy.symm
    rw [h1, GlobalTheory.CompLevelStab.ptF_move hpq hA Xo c, hy, Category.assoc]
  · have hid : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
    have h0 := hρ.1 γ
    rw [GlobalTheory.CompLevelStab.j₀_s₀, hid, Category.comp_id] at h0
    rw [Category.assoc, Category.assoc, GlobalTheory.CompLevelStab.mvF_snd]
    exact h0

end GlobalTheory.LevelMoveRestr
