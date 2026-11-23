import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianLocusEqPreimageModuliAndPrincipal
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FinrankMumfordBundleCechHomologyOrigin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DiagAmpleExt

theorem diag_comm {S S' : Scheme.{0}} {G : Over S} {A : Over S'} (φ : A.left ⟶ G.left)
    (φ₂ : (G2 A).left ⟶ (G2 G).left) (h : IsSquare φ φ₂) :
    φ ≫ (lift (𝟙 G) (𝟙 G)).left = (lift (𝟙 A) (𝟙 A)).left ≫ φ₂ := by
  apply pullback.hom_ext
  · change φ ≫ (lift (𝟙 G) (𝟙 G)).left ≫ (fst G G).left = (lift (𝟙 A) (𝟙 A)).left ≫ φ₂ ≫ (fst G G).left
    rw [h.1, ← Over.comp_left, lift_fst, Over.id_left, Category.comp_id, ← Category.assoc,
      ← Over.comp_left, lift_fst, Over.id_left, Category.id_comp]
  · change φ ≫ (lift (𝟙 G) (𝟙 G)).left ≫ (snd G G).left = (lift (𝟙 A) (𝟙 A)).left ≫ φ₂ ≫ (snd G G).left
    rw [h.2, ← Over.comp_left, lift_snd, Over.id_left, Category.comp_id, ← Category.assoc,
      ← Over.comp_left, lift_snd, Over.id_left, Category.id_comp]

theorem relAmple_diag_of_generic : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left) (φ₂ : (G2 A).left ⟶ (G2 G).left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap W L)) φ → IsSquare φ φ₂ → ∀ (P : LB (G2 A).left) (P' : LB (G2 G).left), P.IsLB → P'.IsLB → LBIso P (P'.pull φ₂) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → Out.RelAmple G (P'.pull (lift (𝟙 G) (𝟙 G)).left) := by
  intro W L _ _ _ _ _ _ G _ A _ φ φ₂ hG hφ hsq P P' hP hP' e hA
  have hAab : IsAbelianScheme A := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hG hφ
  have := hAab.proper
  set dG := (lift (𝟙 G) (𝟙 G)).left
  set dA := (lift (𝟙 A) (𝟙 A)).left
  have hM : (P'.pull dG).IsLB := pull_isLB hP' _
  refine GlobalTheory.ModelAmpleExt.relAmple_of_generic W L G A φ hG hφ (P'.pull dG) hM ?_
  have i1 : LBIso ((P'.pull dG).pull φ) (P'.pull (φ ≫ dG)) :=
    GlobalTheory.OriginCohom.lbIso_pull_pull_comp hP' dG φ
  have i2 : LBIso (P'.pull (dA ≫ φ₂)) ((P'.pull φ₂).pull dA) :=
    GlobalTheory.GenSpread.lbIso_pull_pull hP' dA rfl
  have i3 : LBIso ((P'.pull φ₂).pull dA) (P.pull dA) :=
    GlobalTheory.GenSpread.lbIso_pullback e.symm dA
  rw [diag_comm φ φ₂ hsq] at i1
  have hφ2 := pull_isLB hP' φ₂
  have j : LBIso (P.pull dA) ((P'.pull dG).pull φ) :=
    (LBIso.trans (pull_isLB hM φ) (pull_isLB hP' _) (pull_isLB hP dA) i1 (LBIso.trans (pull_isLB hP' _)
      (pull_isLB hφ2 dA) (pull_isLB hP dA) i2 i3)).symm
  have hsq' : IsPullback (𝟙 A.left) A.hom A.hom (𝟙 _) := IsPullback.of_horiz_isIso ⟨by simp⟩
  exact GlobalTheory.ModelAbLocus.relAmple_of_lbIso_pull hsq' (pull_isLB hP dA) (pull_isLB hM φ)
    (LBIso.trans (pull_isLB hM φ) (pull_isLB hP dA) (pull_isLB (pull_isLB hP dA) _) j.symm
      (GlobalTheory.GenSpread.lbIso_pull_pull hP (𝟙 _) (a := dA) (Category.id_comp _).symm)) hA

end GlobalTheory.DiagAmpleExt
