import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingDeterminedAtGenericPoint
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteEtaleCoverConstantTorsion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionSectionExtendsAbLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FibrePull

theorem fibre_isPull : ∀ (S T : Scheme.{0}) (A₀ : Over T) [GrpObj A₀] [IsCommMonObj A₀] (P₀ : LB (G2 A₀).left) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left) (f : T ⟶ S), P₀.IsLB → P.IsLB → SameFib A₀ P₀ (𝟙 _) A P f → ∃ (φ : A₀.left ⟶ A.left) (φ₂ : (G2 A₀).left ⟶ (G2 A).left), IsGrpPullback A₀ A f φ ∧ IsSquare φ φ₂ ∧ LBIso P₀ (P.pull φ₂) ∧ LBIso (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull φ) := by
  intro S T A₀ _ _ P₀ A _ _ P f hP₀ hP hS
  obtain ⟨H, _, _, a, a₂, a', a₂', h₁, s₁, h₂, s₂, w⟩ := hS
  have : IsMonHom (Iso.refl A₀).hom := inferInstanceAs (IsMonHom (𝟙 A₀))
  obtain ⟨e, he, hea⟩ := grpPullback_iso h₁ (isGrpPullback_of_iso (Iso.refl A₀))
  have hea' : e.hom.left = a := by simpa using hea
  have : IsMonHom e.symm.hom := inferInstanceAs (IsMonHom e.inv)
  have hinv : e.inv.left ≫ a = 𝟙 _ := by rw [← hea', ← Over.comp_left, e.inv_hom_id, Over.id_left]
  let ψ : G2 A₀ ⟶ G2 H := lift (fst A₀ A₀ ≫ e.inv) (snd A₀ A₀ ≫ e.inv)
  have ext2 : ∀ {G : Over T} {X : Scheme.{0}} (u v : X ⟶ (G2 G).left), u ≫ (fst G G).left = v ≫ (fst G G).left →
      u ≫ (snd G G).left = v ≫ (snd G G).left → u = v := fun u v h1 h2 => Over.tensorObj_ext _ _ h1 h2
  have ext2' : ∀ {X : Scheme.{0}} (u v : X ⟶ (G2 A).left), u ≫ (fst A A).left = v ≫ (fst A A).left →
      u ≫ (snd A A).left = v ≫ (snd A A).left → u = v := fun u v h1 h2 => Over.tensorObj_ext _ _ h1 h2
  have k1 : ψ.left ≫ (fst H H).left = (fst A₀ A₀).left ≫ e.inv.left := by rw [← Over.comp_left, lift_fst, Over.comp_left]
  have k2 : ψ.left ≫ (snd H H).left = (snd A₀ A₀).left ≫ e.inv.left := by rw [← Over.comp_left, lift_snd, Over.comp_left]
  have d1 : (lift (𝟙 A₀) (𝟙 A₀)).left ≫ (fst A₀ A₀).left = 𝟙 _ := by rw [← Over.comp_left, lift_fst, Over.id_left]
  have d2 : (lift (𝟙 A₀) (𝟙 A₀)).left ≫ (snd A₀ A₀).left = 𝟙 _ := by rw [← Over.comp_left, lift_snd, Over.id_left]
  have d1' : (lift (𝟙 A) (𝟙 A)).left ≫ (fst A A).left = 𝟙 _ := by rw [← Over.comp_left, lift_fst, Over.id_left]
  have d2' : (lift (𝟙 A) (𝟙 A)).left ≫ (snd A A).left = 𝟙 _ := by rw [← Over.comp_left, lift_snd, Over.id_left]
  have hψ : ψ.left ≫ a₂ = 𝟙 _ := by
    apply ext2
    · rw [Category.assoc, s₁.1, Category.id_comp, ← Category.assoc, k1, Category.assoc, hinv, Category.comp_id]
    · rw [Category.assoc, s₁.2, Category.id_comp, ← Category.assoc, k2, Category.assoc, hinv, Category.comp_id]
  have hψ₀ : LBIso P₀ ((P₀.pull a₂).pull ψ.left) :=
    GlobalTheory.ThetaAffineGlue.lbIso_cancel hP₀ (pull_isLB hP₀ _) hP₀
      (by rw [hψ]; exact GlobalTheory.ThetaAffineGlue.lbIso_pull_id hP₀)
      (LBIso.trans (pull_isLB hP₀ _) (pull_isLB hP _) (pull_isLB hP₀ _) w w.symm)
  have hP₀₂ : LBIso P₀ (P.pull (ψ.left ≫ a₂')) :=
    hψ₀.trans hP₀ (pull_isLB (pull_isLB hP₀ _) _) (pull_isLB hP _) (GlobalTheory.ThetaAffineGlue.lbIso_pull w ψ.left)
  have hd : (lift (𝟙 A₀) (𝟙 A₀)).left ≫ (ψ.left ≫ a₂') = (e.inv.left ≫ a') ≫ (lift (𝟙 A) (𝟙 A)).left := by
    apply ext2'
    · simp only [Category.assoc]
      rw [s₂.1, d1', Category.comp_id, ← Category.assoc ψ.left, k1, ← Category.assoc, ← Category.assoc, d1, Category.id_comp]
    · simp only [Category.assoc]
      rw [s₂.2, d2', Category.comp_id, ← Category.assoc ψ.left, k2, ← Category.assoc, ← Category.assoc, d2, Category.id_comp]
  refine ⟨e.inv.left ≫ a', ψ.left ≫ a₂', ?_, ?_, hP₀₂, ?_⟩
  · exact ((isGrpPullback_of_iso e.symm).comp h₂).congr (Category.id_comp _) rfl
  · constructor
    · rw [Category.assoc, s₂.1, ← Category.assoc, ← Over.comp_left, lift_fst, Over.comp_left, Category.assoc]
    · rw [Category.assoc, s₂.2, ← Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left, Category.assoc]
  · have h3 := GlobalTheory.ThetaAffineGlue.lbIso_pull hP₀₂ (lift (𝟙 A₀) (𝟙 A₀)).left
    rw [hd] at h3
    have hΔ := pull_isLB hP (lift (𝟙 A) (𝟙 A)).left
    exact h3.trans (pull_isLB hP₀ _) (pull_isLB hP _) (pull_isLB hΔ _)
      (GlobalTheory.ThetaAffineGlue.lbIso_pull
        (show LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left) (P.pull (lift (𝟙 A) (𝟙 A)).left) from
          LBIso.trans hΔ (pull_isLB hΔ _) hΔ (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hΔ) (LBIso.symm (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hΔ))) (e.inv.left ≫ a')).symm

end GlobalTheory.FibrePull
