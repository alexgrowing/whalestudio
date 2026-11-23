import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivialLocusRigidifiedBundleClosedSeesawStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleExternalTensorPowerGroupPower
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SqIsPowGrp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdivisibleBaseChangeIsoSemiabelian
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

open GlobalTheory.CechPic

noncomputable section

namespace GlobalTheory.EndLoc.AdjClosed

variable {S : Scheme.{0}}

theorem hom_ext_sq {A : Over S} {X : Scheme.{0}} {u v : X ⟶ (A ⊗ A).left}
    (h₁ : u ≫ (fst A A).left = v ≫ (fst A A).left) (h₂ : u ≫ (snd A A).left = v ≫ (snd A A).left) : u = v := by
  have p : IsPullback (fst A A).left (snd A A).left A.hom A.hom := IsPullback.of_hasPullback _ _
  exact p.hom_ext h₁ h₂

theorem comm_left {S' : Scheme.{0}} {A : Over S} {A' : Over S'} {φ : A'.left ⟶ A.left}
    {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} (hsq : IsSquare φ φ₂) (f : A ⟶ A) (g : A' ⟶ A')
    (hg : g.left ≫ φ = φ ≫ f.left) :
    (lift (fst A' A' ≫ g) (snd A' A')).left ≫ φ₂ = φ₂ ≫ (lift (fst A A ≫ f) (snd A A)).left := by
  apply hom_ext_sq
  · rw [Category.assoc, hsq.1, Category.assoc, ← Over.comp_left, lift_fst, ← Category.assoc, ← Over.comp_left,
      lift_fst, Over.comp_left, Over.comp_left, Category.assoc, hg]
    simp only [← Category.assoc, hsq.1]
  · rw [Category.assoc, hsq.2, Category.assoc, ← Over.comp_left, lift_snd, ← Category.assoc, ← Over.comp_left,
      lift_snd, hsq.2]

theorem comm_right {S' : Scheme.{0}} {A : Over S} {A' : Over S'} {φ : A'.left ⟶ A.left}
    {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} (hsq : IsSquare φ φ₂) (f : A ⟶ A) (g : A' ⟶ A')
    (hg : g.left ≫ φ = φ ≫ f.left) :
    (lift (fst A' A') (snd A' A' ≫ g)).left ≫ φ₂ = φ₂ ≫ (lift (fst A A) (snd A A ≫ f)).left := by
  apply hom_ext_sq
  · rw [Category.assoc, hsq.1, Category.assoc, ← Over.comp_left, lift_fst, ← Category.assoc, ← Over.comp_left,
      lift_fst, hsq.1]
  · rw [Category.assoc, hsq.2, Category.assoc, ← Over.comp_left, lift_snd, ← Category.assoc, ← Over.comp_left,
      lift_snd, Over.comp_left, Over.comp_left, Category.assoc, hg]
    simp only [← Category.assoc, hsq.2]

end GlobalTheory.EndLoc.AdjClosed

open GlobalTheory.EndLoc.AdjClosed in

theorem GlobalTheory.EndLoc.exists_closed_adj : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), IsAbelianScheme A → Q.IsLB → (∃ t : (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso Q (Q.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (Q.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (f f' : A ⟶ A), IsMonHom f → IsMonHom f' → ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] [IsCommMonObj A'] (φ' : A'.left ⟶ A.left) (φ₂' : (A' ⊗ A').left ⟶ (A ⊗ A).left) (g g' : A' ⟶ A'), IsGrpPullback A' A t φ' → IsSquare φ' φ₂' → g.left ≫ φ' = φ' ≫ f.left → g'.left ≫ φ' = φ' ≫ f'.left → (LBIso ((Q.pull φ₂').pull (lift (fst A' A' ≫ g) (snd A' A')).left) ((Q.pull φ₂').pull (lift (fst A' A') (snd A' A' ≫ g')).left) ↔ ∃ z : T ⟶ Z, z ≫ i = t) := by
  intro S _ A _ _ Q hA hQ h0l h0r hsym hamp f f' hf hf'
  let β := (lift (fst A A ≫ f) (snd A A)).left
  let β' := (lift (fst A A) (snd A A ≫ f')).left
  let N := LB.LinComb Q (K := Fin 2) ![β, β'] ![1, -1]
  have hN : N.IsLB := LB.isLB_linComb hQ _ _
  have hc : cls N hN = pull β (cls Q hQ) - pull β' (cls Q hQ) := by
    rw [cls_linComb hQ]
    simp [Fin.sum_univ_two, sub_eq_add_neg]
  have hrig : Out.Rigidified (A ⊗ A) N := by
    have e : η[A ⊗ A] ≫ lift (fst A A ≫ f) (snd A A) = η[A ⊗ A] ≫ lift (fst A A) (snd A A ≫ f') := by
      have h₁ : η[A ⊗ A] ≫ fst A A = η[A] := IsMonHom.one_hom (fst A A)
      have h₂ : η[A ⊗ A] ≫ snd A A = η[A] := IsMonHom.one_hom (snd A A)
      apply CartesianMonoidalCategory.hom_ext
      · rw [Category.assoc, lift_fst, Category.assoc, lift_fst, ← Category.assoc, h₁, IsMonHom.one_hom]
      · rw [Category.assoc, lift_snd, Category.assoc, lift_snd, ← Category.assoc, h₂, IsMonHom.one_hom]
    have e' : eSec (A ⊗ A) ≫ β = eSec (A ⊗ A) ≫ β' := by
      simp only [eSec, β, β', ← Over.comp_left, e]
    refine (cls_eq_zero_iff (pull_isLB hN _)).1 ?_
    rw [cls_pull hN, hc, map_sub, ← pull_comp, ← pull_comp, e', sub_self]
  let L₀ := Out.boxLB (Q.pull (lift (𝟙 A) (𝟙 A)).left) (GlobalTheory.SquarePol.sqIsPowGrp A).pr
  have hL₀ : L₀.IsLB := LB.isLB_linComb (pull_isLB hQ _) _ _
  have hamp₀ : Out.RelAmple (A ⊗ A) L₀ :=
    GlobalTheory.relAmple_boxLB S _ A 2 (GlobalTheory.SquarePol.sqIsPowGrp A) _ (pull_isLB hQ _) hamp
  have hAA : IsAbelianScheme (A ⊗ A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  obtain ⟨Z, i, hi, hZ⟩ := GlobalTheory.T.trivial_locus_rigidified_bundle_closed_seesaw S (A ⊗ A) L₀ N hAA hL₀ hamp₀ hN hrig
  refine ⟨Z, i, hi, fun T t A' _ _ φ' φ₂' g g' hpb hsq hg hg' => ?_⟩
  have hpb₂ := GlobalTheory.WeilIntegral.isGrpPullback_prod hpb hpb hsq.1 hsq.2
  rw [← hZ T t (A' ⊗ A') φ₂' hpb₂, ← cls_eq_zero_iff (pull_isLB hN _), cls_pull hN, hc, map_sub, ← pull_comp,
    ← pull_comp, ← comm_left hsq f g hg, ← comm_right hsq f' g' hg', pull_comp, pull_comp, sub_eq_zero,
    ← cls_eq_iff (pull_isLB (pull_isLB hQ _) _) (pull_isLB (pull_isLB hQ _) _)]
  rfl
