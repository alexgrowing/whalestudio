import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLiftSquareZeroOfMumfordBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoMumfordLambdaOfLocalQuotientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleOfReductions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLocalRingQuotientPow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelStructurePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSquareUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AxisTrivialLineBundleGroupPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalPullbackBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleThickeningSquareTheoremStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PolRoot

namespace GlobalTheory.PolRootComplete

theorem root_given {S T : Scheme.{0}} {A : Over S} [GrpObj A] {P : LB (G2 A).left} (hP : P.IsLB) {t : T ⟶ S}
    (h : Root A P t) {B : Over T} [GrpObj B] [IsCommMonObj B] {β : B.left ⟶ A.left}
    {β₂ : (G2 B).left ⟶ (G2 A).left} (hβ : IsGrpPullback B A t β) (hsq : IsSquare β β₂) :
    ∃ L : LB B.left, L.IsLB ∧ LBIso (abelian₂ B L) (P.pull β₂) := by
  obtain ⟨C, _, _, c, c₂, hc, hsqc, L, hL, H⟩ := h
  let φ : B.left ⟶ C.left := hc.1.lift β B.hom hβ.1.w
  have hφc : φ ≫ c = β := hc.1.lift_fst _ _ _
  have hφw : φ ≫ C.hom = B.hom ≫ 𝟙 T := (hc.1.lift_snd _ _ _).trans (Category.comp_id _).symm
  have hφ : IsGrpPullback B C (𝟙 T) φ := hc.cancel (hβ.congr (Category.id_comp t).symm hφc.symm) hφw
  obtain ⟨φ₂, hφ₂⟩ := GlobalTheory.ZM.SiegPull.exists_isSquare hφw
  have e : φ₂ ≫ c₂ = β₂ :=
    GlobalTheory.ZM.SiegPull.isSquare_unique (GlobalTheory.ZM.SiegPull.isSquare_comp hφ₂ hsqc) hsq hφc
  have hLφ : (L.pull φ).IsLB := pull_isLB hL φ
  refine ⟨L.pull φ, hLφ, ?_⟩
  have h1 : LBIso (abelian₂ B (L.pull φ)) ((abelian₂ C L).pull φ₂) :=
    GlobalTheory.ZM.SiegPull.lbIso_lam_pull hφ (GlobalTheory.GtBaseChange.lbIso_refl hLφ) hφ₂
  have h2 : LBIso ((abelian₂ C L).pull φ₂) (P.pull (φ₂ ≫ c₂)) := GlobalTheory.ZM.SiegPull.lbIso_pull_comp H φ₂
  rw [e] at h2
  exact LBIso.trans (LB.isLB_linComb hLφ _ _) (pull_isLB (LB.isLB_linComb hL _ _) _) (pull_isLB hP _) h1 h2

theorem root_of_closedFibre (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hR : IsAdicComplete (maximalIdeal R) R) (B : Over (Sp R)) [GrpObj B] [IsCommMonObj B]
    (hB : IsAbelianScheme B) (P : LB (G2 B).left) (hP : P.IsLB)
    (g1 : ∃ u : (P.pull (lift (1 : B ⟶ B) (𝟙 B)).left).Gen, u.IsGen)
    (g2 : ∃ u : (P.pull (lift (𝟙 B) (1 : B ⟶ B)).left).Gen, u.IsGen)
    (gamp : RelAmple B (P.pull (lift (𝟙 B) (𝟙 B)).left))
    (h0 : ∃ L₀ : LB (thickObj R (maximalIdeal R) 0 B).left, L₀.IsLB ∧
      ∀ b₂ : (G2 (thickObj R (maximalIdeal R) 0 B)).left ⟶ (G2 B).left,
        IsSquare (pullback.fst B.hom (thick R (maximalIdeal R) 0)) b₂ →
          LBIso (abelian₂ (thickObj R (maximalIdeal R) 0 B) L₀) (P.pull b₂)) :
    ∃ L : LB B.left, L.IsLB ∧ LBIso (abelian₂ B L) P := by
  let Q : ∀ e, LB (thickObj R (maximalIdeal R) e B).left → Prop := fun e L => L.IsLB ∧
    ∀ b₂ : (G2 (thickObj R (maximalIdeal R) e B)).left ⟶ (G2 B).left,
      IsSquare (pullback.fst B.hom (thick R (maximalIdeal R) e)) b₂ →
        LBIso (abelian₂ (thickObj R (maximalIdeal R) e B) L) (P.pull b₂)
  have step : ∀ e (L : {L // Q e L}), ∃ L' : {L' // Q (e + 1) L'},
      LBIso (L'.1.pull (thickMap R (maximalIdeal R) e B)) L.1 := fun e L => by
    obtain ⟨L', h1', h2', h3'⟩ := GlobalTheory.T.line_bundle_thickening_square_theorem R B hB P hP g1 g2 e L.1 L.2.1 L.2.2
    exact ⟨⟨L', h1', h2'⟩, h3'⟩
  choose F hF using step
  obtain ⟨L₀, hL₀⟩ := h0
  let N : ∀ e, {L // Q e L} := fun e => Nat.rec ⟨L₀, hL₀⟩ (fun e L => F e L) e
  have hN : ∀ e, LBIso ((N (e + 1)).1.pull (thickMap R (maximalIdeal R) e B)) (N e).1 := fun e => hF e (N e)
  have hproj : GlobalTheory.AbLaw.IsProjBy B.hom := GlobalTheory.WtTower.isProjBy_of_relAmple B (pull_isLB hP _) gamp
  obtain ⟨M, hM, HM⟩ := GlobalTheory.LBAlgComplete.exists_lineBundle_of_reductions GlobalTheory.formalAlgebraisation R
    (maximalIdeal R) hR B hproj (fun e => thickObj R (maximalIdeal R) e B)
    (fun e => thickMap R (maximalIdeal R) e B) (fun e => pullback.fst B.hom (thick R (maximalIdeal R) e))
    (fun e => (isGrpPullback_pullback B (thick R (maximalIdeal R) e)).1)
    (fun e => (pullback.lift_fst _ _ _).trans (Category.comp_id _)) (fun e => (N e).1) (fun e => (N e).2.1)
    (fun e => (hN e).symm)
  haveI := GlobalTheory.WtTower.isLocalRing_quotient_pow R 0
  obtain ⟨b₂, hb₂⟩ := GlobalTheory.ZM.SiegPull.exists_isSquare (isGrpPullback_pullback B (thick R (maximalIdeal R) 0)).1.w
  exact ⟨M, hM, GlobalTheory.T.lineBundleIso_mumfordLambda_of_local_quotient R (R ⧸ maximalIdeal R ^ (0 + 1)) (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective B (thickObj R (maximalIdeal R) 0 B) (pullback.fst _ _) b₂ hB
    (isGrpPullback_pullback B _) hb₂ P hP g1 g2 M (N 0).1 hM (N 0).2.1 (HM 0).symm ((N 0).2.2 b₂ hb₂)⟩

theorem root_of_residue : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R], IsAdicComplete (maximalIdeal R) R → ∀ t : Sp R ⟶ S, Root A P (spMap (residue R) ≫ t) → Root A P t := by
  intro S A _ _ hA P hP h1 h2 hamp R _ _ _ hR t hroot
  obtain ⟨B, _, β, hβ⟩ := GlobalTheory.FlagTan.exists_isGrpPullback A t
  have hB : IsAbelianScheme B := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hβ
  haveI : IsCommMonObj B := hB.comm
  obtain ⟨β₂, hsq⟩ := GlobalTheory.ZM.SiegPull.exists_isSquare hβ.1.w
  obtain ⟨g1, g2⟩ := GlobalTheory.T.axisTrivial_lineBundle_groupPullback S (Sp R) A P hP h1 h2 t B β β₂ hβ hsq
  have gamp := GlobalTheory.T.relAmple_diagonal_pullback_baseChange S (Sp R) A hA P hP hamp t B β β₂ hβ.1 hsq
  have le : maximalIdeal R ≤ maximalIdeal R ^ (0 + 1) := by rw [zero_add, pow_one]
  have ethick : thick R (maximalIdeal R) 0 =
      spMap (Ideal.Quotient.factor le) ≫ spMap (residue R) := by
    simp only [thick, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hres : Root A P (thick R (maximalIdeal R) 0 ≫ t) := by
    rw [ethick, Category.assoc]
    exact hroot.comp hA _
  have hY := isGrpPullback_pullback B (thick R (maximalIdeal R) 0)
  obtain ⟨b₂, hb₂⟩ := GlobalTheory.ZM.SiegPull.exists_isSquare hY.1.w
  obtain ⟨L₀, hL₀, H₀⟩ := root_given hP hres (hY.comp hβ) (GlobalTheory.ZM.SiegPull.isSquare_comp hb₂ hsq)
  obtain ⟨L, hL, HL⟩ := root_of_closedFibre R hR B hB (P.pull β₂) (pull_isLB hP _) g1 g2 gamp
    ⟨L₀, hL₀, fun b₂' hb₂' => by
      have e : b₂' = b₂ := GlobalTheory.ZM.SiegPull.isSquare_unique hb₂' hb₂ rfl
      subst e
      exact LBIso.trans (LB.isLB_linComb hL₀ _ _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) H₀
        (GlobalTheory.ZM.SiegPull.lbIso_pull_comp (GlobalTheory.GtBaseChange.lbIso_refl (pull_isLB hP β₂)) b₂').symm⟩
  exact ⟨B, inferInstance, inferInstance, β, β₂, hβ, hsq, L, hL, HL⟩

end GlobalTheory.PolRootComplete
