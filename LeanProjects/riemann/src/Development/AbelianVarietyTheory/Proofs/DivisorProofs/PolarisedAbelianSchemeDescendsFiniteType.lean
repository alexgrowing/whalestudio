import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsGPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegPreDataDescends
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleSpreadSubring
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.PolModel

open GlobalTheory.SiegApprox GlobalTheory.SiegelDescent ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

theorem polarised_descends : ∀ (B : Type) [CommRing B] (A : Over (Sp B)) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∃ (B₀ : Subring B) (A₀ : Over (Sp B₀)) (_ : GrpObj A₀) (_ : IsCommMonObj A₀) (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P₀ : LB (G2 A₀).left), Algebra.FiniteType ℤ B₀ ∧ IsAbelianScheme A₀ ∧ IsGrpPullback A A₀ (spMap B₀.subtype) φ ∧ IsSquare φ φ₂ ∧ P₀.IsLB ∧ LBIso P (P₀.pull φ₂) ∧ (∃ t : (P₀.pull (lift (1 : A₀ ⟶ A₀) (𝟙 A₀)).left).Gen, t.IsGen) ∧ (∃ t : (P₀.pull (lift (𝟙 A₀) (1 : A₀ ⟶ A₀)).left).Gen, t.IsGen) ∧ LBIso P₀ (P₀.pull (lift (snd A₀ A₀) (fst A₀ A₀)).left) ∧ Out.RelAmple A₀ (P₀.pull (lift (𝟙 A₀) (𝟙 A₀)).left) := by
  intro R _ A _ _ P hA hP rig₁ rig₂ hsymm hamp
  classical
  obtain ⟨S, B, _, _, φ, φ₂, P₀, -, hS, hB, hφ, sq, hP₀, hw⟩ := model_exists R A ∅ hA P hP
  have one : (1 : A ⟶ A).left ≫ φ = φ ≫ (1 : B ⟶ B).left := one_comp hφ A B φ hφ.1.w
  have idφ : (𝟙 A : A ⟶ A).left ≫ φ = φ ≫ (𝟙 B : B ⟶ B).left := by simp
  obtain ⟨F₁, hF₁⟩ := rig_descends R S A B φ φ₂ P P₀ (lift 1 (𝟙 A)) (lift 1 (𝟙 B)) hB hφ sq hP hP₀ hw
    (lift_square sq one idφ) rig₁
  obtain ⟨F₂, hF₂⟩ := rig_descends R S A B φ φ₂ P P₀ (lift (𝟙 A) 1) (lift (𝟙 B) 1) hB hφ sq hP hP₀ hw
    (lift_square sq idφ one) rig₂
  obtain ⟨F₃, hF₃⟩ := symm_descends R S A B φ φ₂ P P₀ hB hφ sq hP hP₀ hw hsymm
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing ℤ S
  have := hB.proper
  have : Flat B.hom := by have := hB.smooth; infer_instance
  obtain ⟨F₄, hF₄⟩ := GlobalTheory.AmpleApprox.relAmple_spread_subring (pull_isLB hP₀ _) hφ.1 (pull_isLB hP _)
    (GlobalTheory.SiegelPull.diag_iso sq hw) hamp
  let F : Finset R := F₁ ∪ F₂ ∪ F₃ ∪ F₄
  obtain ⟨R₁, hSR, hFR, hR₁⟩ := GlobalTheory.KeyTf.exists_finiteType_subring_adjoin R S F hS
  have hF₁R : (F₁ : Set R) ⊆ R₁ := fun x hx => hFR (by simp [F, hx])
  have hF₂R : (F₂ : Set R) ⊆ R₁ := fun x hx => hFR (by simp [F, hx])
  have hF₃R : (F₃ : Set R) ⊆ R₁ := fun x hx => hFR (by simp [F, hx])
  have hF₄R : (F₄ : Set R) ⊆ R₁ := fun x hx => hFR (by simp [F, hx])
  let iS : Sp R₁ ⟶ Sp S := spMap (Subring.inclusion hSR)
  have hiS : spMap S.subtype = spMap R₁.subtype ≫ iS := by
    simp only [iS, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hφ' : IsGrpPullback A B (spMap R₁.subtype ≫ iS) φ := hiS ▸ hφ
  have hφ₁ := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor iS (spMap R₁.subtype) hφ'
  set φ₁ := pullback.lift φ (A.hom ≫ spMap R₁.subtype) (by rw [hφ'.1.w, Category.assoc]) with hφ₁def
  let B₁ := (Over.pullback iS).obj B
  have hB₁ : IsAbelianScheme B₁ := GlobalTheory.isAbelianScheme_pullback_obj iS B hB
  have hψφ : φ₁ ≫ pφ iS B = φ := pullback.lift_fst _ _ _
  let φ₂₁ := (GlobalTheory.GenericSpread.sqMap hφ₁).left
  have sq₁ : IsSquare φ₁ φ₂₁ :=
    ⟨congrArg (fun z => z.left) (lift_fst (pushPt hφ₁.1.w (fst A A)) (pushPt hφ₁.1.w (snd A A))),
     congrArg (fun z => z.left) (lift_snd (pushPt hφ₁.1.w (fst A A)) (pushPt hφ₁.1.w (snd A A)))⟩
  have hψ₂ : φ₂₁ ≫ pφ₂ iS B = φ₂ := by
    apply adelic_GL2_ext_of_local_components
    · rw [Category.assoc, pφ₂_fst, ← Category.assoc, sq₁.1, Category.assoc, hψφ, sq.1]
    · rw [Category.assoc, pφ₂_snd, ← Category.assoc, sq₁.2, Category.assoc, hψφ, sq.2]
  have hP₁ : (P₀.pull (pφ₂ iS B)).IsLB := pull_isLB hP₀ _
  have r₁ := hF₁ R₁ hSR hF₁R (lift 1 (𝟙 B₁)) (lift_one_id iS B)
  have r₂ := hF₂ R₁ hSR hF₂R (lift (𝟙 B₁) 1) (lift_id_one iS B)
  have s₁ := hF₃ R₁ hSR hF₃R
  have sqp : IsSquare (G' := B₁) (G := B) (pφ iS B) (pφ₂ iS B) := ⟨pφ₂_fst iS B, pφ₂_snd iS B⟩
  have := hB₁.proper
  have amp : Out.RelAmple B₁ ((P₀.pull (pφ₂ iS B)).pull (lift (𝟙 B₁) (𝟙 B₁)).left) :=
    GlobalTheory.AmpleApprox.relAmple_of_lbIso_self (pull_isLB (pull_isLB hP₀ _) _) (pull_isLB hP₁ _)
      (GlobalTheory.SiegelPull.diag_iso sqp (GlobalTheory.lbIso_refl hP₁))
      (hF₄ R₁ hSR hF₄R B₁ (pφ iS B) (IsPullback.of_hasPullback B.hom iS))
  refine ⟨R₁, B₁, inferInstance, inferInstance, φ₁, φ₂₁, P₀.pull (pφ₂ iS B), hR₁, hB₁, hφ₁, sq₁, hP₁, ?_, r₁, r₂,
    s₁, amp⟩
  exact LBIso.trans hP (pull_isLB hP₀ _) (pull_isLB hP₁ _) hw
    (GlobalTheory.GenSpread.lbIso_pull_pull hP₀ φ₂₁ hψ₂.symm)

end GlobalTheory.PolModel
