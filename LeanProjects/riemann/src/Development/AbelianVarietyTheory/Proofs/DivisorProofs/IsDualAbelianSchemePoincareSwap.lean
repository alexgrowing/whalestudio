import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualPoincareLeftKernelTrivialAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualAbelianSchemePoincareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfIsDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomOfClassifying
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearIsIsoOfIsProperOfFinitePresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDualOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLeftFst
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsoPolarisedAbelianSchemesDvrOfFieldExtens
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BidualAbelian

theorem isAdditive_swap_swap {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] {P : LB (A ⊗ B).left}
    (hP : P.IsLB) (h : IsAdditive P) : IsAdditive (swap (swap P)) := by
  have hs : (swap P).IsLB := pull_isLB hP _
  have hss : (swap (swap P)).IsLB := pull_isLB hs _
  refine (isAdditive_iff hss).2 fun Y a a' t ↦ ?_
  rw [evc_swap hs hss, evc_swap hs hss, evc_swap hs hss, evc_swap hP hs, evc_swap hP hs, evc_swap hP hs]
  exact (isAdditive_iff hP).1 h Y a a' t

theorem fibre_isIso : ∀ (S : Scheme.{0}) (A B C : Over S) [GrpObj A] [GrpObj B] [GrpObj C] (P : LB (A ⊗ B).left)
    (Q : LB (B ⊗ C).left) (κ : A ⟶ C), IsAbelianScheme A → IsAbelianScheme B → IsAbelianScheme C → DimLe A B →
    DimLe B C → IsDual A B P → IsDual B C Q → IsMonHom κ → LBIso (swap P) (ev Q (fst B A) (snd B A ≫ κ)) →
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ S), IsIso ((Over.pullback t).map κ) := by
  intro S A B C _ _ _ P Q κ hA hB hC hAB hBC hd hQ hm e Ω _ _ t
  have hA' := GlobalTheory.IsoOverField.isAbelianScheme_pullback t A hA
  have hB' := GlobalTheory.IsoOverField.isAbelianScheme_pullback t B hB
  have hC' := GlobalTheory.IsoOverField.isAbelianScheme_pullback t C hC
  obtain ⟨g, hgA⟩ := GlobalTheory.AbelianDim.exists_relDim Ω ((Over.pullback t).obj A) hA'
  have hgB : SmoothOfRelativeDimension g ((Over.pullback t).obj B).hom := hAB g (Sp Ω) t hgA
  have hgC : SmoothOfRelativeDimension g ((Over.pullback t).obj C).hom := hBC g (Sp Ω) t hgB
  have key : ∀ {X Y : Over S} (a : X ⟶ Y),
      ((Over.pullback t).map a).left ≫ pullback.fst Y.hom t = pullback.fst X.hom t ≫ a.left :=
    fun a ↦ pullback.lift_fst _ _ _
  let h : ((Over.pullback t).obj A ⊗ (Over.pullback t).obj B).left ⟶ (A ⊗ B).left :=
    (Functor.LaxMonoidal.μ (Over.pullback t) A B).left ≫ pullback.fst (A ⊗ B).hom t
  have h₁ : h ≫ (fst A B).left = (fst ((Over.pullback t).obj A) ((Over.pullback t).obj B)).left ≫
      pullback.fst A.hom t := by
    simp only [h, Category.assoc]
    rw [← key, ← Category.assoc, ← Over.comp_left]
    rw [show Functor.LaxMonoidal.μ (Over.pullback t) A B ≫ (Over.pullback t).map (fst A B) = fst _ _ by simp]
  have h₂ : h ≫ (snd A B).left = (snd ((Over.pullback t).obj A) ((Over.pullback t).obj B)).left ≫
      pullback.fst B.hom t := by
    simp only [h, Category.assoc]
    rw [← key, ← Category.assoc, ← Over.comp_left]
    rw [show Functor.LaxMonoidal.μ (Over.pullback t) A B ≫ (Over.pullback t).map (snd A B) = snd _ _ by simp]
  have hP' : (P.pull h).IsLB := pull_isLB hd.isLB _
  have hd' : IsDual _ _ (P.pull h) := IsDual.baseChange (isGrpPullback_pullback A t) (isGrpPullback_pullback B t)
    h₁ h₂ hP' ((cls_eq_iff hP' hP').1 rfl) hd
  have ker := GlobalTheory.T.dualPoincare_left_kernel_trivial_algClosed Ω _ _ g (P.pull h) hA' hB' hgA hgB hd'
  have hs : (swap P).IsLB := pull_isLB hd.isLB _
  have hE : (ev Q (fst B A) (snd B A ≫ κ)).IsLB := pull_isLB hQ.isLB _
  have ce : cls _ hs = cls _ hE := (cls_eq_iff hs hE).2 e
  have mono : Mono ((Over.pullback t).map κ) := by
    constructor
    intro T x y hxy
    have z1 : (x * y⁻¹) ≫ (Over.pullback t).map κ = 1 := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, hxy, mul_inv_cancel]
    have tr : Triv (ev (P.pull h) (fst T ((Over.pullback t).obj B) ≫ (x * y⁻¹)) (snd T ((Over.pullback t).obj B))) := by
      refine (triv_ev_iff hP' _ _).2 ?_
      let a : Over.mk (T ⊗ (Over.pullback t).obj B).hom ⟶ (Over.pullback t).obj A :=
        fst T ((Over.pullback t).obj B) ≫ (x * y⁻¹)
      let b : Over.mk (T ⊗ (Over.pullback t).obj B).hom ⟶ (Over.pullback t).obj B := snd T _
      let a₀ := pushP (isGrpPullback_pullback A t) (s₀ := (T ⊗ (Over.pullback t).obj B).hom ≫ t) rfl a
      let b₀ := pushP (isGrpPullback_pullback B t) (s₀ := (T ⊗ (Over.pullback t).obj B).hom ≫ t) rfl b
      have e1 : evc hP' a b = evc hd.isLB a₀ b₀ := evc_eq h₁ h₂ hd.isLB hP' ((cls_eq_iff hP' hP').1 rfl) a b a₀ b₀ rfl rfl
      refine e1.trans ?_
      have one : a₀ ≫ κ = 1 := by
        apply Over.OverMorphism.ext
        rw [Over.comp_left]
        show (a.left ≫ pullback.fst A.hom t) ≫ κ.left = _
        rw [Category.assoc, ← key, ← Category.assoc, ← Over.comp_left]
        show (fst T ((Over.pullback t).obj B) ≫ (x * y⁻¹) ≫ (Over.pullback t).map κ).left ≫ _ = _
        rw [z1, MonObj.comp_one]
        exact one_left_comp (isGrpPullback_pullback C t) rfl
      have e2 : evc hs b₀ a₀ = evc hE b₀ a₀ := by unfold evc; rw [ce]
      rw [← evc_swap hd.isLB hs, e2, evc_ev hQ.isLB, lift_fst, lift_snd_assoc, one, evc_one_right hQ.isLB hQ.zero]
    have hz := ker T (x * y⁻¹) tr
    calc x = x * y⁻¹ * y := (inv_mul_cancel_right x y).symm
      _ = y := by rw [hz, _root_.one_mul]
  exact GlobalTheory.AbMonoIso.isIso_of_mono (Sp Ω) _ _ hA' hC' g g hgA hgC le_rfl _ inferInstance mono

theorem isDual_swap : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left),
    IsAbelianScheme A → IsAbelianScheme B → DimLe A B → IsDual A B P → IsDual B A (swap P) := by
  intro S A B _ _ P hA hB hAB hd
  obtain ⟨C, _, Q, hC, hBC, hQ⟩ := GlobalTheory.T.exists_dual_abelianScheme_poincare S B hB
  have hs : (swap P).IsLB := pull_isLB hd.isLB _
  have ha : IsAdditive (swap P) := isDual_isAdditive_swap S A B P hB hd
  obtain ⟨κ, e, -⟩ := hQ.univ A (swap P) hs ha
  have hm : IsMonHom κ := isMonHom_of_classifying S B A C (swap P) Q hQ
    (isDual_isAdditive_swap S B C Q hC hQ) hs (isAdditive_swap_swap hd.isLB hd.additive) κ e
  have hi : IsIso κ := isIso_of_isIso_pullback hA hC κ fun Ω _ _ t ↦
    fibre_isIso S A B C P Q κ hA hB hC hAB hBC hd hQ hm e Ω t
  exact transport S B A C (swap P) Q hQ hs κ hi hm e

end GlobalTheory.BidualAbelian
