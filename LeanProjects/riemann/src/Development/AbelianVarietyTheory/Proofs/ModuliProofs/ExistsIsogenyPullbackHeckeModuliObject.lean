import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.KerScheme
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsHomFamilyBaseChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

noncomputable section

namespace GlobalTheory.HkFam

theorem lbIso_pow_pull_square {B B' G G' : Scheme.{0}} {β : B' ⟶ B} {π : G' ⟶ G} {φ : B ⟶ G} {φ' : B' ⟶ G'}
    (h : φ' ≫ π = β ≫ φ) {P : LB G} {P' : LB G'} {M : LB B} {M' : LB B'} (hP : P.IsLB) (hP' : P'.IsLB)
    (hM : M.IsLB) (hM' : M'.IsLB) (eP : LBIso P' (P.pull π)) (eM : LBIso M' (M.pull β)) {n : ℕ}
    (hI : LBIso (lbPow M n) (P.pull φ)) : LBIso (lbPow M' n) (P'.pull φ') := by
  obtain ⟨w, hw⟩ := eP
  have e₁ : LBIso (P'.pull φ') (P.pull (φ' ≫ π)) :=
    iso_linComb ((isGen_iff w).1 hw) (fun _ : PUnit => φ') (fun _ => 1)
  have e₂ : LBIso (P.pull (φ' ≫ π)) ((P.pull φ).pull β) :=
    LBIso.chartPull (chartPullSame P _ _ _ β fun _ => h) (chartPullPull _ β) (lbIso_refl (pull_isLB hP φ))
  have e₃ := LBIso.trans (pull_isLB hP' _) (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) e₁ e₂
  refine LBIso.trans (isLB_lbPow hM' _) (pull_isLB (pull_isLB hP _) _) (pull_isLB hP' _) ?_ e₃.symm
  exact LBIso.trans (isLB_lbPow hM' _) (isLB_lbPow (pull_isLB hM _) _) (pull_isLB (pull_isLB hP _) _)
    (lbIso_lbPow eM _) (LBIso.chartPull (chartPullPowPull M β _) (chartPullPull _ β) hI)

theorem KerSet.pull {S S' : Scheme.{0}} {f : S' ⟶ S} {B G : Over S} {B' G' : Over S'} [GrpObj G] [GrpObj G']
    {β : B'.left ⟶ B.left} {π : G'.left ⟶ G.left} (hβ : β ≫ B.hom = B'.hom ≫ f) (hπ : IsGrpPullback G' G f π)
    {ψ : B ⟶ G} {ψ' : B' ⟶ G'} (h : ψ'.left ≫ π = β ≫ ψ.left) {K : Set B.left} (hK : KerSet ψ K) :
    KerSet ψ' (β ⁻¹' K) := by
  intro k _ _ x z
  have e : pushHom hπ (Over.mk x) (z ≫ ψ') = pushPt hβ z ≫ ψ := Over.OverMorphism.ext (by
    show (z.left ≫ ψ'.left) ≫ π = (z.left ≫ β) ≫ ψ.left
    rw [Category.assoc, Category.assoc, h])
  have e₁ : z ≫ ψ' = 1 ↔ pushPt hβ z ≫ ψ = 1 := by
    rw [← e]
    refine ⟨fun q => by rw [q, map_one], fun q => PureType.eq_of_comp_eq hπ.1 ?_⟩
    exact congrArg (fun u => u.left) (q.trans (map_one (pushHom hπ (Over.mk x))).symm)
  refine e₁.trans ((hK k (x ≫ f) (pushPt hβ z)).trans ?_)
  show Set.range (z.left ≫ β) ⊆ K ↔ _
  simp only [Set.range_subset_iff, Set.mem_preimage, Scheme.Hom.comp_apply]

theorem isog_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (p : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp (KA l)) (s' : S' ⟶ Sp (KA l)) (f : S' ⟶ S) (o₁ o₂ : Ob D l s) (o₁' o₂' : Ob D l s') (n₁ : ObjMap o₁' o₁ f) (n₂ : ObjMap o₂' o₂ f) (ψ : o₁.t.G ⟶ o₂.t.G), (∃! ψ' : o₁'.t.G ⟶ o₂'.t.G, ψ'.left ≫ n₂.toSABMap.φ = n₁.toSABMap.φ ≫ ψ.left) ∧ ∀ ψ' : o₁'.t.G ⟶ o₂'.t.G, ψ'.left ≫ n₂.toSABMap.φ = n₁.toSABMap.φ ≫ ψ.left → (IsIsog o₁ o₂ p ψ → IsIsog o₁' o₂' p ψ') ∧ ∀ K, IsMonHom ψ → KerSet ψ K → KerSet ψ' (n₁.toSABMap.φ ⁻¹' K) := by
  intro E _ _ _ H D l p S S' s s' f o₁ o₂ o₁' o₂' n₁ n₂ ψ
  have c₁ := n₁.toSABMap.cart
  have c₂ := n₂.toSABMap.cart
  refine ⟨?_, fun ψ' h => ⟨?_, fun K _ hK => KerSet.pull c₁.1.w c₂ h hK⟩⟩
  · obtain ⟨ψ', h⟩ := PureType.exists_hom_over c₁.1.w c₂.1 ψ
    exact ⟨ψ', h, fun χ hχ => PureType.eq_of_comp_eq c₂.1 (hχ.trans h.symm)⟩
  rintro ⟨⟨h₁, h₂, h₃, h₄, h₅, h₆⟩, h₇⟩
  have sq : IsPullback n₁.toSABMap.φ ψ'.left ψ.left n₂.toSABMap.φ :=
    IsPullback.of_bot (by rw [Over.w, Over.w]; exact c₁.1) h.symm c₂.1
  have lev : ∀ {u : 𝟙_ (Over S) ⟶ o₁.t.G} {v : 𝟙_ (Over S) ⟶ o₂.t.G} {u' : 𝟙_ (Over S') ⟶ o₁'.t.G}
      {v' : 𝟙_ (Over S') ⟶ o₂'.t.G}, u'.left ≫ n₁.toSABMap.φ = f ≫ u.left → v'.left ≫ n₂.toSABMap.φ = f ≫ v.left →
      u ≫ ψ = v → u' ≫ ψ' = v' := fun {u v u' v'} hu hv e => PureType.eq_of_comp_eq c₂.1 (by
    refine Eq.trans ?_ hv.symm
    rw [← e, Over.comp_left, Over.comp_left, Category.assoc]
    exact (congrArg (u'.left ≫ ·) h).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ ψ.left) hu).trans (Category.assoc _ _ _))))
  refine ⟨⟨PureType.isMonHom_over c₁ c₂ h, MorphismProperty.of_isPullback (P := @IsFinite) sq h₂,
    MorphismProperty.of_isPullback (P := @Etale) sq h₃, MorphismProperty.of_isPullback (P := @Surjective) sq h₄,
    fun a => PureType.eq_of_comp_eq c₂.1 ?_, ?_⟩, fun p' hp a =>
    ⟨lev (n₁.eta _) (n₂.eta _) (h₇ p' hp a).1, lev (n₁.etaA _) (n₂.etaA _) (h₇ p' hp a).2⟩⟩
  · have e : (o₁.t.act.act a).left ≫ ψ.left = ψ.left ≫ (o₂.t.act.act a).left := congrArg (fun u => u.left) (h₅ a)
    have h' : ψ'.left ≫ n₂.cm.F = n₁.cm.F ≫ ψ.left := h
    rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, n₂.act, h', reassoc_of% h',
      reassoc_of% (n₁.act a), e]
  · exact lbIso_pow_pull_square h o₂.t.PP.isLB o₂'.t.PP.isLB o₁.t.PP.isLB o₁'.t.PP.isLB
      (n₂.lin.imp fun _ q => q.1) (n₁.lin.imp fun _ q => q.1) h₆

end GlobalTheory.HkFam

end
