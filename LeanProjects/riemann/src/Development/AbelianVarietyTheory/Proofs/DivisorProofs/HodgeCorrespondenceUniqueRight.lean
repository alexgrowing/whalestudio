import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeIntoDeRhamInjectiveImports
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.LieVB

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HodgeSub

open MonoidalCategory MonObj

theorem unit_base_change_fst {S S' : Scheme.{0}} (f : S' ⟶ S) :
    (Functor.LaxMonoidal.ε (Over.pullback f)).left ≫ pullback.fst (𝟙_ (Over S)).hom f = f := by
  have h1 : pullback.fst (𝟙_ (Over S)).hom f ≫ (𝟙_ (Over S)).hom =
      pullback.snd (𝟙_ (Over S)).hom f ≫ f := pullback.condition
  have h2 := Over.w (Functor.LaxMonoidal.ε (Over.pullback f))
  have h3 : (𝟙_ (Over S)).hom = 𝟙 S := rfl
  have h4 : (𝟙_ (Over S')).hom = 𝟙 S' := rfl
  rw [h3] at h1
  erw [Category.comp_id] at h1
  erw [h1, ← Category.assoc]
  change (Functor.LaxMonoidal.ε (Over.pullback f)).left ≫
    ((Over.pullback f).obj (𝟙_ (Over S))).hom ≫ f = f
  rw [← Category.assoc, h2, h4]
  erw [Category.id_comp]

theorem unit_section_affine_fst {T : Scheme.{0}} (A : Over T) [GrpObj A] {V : T.Opens} (hV : IsAffineOpen V) :
    η[onAff A hV].left ≫ pullback.fst A.hom hV.fromSpec =
      hV.fromSpec ≫ GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.zeroSec A := by
  set f := hV.fromSpec
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.zeroSec, Functor.obj.η_def, Over.comp_left, Category.assoc]
  rw [show ((Over.pullback f).map η[A]).left ≫ pullback.fst A.hom f =
      pullback.fst (𝟙_ (Over T)).hom f ≫ η[A].left from pullback.lift_fst _ _ _]
  rw [← Category.assoc, unit_base_change_fst]

theorem corr_unique : GlobalTheory.CovTop.Hypotheses2 → ∀ (T : Scheme.{0}) (A : Over T) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A, V)) (c c' : primDR (onAff A hV)),
      GlobalTheory.HodgeSub.Corr A hV s c → GlobalTheory.HodgeSub.Corr A hV s c' → c = c' := by
  intro P T A _ g hA hg V hV s c c' hc hc'
  have hA' : IsAbelianScheme (onAff A hV) := GlobalTheory.isAbelianScheme_pullback_obj _ A hA
  have hg' : SmoothOfRelativeDimension g (onAff A hV).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hg
  obtain ⟨hL, -⟩ := P.p5.2.1 Γ(T, V) (onAff A hV) g hA' hg'
  obtain ⟨-, hproj, -⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim P.p5.1 hA' hg'
  have key : ∀ h : HdR (onAff A hV), h c = h c' := by
    intro h
    obtain ⟨v, hv, -⟩ := hL.1 h
    have w : (v.left ≫ pullback.fst A.hom hV.fromSpec) ≫ A.hom =
        (Pdiv.specO Γ(T, V) (DualNumber Γ(T, V))).hom ≫ hV.fromSpec := by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact congrArg (· ≫ hV.fromSpec) (Over.w v)
    have we : sec (epsZero Γ(T, V)) ≫ v.left ≫ pullback.fst A.hom hV.fromSpec =
        hV.fromSpec ≫ GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.zeroSec A := by
      rw [← Category.assoc]
      have ht := hv.1
      unfold IsTangent at ht
      erw [ht]
      exact unit_section_affine_fst A hV
    rw [hc v h hv w we, hc' v h hv w we]
  have h0 := (Module.forall_dual_apply_eq_zero_iff Γ(T, V) (c - c')).1
    (fun h => by rw [map_sub, key, sub_self])
  exact sub_eq_zero.1 h0

end GlobalTheory.HodgeSub
