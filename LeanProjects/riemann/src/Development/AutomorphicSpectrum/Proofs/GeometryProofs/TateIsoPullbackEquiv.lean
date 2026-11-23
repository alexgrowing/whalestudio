import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.MemEigSpOfMemHtDual
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFullLevelAt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AdjointBaseChange

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.XR
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.XR

theorem tateIsoAt_move : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (m : SABMap t' t f) (k : Type) [Field k] (x' : Sp k ⟶ X') (x : Sp k ⟶ X), x = x' ≫ f → (∀ I : TateIsoAt D t x, ∃ I' : TateIsoAt D t' x', I'.ζ = I.ζ ∧ ∀ n a, (I'.ev n a).left ≫ m.φ = (I.ev n a).left) ∧ ∀ I' : TateIsoAt D t' x', ∃ I : TateIsoAt D t x, I'.ζ = I.ζ ∧ ∀ n a, (I'.ev n a).left ≫ m.φ = (I.ev n a).left := by
  intro E _ _ _ H D X X' t t' f m k _ x' x hx
  subst hx
  have hL : LBIso t'.PP.L (t.PP.L.pull m.φ) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv m.cart (Over.mk x') (x' ≫ f) rfl
  have eact : ∀ c y, e (y ≫ t'.act.act c) = e y ≫ t.act.act c := fun c y => Over.OverMorphism.ext (by
    rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, m.act, Category.assoc])
  have eact' : ∀ c y, e.symm (y ≫ t.act.act c) = e.symm y ≫ t'.act.act c := fun c y =>
    e.injective (by rw [eact, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply])
  have weil : ∀ (n : ℤ) (y y' : Over.mk x' ⟶ t'.G) (c : Γ(Sp k, ⊤)ˣ),
      Out.WeilIs t'.G t'.PP.L n y y' c ↔ Out.WeilIs t.G t.PP.L n (e y) (e y') c := fun n y y' c =>
    GlobalTheory.weilIs_grpPullback_of_comm' _ _ _ _ _ m.φ _ _ t.PP.isLB t'.PP.isLB m.cart hL (Over.mk x') n y y' (e y) (e y') c
      (he y) (he y')
  refine ⟨fun I => ⟨GlobalTheory.PELPeriod.tateIsoMap I e.symm eact' fun n y y' c h => (weil n _ _ _).2 ?_, rfl,
    fun n a => ?_⟩, fun I' => ⟨GlobalTheory.PELPeriod.tateIsoMap I' e eact fun n y y' c h => (weil n _ _ _).1 h, rfl,
    fun n a => (he _).symm⟩⟩
  · rwa [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  · show (e.symm (I.ev n a)).left ≫ m.φ = _
    rw [← he, MulEquiv.apply_symm_apply]

end GlobalTheory.CompanionTheory.Ar.XR
