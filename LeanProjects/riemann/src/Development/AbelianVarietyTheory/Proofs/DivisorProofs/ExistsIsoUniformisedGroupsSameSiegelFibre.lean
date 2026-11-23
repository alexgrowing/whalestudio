import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem exists_iso_of_overPt : ∀ {X : Scheme.{0}} {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre g n ζ sX) (R : Type) [CommRing R] [IsDomain R] (J : Ideal R), AdmBase R J → ∀ (D₁ : DegData R J) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre J D₁ A₁ G₁) (D₂ : DegData R J) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre J D₂ A₂ G₂), IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (y : Sp (FractionRing R) ⟶ X) (α₁ : A₁.A.left ⟶ c.A.left) (α₂ : A₂.A.left ⟶ c.A.left), OverPt c A₁ y α₁ → OverPt c A₂ y α₂ → ∃ (a : G₁ ≅ G₂) (cA : A₁.A ≅ A₂.A), IsMonHom a.hom ∧ IsMonHom cA.hom ∧ Gen₀ U₁ U₂ a.hom cA.hom ∧ cA.hom.left ≫ α₂ = α₁ ∧ LBIso (abelian₂ A₁.A A₁.L) ((abelian₂ A₂.A A₂.L).pull (lift (fst A₁.A A₁.A ≫ cA.hom) (snd A₁.A A₁.A ≫ cA.hom) : G2 A₁.A ⟶ G2 A₂.A).left) := by
  intro X g n B _ ζ sX c R _ _ J hR D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ hG₁ hG₂ y α₁ α₂ hO₁ hO₂
  haveI : IsNoetherianRing R := hR.1
  haveI : IsIntegrallyClosed R := hR.2.2.1
  obtain ⟨hp₁, β₁, hsq₁, hL₁⟩ := hO₁
  obtain ⟨hp₂, β₂, hsq₂, hL₂⟩ := hO₂
  obtain ⟨cA, hcA, hcα⟩ := grpPullback_iso hp₁ hp₂
  haveI := U₁.gen_hom
  haveI := U₂.gen_hom
  haveI := hcA
  let e : (Over.pullback (jK R)).obj G₁ ≅ (Over.pullback (jK R)).obj G₂ := U₁.gen ≪≫ cA ≪≫ U₂.gen.symm
  haveI : IsMonHom e.hom := by
    show IsMonHom (U₁.gen.hom ≫ cA.hom ≫ U₂.gen.inv)
    infer_instance
  obtain ⟨a, ⟨ha, hae⟩, -⟩ :=
    GlobalTheory.SemiAbExtDomain.existsUnique_iso_extension_generic (FractionRing R) G₁ G₂ hG₁ hG₂ e
  refine ⟨a, cA, ha, hcA, ?_, hcα, ?_⟩
  · show (Over.pullback (jK R)).map a.hom ≫ U₂.gen.hom = U₁.gen.hom ≫ cA.hom
    rw [show (Over.pullback (jK R)).map a.hom = e.hom from hae]
    simp [e]
  · set β := (lift (fst A₁.A A₁.A ≫ cA.hom) (snd A₁.A A₁.A ≫ cA.hom) : G2 A₁.A ⟶ G2 A₂.A).left with hβdef
    have hβ : β ≫ β₂ = β₁ := by
      have h1 : (β ≫ β₂) ≫ (fst c.A c.A).left = β₁ ≫ (fst c.A c.A).left := by
        rw [Category.assoc, hsq₂.1, hsq₁.1, ← Category.assoc, hβdef, ← Over.comp_left, lift_fst, Over.comp_left,
          Category.assoc, hcα]
      have h2 : (β ≫ β₂) ≫ (snd c.A c.A).left = β₁ ≫ (snd c.A c.A).left := by
        rw [Category.assoc, hsq₂.2, hsq₁.2, ← Category.assoc, hβdef, ← Over.comp_left, lift_snd, Over.comp_left,
          Category.assoc, hcα]
      simp only [Over.fst_left, Over.snd_left] at h1 h2
      exact pullback.hom_ext h1 h2
    have iL₁ : (abelian₂ A₁.A A₁.L).IsLB := LB.isLB_linComb A₁.isLB _ _
    have iL₂ : ((abelian₂ A₂.A A₂.L).pull β).IsLB := pull_isLB (LB.isLB_linComb A₂.isLB _ _) _
    have iP₁ : (c.P.pull β₁).IsLB := pull_isLB c.isLB _
    have iP₂ : ((c.P.pull β₂).pull β).IsLB := pull_isLB (pull_isLB c.isLB _) _
    have h₃ : LBIso ((abelian₂ A₂.A A₂.L).pull β) ((c.P.pull β₂).pull β) :=
      LBIso.chartPull (chartPullPull _ β) (chartPullPull _ β) hL₂
    exact hL₁.trans iL₁ iP₁ iL₂ ((GlobalTheory.ClosedPol.lbIso_pull_comp c.isLB β₂ β β₁ hβ).trans iP₁ iP₂ iL₂ h₃.symm)

end GlobalTheory.TInj
