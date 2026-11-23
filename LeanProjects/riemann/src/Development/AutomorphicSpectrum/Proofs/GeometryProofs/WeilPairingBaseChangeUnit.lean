import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ThetaMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

private theorem gm_unitRes' {S : Scheme} {T : Over S} (V : T.left.Opens) {Z : Scheme}
    (r : Z ⟶ (Out.overRes V).left) (z : Z) (a : (↑(T.left.presheaf.obj (Opposite.op ⊤)))ˣ) :
    gm r z ⊤ (Out.unitRes V a) = gm (r ≫ V.ι) z ⊤ a :=
  gm_pull r V.ι z ⊤ trivial a

private theorem unitOn_units_map {k M : Type} [Field k] [Field M] (j : k →+* M) (c : kˣ) :
    unitOn (Units.map j.toMonoidHom c) = Units.map (spMap j).appTop.hom (unitOn c) := by
  ext
  show (Scheme.ΓSpecIso (CommRingCat.of M)).inv.hom (j c) =
    (Spec.map (CommRingCat.ofHom j)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)
  exact congrArg (fun g => g.hom (c : k)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))

theorem weilIs_fieldExt : ∀ {X : Scheme.{0}} (G : Over X) [GrpObj G] [IsCommMonObj G] (L : LB G.left), L.IsLB → ∀ (k M : Type) [Field k] [Field M] (j : k →+* M) (q : Sp k ⟶ X) (q' : Sp M ⟶ X), q' = spMap j ≫ q → ∀ (n : ℤ) (x y : Over.mk q ⟶ G) (x' y' : Over.mk q' ⟶ G), x'.left = spMap j ≫ x.left → y'.left = spMap j ≫ y.left → ∀ (c : kˣ) (c' : Mˣ), Out.WeilIs G L n x y (unitOn c) → Out.WeilIs G L n x' y' (unitOn c') → c' = Units.map j.toMonoidHom c := by
  intro X G _ _ L hL k M _ _ j q q' hq n x y x' y' hx hy c c' h1 h2
  let p' : (Over.mk q').left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum M)
  obtain ⟨V', hpV', -, H2⟩ := h2 p'
  obtain ⟨V, hpV, ⟨θx₀, θy₀, hθx₀, hθy₀⟩, H1'⟩ := h1 ((spMap j).base p')
  have H1 := H1' θx₀ θy₀ hθx₀ hθy₀
  have key : ∀ I : Ideal k, I.IsPrime → I = ⊥ := fun I _ => Ideal.eq_bot_of_prime I
  have hall : ∀ z : (Over.mk q).left, z ∈ V := by
    intro z
    have hz : z = (spMap j).base p' := by
      apply PrimeSpectrum.ext
      exact (key z.asIdeal z.isPrime).trans (key _ ((spMap j).base p').isPrime).symm
    rw [hz]; exact hpV
  let τ : (Out.overRes V').left ⟶ (Out.overRes V).left :=
    IsOpenImmersion.lift V.ι (V'.ι ≫ spMap j) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨z, rfl⟩
      exact hall _)
  have hτι : τ ≫ V.ι = V'.ι ≫ spMap j := IsOpenImmersion.lift_fac _ _ _
  have hτ : τ ≫ (Out.overRes V).hom = (Out.overRes V').hom ≫ 𝟙 X := by
    change τ ≫ (V.ι ≫ q) = (V'.ι ≫ q') ≫ 𝟙 X
    rw [← Category.assoc, hτι, hq]
    simp
  haveI : IsMonHom (Iso.refl G).hom := by
    show IsMonHom (𝟙 G)
    infer_instance
  have hp : IsGrpPullback G G (𝟙 X) (𝟙 G.left) :=
    (isGrpPullback_of_iso (Iso.refl G)).congr rfl (by simp)
  obtain ⟨w, hw⟩ : LBIso L (L.pull (𝟙 G.left)) :=
    LBIso.chartPull (chartPullId L) (chartPullPull L (𝟙 _) (𝟙 _) rfl) (GlobalTheory.PolBaseChange.lbIso_refl hL)
  have hxpt : τ ≫ θx₀.pt.left = (Out.overResι V' ≫ x').left ≫ 𝟙 G.left := by
    rw [hθx₀]
    change τ ≫ (V.ι ≫ x.left) = (V'.ι ≫ x'.left) ≫ 𝟙 G.left
    rw [hx, Category.comp_id, ← Category.assoc τ, hτι, Category.assoc]
  have hypt : τ ≫ θy₀.pt.left = (Out.overResι V' ≫ y').left ≫ 𝟙 G.left := by
    rw [hθy₀]
    change τ ≫ (V.ι ≫ y.left) = (V'.ι ≫ y'.left) ≫ 𝟙 G.left
    rw [hy, Category.comp_id, ← Category.assoc τ, hτι, Category.assoc]
  obtain ⟨θx, hθx, hPx⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_theta_move hp τ hτ hL hL w hw n (Out.overResι V' ≫ x') θx₀ hxpt
  obtain ⟨θy, hθy, hPy⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_theta_move hp τ hτ hL hL w hw n (Out.overResι V' ≫ y') θy₀ hypt
  have hgm : ∀ (Z : Scheme) (r : Z ⟶ (Out.overRes V').left) (z : Z),
      gm (r ≫ τ) z ⊤ (Out.unitRes V (unitOn c)) =
        gm r z ⊤ (Out.unitRes V' (unitOn (Units.map j.toMonoidHom c))) := by
    intro Z r z
    rw [gm_unitRes', gm_unitRes', unitOn_units_map]
    erw [gm_pull (r ≫ V'.ι) (spMap j) z ⊤ trivial (unitOn c)]
    rw [Category.assoc, hτι, Category.assoc]
  have HC := ReciprocityTheory.ChartRestriction.G.H1.commIsOf_move hp τ hτ hL hL w n θx₀ θy₀ θx θy
    (by rw [hθx]; exact hxpt) (by rw [hθy]; exact hypt) hPx hPy _ _ hgm H1
  have HC2 := H2 θx θy hθx hθy
  have heq := ReciprocityTheory.ChartRestriction.G.H1.commIsOf_unique hL θx θy _ _ HC2 HC
  let pt : (Out.overRes V').left := ⟨p', hpV'⟩
  have e := (gm_unitRes' V' (𝟙 (Out.overRes V').left) pt (unitOn c')).symm.trans
    ((congrArg (gm (𝟙 (Out.overRes V').left) pt ⊤) heq).trans
      (gm_unitRes' V' (𝟙 (Out.overRes V').left) pt _))
  have e' := (gm_val (𝟙 (Out.overRes V').left ≫ V'.ι) pt ⊤ trivial (unitOn c')).symm.trans
    ((congrArg Units.val e).trans
      (gm_val (𝟙 (Out.overRes V').left ≫ V'.ι) pt ⊤ trivial _))
  apply Units.ext
  refine (RingHom.injective
    (((Out.overRes V').left.presheaf.germ ((TopologicalSpace.Opens.map (𝟙 (Out.overRes V').left ≫ V'.ι).base).obj ⊤)
      pt trivial).hom.comp
      (((𝟙 (Out.overRes V').left ≫ V'.ι).app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of M)).inv.hom))) ?_
  have e'' := by simpa [unitOn] using e'
  exact e''

end GlobalTheory.CompanionTheory.Ar
