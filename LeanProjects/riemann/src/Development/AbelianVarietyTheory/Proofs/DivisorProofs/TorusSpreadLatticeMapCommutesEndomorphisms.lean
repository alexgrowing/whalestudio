import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationEndomorphismClosedFibreTorusCharac
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationTorusMonoAndFactor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

noncomputable section

namespace GlobalTheory.Poinc.Sep.Spz

theorem endU_gtTorus_comp {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {D : DegData V (maximalIdeal V)}
    {A : PolAV (Sp (FractionRing V))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G)
    (E : EndU U.toUnifPre) {κ : Type} [Field κ] {a : V →+* κ} (ha : ∀ x ∈ maximalIdeal V ^ (0 + 1), a x = 0)
    {G₀ : Over (Sp κ)} [GrpObj G₀] {φ : G₀.left ⟶ G.left} (h : IsGrpPullback G₀ G (spMap a) φ) (f₀ : G₀ ⟶ G₀)
    (hf : f₀.left ≫ φ = φ ≫ E.aG.left) :
    GlobalTheory.TorusPart.gtTorus (U.gt 0) ha h ≫ f₀ =
      GlobalTheory.SplitTorus.torusMap (Sp κ) E.h ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) ha h := by
  obtain ⟨t, ht, hi⟩ := E.i_lin 0
  have htm := GlobalTheory.Poinc.Eq8.eq_torusMap_of_torusEndOf E.h t ht
  have k := GlobalTheory.TorusPart.isGrpPullback_thickLift ha h
  have e : f₀.left ≫ GlobalTheory.TorusPart.thickLift ha h =
      GlobalTheory.TorusPart.thickLift ha h ≫ ((Over.pullback (thick V (maximalIdeal V) 0)).map E.aG).left := by
    apply pullback.hom_ext
    · rw [Category.assoc, GlobalTheory.TorusPart.thickLift_fst, hf, Category.assoc]
      simp only [GlobalTheory.TorusPart.thickLift, Over.pullback_map_left]
      rw [pullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [GlobalTheory.TorusPart.thickLift, Over.pullback_map_left]
      rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc,
        Over.w]
  have hc := GlobalTheory.TorusPart.pullTorus_comp k k _ f₀ e (U.gt 0).i
  unfold GlobalTheory.TorusPart.gtTorus
  rw [← hc, hi, htm, GlobalTheory.TorusPart.pullTorus_torusMap_comp]

def pullEnd {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (u : G ⟶ G) : G' ⟶ G' :=
  Over.homMk (h.1.lift (φ ≫ u.left) G'.hom (by rw [Category.assoc, Over.w, h.1.w])) (h.1.lift_snd _ _ _)

theorem pullEnd_left {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (u : G ⟶ G) : (pullEnd h u).left ≫ φ = φ ≫ u.left :=
  h.1.lift_fst _ _ _

theorem over_of_two_pullbacks {B S₁ : Scheme.{0}} {H : Over B} {G₁ : Over S₁} {X Y : Scheme.{0}} {ξ₁ : S₁ ⟶ B}
    {β₁ : G₁.left ⟶ H.left} (h₁ : IsPullback β₁ G₁.hom H.hom ξ₁) {φW : Y ⟶ H.left} {n : X ⟶ Y} {n₁ : X ⟶ G₁.left}
    {f₀ : X ⟶ X} {FW : Y ⟶ Y} {Fm : H.left ⟶ H.left} {a : G₁.left ⟶ G₁.left}
    (e1 : f₀ ≫ n = n ≫ FW) (e2 : FW ≫ φW = φW ≫ Fm) (e3 : n ≫ φW = n₁ ≫ β₁) (e4 : a ≫ β₁ = β₁ ≫ Fm)
    (e5 : a ≫ G₁.hom = G₁.hom) (e6 : f₀ ≫ n₁ ≫ G₁.hom = n₁ ≫ G₁.hom) : f₀ ≫ n₁ = n₁ ≫ a := by
  apply h₁.hom_ext
  · rw [Category.assoc, ← e3, ← Category.assoc, e1, Category.assoc, e2, ← Category.assoc, e3, Category.assoc,
      Category.assoc, e4]
  · rw [Category.assoc, e6, Category.assoc, e5]

theorem spread₂_endU_comm : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], GlobalTheory.Mum.Base V₁ → ∀ (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (D₁ : DegData V₁ (maximalIdeal V₁)) (A₁ : PolAV (Sp (FractionRing V₁))) (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left), IsGrpPullback G₁ H ξ₁ β₁ → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂], GlobalTheory.Mum.Base V₂ → ∀ (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left), IsGrpPullback G₂ H ξ₂ β₂ → ∀ ρ : D₂.toPre.X →+ D₁.toPre.X, Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ → ∀ (Fm : H ⟶ H) (E₁ : EndU U₁.toUnifPre) (E₂ : EndU U₂.toUnifPre), E₁.aG.left ≫ β₁ = β₁ ≫ Fm.left → E₂.aG.left ≫ β₂ = β₂ ≫ Fm.left → ∀ y, ρ (E₂.h y) = E₁.h (ρ y) := by
  intro B H _ _ hH V₁ _ _ _ hV₁ G₁ _ _ hG₁ D₁ A₁ U₁ ξ₁ β₁ h₁ V₂ _ _ _ hV₂ G₂ _ _ hG₂ D₂ A₂ U₂ ξ₂ β₂ h₂ ρ hsp
    Fm E₁ E₂ hE₁ hE₂
  obtain ⟨W, _, _, _, ψ, GW, _, _, φW, j, Ω, _, α, b₁, hb₁, GΩ, _, n, hn, n₁, hn₁, κ, _, c, b₂, hb₂, Gκ, _, m, hm, m₂, hm₂,
    hW, hj, hα, -, -, -, hnφ, hmφ, hjΩ, hjκ⟩ := hsp
  let FW := pullEnd hW Fm
  have hFW : FW.left ≫ φW = φW ≫ Fm.left := pullEnd_left hW Fm

  have key : j ≫ FW = GlobalTheory.SplitTorus.torusMap _ E₁.h ≫ j := by
    have : IsSchemeTheoreticallyDominant (spMap α) :=
      GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ hα
    have : IsSeparated H.hom := hH.separated
    have : IsSeparated GW.hom := MorphismProperty.of_isPullback hW.1 this
    have : Flat (splitTorusAff ZU D₁.toPre.X).hom :=
      (GlobalTheory.ExtUnique.splitTorusAff_flat_and_isSeparated _ _).1
    have : Flat (splitTorus (Sp W) D₁.toPre.X).hom := inferInstanceAs (Flat (pullback.snd _ _))
    refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback (GlobalTheory.SplitTorus.isPullback_bcMap (spMap α) _) ?_
    let FΩ := pullEnd hn FW
    have hFΩ : FΩ.left ≫ n = n ≫ FW.left := pullEnd_left hn FW
    have hover : FΩ.left ≫ n₁ = n₁ ≫ E₁.aG.left :=
      over_of_two_pullbacks h₁.1 hFΩ hFW hnφ hE₁ (Over.w E₁.aG)
        (by rw [hn₁.1.w, ← Category.assoc, Over.w FΩ])
    have e1 := GlobalTheory.TorusPart.pullTorus_comp hn hn FW FΩ hFΩ j
    have e2 := GlobalTheory.TorusPart.pullTorus_torusMap_comp hn j E₁.h
    have e3 := endU_gtTorus_comp U₁ E₁ hb₁ hn₁ FΩ hover
    rw [hjΩ, e3] at e1
    rw [hjΩ] at e2
    rw [← GlobalTheory.TorusPart.pullTorus_left hn, ← GlobalTheory.TorusPart.pullTorus_left hn, e1, e2]

  let Fκ := pullEnd hm FW
  have hFκ : Fκ.left ≫ m = m ≫ FW.left := pullEnd_left hm FW
  have hover₂ : Fκ.left ≫ m₂ = m₂ ≫ E₂.aG.left :=
    over_of_two_pullbacks h₂.1 hFκ hFW hmφ hE₂ (Over.w E₂.aG)
      (by rw [hm₂.1.w, ← Category.assoc, Over.w Fκ])
  have hmono := (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U₂.gt 0) hb₂ hm₂).1
  have e := congrArg (GlobalTheory.TorusPart.pullTorus hm) key
  rw [GlobalTheory.TorusPart.pullTorus_comp hm hm FW Fκ hFκ j, GlobalTheory.TorusPart.pullTorus_torusMap_comp hm j, hjκ, Category.assoc,
    endU_gtTorus_comp U₂ E₂ hb₂ hm₂ Fκ hover₂, ← Category.assoc, ← Category.assoc,
    ← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_comp] at e
  have : Nonempty (Sp κ) := inferInstance
  have e' := GlobalTheory.SplitTorus.torusMap_injective ((cancel_mono _).1 e)
  intro y
  exact DFunLike.congr_fun e' y

end GlobalTheory.Poinc.Sep.Spz
