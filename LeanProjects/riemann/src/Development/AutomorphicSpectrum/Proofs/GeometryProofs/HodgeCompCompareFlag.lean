import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DomBy
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagLabelBasesExist
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NotIsGenericFlagSelf
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsVBOneOfChartGenerators
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTail

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert

namespace GlobalTheory.CompanionTheory.Ar.OrVert.LieCmp

theorem exists_ext {S : Scheme.{0}} {G : Over S} [GrpObj G] (hs : Smooth G.hom) {R R' : Type} [Field R] [Field R']
    (i : R →+* R') (x : Sp R ⟶ S) (y : Sp R' ⟶ S) (hy : spMap i ≫ x = y) {E E' : Type} [AddCommGroup E] [Module R E]
    [AddCommGroup E'] [Module R' E'] (M : LieModel G x E) (M' : LieModel G y E') :
    ∃ j : E →+ E', (∀ e, (M'.pt (j e)).left = spMap (dualMap i) ≫ (M.pt e).left) ∧ IsExtOver i j ∧
      Submodule.span R' (Set.range j) = ⊤ := by
  subst hy
  letI := i.toAlgebra
  obtain ⟨j, hj, hl, hsp⟩ := GlobalTheory.T.lie_model_base_change_map S G R R' x E E' M M'
  have hbc := hsp hs
  obtain ⟨m, ⟨b₁⟩⟩ := GlobalTheory.T.lie_model_free_over_local_ring S G hs R x E M
  refine ⟨j, hj, ⟨hl, fun n b hb => LiePull.indep_of_bases b₁ j (fun m B => (hbc m B).1) b hb⟩, ?_⟩
  refine top_le_iff.1 ((hbc m b₁).2.symm.le.trans (Submodule.span_mono ?_))
  rintro _ ⟨k, rfl⟩
  exact ⟨_, rfl⟩

variable {Ω Ω₀ F F₀ : Type} [Field Ω] [Field Ω₀] [AddCommGroup F] [Module Ω F] [AddCommGroup F₀] [Module Ω₀ F₀]

theorem span_span (W A : Subring Ω) (h : ∀ a ∈ A, a ∈ W) (T : Set F) :
    Submodule.span W ((Submodule.span A T : Submodule A F) : Set F) = Submodule.span W T := by
  refine le_antisymm (Submodule.span_le.2 fun x hx => ?_) (Submodule.span_mono Submodule.subset_span)
  induction hx using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx => exact Submodule.smul_mem _ (⟨(a : Ω), h _ a.2⟩ : W) hx

theorem span_image_span (i : Ω₀ →+* Ω) (ι : F₀ →+ F) (hι : ∀ (a : Ω₀) (e : F₀), ι (a • e) = i a • ι e)
    (W : Subring Ω) (A : Subring Ω₀) (h : ∀ a ∈ A, i a ∈ W) (T : Set F₀) :
    Submodule.span W (ι '' ((Submodule.span A T : Submodule A F₀) : Set F₀)) = Submodule.span W (ι '' T) :=
  _root_.UpperTheory.Reformulated.B.DYha5.main i ι hι W A h T

theorem lie_cmp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (K K₀ : Type) [Fintype K] [Fintype K₀] (J : K → Type) (J₀ : K₀ → Type) (y : (Σ k, J k) → Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (𝔐 : HodgeCpt Y S y) (𝔐₀ : HodgeCpt Y S₀ y₀) (Fl₀ : 𝔐₀.Flag) (i : Ω₀ →+* Ω), 𝔐.ξ ≫ 𝔐.f = spMap i ≫ 𝔐₀.ξ ≫ 𝔐₀.f → ∃ ι : 𝔐₀.Li →+ 𝔐.Li, IsExtOver i ι ∧ Submodule.span Ω (Set.range ι) = ⊤ ∧ (∀ (e : 𝔐₀.Li) (e' : 𝔐.Li), (𝔐.M.pt e').left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (𝔐₀.M.pt e).left ≫ 𝔐₀.m.φ ↔ e' = ι e) ∧ ∀ (W : Subring Ω) (q : Cpt 𝔐.ξ) (q₀ : Cpt 𝔐₀.ξ), (∀ a ∈ regAt 𝔐.ξ q, a ∈ W) → (∀ a ∈ regAt 𝔐₀.ξ q₀, i a ∈ W) → 𝔐.f q.1 = 𝔐₀.f q₀.1 → Submodule.span W ((𝔐.M.lat q : Set 𝔐.Li)) = Submodule.span W (ι '' (𝔐₀.M.lat q₀ : Set 𝔐₀.Li)) := by
  intro E _ _ _ H D l Xo c Y S S₀ Ω Ω₀ _ _ K K₀ _ _ J J₀ y y₀ 𝔐 𝔐₀ Fl₀ i hh
  have hs : Smooth Y.t.G.hom := Y.t.semi.smooth
  obtain ⟨ι, hpt, hext, hspan⟩ := exists_ext hs i (𝔐₀.ξ ≫ 𝔐₀.f) (𝔐.ξ ≫ 𝔐.f) hh.symm
    (LieMove.pushModel 𝔐₀.m.cart 𝔐₀.M) (LieMove.pushModel 𝔐.m.cart 𝔐.M)
  have hpt' : ∀ e, (𝔐.M.pt (ι e)).left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (𝔐₀.M.pt e).left ≫ 𝔐₀.m.φ := hpt
  have hd : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ 𝔐₀.ξ₀ 𝔐.f (i.comp 𝔐₀.fn) := by
    have h₀ : 𝔐₀.ξ ≫ 𝔐₀.f = Spec.map (CommRingCat.ofHom 𝔐₀.fn) ≫ 𝔐₀.ξ₀ := 𝔐₀.fn_over
    show 𝔐.ξ ≫ 𝔐.f = _
    rw [hh, h₀, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  have hj' : ∀ e, (𝔐.M.pt ((ι.comp Fl₀.j) e)).left ≫ 𝔐.m.φ =
      Spec.map (CommRingCat.ofHom (dualMap (i.comp 𝔐₀.fn))) ≫ (Fl₀.M₀.pt e).left := by
    intro e
    rw [AddMonoidHom.comp_apply, hpt', Fl₀.j_pt, ← LiePull.dualMap_comp, CommRingCat.ofHom_comp, Spec.map_comp,
      Category.assoc]
  have m₀ := (LiePull.main Y.X 𝔐₀.X 𝔐₀.Ω₀ Ω₀ 𝔐₀.ξ₀ 𝔐₀.ξ 𝔐₀.f 𝔐₀.fn Y.t.G 𝔐₀.t.G 𝔐₀.m.φ Fl₀.Li₀ 𝔐₀.Li Fl₀.M₀ 𝔐₀.M
    Fl₀.j 𝔐₀.gen₀ 𝔐₀.tie.gen 𝔐₀.fn_over 𝔐₀.m.cart hs Fl₀.j_pt).2.2
  have m₁ := (LiePull.main Y.X 𝔐.X 𝔐₀.Ω₀ Ω 𝔐₀.ξ₀ 𝔐.ξ 𝔐.f (i.comp 𝔐₀.fn) Y.t.G 𝔐.t.G 𝔐.m.φ Fl₀.Li₀ 𝔐.Li Fl₀.M₀ 𝔐.M
    (ι.comp Fl₀.j) 𝔐₀.gen₀ 𝔐.tie.gen hd 𝔐.m.cart hs hj').2.2
  refine ⟨ι, hext, hspan, fun e e' => ⟨fun h => ?_, ?_⟩, fun W q q₀ hq hq₀ hf => ?_⟩
  · exact (LieMove.pushModel 𝔐.m.cart 𝔐.M).inj (Over.OverMorphism.ext (h.trans (hpt' e).symm))
  · rintro rfl
    exact hpt' e
  · have a₁ := congrFun m₁ q
    rw [Lat.pull_apply _ hd] at a₁
    have a₀ := congrFun m₀ q₀
    rw [Lat.pull_apply _ 𝔐₀.fn_over] at a₀
    have es : (⟨𝔐.f q.1, hd.specializes q⟩ : Cpt 𝔐₀.ξ₀) = ⟨𝔐₀.f q₀.1, 𝔐₀.fn_over.specializes q₀⟩ := Subtype.ext hf
    rw [a₁, a₀, es, span_span W _ hq, span_image_span i ι hext.1 W _ hq₀, Set.image_image]
    rfl

end GlobalTheory.CompanionTheory.Ar.OrVert.LieCmp
