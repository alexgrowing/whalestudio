import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothOfAlgClosedUnif
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlag.LQF

theorem finite_preimage_of_finite_points {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f] (y : Y)
    (H : {z : Spec (CommRingCat.of (AlgebraicClosure (Y.residueField y))) ⟶ X | z ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) (AlgebraicClosure (Y.residueField y)))) ≫
        Y.fromSpecResidueField y}.Finite) : (f ⁻¹' {y}).Finite := by
  let k := Y.residueField y
  let K := AlgebraicClosure k
  let pt : Spec (CommRingCat.of K) := (⊥ : PrimeSpectrum K)
  have hcl : closedPoints (f.fiber y) ⊆ f.fiberι y ⁻¹' ((fun z : Spec (CommRingCat.of K) ⟶ X => z pt) '' {z |
      z ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K)) ≫ Y.fromSpecResidueField y}) := by
    intro w hw
    have hw' : IsClosed ({w} : Set (f.fiber y)) := hw
    have h1 : LocallyOfFiniteType ((f.fiber y).fromSpecResidueField w) :=
      isClosed_singleton_iff_locallyOfFiniteType.1 hw'
    have h0 : LocallyOfFiniteType (f.fiberToSpecResidueField y) :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback f (Y.fromSpecResidueField y)) ‹LocallyOfFiniteType f›
    have h2 : LocallyOfFiniteType ((f.fiber y).fromSpecResidueField w ≫ f.fiberToSpecResidueField y) := inferInstance
    have h3 : IsFinite ((f.fiber y).fromSpecResidueField w ≫ f.fiberToSpecResidueField y) :=
      isFinite_iff_locallyOfFiniteType_of_jacobsonSpace.2 h2
    obtain ⟨φ, hφ⟩ := Spec.map_surjective ((f.fiber y).fromSpecResidueField w ≫ f.fiberToSpecResidueField y)
    have h4 : φ.hom.Finite := by
      rw [← IsFinite.SpecMap_iff, hφ]; exact h3
    letI : Algebra k ((f.fiber y).residueField w) := φ.hom.toAlgebra
    haveI : Module.Finite k ((f.fiber y).residueField w) := h4
    haveI : Algebra.IsAlgebraic k ((f.fiber y).residueField w) := Algebra.IsIntegral.isAlgebraic
    let ι : (f.fiber y).residueField w →ₐ[k] K := IsAlgClosed.lift
    refine ⟨Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ (f.fiber y).fromSpecResidueField w ≫ f.fiberι y, ?_, ?_⟩
    · show _ = _
      rw [Category.assoc, Category.assoc, Scheme.Hom.fiber_fac, ← Category.assoc ((f.fiber y).fromSpecResidueField w),
        ← hφ, ← Category.assoc, ← Spec.map_comp]
      congr 2
      ext a
      exact ι.commutes a
    · show (Spec.map _ ≫ _ ≫ _) pt = _
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  have hfin : (closedPoints (f.fiber y)).Finite :=
    ((H.image _).preimage (f.fiberι y).isEmbedding.injective.injOn).subset hcl
  have huniv : (Set.univ : Set (f.fiber y)) = closedPoints (f.fiber y) := by
    have hc : IsClosed (closedPoints (f.fiber y)) := by
      rw [← Set.biUnion_of_singleton (closedPoints (f.fiber y))]
      exact hfin.isClosed_biUnion fun x hx => hx
    rw [← JacobsonSpace.closure_inter_closedPoints isClosed_univ, Set.univ_inter, hc.closure_eq]
  haveI : Finite (f.fiber y) := Set.finite_univ_iff.1 (huniv ▸ hfin)
  rw [← Scheme.Hom.range_fiberι]
  exact Set.finite_range _

end GlobalTheory.VarFlag.LQF

namespace GlobalTheory.VarFlag.LQF

open GlobalTheory.FlagMod (FlagCover FlagModel Frames initSpan initSpan_le_of_tri)
open GlobalTheory.ShFam (EigFrame FlagCpt)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)

open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem eq_sum_of_isCombAtG {Y : Model Xo c (RingHom.id c.F)} {K : Type} [Field K] {x x' : Sp K ⟶ Y.X} (e : x' = x)
    {m : ℕ} (u : Fin m → TanM x Y.t.G) (cf : Fin m → K) (w : TanM x Y.t.G)
    (h : IsCombAtG Y.t x' (fun j => (tv (u j)).left) cf (tv w).left) : w = ∑ j, cf j • u j := by
  subst e
  exact (GlobalTheory.LieMet.isComb_iff u cf w).1 h

theorem vecAt_left {Y : Model Xo c (RingHom.id c.F)} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π) {K : Type}
    [Field K] (k : F.J) (z : Sp K ⟶ Z) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) {x : Sp K ⟶ Y.X} (hx : z ≫ π = x) (σ : E →+* ℂ)
    (i : Fin (Dw.mult σ)) : (tv (F.vecAt k z hz hx σ i)).left = (tv (F.vecAt k z hz rfl σ i)).left := by
  subst hx; rfl

theorem initSpan_le_of_frameTri {Y : Model Xo c (RingHom.id c.F)} {Z : Scheme.{0}} {π : Z ⟶ Y.X} (F : Frames Y π)
    {K : Type} [Field K] {φ φ' : c.F →+* K} (z z' : Sp K ⟶ Z) {x : Sp K ⟶ Y.X} (hx : z ≫ π = x) (hx' : z' ≫ π = x)
    (k k' : F.J) (hz : ⊤ ≤ z ⁻¹ᵁ F.U k) (hz' : ⊤ ≤ z' ⁻¹ᵁ F.U k') (g : EigFrame Y φ (z ≫ π))
    (g' : EigFrame Y φ' (z' ≫ π)) (hg : IsFrameAt F z k hz g) (hg' : IsFrameAt F z' k' hz' g')
    (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ) (ht : g.Tri (RingHom.id K) g' t) (σ : E →+* ℂ) (i : ℕ) :
    initSpan K (F.vecAt k' z' hz' hx' σ) i ≤ initSpan K (F.vecAt k z hz hx σ) i := by
  have h1 : spMap (dualMap (RingHom.id K)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  have ex : ∀ j : Fin (Dw.mult σ), ∃ cf : Fin (Dw.mult σ) → K, (∀ k, j < k → cf k = 0) ∧
      F.vecAt k' z' hz' hx' σ j = ∑ a, cf a • F.vecAt k z hz hx σ a := fun j => by
    obtain ⟨cf, -, hcf, hc⟩ := ht.2.2 σ j
    refine ⟨cf, hcf, eq_sum_of_isCombAtG hx' _ cf _ ?_⟩
    have e1 : (fun a => spMap (dualMap (RingHom.id K)) ≫ g.v σ a) =
        fun a => (tv (F.vecAt k z hz hx σ a)).left := funext fun a => by
      rw [h1, Category.id_comp, hg σ a, vecAt_left F k z hz hx σ a]
    rw [e1, hg' σ j, ← vecAt_left F k' z' hz' hx' σ j] at hc
    exact hc
  choose cf hcf e using ex
  exact initSpan_le_of_tri (B := Matrix.of fun a j => cf j a) (fun j a h => hcf a j h) e i

end GlobalTheory.VarFlag.LQF

namespace GlobalTheory.VarFlag.LQF

open GlobalTheory.FlagMod (FlagCover FlagModel Frames initSpan)
open GlobalTheory.ShFam (EigFrame FlagCpt)
open GlobalTheory.CompHS (Y₀ inc₀)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem carries_base {Y : Model Xo c (RingHom.id c.F)} (C : FlagCpt Y (RingEquiv.refl c.F)) {K : Type} [Field K]
    {φ : c.F →+* K} {x : Sp K ⟶ Y.X} {p : Sp K ⟶ C.Y.X} {g : EigFrame Y φ x} (h : C.Carries p g) :
    x = p ≫ C.π ≫ GlobalTheory.Toroidal.genι Y := by
  obtain ⟨y, ψ, φ₁, f, t, t', hp, -, htri⟩ := h
  rw [htri.1, hp, Category.assoc]

theorem tri_of_carries {Y : Model Xo c (RingHom.id c.F)} (C : FlagCpt Y (RingEquiv.refl c.F)) (hC : CarriesTri C)
    {K : Type} [Field K] {φ φ' : c.F →+* K} {x x' : Sp K ⟶ Y.X} (e : x = x') {p : Sp K ⟶ C.Y.X}
    (g : EigFrame Y φ x) (g' : EigFrame Y φ' x') (h : C.Carries p g) (h' : C.Carries p g') :
    ∃ t, g.Tri (RingHom.id K) g' t := by
  subst e
  exact hC K φ φ' x p g g' h h'

theorem finite_points {Y : Model Xo c (RingHom.id c.F)} (X : FlagModel Y) (C : FlagCpt Y (RingEquiv.refl c.F))
    (hC : CarriesTri C) (Z : Formalism.L2.Pj.Comp Xo c) (h : Y₀ X.toFlagCover Z ⟶ C.Y.X)
    (hR : ∀ (K : Type) [Field K] (z : Sp K ⟶ Y₀ X.toFlagCover Z), Rel X.F C (z ≫ inc₀ X.toFlagCover Z) (z ≫ h))
    (K : Type) [Field K] [IsAlgClosed K] (p : Sp K ⟶ C.Y.X) : {z : Sp K ⟶ Y₀ X.toFlagCover Z | z ≫ h = p}.Finite := by
  rcases Set.eq_empty_or_nonempty {z : Sp K ⟶ Y₀ X.toFlagCover Z | z ≫ h = p} with h0 | ⟨z₁, hz₁⟩
  · rw [h0]; exact Set.finite_empty
  have hfin := X.fin K (z₁ ≫ inc₀ X.toFlagCover Z)
  refine (hfin.preimage (f := fun z => z ≫ inc₀ X.toFlagCover Z)
    (fun a _ b _ e => (cancel_mono (inc₀ X.toFlagCover Z)).1 e)).subset ?_
  intro z hz
  have key : ∀ w : Sp K ⟶ Y₀ X.toFlagCover Z, w ≫ h = p → ∃ (φ : c.F →+* K) (k : X.F.J)
      (hk : ⊤ ≤ (w ≫ inc₀ X.toFlagCover Z) ⁻¹ᵁ X.F.U k)
      (g : EigFrame Y φ ((w ≫ inc₀ X.toFlagCover Z) ≫ X.π)), IsFrameAt X.F _ k hk g ∧ C.Carries p g := by
    intro w hw
    obtain ⟨φ, k, hk, g, -, hg, hc⟩ := hR K w
    exact ⟨φ, k, hk, g, hg, hw ▸ hc⟩
  obtain ⟨φ, k, hk, g, hg, hc⟩ := key z hz
  obtain ⟨φ₁, k₁, hk₁, g₁, hg₁, hc₁⟩ := key z₁ hz₁
  have hx : (z ≫ inc₀ X.toFlagCover Z) ≫ X.π = (z₁ ≫ inc₀ X.toFlagCover Z) ≫ X.π :=
    (carries_base C hc).trans (carries_base C hc₁).symm
  refine ⟨hx, fun σ i => ?_⟩
  obtain ⟨t, ht⟩ := tri_of_carries C hC hx g g₁ hc hc₁
  obtain ⟨t', ht'⟩ := tri_of_carries C hC hx.symm g₁ g hc₁ hc
  rw [X.F.step_eq k _ hk hx, X.F.step_eq k₁ _ hk₁ rfl]
  exact le_antisymm (initSpan_le_of_frameTri X.F _ _ rfl hx k₁ k hk₁ hk g₁ g hg₁ hg t' ht' σ i)
    (initSpan_le_of_frameTri X.F _ _ hx rfl k k₁ hk hk₁ g g₁ hg hg₁ t ht σ i)

end GlobalTheory.VarFlag.LQF

theorem GlobalTheory.VarFlag.locallyQuasiFinite_flag : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}, ∀ (X : GlobalTheory.FlagMod.FlagModel Y) (C : GlobalTheory.ShFam.FlagCpt Y (RingEquiv.refl c.F)), GlobalTheory.VarFlag.CarriesTri C → ∀ (Z : Formalism.L2.Pj.Comp Xo c) (h : GlobalTheory.CompHS.Y₀ X.toFlagCover Z ⟶ C.Y.X) [IsProper h], (∀ (K : Type) [Field K] (z : Sp K ⟶ GlobalTheory.CompHS.Y₀ X.toFlagCover Z), GlobalTheory.VarFlag.Rel X.F C (z ≫ GlobalTheory.CompHS.inc₀ X.toFlagCover Z) (z ≫ h)) → LocallyQuasiFinite h := by
  intro E _ _ _ H Dw l Xo c Y X C hC Z h _ hR
  refine LocallyQuasiFinite.of_finite_preimage_singleton h fun p => ?_
  exact GlobalTheory.VarFlag.LQF.finite_preimage_of_finite_points h p
    (GlobalTheory.VarFlag.LQF.finite_points X C hC Z h hR _ _)
