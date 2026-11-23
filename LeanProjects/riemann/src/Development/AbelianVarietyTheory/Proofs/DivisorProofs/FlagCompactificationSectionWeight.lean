import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DrAtNonneg
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GrNormPosOfBasis
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeGenericAffineOpen
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
open AlgebraicGeometry CategoryTheory
open GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)

open CategoryTheory.Limits

noncomputable section

namespace GlobalTheory.ShFam.CoordField

theorem unit_prod_cancel' {K ι : Type} [CommRing K] [Fintype ι] (t : ι → Kˣ) (n : ι → ℤ) (a : K) :
    ((∏ z, t z ^ n z : Kˣ) : K) * a * ((∏ z, t z ^ (-n z) : Kˣ) : K) = a := by
  rw [mul_right_comm, ← Units.val_mul, ← Finset.prod_mul_distrib]
  simp

theorem isCoord_val_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (C : FlagCpt Z e) (ex : Ix Dw → ℤ) (g : Rul Xo c), ex none = 0 → g ∈ AllWt.secZ Xo c ex → ∀ (K : Type) [Field K] [Algebra c.F K] (yC : FrPt Xo c K) (xg : Sp K ⟶ Z.X) (gf : EigFrame Z (algebraMap c.F K) xg), (∀ τ i, ∃ w : Sp (DualNumber K) ⟶ Z.oF.t.G.left, w ≫ Z.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ AllWt.ptF yC ∧ w ≫ Z.m0.toSABMap.φ = yC.u τ i ∧ w ≫ Z.m.φ = gf.v τ i) → ∀ x : Sp K ⟶ C.Y.X, x ≫ C.π = AllWt.ptF yC ≫ Z.jQ → C.Carries x gf → IsCoord C x gf (fun z => -ex (some z)) (C.val g) (evR Xo c g yC) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e C ex g hex hsec K _ _ yC xg gf hu x hxπ hC
  obtain ⟨y, ψ, φ₁, f, t, t', hp, a1, b1⟩ := hC
  have hs : x (IsLocalRing.closedPoint K) ⤳ y := by
    have : x (IsLocalRing.closedPoint K) ∈ Set.range (C.Y.X.fromSpecStalk y) := by rw [hp]; exact ⟨_, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  let ρ : C.Y.X.presheaf.stalk y →+* C.Y.X.presheaf.stalk (x (IsLocalRing.closedPoint K)) :=
    (C.Y.X.presheaf.stalkSpecializes hs).hom
  have h1 : spMap ρ ≫ stalkPt C.Y y = stalkPt C.Y (x (IsLocalRing.closedPoint K)) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk hs
  let χ : C.Y.X.presheaf.stalk (x (IsLocalRing.closedPoint K)) →+* K := (Scheme.stalkClosedPointTo x).hom
  have hχx : spMap χ ≫ stalkPt C.Y (x (IsLocalRing.closedPoint K)) = x :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk x
  have h2 : χ.comp ρ = ψ := EigLoc.spMap_inj ((cancel_mono (C.Y.X.fromSpecStalk y)).1 (by
    refine Eq.trans ?_ (hχx.trans hp)
    rw [← h1, ← Category.assoc, ← Spec.map_comp]; rfl))
  have h3 : (algebraMap _ C.Y.X.functionField).comp ρ = algebraMap (C.Y.X.presheaf.stalk y) C.Y.X.functionField :=
    congrArg CommRingCat.Hom.hom (C.Y.X.presheaf.stalkSpecializes_comp _ hs)
  obtain ⟨f', hf⟩ := f.exists_isMap ρ (x' := stalkPt C.Y (x (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z) rfl
    (by rw [← h1, Category.assoc])
  have key : ∀ {k : Type} [CommRing k] (χ : C.Y.X.presheaf.stalk (x (IsLocalRing.closedPoint K)) →+* k)
      {φ' : c.F →+* k} {x' : Sp k ⟶ Z.X}
      {g : EigFrame Z φ' x'} {t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → kˣ}, f.Tri (χ.comp ρ) g t → f'.Tri χ g t :=
    fun χ _ _ g t h => ⟨by rw [h.1, ← h1, Category.assoc, ← Category.assoc (spMap χ), ← Spec.map_comp]; rfl, h.2.1,
      fun τ i => by simpa only [hf τ, GlobalTheory.GradedPieces.dual_comp] using h.2.2 τ i⟩
  have a1' := key _ (h3.symm ▸ a1)
  have b1' := key _ (h2.symm ▸ b1)

  letI : Algebra c.F (C.Y.X.presheaf.stalk (x (IsLocalRing.closedPoint K))) := (ρ.comp φ₁).toAlgebra
  letI : Algebra c.F C.Y.Fn := (constF e C.Y).toAlgebra
  haveI := Z.jQ_open
  let ι : C.Y.X.presheaf.stalk (x (IsLocalRing.closedPoint K)) →+* C.Y.Fn := algebraMap _ C.Y.X.functionField
  have hι : Function.Injective ι :=
    IsFractionRing.injective (C.Y.X.presheaf.stalk (x (IsLocalRing.closedPoint K))) C.Y.X.functionField
  haveI : IsLocalHom χ := inferInstanceAs (IsLocalHom (Scheme.stalkClosedPointTo x).hom)
  let x' : Sp (C.Y.X.presheaf.stalk (x (IsLocalRing.closedPoint K))) ⟶ gen Z :=
    stalkPt C.Y (x (IsLocalRing.closedPoint K)) ≫ C.π
  have hy : AllWt.ptF yC ≫ Z.jQ = spMap χ ≫ x' := by
    rw [← hxπ]
    show _ = spMap χ ≫ stalkPt C.Y (x (IsLocalRing.closedPoint K)) ≫ C.π
    rw [← Category.assoc, hχx]
  have hr : Set.range x' ⊆ Set.range Z.jQ := by
    rintro _ ⟨q, rfl⟩
    have hq : q ⤳ spMap χ (IsLocalRing.closedPoint K) := by
      have : spMap χ (IsLocalRing.closedPoint K) = IsLocalRing.closedPoint _ := IsLocalRing.comap_closedPoint χ
      rw [this]
      exact IsLocalRing.specializes_closedPoint q
    refine (hq.map x'.continuous).mem_open Z.jQ.isOpenEmbedding.isOpen_range
      ⟨AllWt.ptF yC (IsLocalRing.closedPoint K), ?_⟩
    exact congrArg (fun m : Sp K ⟶ gen Z => m (IsLocalRing.closedPoint K)) hy
  let xF := IsOpenImmersion.lift Z.jQ x' hr
  have hxF : xF ≫ Z.jQ = x' := IsOpenImmersion.lift_fac _ _ _
  have hpt : AllWt.ptF yC = spMap χ ≫ xF := by
    rw [← cancel_mono Z.jQ, Category.assoc, hxF, hy]
  have hgen : genericPt C.Y = spMap ι ≫ stalkPt C.Y (x (IsLocalRing.closedPoint K)) :=
    (Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes _)).symm
  have hpt0 : AllWt.ptF C.y0 = spMap ι ≫ xF := by
    rw [← cancel_mono Z.jQ, Category.assoc, hxF, C.y0_x, hgen, Category.assoc]
  have hs' : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F (C.Y.X.presheaf.stalk (x (IsLocalRing.closedPoint K)))) := by
    obtain ⟨φ₂, h⟩ := Spec.map_surjective (xF ≫ pullback.snd _ _)
    have h1 : spMap ι ≫ spMap φ₂.hom = spMap (algebraMap c.F C.Y.Fn) := by
      have h0 : AllWt.ptF C.y0 ≫ pullback.snd _ _ = spMap (algebraMap c.F C.Y.Fn) := pullback.lift_snd _ _ _
      rw [← h0, hpt0, Category.assoc, ← h]
      rfl
    rw [OpenReg.spMap_comp] at h1
    have h2 : ι.comp φ₂.hom = algebraMap c.F C.Y.Fn := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    have h3 : φ₂.hom = ρ.comp φ₁ := RingHom.ext fun r =>
      hι ((RingHom.congr_fun h2 r).trans (RingHom.congr_fun a1'.2.1 r))
    rw [← h]
    show Spec.map φ₂ = Spec.map (CommRingCat.ofHom (ρ.comp φ₁))
    exact congrArg Spec.map (CommRingCat.hom_ext h3)
  obtain ⟨a, ha⟩ := ChartValue.exists_evR_eq_of_tri (Z := Z) xF hs'
    (x := stalkPt C.Y (x (IsLocalRing.closedPoint K)) ≫ C.π ≫ genι Z) (by rw [← Category.assoc, hxF]; rfl) f' hex hsec
  let ι' : C.Y.X.presheaf.stalk (x (IsLocalRing.closedPoint K)) →ₐ[c.F] C.Y.Fn :=
    { ι with commutes' := fun r => (RingHom.congr_fun a1'.2.1 r).symm }
  have hv1 := ha C.Y.Fn ι' C.f0.v t C.y0 (fun τ i => by
      obtain ⟨cf, c1, c2, c3⟩ := a1'.2.2 τ i
      exact ⟨cf, c1, c2, (congrArg (fun X => IsCombAtG Z.t X (fun k => spMap (dualMap ι) ≫ f'.v τ k) cf (C.f0.v τ i))
        a1'.1).mp c3⟩) hpt0 C.flagComponentFramedPoint_frame
  let χ' : C.Y.X.presheaf.stalk (x (IsLocalRing.closedPoint K)) →ₐ[c.F] K :=
    { χ with commutes' := fun r => (RingHom.congr_fun b1'.2.1 r).symm }
  have hv2 := ha K χ' gf.v t' yC (fun τ i => by
      obtain ⟨cf, c1, c2, c3⟩ := b1'.2.2 τ i
      exact ⟨cf, c1, c2, (congrArg (fun X => IsCombAtG Z.t X (fun k => spMap (dualMap χ) ≫ f'.v τ k) cf (gf.v τ i))
        b1'.1).mp c3⟩) hpt hu
  refine ⟨x (IsLocalRing.closedPoint K), χ, ρ.comp φ₁, f', t, t', a, hχx.symm, a1', b1', ?_, ?_⟩
  · show ι a = evR Xo c g C.y0 * _
    rw [hv1]
    exact (unit_prod_cancel' (fun z : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => t z.1 z.2) (fun z => ex (some z)) (ι a)).symm
  · rw [hv2]
    show _ = χ a * _
    simp only [neg_neg]
    exact mul_comm _ _

end GlobalTheory.ShFam.CoordField
