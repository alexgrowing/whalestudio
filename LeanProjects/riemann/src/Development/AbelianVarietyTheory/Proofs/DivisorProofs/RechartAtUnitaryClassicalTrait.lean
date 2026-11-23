import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.Points GlobalTheory.ZM GlobalTheory.SiegelTor

namespace GlobalTheory.UPoinc

theorem rechart_at_uClassical_trait : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct : UCTrait X p z) (U : X.M.Z.Opens) (u' : Sp (ratHull (X.M.ringOn U)) ⟶ Xo.XF cf), IsAffineOpen U → (gPt p ≫ ct.y) (closedPoint (PadicAlgCl p)) ∈ U → spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ u' = X.uΩ → X.M.ringOn U ≤ X.M.O ((gPt p ≫ ct.y) (closedPoint (PadicAlgCl p))) ∧ ∃ y₁ : ratHull (X.M.ringOn U) →+* PadicAlgCl p, (∀ a : X.M.ringOn U, y₁ (toRat _ a) = X.M.val (gPt p ≫ ct.y) a) ∧ spMap y₁ ≫ u' = spMap ct.ι ≫ ct.T.y ∧ ∀ a : X.o₁, ‖y₁ (toRat _ (algebraMap X.o₁ (X.M.ringOn U) a))‖ ≤ 1 := by
  intro E _ _ _ H Dw hpq l Xo cf C X p _ z ct U u' hU hwU hu'
  haveI := X.ar.char
  set w := (gPt p ≫ ct.y) (closedPoint (PadicAlgCl p)) with hw
  have hne : (U : Set X.M.Z).Nonempty := ⟨w, hwU⟩
  have hle : X.M.ringOn U ≤ X.M.O w := RatModel.ringOn_le_O hwU
  have hsp : ∀ w', (gPt p ≫ ct.y) w' ⤳ w := fun w' => by
    rw [Subsingleton.elim w' (closedPoint (PadicAlgCl p))]
  let y₀ : X.M.ringOn U →+* PadicAlgCl p :=
    (RatModel.valHomOf (gPt p ≫ ct.y) w hsp).comp (Subalgebra.inclusion hle).toRingHom
  have hy₀ : ∀ a : X.M.ringOn U, y₀ a = X.M.val (gPt p ≫ ct.y) a := fun a => rfl
  obtain ⟨y₁, hy₁, -⟩ := existsUnique_ratLift (X.M.ringOn U) (K := PadicAlgCl p)
    (fun n hn => IsUnit.mk0 _ (Int.cast_ne_zero.2 hn)) y₀
  have hy₁' : ∀ a : X.M.ringOn U, y₁ (toRat _ a) = y₀ a := fun a => RingHom.congr_fun hy₁ a
  let e : Sp (X.M.ringOn U) ⟶ X.M.Z :=
    Spec.map (CommRingCat.ofHom (X.M.sectionsEquiv U hne).toRingHom) ≫ hU.fromSpec
  have he : ∀ {K : Type} [CommRing K] (φ : X.M.ringOn U →+* K), ⊤ ≤ (spMap φ ≫ e) ⁻¹ᵁ U ∧
      ∀ f, valR (spMap φ ≫ e) U f = φ (X.M.sectionsEquiv U hne f) := by
    intro K _ φ
    have e2 : spMap φ ≫ e = Spec.map (CommRingCat.ofHom (φ.comp (X.M.sectionsEquiv U hne).toRingHom)) ≫
        hU.fromSpec := by
      rw [← Category.assoc, ← Spec.map_comp]; rfl
    rw [e2]
    have hx := le_preimage_specMap_fromSpec hU (CommRingCat.ofHom (φ.comp (X.M.sectionsEquiv U hne).toRingHom))
    refine ⟨hx, fun f => ?_⟩
    rw [valR_eq _ U hx, valMap_specMap_fromSpec]
    rfl
  have hyU : ⊤ ≤ (gPt p ≫ ct.y) ⁻¹ᵁ U := (le_preimage_iff _ U).2 hwU
  have ha : spMap y₀ ≫ e = gPt p ≫ ct.y := by
    refine ext_of_valR hU (he y₀).1 hyU fun f => ?_
    rw [(he y₀).2, hy₀, RatModel.coe_sectionsEquiv, RatModel.val_valF ((top_le_preimage_iff _ _).1 hyU)]
    rfl
  have hgen : spMap (X.M.ringOn U).val.toRingHom ≫ e = X.M.pt := by
    refine ext_of_valR hU (he _).1 (X.M.top_le_preimage_pt hne) fun f => ?_
    rw [(he _).2]
    exact (RatModel.coe_sectionsEquiv U hne f).trans (valF_eq_valR _ _ _)
  have hdom : IsDominant (spMap (ratHull (X.M.ringOn U)).val.toRingHom) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 Subtype.val_injective]; exact bot_le)⟩
  haveI : IsProper C.z := ThetaDescent.isProper_of_isProjOver C.proj
  have hgen2 : spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ ((spMap (toRat _) ≫ e) ≫ X.π) =
      spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ (u' ≫ C.i) := by
    rw [← Category.assoc, ← Category.assoc, spMap_val_toRat, hgen, X.comp, ← Category.assoc _ u' C.i, hu']
    simp only [USetup.uΩ, Category.assoc]
  have hb : (spMap (toRat _) ≫ e) ≫ X.π = u' ≫ C.i :=
    ext_of_isDominant_of_isSeparated C.z
      (ext_of_isDominant (spMap (ratHull (X.M.ringOn U)).val.toRingHom) (by
        simp only [← Category.assoc] at hgen2 ⊢; rw [hgen2]))
      (spMap (ratHull (X.M.ringOn U)).val.toRingHom) hgen2
  haveI := C.isPreimmersion_i
  have hy01 : spMap y₁ ≫ spMap (toRat (X.M.ringOn U)) = spMap y₀ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hy₁]
  have hpt' : spMap y₁ ≫ u' = spMap ct.ι ≫ ct.T.y := by
    rw [← cancel_mono C.i, Category.assoc, ← hb, ← Category.assoc, ← Category.assoc, hy01, ha, Category.assoc,
      ct.comm, Category.assoc]
  let τ := Spec.preimage (ct.y ≫ X.M.s)
  have hσ : (gPt p ≫ ct.y) ≫ X.M.s = spMap ((OO p).subtype.comp τ.hom) := by
    rw [Category.assoc, ← Spec.map_preimage (ct.y ≫ X.M.s), ← Spec.map_comp]; rfl
  refine ⟨hle, y₁, fun a => (hy₁' a).trans (hy₀ a), hpt', fun a => ?_⟩
  rw [hy₁', hy₀]
  show ‖X.M.val (gPt p ≫ ct.y) (algebraMap X.o₁ X.Ω₁ a)‖ ≤ 1
  rw [RatModel.val_algebraMap hσ a]
  exact (mem_OO_iff _).1 (τ.hom a).2

end GlobalTheory.UPoinc
