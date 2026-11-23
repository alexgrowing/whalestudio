import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSectionOfChg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenBasisSameVec

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine

namespace GlobalTheory.DetLine

theorem exists_vecEquiv {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
    (Y : Model Xo c β) {R : Type} [CommRing R] (x : Sp R ⟶ Xo.XF c) :
    ∃ e : (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G) ≃ (epsAt ((x ≫ Y.jQ) ≫ genι Y) ⟶ Y.t.G),
      ∀ (n : ℕ) (v : Fin n → (epsAt (x ≫ toX Xo c) ⟶ Xo.univ.t.G)),
        SameVecs Y x v (fun i => e (v i)) ∧ ∀ χ : 𝓞 E →+* R,
          IsEigBasisAt Xo.univ.t.act (x ≫ toX Xo c) χ v ↔
            IsEigBasisAt Y.t.act ((x ≫ Y.jQ) ≫ genι Y) χ (fun i => e (v i)) := by
  obtain ⟨e₀, he₀, hb₀⟩ := BdryUnit.exists_eigEquiv Y.m0.toSABMap.cart Y.m0.toSABMap.act x (x ≫ toX Xo c) rfl
  obtain ⟨e, he, hb⟩ := BdryUnit.exists_eigEquiv Y.m.cart Y.m.act x ((x ≫ Y.jQ) ≫ genι Y) (Category.assoc _ _ _)
  refine ⟨e₀.symm.trans e, fun n v => ⟨fun i => ⟨e₀.symm (v i), ?_, (he _).symm⟩, fun χ => ?_⟩⟩
  · exact (he₀ _).symm.trans (congrArg (fun z => z.left) (e₀.apply_symm_apply (v i)))
  · have h := hb₀ χ n fun i => e₀.symm (v i)
    have hv : (fun i => e₀ (e₀.symm (v i))) = v := funext fun i => e₀.apply_symm_apply (v i)
    rw [hv] at h
    exact h.symm.trans (hb χ n fun i => e₀.symm (v i))

theorem frame_transfer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (R : Type) [CommRing R] (j : c.F →+* R) (x : Sp R ⟶ Xo.XF c), (∀ v w, FrU Xo c U τ j x v w → ∃ vb wb, FrY Y (compactOf Y U) τ j (x ≫ Y.jQ) vb wb ∧ SameVecs Y x v vb ∧ SameVecs Y x w wb) ∧ (∀ (V : Set (gen Y)) vb wb, Set.range x ⊆ U → FrY Y V τ j (x ≫ Y.jQ) vb wb → ∃ v w, FrU Xo c U τ j x v w ∧ SameVecs Y x v vb ∧ SameVecs Y x w wb) := by
  intro E _ _ _ H D l Xo c O _ β Y U τ R _ j x
  obtain ⟨e, he⟩ := exists_vecEquiv Y x
  have hs : (x ≫ Y.jQ) ≫ genStr Y = x ≫ toF Xo c := by
    rw [Category.assoc]
    exact congrArg (x ≫ ·) Y.jQ_over
  refine ⟨fun v w h => ⟨fun i => e (v i), fun i => e (w i),
    ⟨hs.trans h.1, ?_, ((he _ v).2 _).1 h.2.2.1, ((he _ w).2 _).1 h.2.2.2⟩, (he _ v).1, (he _ w).1⟩,
    fun V vb wb hU h => ?_⟩
  · rintro _ ⟨z, rfl⟩
    exact subset_closure ⟨x z, h.2.1 ⟨z, rfl⟩, by simp⟩
  · obtain ⟨v, rfl⟩ : ∃ v : Fin D.p → _, vb = fun i => e (v i) :=
      ⟨fun i => e.symm (vb i), funext fun i => (e.apply_symm_apply _).symm⟩
    obtain ⟨w, rfl⟩ : ∃ w : Fin D.q → _, wb = fun i => e (w i) :=
      ⟨fun i => e.symm (wb i), funext fun i => (e.apply_symm_apply _).symm⟩
    exact ⟨v, w, ⟨hs.symm.trans h.1, hU, ((he _ v).2 _).2 h.2.2.1, ((he _ w).2 _).2 h.2.2.2⟩, (he _ v).1, (he _ w).1⟩

end GlobalTheory.DetLine
