import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFrPtOfEigFrame

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.OpenReg

namespace GlobalTheory.CuspFrom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def IsEigBasis {S : Scheme.{0}} (t : SAB H S) {R : Type} [CommRing R] (φ : c.F →+* R) (x : Sp R ⟶ S) (τ : E →+* ℂ)
    {n : ℕ} (v : Fin n → (Sp (DualNumber R) ⟶ t.G.left)) : Prop :=
  (∀ i, IsTanAtG t x (v i)) ∧ (∀ i (a : 𝓞 E), v i ≫ (t.act.act a).left = spMap (epsMul (φ (embK c τ a))) ≫ v i) ∧
    ∀ w, IsTanAtG t x w → (∀ a : 𝓞 E, w ≫ (t.act.act a).left = spMap (epsMul (φ (embK c τ a))) ≫ w) →
      ∃! a : Fin n → R, IsCombAtG t x v a w

variable {O : Type} [CommRing O] {β : O →+* c.F}

theorem EigFrame.isEigBasis {Z : Model Xo c β} {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X}
    (g : EigFrame Z φ x) (τ : E →+* ℂ) : IsEigBasis Z.t φ x τ (g.v τ) :=
  ⟨g.tan τ, g.eig τ, g.basis τ⟩

def eigFrameOf {Z : Model Xo c β} {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ Z.X}
    (v : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber R) ⟶ Z.t.G.left)) (h : ∀ τ, IsEigBasis Z.t φ x τ (v τ)) :
    EigFrame Z φ x :=
  ⟨v, fun τ => (h τ).1, fun τ => (h τ).2.1, fun τ => (h τ).2.2⟩

section Transport

variable {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
  {R : Type} [CommRing R] {φ : c.F →+* R} {x : Sp R ⟶ S'} {τ : E →+* ℂ} {n : ℕ}

theorem isEigBasis_push {v : Fin n → (Sp (DualNumber R) ⟶ t'.G.left)} (h : IsEigBasis t' φ x τ v) :
    IsEigBasis t φ (x ≫ f) τ (fun i => v i ≫ m.φ) := by
  have hv : ∀ i, v i ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x := fun i => (h.1 i).1
  refine ⟨fun i => (tan_iff m rfl (hv i)).2 (h.1 i), fun i a => (eig_iff m (hv i) a _).2 (h.2.1 i a),
    fun w hw he => ?_⟩
  obtain ⟨w', hw1, rfl⟩ := exists_lift m (spMap (algebraMap R (DualNumber R)) ≫ x) w (by rw [hw.1, Category.assoc])
  have hb := h.2.2 w' ((tan_iff m rfl hw1).1 hw) fun a => (eig_iff m hw1 a _).1 (he a)
  exact (existsUnique_congr fun cf => comb_iff m rfl hv cf hw1).2 hb

theorem isEigBasis_pull {v : Fin n → (Sp (DualNumber R) ⟶ t.G.left)} (h : IsEigBasis t φ (x ≫ f) τ v) :
    ∃ v' : Fin n → (Sp (DualNumber R) ⟶ t'.G.left), (∀ i, v' i ≫ m.φ = v i) ∧ IsEigBasis t' φ x τ v' := by
  choose v' hv1 hv2 using fun i =>
    exists_lift m (spMap (algebraMap R (DualNumber R)) ≫ x) (v i) (by rw [(h.1 i).1, Category.assoc])
  have e : v = fun i => v' i ≫ m.φ := funext fun i => (hv2 i).symm
  subst e
  refine ⟨v', fun i => rfl, fun i => (tan_iff m rfl (hv1 i)).1 (h.1 i), fun i a => (eig_iff m (hv1 i) a _).1 (h.2.1 i a),
    fun w hw he => ?_⟩
  have hb := h.2.2 (w ≫ m.φ) ((tan_iff m rfl hw.1).2 hw) fun a => (eig_iff m hw.1 a _).2 (he a)
  exact (existsUnique_congr fun cf => comb_iff m rfl hv1 cf hw.1).1 hb

end Transport

end GlobalTheory.CuspFrom
