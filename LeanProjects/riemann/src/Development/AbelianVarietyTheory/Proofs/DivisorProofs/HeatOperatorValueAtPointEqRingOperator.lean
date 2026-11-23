import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.HeatPointValue

section Val

variable {A : Type} [CommRing A] {Y : Scheme.{0}}

def evalAt (x : Sp A ⟶ Y) (V : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) : Γ(Y, V) →+* A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp (x.appLE V ⊤ h).hom

theorem valR_eq_evalAt (x : Sp A ⟶ Y) (V : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(Y, V)) :
    valR x V f = evalAt x V h f := by
  unfold valR
  rw [dif_pos h]
  rfl

theorem evalAt_constFn {B : Type} [CommRing B] (x : Sp A ⟶ Y) (p : Y ⟶ Sp B) (ψ : B →+* A) (hx : x ≫ p = spMap ψ)
    (V : Y.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V) (a : B) : evalAt x V h (constFn p V a) = ψ a := by
  have e₁ : p.appLE ⊤ V (fun _ _ => trivial) ≫ x.appLE V ⊤ h = (x ≫ p).appLE ⊤ ⊤ le_rfl :=
    Scheme.Hom.appLE_comp_appLE x p ⊤ V ⊤ _ h
  have e₂ : ∀ q : Sp A ⟶ Sp B, q.appLE ⊤ ⊤ le_rfl = q.appTop := fun q => (Scheme.Hom.app_eq_appLE _).symm
  rw [e₂, hx] at e₁
  have n := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ))
  change (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom (ψ a) =
    (spMap ψ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom a) at n
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
    ((p.appLE ⊤ V (fun _ _ => trivial) ≫ x.appLE V ⊤ h).hom ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom a)) = ψ a
  rw [e₁, ← n]
  exact (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id_apply _

theorem rsT_same {O₀ : Y.Opens} (s : Γ(Y, O₀)) : rsT s O₀ = s := by
  have e : rsT s O₀ = resG Y le_rfl s := dif_pos le_rfl
  rw [e]
  change (Y.presheaf.map (𝟙 _)).hom s = s
  rw [Y.presheaf.map_id]; rfl

end Val

theorem value_acts : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (X : Scheme.{0}) (m : G.left ⟶ X) (L : LB X) (n : ℕ) (dd : Fin n → Fld G.left) (D : R → R) (h : Heat G m L dd D) (i0 : h.J) (Ω : Type) [CommRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ G.left), x ≫ G.hom = spMap φ → ∀ (δ : Fin n → Derivation ℤ Ω Ω), (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → ∀ (dΩ : Derivation ℤ Ω Ω), ⊤ ≤ x ⁻¹ᵁ h.W i0 → (∀ O f, O ≤ h.W i0 → ⊤ ≤ x ⁻¹ᵁ O → valR x O (h.d i0 O f) = dΩ (valR x O f)) → (∀ r, dΩ (φ r) = φ (D r)) ∧ ∀ (k : ℕ) (τ τ' : SecM m L k), h.Acts k τ τ' → valR x (h.W i0) (rsT (τ'.f fun _ => h.j i0) (h.W i0)) = ringOp ⇑dΩ (fun a => ⇑(δ a)) (φ.mapMatrix h.Θ) (fun a => φ (h.u a)) (valR x _ (h.p i0)) (valR x _ (h.p' i0)) k (valR x (h.W i0) (rsT (τ.f fun _ => h.j i0) (h.W i0))) := by
  intro R _ G _ _ X m L n dd D h i0 Ω _ φ x hx δ hδ dΩ hW hd
  have hδ' : ∀ a f, evalAt x _ hW (dd a (h.W i0) f) = δ a (evalAt x _ hW f) := fun a f => by
    rw [← valR_eq_evalAt, ← valR_eq_evalAt]; exact hδ a _ f hW
  have hd' : ∀ f, evalAt x _ hW (h.d i0 (h.W i0) f) = dΩ (evalAt x _ hW f) := fun f => by
    rw [← valR_eq_evalAt, ← valR_eq_evalAt]; exact hd _ f le_rfl hW
  have hc := evalAt_constFn x G.hom φ hx _ hW
  refine ⟨fun r => ?_, fun k τ τ' ha => ?_⟩
  · rw [← hc, ← hc, ← hd', (h.lift i0).2 _ le_rfl]
  · rw [ha i0]
    simp only [valR_eq_evalAt x _ hW]
    unfold GlobalTheory.Heat.op ringOp
    simp only [map_add, map_sub, map_mul, map_sum, map_pow, map_natCast, map_ofNat, hδ', hd', hc, rsT_same,
      RingHom.mapMatrix_apply, Matrix.map_apply]

end GlobalTheory.HeatPointValue
