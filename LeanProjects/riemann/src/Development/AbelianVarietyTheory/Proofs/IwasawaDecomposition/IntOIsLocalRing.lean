import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorsUniversalBasis

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.FactorDepth

namespace GlobalTheory.LatDRFree

attribute [local instance] Over.cartesianMonoidalCategory

theorem intO_isLocalRing (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] : IsLocalRing ↥(intO C) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  have hu : ∀ b : ↥(intO C), ‖(b : C)‖ = 1 → IsUnit b := fun b hb => by
    have h0 : (b : C) ≠ 0 := fun h => by simp [h] at hb
    have hi : (b : C)⁻¹ ∈ intO C := by
      show ‖(b : C)⁻¹‖ ≤ 1
      rw [norm_inv, hb, inv_one]
    exact IsUnit.of_mul_eq_one ⟨_, hi⟩ (Subtype.ext (mul_inv_cancel₀ h0))
  have ha : ‖(a : C)‖ ≤ 1 := a.2
  rcases ha.eq_or_lt with h | h
  · exact Or.inl (hu a h)
  · refine Or.inr (hu _ ?_)
    have : ‖(1 : C) + (-(a : C))‖ = max ‖(1 : C)‖ ‖-(a : C)‖ :=
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg, norm_one]; exact h.ne')
    rw [norm_neg, norm_one, max_eq_left h.le, ← sub_eq_add_neg] at this
    exact this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

open MonObj in
theorem comb_map {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') {x : Sp S ⟶ X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} {cf : Fin m → S} {w : Sp (DualNumber S) ⟶ t.G.left}
    (h : IsCombAtG t x v cf w) :
    IsCombAtG t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ v i) (fun i => φ (cf i)) (spMap (dualMap φ) ≫ w) := by
  obtain ⟨u, hu, rfl⟩ := h
  let δ : tEpsG (spMap φ ≫ x) ⟶ tEpsG x := Over.homMk (spMap (dualMap φ)) (by
    show spMap (dualMap φ) ≫ spMap (algebraMap S (DualNumber S)) ≫ x =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap φ ≫ x
    rw [← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_alg])
  refine ⟨fun i => δ ≫ u i, fun i => ?_, ?_⟩
  · simp only [Over.comp_left, δ, Over.homMk_left]
    rw [hu i, ← Category.assoc, ← Category.assoc, spMap_comp', spMap_comp', dualMap_comp_epsMul]
  · rw [List.prod_ofFn, List.prod_ofFn, ← comp_prodT]
    rfl

theorem latDR_free : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (xO : Sp ↥(intO C) ⟶ X), (∀ xO' : Sp ↥(intO C) ⟶ X, spMap (intO C).subtype ≫ xO' = spMap (intO C).subtype ≫ xO → xO' = xO) → ∃ (g : ℕ) (v : Fin g → (Sp (DualNumber C) ⟶ t.G.left)), (∀ i, IsTanAtG t (spMap (intO C).subtype ≫ xO) (v i)) ∧ (∀ w, IsTanAtG t (spMap (intO C).subtype ≫ xO) w → ∃! cf : Fin g → C, IsCombAtG t (spMap (intO C).subtype ≫ xO) v cf w) ∧ ∀ (cf : Fin g → C) w, IsCombAtG t (spMap (intO C).subtype ≫ xO) v cf w → (w ∈ latDR t (spMap (intO C).subtype ≫ xO) ↔ ∀ i, ‖cf i‖ ≤ 1) := by
  intro E _ _ _ H X t C _ _ xO huniq
  have := intO_isLocalRing C
  obtain ⟨n, D, hD, hDb⟩ := GlobalTheory.LieLocBasis.exists_lie_basis_stable E H X t (↥(intO C)) xO
  have h1 : spMap (RingHom.id ↥(intO C)) = 𝟙 _ := Spec.map_id _
  have h2 : dualMap (RingHom.id ↥(intO C)) = RingHom.id _ := by
    refine RingHom.ext fun z => ?_
    ext <;> simp [dualMap]
  have h3 : spMap (dualMap (RingHom.id ↥(intO C))) = 𝟙 _ := by rw [h2]; exact Spec.map_id _
  have hD0 : ∀ w, IsTanAtG t xO w → ∃! a : Fin n → ↥(intO C), IsCombAtG t xO D a w := by
    have h := hDb _ (RingHom.id ↥(intO C))
    simp only [h1, h3, Category.id_comp] at h
    exact h
  have hDk := fun j => isTanAtG_map t (intO C).subtype (hD j)
  refine ⟨n, fun e => spMap (dualMap (intO C).subtype) ≫ D e, hDk, hDb C _, fun cf w hw => ⟨?_, fun hc => ?_⟩⟩
  · rintro ⟨xO', hx, vO, hv, rfl⟩
    obtain rfl := huniq xO' hx
    obtain ⟨a, ha, -⟩ := hD0 vO hv
    have e := (hDb C _ _ (isTanAtG_map t (intO C).subtype hv)).unique hw (comb_map t (intO C).subtype ha)
    intro i
    rw [e]
    exact (a i).2
  · let a : Fin n → ↥(intO C) := fun i => ⟨cf i, hc i⟩
    have ha : IsCombAtG t xO D a (combT xO (fun j => ovT (hD j)) a).left :=
      (isCombAtG_iff t xO (fun j => ovT (hD j)) a _).2 rfl
    refine ⟨xO, rfl, _, isTanAtG_of _ (combT_tan _ (fun j => ovT (hD j)) (fun j => smT_zero_ovT _) a), ?_⟩
    have hb := comb_map t (intO C).subtype ha
    exact ((isCombAtG_iff t _ (fun j => ovT (hDk j)) _ _).1 hb).symm.trans
      ((isCombAtG_iff t _ (fun j => ovT (hDk j)) _ _).1 hw)

end GlobalTheory.LatDRFree
