import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallHeightOneExistsDvdMul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.SquareSpread

theorem germ_res_hom {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) {x : X} (hx : x ∈ V) (s : Γ(X, U)) :
    (X.presheaf.germ V x hx).hom ((X.presheaf.map (homOfLE h).op).hom s) =
      (X.presheaf.germ U x (h hx)).hom s :=
  TopCat.Presheaf.germ_res_apply _ (homOfLE h) x hx s

theorem res_res_hom {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₂).op).hom ((X.presheaf.map (homOfLE h₁).op).hom s) =
      (X.presheaf.map (homOfLE (h₂.trans h₁)).op).hom s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem exists_res_eq {X : Scheme.{0}} {U : X.Opens} {x : X} (hx : x ∈ U) (s t : Γ(X, U))
    (h : (X.presheaf.germ U x hx).hom s = (X.presheaf.germ U x hx).hom t) :
    ∃ W : X.Opens, ∃ hW : W ≤ U, x ∈ W ∧
      (X.presheaf.map (homOfLE hW).op).hom s = (X.presheaf.map (homOfLE hW).op).hom t := by
  obtain ⟨W, hxW, iU, iV, e⟩ := TopCat.Presheaf.germ_eq X.presheaf x hx hx s t h
  refine ⟨W, iU.le, hxW, ?_⟩
  have h1 : iU = homOfLE iU.le := rfl
  have h2 : iV = homOfLE iU.le := Subsingleton.elim _ _
  rw [h1] at e
  rw [h2] at e
  exact e

end GlobalTheory.Mum.SquareSpread

open GlobalTheory.Mum.SquareSpread in

theorem GlobalTheory.Mum.unit_mul_sq_spread : ∀ (X : Scheme.{0}) (L2 : LB X) (h : L2.Sec) (x : X) (j₀ : L2.ι) (hx : x ∈ L2.U j₀) (u : (X.presheaf.stalk x)ˣ) (a : X.presheaf.stalk x), a ≠ 0 → (X.presheaf.germ (L2.U j₀) x hx).hom (h.f j₀) = u * a ^ 2 → ∃ V : X.Opens, x ∈ V ∧ ∃ a : Γ(X, V), a ≠ 0 ∧ ∀ j, ∃ u : Γ(X, V ⊓ L2.U j)ˣ, (X.presheaf.map (homOfLE inf_le_right).op).hom (h.f j) = (u : Γ(X, V ⊓ L2.U j)) * (X.presheaf.map (homOfLE inf_le_left).op).hom a ^ 2 := by
  intro X L2 h x j₀ hx u a ha hh

  obtain ⟨W₁, hW₁, hx₁, a', ha'⟩ := TopCat.Presheaf.exists_le_germ_eq X.presheaf a hx
  obtain ⟨W₂, hW₂, hx₂, u', hu'⟩ := TopCat.Presheaf.exists_le_germ_eq X.presheaf (u : X.presheaf.stalk x) hx₁
  obtain ⟨W₃, hW₃, hx₃, v', hv'⟩ := TopCat.Presheaf.exists_le_germ_eq X.presheaf ((u⁻¹ : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x) hx₂
  have l31 : W₃ ≤ W₁ := hW₃.trans hW₂
  have l30 : W₃ ≤ L2.U j₀ := l31.trans hW₁
  set A : Γ(X, W₃) := (X.presheaf.map (homOfLE l31).op).hom a' with hA
  set U' : Γ(X, W₃) := (X.presheaf.map (homOfLE hW₃).op).hom u' with hU'
  set H : Γ(X, W₃) := (X.presheaf.map (homOfLE l30).op).hom (h.f j₀) with hH
  have gA : (X.presheaf.germ W₃ x hx₃).hom A = a := by rw [hA, germ_res_hom]; exact ha'
  have gU : (X.presheaf.germ W₃ x hx₃).hom U' = u := by rw [hU', germ_res_hom]; exact hu'
  have gV : (X.presheaf.germ W₃ x hx₃).hom v' = ((u⁻¹ : (X.presheaf.stalk x)ˣ) : X.presheaf.stalk x) := hv'
  have gH : (X.presheaf.germ W₃ x hx₃).hom H = u * a ^ 2 := by rw [hH, germ_res_hom]; exact hh
  obtain ⟨W₄, hW₄, hx₄, e₄⟩ := exists_res_eq hx₃ (U' * v') 1 (by
    rw [map_mul, map_one, gU, gV, Units.mul_inv])
  obtain ⟨W₅, hW₅, hx₅, e₅⟩ := exists_res_eq hx₃ H (U' * A ^ 2) (by
    rw [map_mul, map_pow, gU, gA, gH])

  have lV3 : W₄ ⊓ W₅ ≤ W₃ := inf_le_left.trans hW₄
  have hxV : x ∈ W₄ ⊓ W₅ := ⟨hx₄, hx₅⟩
  have e₄' : (X.presheaf.map (homOfLE lV3).op).hom U' * (X.presheaf.map (homOfLE lV3).op).hom v' = 1 := by
    rw [← map_mul, ← map_one (X.presheaf.map (homOfLE lV3).op).hom, ← res_res_hom hW₄ (inf_le_left : W₄ ⊓ W₅ ≤ W₄),
      ← res_res_hom hW₄ (inf_le_left : W₄ ⊓ W₅ ≤ W₄) 1, e₄]
  have e₅' : (X.presheaf.map (homOfLE lV3).op).hom H = (X.presheaf.map (homOfLE lV3).op).hom U' *
      ((X.presheaf.map (homOfLE lV3).op).hom A) ^ 2 := by
    rw [← map_pow, ← map_mul, ← res_res_hom hW₅ (inf_le_right : W₄ ⊓ W₅ ≤ W₅),
      ← res_res_hom hW₅ (inf_le_right : W₄ ⊓ W₅ ≤ W₅) (U' * A ^ 2), e₅]
  let uV : Γ(X, W₄ ⊓ W₅)ˣ := ⟨_, _, e₄', by rw [mul_comm]; exact e₄'⟩
  refine ⟨W₄ ⊓ W₅, hxV, (X.presheaf.map (homOfLE lV3).op).hom A, ?_, ?_⟩
  · intro h0
    apply ha
    rw [← gA, ← germ_res_hom lV3 hxV, h0, map_zero]
  · intro j
    have k : W₄ ⊓ W₅ ⊓ L2.U j ≤ L2.U j ⊓ L2.U j₀ := le_inf inf_le_right (inf_le_left.trans (lV3.trans l30))
    refine ⟨res k (L2.g j j₀) * Units.map (X.presheaf.map (homOfLE (inf_le_left : W₄ ⊓ W₅ ⊓ L2.U j ≤ W₄ ⊓ W₅)).op).hom uV, ?_⟩
    have c := congrArg (X.presheaf.map (homOfLE k).op).hom (h.compat j j₀)
    rw [map_mul, res_res_hom, res_res_hom] at c
    have e6 := congrArg (X.presheaf.map (homOfLE (inf_le_left : W₄ ⊓ W₅ ⊓ L2.U j ≤ W₄ ⊓ W₅)).op).hom e₅'
    rw [map_mul, map_pow, hH, res_res_hom, res_res_hom, res_res_hom] at e6
    rw [Units.val_mul, Units.coe_map, res, Units.coe_map]
    simp only [MonoidHom.coe_coe, hA, res_res_hom] at e6 ⊢
    rw [c, e6, _root_.mul_assoc]
    congr 2
    exact (res_res_hom lV3 _ U').symm
