import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.StalkDerField

variable {X : Scheme.{0}} {W : X.Opens} {d : Fld X} {x : X}

theorem germ_field_congr (hd : IsField W d) {O O' : X.Opens} (hO : x ∈ O) (hO' : x ∈ O')
    (hOW : O ≤ W) (hO'W : O' ≤ W) (f : Γ(X, O)) (f' : Γ(X, O'))
    (h : (X.presheaf.germ O x hO).hom f = (X.presheaf.germ O' x hO').hom f') :
    (X.presheaf.germ O x hO).hom (d O f) = (X.presheaf.germ O' x hO').hom (d O' f') := by
  obtain ⟨V, hV, iU, iV, e⟩ := TopCat.Presheaf.germ_eq X.presheaf x hO hO' f f' h
  have h1 : (X.presheaf.germ O x hO).hom (d O f) =
      (X.presheaf.germ V x hV).hom (d V (resG X (leOfHom iU) f)) := by
    rw [hd.2.2 O V (leOfHom iU) hOW f]
    exact (TopCat.Presheaf.germ_res_apply X.presheaf iU x hV _).symm
  have h2 : (X.presheaf.germ O' x hO').hom (d O' f') =
      (X.presheaf.germ V x hV).hom (d V (resG X (leOfHom iV) f')) := by
    rw [hd.2.2 O' V (leOfHom iV) hO'W f']
    exact (TopCat.Presheaf.germ_res_apply X.presheaf iV x hV _).symm
  have e' : resG X (leOfHom iU) f = resG X (leOfHom iV) f' := e
  rw [h1, h2, e']

theorem exists_rep (hxW : x ∈ W) (t : X.presheaf.stalk x) :
    ∃ (O : X.Opens) (hO : x ∈ O) (_ : O ≤ W) (f : Γ(X, O)), (X.presheaf.germ O x hO).hom f = t := by
  obtain ⟨U, m, s, hs⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf t
  refine ⟨U ⊓ W, ⟨m, hxW⟩, inf_le_right, resG X (inf_le_left : U ⊓ W ≤ U) s, ?_⟩
  rw [← hs]
  exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE inf_le_left) x ⟨m, hxW⟩ s

theorem exists_rep₂ (hxW : x ∈ W) (t t' : X.presheaf.stalk x) :
    ∃ (O : X.Opens) (hO : x ∈ O) (_ : O ≤ W) (f f' : Γ(X, O)),
      (X.presheaf.germ O x hO).hom f = t ∧ (X.presheaf.germ O x hO).hom f' = t' := by
  obtain ⟨O₁, h₁, hW₁, f₁, e₁⟩ := exists_rep hxW t
  obtain ⟨O₂, h₂, hW₂, f₂, e₂⟩ := exists_rep hxW t'
  refine ⟨O₁ ⊓ O₂, ⟨h₁, h₂⟩, inf_le_left.trans hW₁, resG X (inf_le_left : O₁ ⊓ O₂ ≤ O₁) f₁,
    resG X (inf_le_right : O₁ ⊓ O₂ ≤ O₂) f₂, ?_, ?_⟩
  · rw [← e₁]; exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE inf_le_left) x ⟨h₁, h₂⟩ f₁
  · rw [← e₂]; exact TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE inf_le_right) x ⟨h₁, h₂⟩ f₂

def germMap (hxW : x ∈ W) (t : X.presheaf.stalk x) : X.presheaf.stalk x :=
  (X.presheaf.germ _ x (exists_rep hxW t).choose_spec.choose).hom
    (d _ (exists_rep hxW t).choose_spec.choose_spec.choose_spec.choose)

theorem germMap_germ (hd : IsField W d) (hxW : x ∈ W) {O : X.Opens} (hO : x ∈ O) (hOW : O ≤ W)
    (f : Γ(X, O)) :
    germMap (d := d) hxW ((X.presheaf.germ O x hO).hom f) = (X.presheaf.germ O x hO).hom (d O f) := by
  have hs := (exists_rep hxW ((X.presheaf.germ O x hO).hom f)).choose_spec.choose_spec
  exact germ_field_congr hd _ hO hs.choose hOW _ f hs.choose_spec.choose_spec

end GlobalTheory.StalkDerField

open GlobalTheory.StalkDerField in

theorem GlobalTheory.StalkDerField.exists_stalk_derivation : ∀ (X : Scheme.{0}) (W : X.Opens) (d : Fld X), IsField W d → ∀ (x : X), x ∈ W → ∃ δ : Derivation ℤ (X.presheaf.stalk x) (X.presheaf.stalk x), ∀ (O : X.Opens) (hO : x ∈ O), O ≤ W → ∀ f, δ ((X.presheaf.germ O x hO).hom f) = (X.presheaf.germ O x hO).hom (d O f) := by
  intro X W d hd x hxW
  let g : X.presheaf.stalk x →+ X.presheaf.stalk x := AddMonoidHom.mk' (germMap (d := d) hxW) (by
    intro t t'
    obtain ⟨O, hO, hOW, f, f', rfl, rfl⟩ := exists_rep₂ hxW t t'
    rw [← map_add, germMap_germ hd hxW hO hOW, germMap_germ hd hxW hO hOW,
      germMap_germ hd hxW hO hOW, hd.1 O hOW f f', map_add])
  refine ⟨Derivation.mk' g.toIntLinearMap ?_, fun O hO hOW f => germMap_germ hd hxW hO hOW f⟩
  intro t t'
  obtain ⟨O, hO, hOW, f, f', rfl, rfl⟩ := exists_rep₂ hxW t t'
  show germMap hxW _ = _ • germMap hxW _ + _ • germMap hxW _
  rw [← map_mul, germMap_germ hd hxW hO hOW, germMap_germ hd hxW hO hOW,
    germMap_germ hd hxW hO hOW, hd.2.1 O hOW f f', smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul]
