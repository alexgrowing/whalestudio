import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.CechDR

variable {X X' : Scheme.{0}}

theorem Pair.exists_basicOpen (φ : X' ⟶ X) (W : X'.affineOpens) {x : X'} (hx : x ∈ W.1) :
    ∃ (p : Pair φ) (f : Γ(X', W.1)), p.1.1.1 = X'.basicOpen f ∧ x ∈ p.1.1.1 := by
  obtain ⟨U, hU, hxU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show φ.base x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨f, hf, hxf⟩ := W.2.exists_basicOpen_le (V := W.1 ⊓ φ ⁻¹ᵁ U) ⟨x, hx, hxU⟩ hx
  exact ⟨⟨(⟨X'.basicOpen f, W.2.basicOpen f⟩, ⟨U, hU⟩), hf.trans inf_le_right⟩, f, rfl, hxf⟩

theorem Pair.exists_le_le (φ : X' ⟶ X) (p q : Pair φ) {x : X'} (hx : x ∈ p.1.1.1 ⊓ q.1.1.1) :
    ∃ r : Pair φ, r ≤ p ∧ r ≤ q ∧ x ∈ r.1.1.1 := by
  have hy : φ.base x ∈ p.1.2.1 ⊓ q.1.2.1 := ⟨p.2 hx.1, q.2 hx.2⟩
  obtain ⟨U, hU, hxU, hUle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hy
  obtain ⟨U', hU', hxU', hU'le⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X'.isBasis_affineOpens
    (show x ∈ p.1.1.1 ⊓ q.1.1.1 ⊓ φ ⁻¹ᵁ U from ⟨hx, hxU⟩)
  refine ⟨⟨(⟨U', hU'⟩, ⟨U, hU⟩), hU'le.trans inf_le_right⟩, ?_, ?_, hxU'⟩
  · exact ⟨hU'le.trans (inf_le_left.trans inf_le_left), hUle.trans inf_le_left⟩
  · exact ⟨hU'le.trans (inf_le_left.trans inf_le_right), hUle.trans inf_le_right⟩

end GlobalTheory.CechDR

namespace GlobalTheory.CechDR
open Opposite
variable {R' : Type} [CommRing R'] {X X' : Scheme.{0}}

theorem Pair.exists_le (φ : X' ⟶ X) (W : X'.affineOpens) {x : X'} (hx : x ∈ W.1) :
    ∃ (p : Pair φ) (hp : p.1.1 ≤ W), x ∈ p.1.1.1 := by
  obtain ⟨p, f, e, hxp⟩ := Pair.exists_basicOpen φ W hx
  exact ⟨p, show p.1.1.1 ≤ W.1 from e ▸ X'.basicOpen_le f, hxp⟩

theorem sec_eq_of_pair (φ : X' ⟶ X) (s' : X' ⟶ Sp R') (W : X'.affineOpens)
    (a b : (OAff s').obj (op W))
    (h : ∀ (p : Pair φ) (hp : p.1.1 ≤ W), mp (OAff s') (homOfLE hp).op a = mp (OAff s') (homOfLE hp).op b) :
    a = b := by
  refine TopCat.Presheaf.section_ext X'.sheaf W.1 a b fun x hx ↦ ?_
  obtain ⟨p, hp, hxp⟩ := Pair.exists_le φ W hx
  have e : (X'.presheaf.germ p.1.1.1 x hxp).hom ((X'.presheaf.map (homOfLE (show p.1.1.1 ≤ W.1 from hp)).op).hom a) =
      (X'.presheaf.germ p.1.1.1 x hxp).hom ((X'.presheaf.map (homOfLE (show p.1.1.1 ≤ W.1 from hp)).op).hom b) :=
    congrArg _ (h p hp)
  have k := X'.presheaf.germ_res (homOfLE (show p.1.1.1 ≤ W.1 from hp)) x hxp
  exact (congrArg (fun t ↦ t.hom a) k).symm.trans (e.trans (congrArg (fun t ↦ t.hom b) k))

end GlobalTheory.CechDR
