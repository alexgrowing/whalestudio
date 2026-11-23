import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

attribute [local instance] Over.cartesianMonoidalCategory

namespace MainStatements.Hodge.Pf.WedgeProjections

theorem affInf {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (hs : IsSeparated s)
    (U V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) : IsAffineOpen (U ⊓ V) := by
  have : IsAffineHom (Limits.pullback.diagonal s) := inferInstance
  exact isAffineHom_diagonal_iff.mp this ⊤ (isAffineOpen_top _) U (by simp) V (by simp) hU hV

@[reducible] def pairSL {X X' : Scheme.{0}} (φ : X' ⟶ X)
    (hX : ∀ U V : X.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V))
    (hX' : ∀ U V : X'.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V)) :
    SemilatticeInf (Pair φ) :=
  { (inferInstance : PartialOrder (Pair φ)) with
    inf := fun p q ↦ ⟨(⟨p.1.1.1 ⊓ q.1.1.1, hX' _ _ p.1.1.2 q.1.1.2⟩, ⟨p.1.2.1 ⊓ q.1.2.1, hX _ _ p.1.2.2 q.1.2.2⟩),
      by
        show p.1.1.1 ⊓ q.1.1.1 ≤ φ ⁻¹ᵁ (p.1.2.1 ⊓ q.1.2.1)
        rw [Scheme.Hom.preimage_inf]
        exact inf_le_inf p.2 q.2⟩
    inf_le_left := fun p q ↦ ⟨(inf_le_left : p.1.1.1 ⊓ q.1.1.1 ≤ p.1.1.1), (inf_le_left : p.1.2.1 ⊓ q.1.2.1 ≤ p.1.2.1)⟩
    inf_le_right := fun p q ↦ ⟨(inf_le_right : p.1.1.1 ⊓ q.1.1.1 ≤ q.1.1.1), (inf_le_right : p.1.2.1 ⊓ q.1.2.1 ≤ q.1.2.1)⟩
    le_inf := fun a b c hab hac ↦ ⟨(le_inf hab.1 hac.1 : a.1.1.1 ≤ b.1.1.1 ⊓ c.1.1.1),
      (le_inf hab.2 hac.2 : a.1.2.1 ≤ b.1.2.1 ⊓ c.1.2.1)⟩ }

theorem pair_cover {X X' : Scheme.{0}} (φ : X' ⟶ X) : ⨆ p : Pair φ, p.1.1.1 = ⊤ := by
  refine eq_top_iff.2 (fun x _ => ?_)
  obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
    (show φ x ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨U, hU, hxU, hUV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X'.isBasis_affineOpens)
    (show x ∈ φ ⁻¹ᵁ V from hxV)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(⟨U, hU⟩, ⟨V, hV⟩), hUV⟩, hxU⟩

theorem pairRes_pull2_injective (hD : DescentSt) (hL : LowSt) {R : Type} [CommRing R] {X X' : Scheme.{0}}
    (s : X ⟶ Sp R) (s' : X' ⟶ Sp R) (φ : X' ⟶ X) (hs : IsSeparated s) (hs' : IsSeparated s') :
    Function.Injective (pairRes φ s').pull2 := by
  letI : SemilatticeInf (Pair φ) := pairSL φ (affInf s hs) (affInf s' hs')
  let S : Sys X' (Pair φ) := ⟨fun p => p.1.1, fun _ _ => rfl, pair_cover φ⟩
  have hq : AllQIso (pairRes φ s') := hD R X' s' hs' (Pair φ) S
  exact (hL R _ _ _ _ (pairRes φ s') hq).2.1.1

end MainStatements.Hodge.Pf.WedgeProjections
