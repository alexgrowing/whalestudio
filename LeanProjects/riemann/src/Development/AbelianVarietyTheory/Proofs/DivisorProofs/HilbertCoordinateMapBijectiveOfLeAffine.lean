import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasicIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineHilbertCoordinateMapBasicOpenBijectiveStatement
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace GlobalTheory.HilbAff

theorem coord_bijective_of_le_affine : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ) (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (W W' : Z.affineOpens), (W' : Z.Opens) ≤ W → Function.Bijective (GlobalTheory.HilbAff.coord A B e σ y W) → Function.Bijective (GlobalTheory.HilbAff.coord A B e σ y W') := by
  intro A B _ _ _ N r e σ Z y W W' hle hW
  have hbas : ∀ f : Γ(Z, W), Function.Bijective (coord A B e σ y (Z.basicOpen f)) := by
    intro f
    rw [GlobalTheory.T.affineHilbertCoordinateMap_basicOpen_bijective A B N r e σ Z y W f]
    exact ⟨LocalizedModule.map_injective _ _ hW.1, LocalizedModule.map_surjective _ _ hW.2⟩
  let s : Set Γ(Z, W') := {g | Function.Bijective (coord A B e σ y (Z.basicOpen g))}
  have hspan : Ideal.span s = ⊤ := by
    rw [← W'.2.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter W.2 W'.2 x ⟨hle hx, hx⟩
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨g, ?_⟩, ?_⟩
    · show Function.Bijective _
      rw [← hfg]; exact hbas f
    · show x ∈ Z.basicOpen g
      rw [← hfg]; exact hxf
  exact bijective_of_localized_span s hspan _ fun g => (GlobalTheory.T.affineHilbertCoordinateMap_basicOpen_bijective A B N r e σ Z y W' g.1).1 g.2

end GlobalTheory.HilbAff
