import Development.EtaleCohomology.EtaleSheaves.LeafGlueProperPf
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.ValuativeCriterion

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite LateralTheory.E.E4 LateralTheory.E.LeafGlueProperPf

namespace LateralTheory.E.LeafGlueIsProperPf

variable {Ω L : Type} [Field Ω] [Field L] [Algebra Ω L] {A B : Subalgebra Ω L} {u : L}

def cov {hAD hBD} (G : Glued Ω L A B (Dr Ω A u) hAD hBD) : G.C0.OpenCover :=
  Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) Bool (fun b => cond b (Sp A) (Sp B))
    (fun | true => G.iA | false => G.iB)
    (by
      intro x
      have hx : x ∈ Set.range G.iA.base ∪ Set.range G.iB.base := G.cover ▸ Set.mem_univ x
      rcases hx with ⟨z, rfl⟩ | ⟨z, rfl⟩
      · exact ⟨true, z, rfl⟩
      · exact ⟨false, z, rfl⟩)
    (by intro b; cases b <;> [exact G.hiB; exact G.hiA])

set_option backward.isDefEq.respectTransparency false in
theorem lft (h : GH Ω L A B u) {hAD hBD} (G : Glued Ω L A B (Dr Ω A u) hAD hBD) :
    LocallyOfFiniteType G.c0 := by
  refine IsZariskiLocalAtSource.of_openCover (P := @AlgebraicGeometry.LocallyOfFiniteType) (cov G) ?_
  intro b
  cases b
  · show LocallyOfFiniteType (G.iB ≫ G.c0)
    rw [G.hcB, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr h.2.2.2.2.1
  · show LocallyOfFiniteType (G.iA ≫ G.c0)
    rw [G.hcA, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr h.2.2.2.1

set_option backward.isDefEq.respectTransparency false in
theorem qc {hAD hBD} (G : Glued Ω L A B (Dr Ω A u) hAD hBD) : QuasiCompact G.c0 := by
  rw [HasAffineProperty.iff_of_isAffine (P := @AlgebraicGeometry.QuasiCompact)]
  refine ⟨?_⟩
  rw [← G.cover]
  exact (isCompact_range G.iA.base.hom.continuous).union (isCompact_range G.iB.base.hom.continuous)

def LeafGlueSep : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u) (G : Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)),
  IsSeparated G.c0

def LeafGlueExistence : Prop := ∀ (Ω L : Type) [Field Ω] [Field L] [Algebra Ω L] (A B : Subalgebra Ω L) (u : L)
  (h : GH Ω L A B u) (G : Glued Ω L A B (Dr Ω A u) (le_Dr_A A u) (le_Dr_B A B u h.2.2.2.2.2.2.2.2.2.2.2.1)),
  ValuativeCriterion.Existence G.c0

theorem LeafGlueIsProper_of (hS : LeafGlueSep) (hE : LeafGlueExistence) : LeafGlueIsProper := by
  intro Ω L _ _ _ A B u h G
  have := hS Ω L A B u h G
  have := qc G
  have := lft h G
  have : UniversallyClosed G.c0 := UniversallyClosed.of_valuativeCriterion _ (hE Ω L A B u h G)
  exact {}

end LateralTheory.E.LeafGlueIsProperPf
