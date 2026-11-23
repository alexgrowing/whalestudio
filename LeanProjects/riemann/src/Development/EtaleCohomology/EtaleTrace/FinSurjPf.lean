import Development.EtaleCohomology.EtaleTrace.LCoverCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

def FSAffine : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k),
  ∀ (N d : ℕ) (ι : X ⟶ PN k N) (π : X ⟶ PN k d) (v : Fin (N + 1) → X.functionField) (w : Fin (d + 1) → X.functionField),
  IsClosedImmersion ι → Coord p ι v → Coord p π w →
  (∀ i, ∃ c : Fin (N + 1) → k, w i = ∑ j, kHom p (c j) * v j) →
  (∀ x : X, ∃ i, w i ≠ 0 ∧ ∀ j, v j / w i ∈ loc X x) →
  IsAffineHom π

def FSDense : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k),
  ∀ (d : ℕ) (π : X ⟶ PN k d) (w : Fin (d + 1) → X.functionField), Coord p π w →
  (∀ (m : ℕ) (F : MvPolynomial (Fin (d + 1)) k), F.IsHomogeneous m → eval₂ (kHom p) w F = 0 → F = 0) →
  IsDominant π

theorem FinSurj_of (h1 : PNBasic) (hA : FSAffine) (hD : FSDense) : FinSurj := by
  intro k _ X _ p hp N d ι π v w hι hπ cv cw hlin hx hind
  have hsep : IsSeparated (PNto k d) := (h1 k d).2.1
  have : IsProper (π ≫ PNto k d) := by rw [hπ]; exact hp
  have : IsProper π := IsProper.of_comp π (PNto k d)
  have : IsAffineHom π := hA k p N d ι π v w hι cv cw hlin hx
  have : IsDominant π := hD k p d π w cw hind
  refine ⟨IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩, ?_⟩
  exact surjective_of_isDominant_of_isClosed_range π (π.isClosedMap.isClosed_range)
