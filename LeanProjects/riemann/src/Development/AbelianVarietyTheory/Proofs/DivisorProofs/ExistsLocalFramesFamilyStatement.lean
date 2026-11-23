import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalFramesFamily
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalModelNonvanishingWeights
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_frames_family : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (n : ℕ) (r m : Fin n → ℕ) (E F : Fin n → B.X.Modules) (u : ∀ i, F i ⟶ E i), (∀ (i : Fin n) (x : B.X), ∃ (V : B.X.Opens) (eF : Fin (m i) → Γ(F i, V)) (eE : Fin (r i) → Γ(E i, V)) (a : Matrix (Fin (r i)) (Fin (m i)) Γ(B.X, V)), x ∈ V ∧ IsAffineOpen V ∧ GlobalTheory.VB.IsFrame eF ∧ GlobalTheory.VB.IsFrame eE ∧ (∀ j, (u i).app V (eF j) = ∑ k, a k j • eE k) ∧ ∃ J : Fin (r i) → Fin (m i), (a.submatrix id J).det ≠ 0) → ∃ (B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B), GlobalTheory.IsNormalScheme B'.X ∧ f.relDim = 0 ∧ ∀ (i : Fin n) (y : B'.X), ∃ (V : B'.X.Opens) (eF : Fin (m i) → Γ((Scheme.Modules.pullback f.f).obj (F i), V)) (eE : Fin (r i) → Γ((Scheme.Modules.pullback f.f).obj (E i), V)) (a : Matrix (Fin (r i)) (Fin (m i)) Γ(B'.X, V)) (J : Fin (r i) → Fin (m i)), y ∈ V ∧ GlobalTheory.VB.IsFrame eF ∧ GlobalTheory.VB.IsFrame eE ∧ (∀ j, ((Scheme.Modules.pullback f.f).map (u i)).app V (eF j) = ∑ k, a k j • eE k) ∧ (a.submatrix id J).det ≠ 0 ∧ ∀ K : Fin (r i) → Fin (m i), (a.submatrix id J).det ∣ (a.submatrix id K).det := by
  first | exact @GlobalTheory.MinorDivide.exists_modification_minor_dvd | exact GlobalTheory.MinorDivide.exists_modification_minor_dvd | (intros; apply GlobalTheory.MinorDivide.exists_modification_minor_dvd <;> assumption)
