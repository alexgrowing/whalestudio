import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeBasisModN
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_lattice_basis_mod_n : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (N : ℕ), 0 < N → ∀ T : 𝓞 E →+ ℤ, (∀ c, T (H.bar c) = - T c) → (∀ c : 𝓞 E, (∀ d : 𝓞 E, (N : ℤ) ∣ T (c * d)) → ∃ b : 𝓞 E, c = N • b) → ∃ e : Fin (D.p + D.q) → D.La, (∀ a : D.La, ∃ c : Fin (D.p + D.q) → 𝓞 E, D.ModN N (a - ∑ i, c i • e i)) ∧ ∀ c d : Fin (D.p + D.q) → 𝓞 E, (N : ℤ) ∣ D.EF (∑ i, c i • e i) (∑ i, d i • e i) - ∑ i, T (c i * H.bar (d i)) := by
  first | exact @GlobalTheory.OrthoFrame.frame | exact GlobalTheory.OrthoFrame.frame | (intros; apply GlobalTheory.OrthoFrame.frame <;> assumption)
