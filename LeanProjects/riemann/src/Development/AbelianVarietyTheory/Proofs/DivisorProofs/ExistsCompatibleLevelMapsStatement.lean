import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleLevelMaps
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_level_maps : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (σ : 𝓞 E ≃+* 𝓞 E), σ H.w0 = H.w0 →
  ∃ f : ℕ → D.La →+ D.La,
    (∀ n : ℕ, 0 < n → ∀ (c : 𝓞 E) (a : D.La), D.ModN n (f n (c • a) - σ c • f n a)) ∧
    (∀ n m : ℕ, 0 < n → 0 < m → ∀ a : D.La, D.ModN n (f (n * m) a - f n a)) ∧
    (∀ n : ℕ, 0 < n → ∀ a : D.La, ∃ b : D.La, D.ModN n (f n b - a)) ∧
    (∀ n : ℕ, 0 < n → ∀ a : D.La, D.ModN n (f n a) → D.ModN n a) ∧
    (∀ n : ℕ, 0 < n → ∀ a b : D.La, (n : ℤ) ∣ D.EF (f n a) (f n b) - D.EF a b) := by
  first | exact @GlobalTheory.TwistIsom.exists_semilinear_isometry | exact GlobalTheory.TwistIsom.exists_semilinear_isometry | (intros; apply GlobalTheory.TwistIsom.exists_semilinear_isometry <;> assumption)
