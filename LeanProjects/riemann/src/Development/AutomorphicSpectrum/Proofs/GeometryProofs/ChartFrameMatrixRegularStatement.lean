import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ChartFrameMatrixRegular
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProdUpdateDiv
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_frame_matrix_regular : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) (x : κ → Ω) (S : Type) [Fintype S] (r n m : S → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (cc : ∀ s, Fin (r s) → E) (M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω) (T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (c₀ : κ) (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) (g : Ω), x c₀ ≠ 0 → g ∈ chartSub x c₀ → g ≠ 0 → (∀ s j l, φ s j (cc s l) = x c₀ ^ m s * (M s * T s) j l) → (∀ q, stepMinor (flagB M T q.1) q.2 (J q) ≠ 0) → algebraMap Ω (GenField Ω r) g ∈ chartSub (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r) ∧ locSub (chartSub (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r)) (algebraMap Ω (GenField Ω r) g) = ratioRing (locSub (chartSub x c₀) g) (flagB M T) J := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.chartRing_eq_ratioRing | exact GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.chartRing_eq_ratioRing | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagBun.Sm.chartRing_eq_ratioRing <;> assumption)
