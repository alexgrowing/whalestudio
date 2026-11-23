import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorRatioRegularOfMatrixIdentity
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.DetMemSubring
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minor_ratio_regular_of_matrix_identity : ∀ {Ω : Type} [Field Ω] {n r : ℕ} (R : Subring Ω) (A C : Matrix (Fin n) (Fin r) Ω)
    (B : Matrix (Fin r) (Fin n) Ω) (T : Matrix (Fin r) (Fin r) Ω) (a : Ω) (hAT : A * T = a • C) (ha : a ≠ 0)
    (hT : T.det ≠ 0) (hBC : B * C = 1) (hC : ∀ j l, C j l ∈ R) (hB : ∀ l j, B l j ∈ R) (J₀ : Fin r → Fin n)
    (hz : (A.submatrix J₀ id).det ≠ 0)
    (hr : ∀ J : Fin r → Fin n, (A.submatrix J id).det / (A.submatrix J₀ id).det ∈ R),
    (C.submatrix J₀ id).det ≠ 0 ∧ (C.submatrix J₀ id).det ∈ R ∧ (C.submatrix J₀ id).det⁻¹ ∈ R ∧
      (A.submatrix J₀ id).det * T.det = a ^ r * (C.submatrix J₀ id).det := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.minor_isUnit_of_leftInverse | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.minor_isUnit_of_leftInverse | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.Frm.minor_isUnit_of_leftInverse <;> assumption)
