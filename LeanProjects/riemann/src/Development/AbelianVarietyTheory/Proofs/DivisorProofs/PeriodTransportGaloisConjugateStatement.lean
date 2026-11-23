import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodTransportGaloisConjugate
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.period_transport_galois_conjugate : ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (L : LB A.left) (L' : LB A'.left) (n : ℕ)
    (u : HolUnif A L n) (u' : HolUnif A' L' n) (g : ℂ ≃+* ℂ) (p : A'.left ⟶ A.left),
    IsGrpPullback A' A (spMap (g : ℂ →+* ℂ)) p → ∀ (Ω₀ Ω₁ : ℂ), Ω₀ ≠ 0 → Ω₁ ≠ 0 →
    (∀ (w : Fin n → ℂ) (v : epsR ℂ ⟶ A) (v' : epsR ℂ ⟶ A'), v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left →
      u.IsDiff w v → u'.IsDiff (fun j ↦ g (Ω₀ * w j) / Ω₁) v') →
    ∀ (m : Fin n → ℂ) (α : A ⟶ A) [IsMonHom α] (α' : A' ⟶ A') [IsMonHom α'], α'.left ≫ p = p ≫ α.left →
      ((∀ w, u.ex (fun j ↦ m j * w j) = u.ex w ≫ α) ↔ (∀ w, u'.ex (fun j ↦ g (m j) * w j) = u'.ex w ≫ α')) := by
  first | exact @GlobalTheory.DiagConj.diag_endo_iff_conj_diag | exact GlobalTheory.DiagConj.diag_endo_iff_conj_diag | (intros; apply GlobalTheory.DiagConj.diag_endo_iff_conj_diag <;> assumption)
