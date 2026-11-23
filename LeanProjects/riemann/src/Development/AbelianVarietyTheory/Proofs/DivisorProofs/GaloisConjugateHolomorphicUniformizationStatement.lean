import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisConjugateHolomorphicUniformization
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDetGen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_conjugate_holomorphic_uniformization : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X X' : Obj F 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ X.A.left) (g : ℂ ≃+* ℂ)
    (c : 𝔠.elt) (n : ℕ) (u : HolUnif X.A (X.diag c) n) (Ω₀ Ω₁ : ℂ), Ω₀ ≠ 0 → Ω₁ ≠ 0 →
    X'.IsPullBy X (spMap (g : ℂ →+* ℂ)) p →
    ∃ u' : HolUnif X'.A (X'.diag c) n, ∀ (w : Fin n → ℂ) (v : epsR ℂ ⟶ X.A) (v' : epsR ℂ ⟶ X'.A),
      v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → u.IsDiff w v →
        u'.IsDiff (fun j ↦ g (Ω₀ * w j) / Ω₁) v' := by
  first | exact @GlobalTheory.ConjTangent.exists_conj_holUnif_tangent | exact GlobalTheory.ConjTangent.exists_conj_holUnif_tangent | (intros; apply GlobalTheory.ConjTangent.exists_conj_holUnif_tangent <;> assumption)
