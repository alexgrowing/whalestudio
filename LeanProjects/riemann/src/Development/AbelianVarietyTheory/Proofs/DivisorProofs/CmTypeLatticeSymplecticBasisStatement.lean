import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeLatticeSymplecticBasis
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.WholeFlag GlobalTheory.ConstLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_type_lattice_symplectic_basis : ∀ (E : Type) [Field E] [NumberField E] [IsGalois ℚ E] (F : Type) [Field F] [NumberField F], Nonempty (E →+* F) →
    ∀ (bar : 𝓞 E ≃+* 𝓞 E) (Φ : Set (E →+* F)),
    (∀ σ τ : E →+* F, (∀ α : 𝓞 E, τ (α : E) = σ ((bar α : 𝓞 E) : E)) → (σ ∈ Φ ↔ τ ∉ Φ)) →
    ∀ {N : ℕ} (ρ : 𝓞 E →+* Matrix (Fin N) (Fin N) ℤ) (J : Matrix (Fin N) (Fin N) ℤ), IsUnit J.det →
    (∀ α, (ρ α).transpose * J = J * ρ (bar α)) → ∀ p : ℕ, p.Prime →
    ∃ (n : ℕ) (P Q : Matrix (Fin N) (Fin N) F), n ≠ 0 ∧
      EigBasis ρ J (fun τ => if τ ∈ Φ then vDiff E p else 0) p n P Q := by
  first | exact @GlobalTheory.EigArith.exists_eigBasis | exact GlobalTheory.EigArith.exists_eigBasis | (intros; apply GlobalTheory.EigArith.exists_eigBasis <;> assumption)
