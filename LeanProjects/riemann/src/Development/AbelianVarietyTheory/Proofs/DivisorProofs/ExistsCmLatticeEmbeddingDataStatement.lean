import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmLatticeEmbeddingData
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayAgree
import Development.AbelianVarietyTheory.Definitions.Divisors.NatCastNeZeroG
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNonarchimedeanW
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cm_lattice_embedding_data : Hypotheses2 → HypothesesH → GlobalTheory.Published.RegularAlteration → GlobalTheory.Published.ScholzeWeinsteinB → GlobalTheory.Published.PrismaticDieudonnePerfd →
    ∀ (D : D7) (O : Setup D), O.Core → ∀ (T : Finset ℕ) (R : ℝ), 2 ≤ R → ∀ p : ℕ, p.Prime → p ∈ T → ∀ c : O.s.Comp,
    ∃ (bar : 𝓞 D.host.E ≃+* 𝓞 D.host.E) (Φ : Set (D.host.E →+* D.what₂.LL))
      (β : Fin (D.R.f * O.N) → (D.host.E →+* D.what₂.LL))
      (ρ : 𝓞 D.host.E →+* Matrix (Fin (D.R.f * O.N + D.R.f * O.N)) (Fin (D.R.f * O.N + D.R.f * O.N)) ℤ)
      (J : Matrix (Fin (D.R.f * O.N + D.R.f * O.N)) (Fin (D.R.f * O.N + D.R.f * O.N)) ℤ),
      (∀ σ τ : D.host.E →+* D.what₂.LL, (∀ α : 𝓞 D.host.E, τ (α : D.host.E) = σ ((bar α : 𝓞 D.host.E) : D.host.E)) →
        (σ ∈ Φ ↔ τ ∉ Φ)) ∧ IsUnit J.det ∧ (∀ α, (ρ α).transpose * J = J * ρ (bar α)) ∧
      ∀ k : ℕ, EqData
        (fun i : Fin (D.R.f * O.N) => adlOf (O.Φ.C c) (O.met.hm c)
          (wholeSym (ArIn.ind T) (some R) (Sum.inl i : Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N))))
        (fun i : Fin (D.R.f * O.N) => adlOf (O.Φ.C c) (O.met.hm c)
          (eigSym O.S.Dw (ArIn.ind T) (some R) (Sum.inl i : Fin (D.R.f * O.N) ⊕ Fin (D.R.f * O.N))))
        β (fun τ => if τ ∈ Φ then vDiff D.host.E p else 0) ρ J p k := by
  first | exact @GlobalTheory.EqHalf.eqData_geo | exact GlobalTheory.EqHalf.eqData_geo | (intros; apply GlobalTheory.EqHalf.eqData_geo <;> assumption)
