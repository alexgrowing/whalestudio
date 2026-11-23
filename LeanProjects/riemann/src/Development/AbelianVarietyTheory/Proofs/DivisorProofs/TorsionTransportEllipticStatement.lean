import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTransportElliptic
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_transport_elliptic : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ), Ω₀ ^ 12 = latDisc Λ₀ → TorsTransport io g t Λ₀ Λ₁ Ω₀ Ω₁ →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)),
        ∃ (X' : Obj (FR E) 𝔠 (Sp ℂ)) (p : X'.A.left ⟶ T.X.A.left)
          (U' : Unif (fun i ↦ (g : ℂ →+* ℂ).comp (φ i)) (lattice c (y * (upIdele K E t)⁻¹)) 0 X'),
          X'.IsPullBy T.X (spMap (g : ℂ →+* ℂ)) p ∧ U'.e = T.U.e ∧ U'.c = T.U.c ∧
          (∀ i, g ((T.U.h i : ℂ) * (Real.sqrt d : ℝ)) = ((modF t : ℝ) : ℂ) * ((U'.h i : ℂ) * (Real.sqrt d : ℝ))) ∧
          (∀ (w : Fin (Module.finrank ℚ (FR E)) → ℂ) (v : epsR ℂ ⟶ T.X.A) (v' : epsR ℂ ⟶ X'.A),
            v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → T.U.u.IsDiff w v →
              U'.u.IsDiff (fun j ↦ g (Ω₀ * w j) / Ω₁) v') ∧
          (∀ (a : E) (α : T.X.A ⟶ T.X.A) [IsMonHom α] (α' : X'.A ⟶ X'.A) [IsMonHom α'], α'.left ≫ p = p ≫ α.left →
            (∀ w, U'.u.ex (fun j ↦ g (φ (U'.e j) a) * w j) = U'.u.ex w ≫ α') →
              ∀ w, T.U.u.ex (fun j ↦ φ (T.U.e j) a * w j) = T.U.u.ex w ≫ α) := by
  first | exact @GlobalTheory.ConjCMPoint.conj_unif | exact GlobalTheory.ConjCMPoint.conj_unif | (intros; apply GlobalTheory.ConjCMPoint.conj_unif <;> assumption)
