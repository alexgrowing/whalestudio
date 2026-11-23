import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralLatticeLAdicReduction
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SzPeriodsOfTangent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyOfForall
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_lattice_l_adic_reduction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
    (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)) (Λ : PeriodPair), IsBaseCond 𝔣 →
    GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ))
    (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X) (A' : Over (Sp ℂ)) [GrpObj A'] (L' : LB A'.left)
    (u : HolUnif A' L' (Module.finrank ℚ (FR E))), IsAbelianScheme A' →
    SmoothOfRelativeDimension (Module.finrank ℚ (FR E)) A'.hom → (∀ w, w ∈ u.Λ ↔ ∀ j, w j ∈ Λ.lattice) →
    ∀ j₀ : Fin (Module.finrank ℚ (FR E)),
    ∃ (α : A' ⟶ X.A) (M : (Fin (Module.finrank ℚ (FR E)) → ℂ) →ₗ[ℂ] (Fin (Module.finrank ℚ (FR E)) → ℂ)) (n N : ℕ),
      IsMonHom α ∧ IsFinite α.left ∧ Flat α.left ∧ Surjective α.left ∧ 1 ≤ N ∧
      (∀ (T : Over (Sp ℂ)) (x : T ⟶ A'), x ≫ α = 1 → x ^ N = 1) ∧ (∀ w, U.u.ex (M w) = u.ex w ≫ α) ∧
      M (Pi.single j₀ 1) = (fun _ ↦ (n : ℂ)) ∧ 0 < n ∧ Sz l lam (a0 𝔣 l) ((n : ℂ)⁻¹) := by
  first | exact @GlobalTheory.CMPowerIsogeny.exists_isogeny | exact GlobalTheory.CMPowerIsogeny.exists_isogeny | (intros; apply GlobalTheory.CMPowerIsogeny.exists_isogeny <;> assumption)
