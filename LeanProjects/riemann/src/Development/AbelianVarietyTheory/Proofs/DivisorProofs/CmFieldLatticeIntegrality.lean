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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumUnramifiedAlmostAllStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedMultiplicationSubmoduleStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanProjInclRationalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianEvaluationNonarchimedeanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawLeftRestrictionIsPairStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatModel

theorem exists_model_periods : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.SerreTateGoodReductionSt → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
    (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)) (Λ : PeriodPair), IsBaseCond 𝔣 → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (Ω : ℂ), Ω ^ 12 = latDisc Λ →
    ∃ (𝔠 : FracId (FR E)) (R : Subring ℂ) (_ : IsPlaceRing E l lam R) (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ))
      (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X) (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A),
      X.IsPullBy X₀ (spMap R.subtype) p ∧
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) ∧
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) ∧
      ∀ (i : I) (e : X₀.Lie →ₗ[R] R) (a : ℂ), IsPeriodGen X₀ U p i e a → a ≠ 0 → Sz l lam (a0 𝔣 l) (a / Ω) := by
  intro hPer hST hDR hDC hPol E _ _ _ _ I _ d φ hF 𝔣 Λ h𝔣 hΛ l _ Q hQ hQl y hy lam Ω hΩ
  have hc : condQ 𝔣 Q ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]
    refine mul_ne_zero (by rw [Ideal.zero_eq_bot]; exact h𝔣.1) (Finset.prod_ne_zero_iff.2 fun q _ ↦ ?_)
    rw [Ideal.zero_eq_bot]; exact q.ne_bot
  obtain ⟨𝔠, X, U, hend⟩ := GlobalTheory.T.cm_order_uniformization_exists E I d φ hF (condQ 𝔣 Q) y hc
  obtain ⟨k₀, R₀, hk₀, hR₀, hR₀k, G₀, _, p₀, P₀, Ψ₀, hG₀, hp₀, hΨ₀, hΨf, hΨfl, hΨs, htan⟩ :=
    GlobalTheory.T.integral_lattice_l_adic_congruence hST hDC E I d φ hF 𝔣 Λ h𝔣 hΛ l Q hQ hQl y hy lam Ω hΩ 𝔠 X U
  obtain ⟨k, hk, H⟩ := (GlobalTheory.T.cm_order_l_adic_endomorphism_integral hDC hDR E I φ hF.2.2.2.2.2.2.1 (condQ 𝔣 Q) y hc l lam 𝔠 X U hend k₀ R₀ hk₀ hR₀ hR₀k
    G₀ p₀ P₀ Ψ₀ hG₀ hp₀ hΨ₀ hΨf hΨfl hΨs).and (GlobalTheory.T.eventually_place_ring E l lam)
  obtain ⟨R, hR⟩ := GlobalTheory.T.exists_place_ring_over_prime l lam k hk
  obtain ⟨⟨X₀, p, cm, hpb, hrm, hcm, hlie⟩, hplace⟩ := H R hR
  refine ⟨𝔠, R, hplace, X₀, X, U, p, cm, hpb, hrm, fun a ↦ ?_, fun i e a he _ ↦ ?_⟩
  · obtain ⟨α, hα, hα'⟩ := hend a
    exact ⟨α, hα, hcm a α hα hα', hα'⟩
  · obtain ⟨v₀, v', W, htv, hvv, hW, hW0, hsz⟩ := htan i
    obtain ⟨v, hv⟩ := hlie v₀ v' htv hvv
    exact sz_period_of_tangent hplace he hv hW hW0 hsz

end GlobalTheory.LatModel
