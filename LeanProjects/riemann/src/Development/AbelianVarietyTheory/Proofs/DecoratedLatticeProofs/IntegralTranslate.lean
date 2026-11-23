import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceModeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinatesOfThetaFunctionAreThetaFunctions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.HalfInvariance

theorem integral_translate {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsAddHaarMeasure] (F : G → ℂ) (a : G) :
    ∫ x, F (x + a) ∂ν = ∫ x, F x ∂ν := by
  simp_rw [add_comm _ a]
  exact integral_add_left_eq_self (μ := ν) F a

set_option maxHeartbeats 1000000 in

theorem half_avg_heis_inv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ e, IsSplitIdem D e → ∀ ℓ₀ : (WO S₀ T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S₀ T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S₀ T f → ℓ₀ (heisO ψ S₀ T u f) = ℓ₀ f) → ∀ H : AddSubgroup (Mx D T.rank ρ), (∀ x, x ∈ H ↔ ∀ i j, cA D e * x i j = x i j) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsAddHaarMeasure], ∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ∫ x : H, ℓ₀ (d.mixS T ψ μ 𝓕 (heisO ψ S T u f) x.1) ∂ν = ∫ x : H, ℓ₀ (d.mixS T ψ μ 𝓕 f x.1) ∂ν := by
  intro D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ hℓ₀ H hH _ _ ν _ u hu f hf
  have hee : cA D (cA D e) * cA D e = 0 := by rw [GlobalTheory.DualPairCheck.cA_cA]; exact he.2.1
  have horth : ∀ {x y : WO S T}, IsHalf (cA D e) x → IsHalf (cA D e) y → symplO S T x y = 0 :=
    fun hx hy => GlobalTheory.SplitScalar.symplO_eq_zero S T hee hx hy
  have hhalfR : ∀ {m n k : ℕ} {t : Mx D m n} (M : Matrix (Fin n) (Fin k) (AE D)), IsHalf (cA D e) t →
      IsHalf (cA D e) (HMul.hMul t M : Mx D m k) := fun M ht i j => by
    simp only [Matrix.mul_apply, Finset.mul_sum, ← mul_assoc, ht i _]

  set a : Mx D T.rank ρ := (d.coordS T u).1 with ha_def
  set w : WO S₀ T := (d.coordS T u).2.1 with hw_def
  set b : Mx D T.rank ρ := (d.coordS T u).2.2 with hb_def
  have hu_eq : u = d.extX T a + d.ext0 T w + d.extY T b := ((d.coordS T).symm_apply_apply u).symm
  have ha : IsHalf (cA D e) a := hhalfR _ hu
  have hw : IsHalf (cA D e) w := hhalfR _ hu
  have hb : IsHalf (cA D e) b := hhalfR _ hu
  have hXa : IsHalf (cA D e) (d.extX T a) := hhalfR _ ha
  have hYb : IsHalf (cA D e) (d.extY T b) := hhalfR _ hb
  have h0w : IsHalf (cA D e) (d.ext0 T w) := hhalfR _ hw
  have hth : ∀ {g : WO S T → ℂ}, IsThetaFunO ψ S T g → ∀ v, IsThetaFunO ψ S T (heisO ψ S T v g) :=
    fun hg v => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg v
  set g₂ := heisO ψ S T (d.extY T b) f with hg₂
  set g₁ := heisO ψ S T (d.ext0 T w) g₂ with hg₁
  have hg₂t : IsThetaFunO ψ S T g₂ := hth hf _
  have hg₁t : IsThetaFunO ψ S T g₁ := hth hg₂t _
  have hsplit : heisO ψ S T u f = heisO ψ S T (d.extX T a) g₁ := by
    have hsum : IsHalf (cA D e) (d.ext0 T w + d.extY T b) := fun i j => by
      simp only [Matrix.add_apply, mul_add, h0w i j, hYb i j]
    rw [hu_eq, add_assoc, GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (horth hXa hsum),
      GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (horth h0w hYb)]
  let v : VolM D T.rank ρ := ⟨μ, 𝓕, hμ⟩
  have key : ∀ x : H, ℓ₀ (d.mixS T ψ μ 𝓕 (heisO ψ S T u f) x.1) = ℓ₀ (d.mixS T ψ μ 𝓕 f (x + ⟨a, (hH a).2 ha⟩).1) := by
    intro x
    have hx : IsHalf (cA D e) x.1 := (hH x.1).1 x.2
    have hxa : IsHalf (cA D e) (x.1 + a) := fun i j => by
      simp only [Matrix.add_apply, mul_add, hx i j, ha i j]
    obtain ⟨c1, -, -, -, -⟩ := GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hψ S S₀ T ρ d v g₁ hg₁t
    obtain ⟨-, -, c3, -, -⟩ := GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hψ S S₀ T ρ d v g₂ hg₂t
    obtain ⟨-, c2, -, -, -⟩ := GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hψ S S₀ T ρ d v f hf
    have e1 : d.mixS T ψ μ 𝓕 (heisO ψ S T u f) x.1 = d.mixS T ψ μ 𝓕 g₁ (x.1 + a) := by
      rw [hsplit]; exact c1 x.1 a
    have e2 : d.mixS T ψ μ 𝓕 g₁ (x.1 + a) = heisO ψ S₀ T w (d.mixS T ψ μ 𝓕 g₂ (x.1 + a)) := c3 (x.1 + a) w
    have e3 : d.mixS T ψ μ 𝓕 g₂ (x.1 + a) = d.mixS T ψ μ 𝓕 f (x.1 + a) := by
      rw [hg₂, c2 (x.1 + a) b, horth (show IsHalf (cA D e) (d.extX T (x.1 + a)) from hhalfR _ hxa) hYb,
        AddChar.map_zero_eq_one, one_smul]
    have hmt : IsThetaFunO ψ S₀ T (d.mixS T ψ μ 𝓕 g₂ (x.1 + a)) :=
      GlobalTheory.MixValues.mixS_theta D ψ hψ S S₀ T ρ d μ 𝓕 hμ g₂ hg₂t (x.1 + a)
    rw [e1, e2, hℓ₀ w hw _ hmt, e3]
    rfl
  rw [integral_congr_ae (Filter.Eventually.of_forall key)]
  exact integral_translate ν (fun x : H => ℓ₀ (d.mixS T ψ μ 𝓕 f x.1)) _

end GlobalTheory.HalfInvariance
