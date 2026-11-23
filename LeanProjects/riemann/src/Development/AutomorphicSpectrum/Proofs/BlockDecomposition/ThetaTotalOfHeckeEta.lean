import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTranslateSchwartzMajorant
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.ExistsIsCovolOneRatMx
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroCoefficientTotalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneThetaTotalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StepTotalOfProductsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductThetaOfSchwartzTensorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductMeasureStatementStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzTensorDensityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationContinuityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationKFiniteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMajorantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaCompactnessStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneMajorantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EuclideanTotalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockTotalOfEuclideanStatement

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ThTot

variable {D : D7}

def subH {k m : ℕ} (b : HermE D m) (e : Fin k → Fin m) : HermE D k :=
  ⟨b.1.submatrix e e, by
    have h := b.2
    funext i j
    exact congrFun (congrFun h (e i)) (e j)⟩

theorem subH_isDiagInv {k m : ℕ} {b : HermE D m} (hb : IsDiagInv b) {e : Fin k → Fin m} (he : Function.Injective e) :
    IsDiagInv (subH b e) := by
  obtain ⟨h1, h2⟩ := hb
  have hd : ∀ i, b.1 i i ≠ 0 := by
    intro i h0
    apply h2
    rw [← h1.diagonal_diag, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) h0
  have hs : (subH b e).1.IsDiag := h1.submatrix he
  refine ⟨hs, ?_⟩
  rw [← hs.diagonal_diag, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.2 fun i _ => hd (e i)

theorem diagonal_invertible_block_form {ρ : ℕ} {b : HermE D (ρ + 1)} (hb : IsDiagInv b) :
    IsBlockSL2Embedding b (subH b (Fin.castAdd 1)) (subH b (Fin.natAdd ρ)) := by
  have hne : ∀ (i : Fin ρ) (j : Fin 1), Fin.castAdd 1 i ≠ Fin.natAdd ρ j := by
    intro i j h
    have := congrArg Fin.val h
    simp at this
    omega
  exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun i j => hb.1 (hne i j), fun i j => hb.1 (hne i j).symm⟩

theorem core (h0 : ZeroTotal) (h1 : OneTotal) (hS : StepTotal) (hH : HeckeEta) (D : D7) :
    ∀ (ρ p : ℕ) (μ : Measure (Mx D ρ p)) (𝓕 : Set (Mx D ρ p)), IsCovolOne (ratMx D ρ p) μ 𝓕 →
    ∀ ψ, IsCharAF D.host.F ψ → ∀ b₀ : HermE D ρ, IsDiagInv b₀ → ∀ χ, IsHeckeChar D χ → ResEta D χ ρ → (ρ = 0 → χ = 1) →
    ∀ θ, IsInfFam θ → Total ψ χ θ b₀ μ := by
  intro ρ
  induction ρ with
  | zero =>
    intro p μ 𝓕 hμ ψ hψ b₀ _ χ _ _ h1' θ hθ
    obtain rfl := h1' rfl
    exact h0 D p μ 𝓕 hμ ψ hψ b₀ θ hθ
  | succ ρ ih =>
    intro p μ 𝓕 hμ ψ hψ b₀ hb χ hχ hr _ θ hθ
    obtain ⟨χ₁, hχ₁, hr₁, he⟩ : ∃ χ₁, IsHeckeChar D χ₁ ∧ ResEta D χ₁ 1 ∧ (ρ = 0 → χ₁ = χ) := by
      by_cases h : ρ = 0
      · subst h
        exact ⟨χ, hχ, hr, fun _ => rfl⟩
      · obtain ⟨χ₁, a, b⟩ := hH D 1
        exact ⟨χ₁, a, b, fun h' => absurd h' h⟩
    have hχ' : IsHeckeChar D (χ * χ₁⁻¹) := by
      refine ⟨?_, fun x => ?_⟩
      · have c1 := hχ.1
        have c2 := hχ₁.1
        exact c1.mul c2.inv
      · have a1 := hχ.2 x
        have a2 := hχ₁.2 x
        rw [MonoidHom.mul_apply, MonoidHom.inv_apply, a1, a2, inv_one, mul_one]
    have hr' : ResEta D (χ * χ₁⁻¹) ρ := by
      refine ⟨hr.1, fun η hη a => ?_⟩
      have e1 := hr.2 η hη a
      have e2 := hr₁.2 η hη a
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, e1, e2, pow_one, pow_succ]
      exact mul_inv_cancel_right _ _
    obtain ⟨μr, 𝓕r, hμr⟩ := GlobalTheory.CompanionTheory.RatMxCovol.exists_isCovolOne_ratMx D ρ p
    obtain ⟨μs, 𝓕s, hμs⟩ := GlobalTheory.CompanionTheory.RatMxCovol.exists_isCovolOne_ratMx D 1 p
    have hinj1 : Function.Injective (Fin.castAdd 1 : Fin ρ → Fin (ρ + 1)) := Fin.castAdd_injective _ _
    have hinj2 : Function.Injective (Fin.natAdd ρ : Fin 1 → Fin (ρ + 1)) := Fin.natAdd_injective _ _
    have hd2 := subH_isDiagInv hb hinj2
    have T := hS D ρ 1 p μr 𝓕r μs 𝓕s μ 𝓕 hμr hμs hμ ψ hψ (χ * χ₁⁻¹) χ₁ θ hθ _ _ b₀ (diagonal_invertible_block_form hb)
      (ih p μr 𝓕r hμr ψ hψ _ (subH_isDiagInv hb hinj1) _ hχ' hr'
        (fun h => by rw [he h]; exact mul_inv_cancel χ) θ hθ)
      (h1 D p μs 𝓕s hμs ψ hψ _ hd2.2 χ₁ hχ₁ hr₁ θ hθ)
    rwa [inv_mul_cancel_right] at T

theorem thTotal_of (h0 : ZeroTotal) (h1 : OneTotal) (hS : StepTotal) : HeckeEta → ThTotal := by
  intro hH D ρ p m ψ hψ b₀ hb χ hχ hr h0' θ hθ
  exact core h0 h1 hS hH D ρ p m.μ m.𝓕 m.hμ ψ hψ b₀ hb χ hχ hr h0' θ hθ

theorem thTotal : HeckeEta → ThTotal :=
  thTotal_of GlobalTheory.T.zero_coefficient_total
    (GlobalTheory.T.rank_one_theta_total GlobalTheory.T.weil_representation_continuity (GlobalTheory.T.rank_one_majorant GlobalTheory.T.weil_representation_continuity GlobalTheory.T.weil_representation_K_finite GlobalTheory.T.orbit_majorant GlobalTheory.T.iwasawa_compactness)
      (GlobalTheory.T.fock_total_of_euclidean GlobalTheory.T.euclidean_total))
    (GlobalTheory.T.step_total_of_products (GlobalTheory.T.product_theta_of_schwartz_tensor GlobalTheory.T.schwartz_tensor_density) GlobalTheory.T.product_measure_statement)

end GlobalTheory.CompanionTheory.ThTot

end
