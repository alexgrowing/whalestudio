import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicMapExtremalVectorEqPhaseSmulLetters
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harmonicMap_extremalVector_eq_phase_smul_letters : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ), (∀ ρ, (u ρ : (R.MW i (sg0 D A)).sm ρ) = v₀ i (sg0 D A) ρ) → ∀ c0 : VsV D i ℂ →ₗ[ℂ] (R.cV i).W, GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsCoefMap R i c0 → ∀ lt : LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank ≃ FVar D (Wc D i).rank (Vc D i).rank, IsLetters (T.Q.Dw ((i : ℕ) + 1)) lt → ∃ ka : ℂ, ‖ka‖ = 1 ∧ ∃ J : VsV D i ℂ →ₗ[ℂ] MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) ℂ, (∀ v, J v ∈ HHa (T.Q.Dw ((i : ℕ) + 1)).mult (Vc D i).rank ℂ ComplexEmbedding.conjugate (InPsi T.Q.H) (fun τ j => wtA (κ i) (τ, j))) ∧ (∀ k : Subfield ℂ, (∀ x ∈ T.Q.c.F, x ∈ k) → ∀ v : VsV D i ℂ, (∀ m, MvPolynomial.coeff m (v : Formalism.L2.DIV.Pol ℂ D.what₂.Tau (Vc D i).rank) ∈ k) → ∀ mo, (J v).coeff mo ∈ k) ∧ ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ v, pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) f (R.ioP i (PiTensorProduct.tprod ℂ u) (c0 v)) = ka • stdF R.ψ R.θ (Vc D i) (Wc D i) (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) f (MvPolynomial.rename lt (J v)) := by
  first | exact @GlobalTheory.SerIntLetters.io_eq_phase_smul_harmLetters | exact GlobalTheory.SerIntLetters.io_eq_phase_smul_harmLetters | (intros; apply GlobalTheory.SerIntLetters.io_eq_phase_smul_harmLetters <;> assumption)
