import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RouteDatumMemAlgebraicVectorsGridFrames
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtHeisenbergOpArchimedeanSumRealPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSecondPos
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCreationPreservesFockVectorsTwoFrames
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialOperatorHeisenbergDerivative

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FockDerUnif

open GlobalTheory.ChainFr Formalism.IndefR.Datum GlobalTheory.FockCreaDir

theorem dRho_ptF_uniform : ∀ {D : D7} {V W : HSp D} (A : GlobalTheory.ChainFr.Fr V) (B : GlobalTheory.ChainFr.Fr W) {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ}, IsStdChar D ψ (-1) → IsInfFam θ → ∀ (τ : D.what₂.Tau) (z : Matrix (Fin W.rank) (Fin V.rank) ℂ), ∃ Δ : PolF D W.rank V.rank →ₗ[ℂ] PolF D W.rank V.rank, ∀ f, GlobalTheory.ChainFr.IsVacF ψ θ A B f → ∀ P, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z (GlobalTheory.ChainFr.ptF ψ θ A B f P) = GlobalTheory.ChainFr.ptF ψ θ A B f (Δ P) := by
  classical
  intro D V W A B θ ψ hψ hθ τ z
  have hS := GlobalTheory.ChainFr.Model.isCartanInv_cart A
  have hT := GlobalTheory.ChainFr.Model.isCartanInv_cart B
  have hdA : IsUnit (A.onb τ).det := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
    exact (Matrix.isUnit_nonsing_inv_det_iff).2 this
  have hdB : IsUnit (B.onb τ).det := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 (B.fr_unit τ)
    exact (Matrix.isUnit_nonsing_inv_det_iff).2 this
  obtain ⟨e, rfl⟩ : ∃ e : Fin W.rank → Fin V.rank → ℂ,
      z = ∑ i, ∑ j, e i j • Formalism.IndefR.Datum.unitMap (A.onb τ) (B.onb τ) i j := ⟨_, eq_sum_unitMap hdB hdA z⟩
  set zz := ∑ i, ∑ j, e i j • Formalism.IndefR.Datum.unitMap (A.onb τ) (B.onb τ) i j with hzz
  have hc0 : ∀ k : FVar D W.rank V.rank, ∃ ck : ℂ, ∀ g, IsThetaFunO ψ V W g →
      annih (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) zz
        (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb k g) =
      aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb k
        (annih (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) zz g) + ck • g :=
    fun k => ⟨_, fun g h => GlobalTheory.FockIndep.annih_aPlus hψ hθ τ zz hS hT k.1 _ h⟩
  choose c hc using hc0
  let Δ₁ : PolF D W.rank V.rank →ₗ[ℂ] PolF D W.rank V.rank :=
    ((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j, (if (B.ε τ i == A.ε τ j) then e i j else starRingEnd ℂ (e i j)) •
      LinearMap.mulLeft ℂ (MvPolynomial.X (τ, i, j) : PolF D W.rank V.rank)
  let Δ₂ : PolF D W.rank V.rank →ₗ[ℂ] PolF D W.rank V.rank :=
    ∑ k, c k • (MvPolynomial.pderiv k : Derivation ℂ (PolF D W.rank V.rank) (PolF D W.rank V.rank)).toLinearMap
  refine ⟨(1 / 2 : ℂ) • (Δ₁ + Δ₂), fun f hf P => ?_⟩

  have hadd : ∀ g g', IsThetaFunO ψ V W g → IsThetaFunO ψ V W g' → IsThetaFunO ψ V W (g + g') :=
    fun _ _ => GlobalTheory.OrientedHeis.theta_add
  have hsm : ∀ (a : ℂ) g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W (a • g) :=
    fun a _ => GlobalTheory.OrientedHeis.theta_smul a
  have hth : ∀ v g, IsThetaFunO ψ V W g → IsThetaFunO ψ V W
      (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb v g) :=
    fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h
  have hX : ∀ v Q,
      pureTensorL (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb) f (MvPolynomial.X v * Q) =
      aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb v
        (pureTensorL (aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb) f Q) := fun v Q => by
    refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ V W) hadd hsm hth ?_ ?_ ?_ hf.1 Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' hψ hθ i.1 _ hS hT j.1 _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h
  have hg : IsThetaFunO ψ V W (GlobalTheory.ChainFr.ptF ψ θ A B f P) :=
    GlobalTheory.FockIndep.pure_mem (P := IsThetaFunO ψ V W) hadd hsm hth hf.1 P
  have hΔ₁ : Δ₁ P = ((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j,
      (if (B.ε τ i == A.ε τ j) then e i j else starRingEnd ℂ (e i j)) • (MvPolynomial.X (τ, i, j) * P) := by
    first
      | simp only [Δ₁, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.mulLeft_apply]
      | simp [Δ₁, LinearMap.sum_apply]
  have hΔ₂ : Δ₂ P = ∑ k, c k • MvPolynomial.pderiv k P := by
    first
      | simp only [Δ₂, LinearMap.sum_apply, LinearMap.smul_apply, Derivation.coeFn_coe]
      | simp [Δ₂, LinearMap.sum_apply]
  have hcr : crea (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) zz (GlobalTheory.ChainFr.ptF ψ θ A B f P) =
      GlobalTheory.ChainFr.ptF ψ θ A B f (Δ₁ P) := by
    have h1 : ∀ (y : Matrix (Fin W.rank) (Fin V.rank) ℂ) g,
        crea (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) y g =
          ((fockScale D τ : ℝ) : ℂ) • Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) y g :=
      fun y g => by
        rw [Formalism.IndefR.Datum.aPlus, smul_smul, mul_inv_cancel₀ (fockScale_ne_zero D τ), one_smul]
    rw [h1, hΔ₁]
    have h2 : GlobalTheory.ChainFr.ptF ψ θ A B f (((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j,
        (if (B.ε τ i == A.ε τ j) then e i j else starRingEnd ℂ (e i j)) • (MvPolynomial.X (τ, i, j) * P)) =
        ((fockScale D τ : ℝ) : ℂ) • ∑ i, ∑ j, (if (B.ε τ i == A.ε τ j) then e i j else starRingEnd ℂ (e i j)) •
          Formalism.IndefR.Datum.aPlus (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ))
            (Formalism.IndefR.Datum.unitMap (A.onb τ) (B.onb τ) i j) (GlobalTheory.ChainFr.ptF ψ θ A B f P) := by
      unfold GlobalTheory.ChainFr.ptF pureTensorO
      simp only [map_smul, map_sum, hX]
      rfl
    rw [h2]
    congr 1
    rw [hzz, GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ τ _ _ hg]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [GlobalTheory.FockSubst.aPlus_dir_sum hψ hθ τ _ _ hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact GlobalTheory.FockSubst.aPlus_dir_smul hψ hθ τ _ _ hg (B.ε τ i == A.ε τ j) _ (cplxO_unitMap_fr A B τ i j)
  have han : annih (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) zz (GlobalTheory.ChainFr.ptF ψ θ A B f P) =
      GlobalTheory.ChainFr.ptF ψ θ A B f (Δ₂ P) := by
    rw [hΔ₂]
    exact GlobalTheory.ArchRec.DerFock.pure_deriv (P := IsThetaFunO ψ V W)
      (A := aPlusAll (heisO ψ V W) θ (fun τ => cplxO (A.cart τ) (B.cart τ)) A.onb B.onb)
      (B := annih (heisO ψ V W) θ τ (cplxO (A.cart τ) (B.cart τ)) zz)
      hadd hsm hth
      (fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' hψ hθ i.1 _ hS hT j.1 _ h)
      (fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h')
      (fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h)
      (fun _ _ h h' => GlobalTheory.FockIndep.annih_add hψ hθ _ _ _ h h')
      (fun a _ h => GlobalTheory.FockIndep.annih_smul hψ hθ _ _ _ a h)
      (fun j g h => hc j g h) hf.1 (hf.2 τ zz) P
  have hsplit : GlobalTheory.ChainFr.ptF ψ θ A B f (((1 / 2 : ℂ) • (Δ₁ + Δ₂)) P) =
      (1 / 2 : ℂ) • (GlobalTheory.ChainFr.ptF ψ θ A B f (Δ₁ P) + GlobalTheory.ChainFr.ptF ψ θ A B f (Δ₂ P)) := by
    rw [LinearMap.smul_apply, LinearMap.add_apply]
    unfold GlobalTheory.ChainFr.ptF
    rw [map_smul, map_add]
  rw [hsplit, ← hcr, ← han, crea, annih]
  module

end GlobalTheory.FockDerUnif
