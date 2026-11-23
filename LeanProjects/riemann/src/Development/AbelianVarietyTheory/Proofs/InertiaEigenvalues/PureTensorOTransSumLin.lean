import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.SingleDatum

theorem pureTensorO_finsetSum {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {ι : Type} (s : Finset ι) (a : ι → ℂ)
    (g : ι → WO S T → ℂ) (hg : ∀ i, IsThetaFunO ψ S T (g i)) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    IsThetaFunO ψ S T (∑ i ∈ s, a i • g i) ∧
      pureTensorO ψ θ S T sS sT BS BT (∑ i ∈ s, a i • g i) φ =
        ∑ i ∈ s, a i • pureTensorO ψ θ S T sS sT BS BT (g i) φ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact ⟨GlobalTheory.OrientedHeis.theta_zero, GlobalTheory.FockFiniteHeis.pureTensorO_zero ψ θ S T hψ hθ sS BS sT BT φ⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    refine ⟨GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul _ (hg i)) ih.1, ?_⟩
    rw [GlobalTheory.FockFiniteHeis.pureTensorO_lin ψ θ S T hψ hθ sS BS sT BT (a i) (hg i) ih.1 φ, ih.2]

theorem pureTensorO_transSum_lin : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW s f₀ → ∀ (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (l₂ : Geo.Tor.Level H) (e : AE D), IsHalfIdem l₂ e → ∀ [Fintype (Fin V.rank → LevQ Dw l₂)] (BV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (w : (Fin V.rank → LevQ Dw l₂) → ℂ) (P : PolF D W.rank V.rank), pureTensorO ψ θ V W (fun _ => 1) s BV BW (transSum ψ V W l₂ ι e f₀ w) P = ∑ q, w q • pureTensorO ψ θ V W (fun _ => 1) s BV BW (transSum ψ V W l₂ ι e f₀ (fun q' => if q' = q then 1 else 0)) P := by
  intro D H Dw ψ θ V W χV χW om ΛV ΛW s f₀ hv ι l₂ e he _ BV BW w P
  have hψ : IsStdChar D ψ (-1) := hv.2.2.2.2.2.2.2.2.1
  have hθ : IsInfFam θ := hv.1.inf
  have hf₀ : IsThetaFunO ψ V W f₀ := hv.2.2.2.2.2.2.2.2.2.2
  have hinf : infPart D e = 0 := by
    obtain ⟨Q, hQ, -⟩ := he
    exact GlobalTheory.PlaceDatum.infPart_idemSum hQ
  have hpt : ∀ q, (levPoint V W l₂ ι e q).map (infPart D) = 0 := by
    intro q
    ext a b
    simp [levPoint, Matrix.map_apply, map_mul, hinf]
  have hth : ∀ q, IsThetaFunO ψ V W (heisO ψ V W (levPoint V W l₂ ι e q) f₀) := fun q =>
    ((GlobalTheory.FinTranslate.finite_translate D ψ θ V W hψ hθ f₀ hf₀).2 _ (hpt q)).1
  have key : ∀ w' : (Fin V.rank → LevQ Dw l₂) → ℂ,
      pureTensorO ψ θ V W (fun _ => 1) s BV BW (transSum ψ V W l₂ ι e f₀ w') P =
        ∑ q, (((Nat.card (Fin V.rank → LevQ Dw l₂) : ℂ))⁻¹ * w' q) •
          pureTensorO ψ θ V W (fun _ => 1) s BV BW (heisO ψ V W (levPoint V W l₂ ι e q) f₀) P := by
    intro w'
    have h1 : transSum ψ V W l₂ ι e f₀ w' = ∑ q, (((Nat.card (Fin V.rank → LevQ Dw l₂) : ℂ))⁻¹ * w' q) •
        heisO ψ V W (levPoint V W l₂ ι e q) f₀ := by
      unfold transSum
      rw [finsum_eq_sum_of_fintype, Finset.smul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [smul_smul]
    rw [h1]
    exact (pureTensorO_finsetSum hψ hθ (fun _ => 1) BV s BW Finset.univ _ _ hth P).2
  rw [key w]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [key, Finset.sum_eq_single q]
  · rw [if_pos rfl, mul_one, mul_comm, ← smul_smul]
  · intro b _ hb
    rw [if_neg hb, mul_zero, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ q) h

end GlobalTheory.SingleDatum

end
