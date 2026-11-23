import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteCommCreation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianTwistedRealReadingEntireAndInjective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntSubIsLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MovedWeilVacuumEqVacuumOfMovedLattices
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DatumReadingSplitPlacesEqClassicalThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetCConstMul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker

namespace GlobalTheory.KJInf.CoreG

theorem om_inv_om {D : D7} (S T : HSp D) (om : Om S T) (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    om (g⁻¹, h⁻¹) (om (g, h) f) = f := by
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, ← Prod.one_eq_mk, map_one]
  rfl

theorem selfDual_latFr {D : D7} (V : HSp D) (hV : V.gram = 1) {n : ℕ} (hn : V.rank = n) (g : GA D V)
    (N : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (hN : Moves V hn g N) :
    ∃ Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E), IsSelfDualC V Λ ∧
      (Λ : Set (Fin V.rank → D.host.E)) = latFr V hn N := by
  subst hn
  exact ⟨N, GlobalTheory.SplitMove.selfDual_move V hV g N hN, rfl⟩

theorem thC_const_mul (D : D7) {a b : ℕ} (δ : ℂ) (sc : ℝ) (SS : Finset (Formalism.L2.DIV.Pl D.host.E))
    (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ)
    (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ) (κ : ℂ) (E : VCx D.what₂.Tau a b → ℂ) :
    thC (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c Ξ (fun z => κ * E z) =
      fun z => κ * thC (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c Ξ E z := by
  funext z
  simp only [thC, xiV, xiL, xiS, Formalism.L2.Th1.H.sumU, Formalism.L2.Th1.H.opU, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

end GlobalTheory.KJInf.CoreG

namespace GlobalTheory.KJInf.CoreG

theorem thetaKernel_eq_jet_thC : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ s : ℂ, (∀ f, IsHol θ S T ψ f → ∀ P, pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P 0 = jetP S T hS hT s (xiN θ S T hS hT δ sc f) P) → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ e (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ vac Φ w, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (intVec D _) (intVec D _) vac → IsSBHalf e (stdHom S T) Φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (stdHom S T) 1 vac Φ w → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), Moves S hS g N → Moves T hT h N' → ∀ c : ℕ, 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → LaFacts (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' → ∀ Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ, (∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, Φ (actO S T g⁻¹ h⁻¹ (γ.map fun r => e * incA D r)) = Ξ (toHom S T hS hT γ)) → (∀ x, Ξ x ≠ 0 → (c : D.host.E) • x ∈ Formalism.L2.Col.homAt SS N N') → (∀ x, ∀ y ∈ Formalism.L2.Col.homAt SS N N', Ξ (x + (c : D.host.E) • y) = Ξ x) → ∀ (κ : ℂ) (E : VCx D.what₂.Tau a b → ℂ), (xiN θ S T hS hT δ sc (om (g, h) vac) = fun z => κ * E z) → ∀ P, thetaKO om g h (pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) w P) = κ * jetP S T hS hT s (thC (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c Ξ E) P := by
  intro D ψ θ S T a b hS hT δ sc hP s hs μ om hW e SS hE vac Φ w hV hSB hTh g hg h hh N N' hN hN' c hc hcP h2 hLa Ξ hΦ hΞ1 hΞ2 κ E hκ P
  obtain ⟨hSBm, hThm⟩ := GlobalTheory.SplitMove.isThetaAt_move D ψ θ S T a b hS hT δ sc hP μ om hW e SS hE vac Φ w hV.2.theta hV.2.lat
    hSB hTh g hg h hh N N' hN hN'
  obtain ⟨hVm, -, -⟩ := GlobalTheory.MovedVac.vac_moved D ψ θ S T a b hS hT δ sc hP μ om hW vac hV g hg h hh N N' hN hN'
  have hD : IsHol θ S T ψ (om (g, h) w) ∧ xiN θ S T hS hT δ sc (om (g, h) w) =
      thC (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c Ξ (xiN θ S T hS hT δ sc (om (g, h) vac)) := by
    exact GlobalTheory.T.datumReading_splitPlaces_eq_classicalTheta D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc hcP h2 hLa (selfDual_latFr S hP.gS hS g N hN)
        (selfDual_latFr T hP.gT hT h N' hN') _ _ _ Ξ hVm hSBm hThm hΦ hΞ1 hΞ2
  obtain ⟨hHolm, hxi⟩ := hD
  have hHolw : IsHol θ S T ψ w := by
    have := (GlobalTheory.AdForm.FinComm.finite_comm_creation D ψ θ S T a b hS hT δ sc hP μ om hW g⁻¹ (inv_mem hg) h⁻¹ (inv_mem hh)
      _ hHolm).1
    rwa [om_inv_om] at this
  have hcomm := ((GlobalTheory.AdForm.FinComm.finite_comm_creation D ψ θ S T a b hS hT δ sc hP μ om hW g hg h hh w hHolw).2 P).2
  have hdiff : Differentiable ℂ fun z =>
      κ * thC (tauE D) δ D.host.d sc (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) SS N N' c Ξ E z := by
    rw [← thC_const_mul, ← hκ, ← hxi]
    exact (GlobalTheory.AdForm.VacRead.xiN_entire_and_injective D ψ θ S T a b hS hT δ sc hP).1 _ hHolm
  unfold thetaKO
  rw [hcomm, hs _ hHolm P, hxi, hκ, thC_const_mul]
  unfold jetP
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [GlobalTheory.ColNorms.jetC_const_mul _ _ _ hdiff]
  ring

end GlobalTheory.KJInf.CoreG
