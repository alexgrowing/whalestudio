import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockComb

theorem om_pureTensorO_comb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ sS sT BS BT (e : WO S T →₀ ℂ) (f₀ f : WO S T → ℂ) (x : ℂ), IsFinComb e → IsThetaFunO ψ S T f₀ → IsThetaFunO ψ S T f → ∀ b ∈ GfC S, ∀ b' ∈ GfC T, om (b, b') f = x • comb ψ S T e f₀ → ∀ P, ∀ a ∈ GinfC S, ∀ a' ∈ GinfC T, om (a * b, a' * b') (pureTensorO ψ θ S T sS sT BS BT f P) = x • comb ψ S T e (om (a, a') (pureTensorO ψ θ S T sS sT BS BT f₀ P)) ∧ ∀ (N : Lat S) (N' : Lat T), Vac ψ S T N N' (fun _ => True) f₀ → Vac ψ S T N N' (fun _ => True) (om (a, a') (pureTensorO ψ θ S T sS sT BS BT f₀ P)) := by
  intro D ψ θ S T χS χT om hθ hW sS sT BS BT e f₀ f x he hf₀ hf b hb b' hb' hfx P a ha a' ha'
  have hψ : IsStdChar D ψ (-1) := hW.std

  have hfin := GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hW hθ sS sS BS BS sT sT BT BT b b'
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hb, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hb', Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hb, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hb', Matrix.one_mul]) f hf P
  have hth₀ : IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f₀ P) :=
    (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T χS χT om hW hθ sS sS BS BS sT sT BT BT 1 1
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (one_mem _), Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (one_mem _), Matrix.one_mul]) f₀ hf₀ P).1

  have hcomb : comb ψ S T e (pureTensorO ψ θ S T sS sT BS BT f₀ P) =
      pureTensorO ψ θ S T sS sT BS BT (comb ψ S T e f₀) P := by
    let q := e.support.equivFin
    have key := (GlobalTheory.FockFiniteHeis.heis_comb_pureTensorO D ψ θ S T hψ hθ sS sT BS BT f₀ hf₀ e.support.card
      (fun i => e (q.symm i).1) (fun i => (q.symm i).1) (fun i => he _ (q.symm i).2) P).1
    have h1 : ∀ g : WO S T → (WO S T → ℂ), ∑ u ∈ e.support, e u • g u = ∑ i, e (q.symm i).1 • g (q.symm i).1 := by
      intro g
      rw [← Finset.sum_coe_sort e.support]
      exact (Equiv.sum_comp q.symm (fun u : e.support => e u.1 • g u.1)).symm
    simp only [comb]
    rw [h1, h1]
    exact key
  refine ⟨?_, fun N N' hv => ?_⟩
  · have e1 : ((a * b, a' * b') : GA D S × GA D T) = (a, a') * (b, b') := rfl
    rw [e1, map_mul, Module.End.mul_apply, hfin.2, hfx, GlobalTheory.FiniteFock.pureTensorO_smul, ← hcomb, map_smul,
      GlobalTheory.FrComb.om_comb hW ha ha' he hth₀]
  · refine ⟨hW.om_pres _ _ hth₀, GlobalTheory.FrComb.latVac_om hW ha ha' hth₀ ?_⟩
    have fix : ∀ u ∈ latO S T (N : Set _) (N' : Set _) (fun _ => True), heisO ψ S T u f₀ = f₀ →
        heisO ψ S T u (pureTensorO ψ θ S T sS sT BS BT f₀ P) = pureTensorO ψ θ S T sS sT BS BT f₀ P := by
      intro u hu h0
      have := ((GlobalTheory.FinTranslate.finite_translate D ψ θ S T hψ hθ f₀ hf₀).2 u (GlobalTheory.SplitScalar.latO_fin hu)).2 sS BS sT BT P
      rw [← this, h0]
    exact ⟨fun u hu => fix (2 • u) (AddSubgroup.nsmul_mem _ hu 2) (hv.2.1 u hu),
      fun e' he' u hu hh => fix u hu (hv.2.2 e' he' u hu hh)⟩

end GlobalTheory.FockComb
