import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelExistsForContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RegularisedIntegralLinearPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmegaCentreLinearStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
noncomputable section

namespace GlobalTheory.Core.Rk.RegKill

variable {D : D7}

theorem foldr_ops_zero {X : Type} (l : List ((X → ℂ) → (X → ℂ))) (hl : ∀ f ∈ l, f 0 = 0) :
    l.foldr (fun f acc => f acc) 0 = 0 := by
  induction l with
  | nil => rfl
  | cons f l ih =>
    rw [List.foldr_cons, ih (fun g hg => hl g (List.mem_cons_of_mem _ hg))]
    exact hl f List.mem_cons_self

theorem opPow_zero {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (hA : ∀ i, A i 0 = 0) (k : ι →₀ ℕ) :
    opPow A k 0 = 0 := by
  unfold opPow
  induction (Multiset.toList (Finsupp.toMultiset k)) with
  | nil => rfl
  | cons i l ih => rw [List.foldr_cons, ih, hA]

theorem centreAct_zero (θ : InfFam D) (τ : D.what₂.Tau) (T : HSp D) (p : MvPolynomial ℕ ℂ) :
    centreAct θ τ T p (0 : GA D T → ℂ) = 0 := by
  have hR : ∀ Z, RderC θ T τ Z (0 : GA D T → ℂ) = 0 := by
    intro Z
    funext g
    simp [RderC, Rder]
  have hg : ∀ k, gelf θ T τ k (0 : GA D T → ℂ) = 0 := by
    intro k
    funext g
    simp only [gelf]
    rw [Finset.sum_apply]
    refine Finset.sum_eq_zero fun idx _ => ?_
    rw [foldr_ops_zero]
    · rfl
    · intro f hf
      obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hf
      exact hR _
  unfold centreAct polyAct
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [opPow_zero _ hg, smul_zero]

theorem laurent_zero (s₀ : ℂ) (n : ℤ) : laurent (fun _ : ℂ => (0 : ℂ)) s₀ n = 0 :=
  CoeffAt.laurent_eq ⟨_, isExtAt_const 0 s₀, laurentConst_of_tendsto (by simpa using tendsto_const_nhds)⟩

section
variable {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))

theorem thetaKO_one_om (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    thetaKO om 1 h (om (g, 1) f) = thetaKO om g h f := by
  unfold thetaKO
  have e : (((1 : GA D S), h) : GA D S × GA D T) * (g, 1) = (g, h) := by ext <;> simp
  rw [← Module.End.mul_apply, ← map_mul, e]

theorem thetaKO_rat {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle} (hω : IsWeilDatumO ψ S T χS χT om)
    {γ : GA D S} (hγ : γ ∈ GQ S) (g : GA D S) (h : GA D T) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    thetaKO om (γ * g) h f = thetaKO om g h f := by
  unfold thetaKO
  have e : ((γ * g, h) : GA D S × GA D T) = (γ, 1) * (g, h) := by ext <;> simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hω.om_aut γ hγ 1 (one_mem _) _ (hω.om_pres _ _ hf)

end

theorem dblInt_regRes_eq_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)), Defin θ A cA a → ∀ (W W₀ : HSp D) (r' : ℕ) (d₀ : HypDec W W₀ r') (b' : GL (Fin W.rank) (AE D)) (χ : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) W), IsWeilDatumO ψ (dblSp A) W 1 χ omh → ∀ (m : Measure (GA D A)) (mW : Measure (GA D W)), m.IsHaarMeasure → mW.IsHaarMeasure → ∀ u : GA D A → ℂ, Continuous u → (∀ γ ∈ GQ A, ∀ g, u (γ * g) = u g) → Kills ψ χ omh m u → EisensteinContinues d₀ b' → ∀ (τ : D.what₂.Tau) (zH : MvPolynomial ℕ ℂ) (P : Polynomial ℂ), P ≠ 0 → (∀ φ', IsThetaFunO ψ (dblSp A) W φ' → RegIntProps ψ omh mW θ τ d₀ b' zH P φ') → ∀ φ, IsThetaFunO ψ (dblSp A) W φ → IsKFinVec omh (Khat A a) φ → GlobalTheory.Eis.dblInt A χ⁻¹ m (regRes omh mW θ τ d₀ b' zH P φ) (fun g => conj (u g)) (fun g => conj (u g)) = 0 := by
  intro D ψ θ A cA a hDef W W₀ r' d₀ b' χ omh hW m mW hm hmW u hu hinv hK hAux τ zH P hP hReg φ hφ hfin
  obtain ⟨φ', hφ', hcol⟩ := GlobalTheory.T.theta_kernel_exists_for_continuous D ψ θ A cA a hDef W χ omh hW φ hφ hfin m hm u hu hinv
  have hZ := GlobalTheory.T.omega_centre_linear D ψ θ (dblSp A) W 1 χ omh hDef.inf hW τ zH
  have hzero : ∀ h, thetaKO omh 1 h φ' = 0 := by
    intro h
    have e := hcol (fun f => thetaKO omh 1 h f)
      (fun f f' _ _ => by simp [thetaKO, map_add])
      (fun c f _ => by simp [thetaKO, map_smul])
      (fun γ hγ g => by
        simp only [thetaKO_one_om]
        exact thetaKO_rat omh hW hγ g h hφ)
    rw [← e]
    simp only [thetaKO_one_om]
    exact hK φ hφ h
  have hshift : ∀ f, IsThetaFunO ψ (dblSp A) W f → ∀ g,
      regRes omh mW θ τ d₀ b' zH P (omh (g, 1) f) 1 = regRes omh mW θ τ d₀ b' zH P f g := by
    intro f hf g
    have hf1 := hW.om_pres (g, 1) f hf
    unfold regRes
    congr 1
    funext s
    unfold regInt thetaPair
    congr 2
    funext q
    unfold AutomorphicL2Unitary.descend
    beta_reduce
    congr 1
    rw [hZ.2.2 _ hf1, hZ.2.2 _ hf]
    simp only [thetaKO_one_om]
  have hrat : ∀ f, IsThetaFunO ψ (dblSp A) W f → ∀ γ ∈ GQ (dblSp A), ∀ g,
      regRes omh mW θ τ d₀ b' zH P f (γ * g) = regRes omh mW θ τ d₀ b' zH P f g := by
    intro f hf γ hγ g
    have hF := (hReg f hf).1
    unfold regRes
    congr 1
    funext s
    unfold regInt thetaPair
    congr 2
    funext q
    unfold AutomorphicL2Unitary.descend
    beta_reduce
    rw [thetaKO_rat omh hW hγ g _ hF]
  have hlin := GlobalTheory.T.regularised_integral_linear_properties D ψ θ (dblSp A) W W₀ r' d₀ b' 1 χ omh hDef.inf hW mW hAux τ zH P hReg
  have e := hcol (fun f => regRes omh mW θ τ d₀ b' zH P f 1)
    (fun f f' hf hf' => hlin.1 f f' hf hf' 1)
    (fun c f hf => hlin.2 c f hf 1)
    (fun γ hγ g => by
      rw [hshift _ hφ, hshift _ hφ, hrat _ hφ γ hγ])
  have hfun : (fun g => regRes omh mW θ τ d₀ b' zH P (omh (g, 1) φ) 1) = regRes omh mW θ τ d₀ b' zH P φ :=
    funext (hshift φ hφ)
  rw [hfun] at e
  rw [e]
  have hI : regInt omh mW θ τ d₀ b' zH P φ' 1 = fun _ => 0 := by
    funext s
    unfold regInt thetaPair
    have hint : (fun h => thetaKO omh 1 h (omCentreT omh θ τ zH φ') * sphericalEisenstein d₀ b' h s) = fun _ => (0 : ℂ) := by
      funext h
      rw [hZ.2.2 _ hφ']
      have h0 : (fun h' => thetaKO omh 1 h' φ') = (0 : GA D W → ℂ) := funext hzero
      rw [h0, centreAct_zero]
      simp
    rw [hint]
    simp [AutomorphicL2Unitary.descend]
  show laurent (regInt omh mW θ τ d₀ b' zH P φ' 1) (rhoH W r') (-1) = 0
  rw [hI]
  exact laurent_zero _ _

end GlobalTheory.Core.Rk.RegKill

end
