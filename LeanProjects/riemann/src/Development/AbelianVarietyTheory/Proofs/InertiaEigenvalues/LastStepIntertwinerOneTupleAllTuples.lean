import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksW
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteLastStepRealIntertwiner
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealIntertwinerOfCompactGroupIntertwiner

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.Chain GlobalTheory.CompactHowe GlobalTheory.CompactHowe.LastStep
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IntertwinerTransfer

variable {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar}

theorem isItW_transfer (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S')
    (ρ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → PolF D W.rank V.rank → PolF D W.rank V.rank)
    (ρ' : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ → PolF D W.rank V.rank → PolF D W.rank V.rank)
    (hd : ∀ τ g φ, (ρ τ g φ).totalDegree ≤ φ.totalDegree) (hd' : ∀ τ h φ, (ρ' τ h φ).totalDegree ≤ φ.totalDegree)
    (ω ω₁ : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (pt pt₁ : PolF D W.rank V.rank →ₗ[ℂ] (WO V W → ℂ))
    (hpt : Function.Injective pt) (hpt₁ : Function.Injective pt₁)
    (hω : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ φ, ω (atTau θ V τ g, 1) (pt φ) = pt (ρ τ g φ))
    (hω' : ∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ), ∀ φ, ω (1, atTau θ W τ h) (pt φ) = pt (ρ' τ h φ))
    (hω₁ : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ φ, ω₁ (atTau θ V τ g, 1) (pt₁ φ) = pt₁ (ρ τ g φ))
    (hω₁' : ∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ), ∀ φ, ω₁ (1, atTau θ W τ h) (pt₁ φ) = pt₁ (ρ' τ h φ))
    (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) (hIt : IsItW θ M M' ω pt It) :
    IsItW θ M M' ω₁ pt₁ It := by
  refine ⟨hIt.ne, hIt.bdd, ?_, ?_, ?_, ?_⟩
  · intro τ g hg φ φ' h v
    rw [hω₁ τ g hg] at h
    refine hIt.eqK τ g hg φ φ' ?_ v
    rw [hω τ g hg, hpt₁ h]
  · intro τ X hX φ φ' h v
    have hm : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
      fun t => GlobalTheory.GardingVec.exp_mem (GlobalTheory.CompactIntertwiner.isUnit_gram M τ) hX t
    simp only [oneP, hω₁ τ _ (hm _)] at h
    refine hIt.eqg τ X hX φ φ' (fun z => ?_) v
    simp only [oneP, hω τ _ (hm _)]
    exact GlobalTheory.CompactIntertwiner.hasDerivAt_pol pt₁ hpt₁ (fun t : ℝ => ρ τ (NormedSpace.exp (t • X)) φ) _
      (fun t => hd τ _ φ) φ' h (LinearMap.proj z ∘ₗ pt)
  · intro τ h hh φ φ' v v' e e'
    rw [hω₁' τ h hh] at e
    refine hIt.invK τ h hh φ φ' v v' ?_ e'
    rw [hω' τ h hh, hpt₁ e]
  · intro τ X hX φ φ' v v' h h'
    have hm : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ) :=
      fun t => GlobalTheory.GardingVec.exp_mem (GlobalTheory.CompactIntertwiner.isUnit_gram M' τ) hX t
    simp only [oneP, hω₁' τ _ (hm _)] at h
    refine hIt.invg τ X hX φ φ' v v' (fun z => ?_) h'
    simp only [oneP, hω' τ _ (hm _)]
    exact GlobalTheory.CompactIntertwiner.hasDerivAt_pol pt₁ hpt₁ (fun t : ℝ => ρ' τ (NormedSpace.exp (t • X)) φ) _
      (fun t => hd' τ _ φ) φ' h (LinearMap.proj z ∘ₗ pt)

open Classical in

theorem isItW_lastStep_transfer (k : Fin D.R.m) (hk : (k : ℕ) + 1 = D.R.m) (a : ℕ) (ha : a = k) (hV : V.SigOK)
    (hW : W.SigOK) (rV : V.rank = D.R.r + k * D.R.t) (rW : W.rank = V.rank + D.R.t)
    (M : DSModel V (parB (Ptw D) a)) (M' : DSModel W (parB (Ptw D) D.R.m)) (θ : InfFam D) (hθ : IsInfFam θ)
    (ψ : AddChar (AF D.host.F) ℂ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M)
    (ω ω₁ : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f f₁ : WO V W → ℂ)
    (hω : IsStepWeil k ψ V W ω) (hf : IsVacVec ψ θ M M' f) (hω₁ : IsStepWeil k ψ V W ω₁) (hf₁ : IsVacVec ψ θ M M' f₁)
    (hIt : IsItW θ M M' ω (ptOf ψ θ M M' f) It) : IsItW θ M M' ω₁ (ptOf ψ θ M M' f₁) It := by
  subst ha
  have hp := fun τ => GlobalTheory.T.lastStep_parameters_partition_extended_by_zeros D k τ V.rank W.rank (M.lam τ) (M.ε τ) (M'.lam τ) (M'.ε τ) hk rV rW (M.enum τ) (M'.enum τ)
  have hε := fun τ => (hp τ).1
  have hε' := fun τ => (hp τ).2.1
  choose x₁ x₃ h1 h3 _ using fun τ => (hp τ).2.2
  have act : ∀ (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (f : WO V W → ℂ), IsStepWeil k ψ V W ω →
      IsVacVec ψ θ M M' f →
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ φ, ω (atTau θ V τ g, 1) (ptOf ψ θ M M' f φ) =
        ptOf ψ θ M M' f (polAct M M' x₁ x₃ (Function.update (fun _ => 1) τ g) (fun _ => 1) φ)) ∧
      (∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ), ∀ φ, ω (1, atTau θ W τ h) (ptOf ψ θ M M' f φ) =
        ptOf ψ θ M M' f (polAct M M' x₁ x₃ (fun _ => 1) (Function.update (fun _ => 1) τ h) φ)) := by
    intro ω f hω hf
    refine ⟨fun τ g hg φ => ?_, fun τ h hh φ => ?_⟩
    · have := om_ptOf hθ hV hW M M' hε hε' x₁ x₃ h1 h3 hω hf (GlobalTheory.PointAtPlaceHom.atTau_mem (θ := θ) V τ g) (one_mem _) φ
      rwa [compAt_atTau hθ τ hg, compAt_one] at this
    · have := om_ptOf hθ hV hW M M' hε hε' x₁ x₃ h1 h3 hω hf (one_mem _) (GlobalTheory.PointAtPlaceHom.atTau_mem (θ := θ) W τ h) φ
      rwa [compAt_atTau hθ τ hh, compAt_one] at this
  have a0 := act ω f hω hf
  have a1 := act ω₁ f₁ hω₁ hf₁
  exact isItW_transfer θ M M' (fun τ g => polAct M M' x₁ x₃ (Function.update (fun _ => 1) τ g) fun _ => 1)
    (fun τ h => polAct M M' x₁ x₃ (fun _ => 1) (Function.update (fun _ => 1) τ h))
    (fun _ _ _ => totalDegree_polAct _ _ _ _ _ _ _) (fun _ _ _ => totalDegree_polAct _ _ _ _ _ _ _) ω ω₁
    (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f)
    (pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f₁)
    (GlobalTheory.T.fockVectorsOfThetaDatum_injective D V W _ _ ψ θ M M' f hω.choose_spec.choose_spec.1.std hθ hf)
    (GlobalTheory.T.fockVectorsOfThetaDatum_injective D V W _ _ ψ θ M M' f₁ hω₁.choose_spec.choose_spec.1.std hθ hf₁)
    a0.1 a0.2 a1.1 a1.2 It hIt

theorem pItX_of_one : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.chain_ωX → R.chain_vX → ∀ (t₀ : T) (y : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank →ₗ[ℂ] SmT R.MX →ₗ[ℂ] SmT (R.MY (D.R.m - 1))), IsItW R.θ (R.MY (D.R.m - 1)) R.MX (R.ωX t₀) (R.ptX t₀) y → R.PItX y := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL hM hω hv t₀ y hy t
  have hm := D.R.two_le_m
  let k : Fin D.R.m := ⟨D.R.m - 1, by omega⟩
  have hk : (k : ℕ) = D.R.m - 1 := rfl
  have hS := fun t => GlobalTheory.T.lastThetaChainStep_exponents_and_nonzero_vacuum D G Pl0 T A Ks R hL hM.inf hω hv t k hk
  have rV : (Yc D (D.R.m - 1)).rank = D.R.r + k * D.R.t := by
    rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left (Nat.sub_le _ _)]; rfl
  have rW : D.sp.X'.rank = (Yc D (D.R.m - 1)).rank + D.R.t := by
    rw [rV, D.sp.X'_rank, Ranks.rankX', add_assoc, ← Nat.succ_mul]
    congr 2
    omega
  exact isItW_lastStep_transfer k (by omega) (min (D.R.m - 1) D.R.m) (by omega) (D.sp.Y_sig _) D.sp.X'_sig rV rW
    (R.MY (D.R.m - 1)) R.MX R.θ hM.inf R.ψ y (R.ωX t₀) (R.ωX t) (R.vX t₀) (R.vX t) (hS t₀).1 (hS t₀).2 (hS t).1 (hS t).2 hy

end GlobalTheory.IntertwinerTransfer
