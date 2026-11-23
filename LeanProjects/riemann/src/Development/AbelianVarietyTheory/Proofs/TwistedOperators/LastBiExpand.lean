import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationTwoVariableModelAndLineExte
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDoubleStepKernelLocalModels
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntIndFromCols
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.LastSeeSawGen.lastBi_expand : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), GlobalTheory.SplitWeil.IsUnitVol ν → ∀ (p : GlobalTheory.LocMod.Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ψk : AddChar k Circle), p.IsChar ψ ψk → GlobalTheory.SplitWeil.HasConductor ψk 1 → ∀ (ρ : ℕ) (B : GlobalTheory.Unf.BesLev D ρ) (W X T L'' : HSp D) (o'' : OrthDec X T L'') (τ : Matrix (Fin B.L.rank) (Fin L''.rank) D.host.E), L''.rank = 1 → τᴴ * (B.L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∀ (a : k) (z₀ : Fin L''.rank → k), a ≠ 0 → τ.map p.pr *ᵥ z₀ = (-(p.xi * a)) • (fun i => p.pr (B.ζ i)) → ∀ (n : Type) [Fintype n] [DecidableEq n] (n' : Type) [Fintype n'] [DecidableEq n'] (Z : Type) [Fintype Z] [DecidableEq Z] (FA : GlobalTheory.LocMod.Frame k B.A.rank n') (F₀ : GlobalTheory.LocMod.Frame k B.V₀.rank (n' ⊕ Unit)) (FS : GlobalTheory.LocMod.Frame k W.rank n) (FT : GlobalTheory.LocMod.Frame k T.rank Z) (FX : GlobalTheory.LocMod.Frame k X.rank (Z ⊕ Unit)), p.IsCoreFrame B a FA F₀ → FX.β = fromCols (o''.iA.map p.pr * FT.β) (Matrix.of fun r _ => (o''.iB.map p.pr *ᵥ z₀) r) → ∀ T₁ T₂, p.IsModel ψ F₀ FS T₁ → p.IsModel ψ FS FT T₂ → ∀ Φ₁ Φ₂ O₁ O₂, GlobalTheory.LocMod.IsOne O₁ → GlobalTheory.LocMod.IsOne O₂ → ∀ (I : Type) (S : Finset I) (x : I → ℂ) (Ξ₁ : I → GlobalTheory.SplitWeil.SB (Matrix n n' k)) (Ξ₂ : I → GlobalTheory.SplitWeil.SB (Matrix (Z ⊕ Unit) n k)) (c₁ : I → WO B.A W →₀ ℂ) (c₂ : I → WO W X →₀ ℂ), (∀ i ∈ S, p.IsCombAt ψ FA FS (c₁ i) (Ξ₁ i).1 ∧ p.IsCombAt ψ FS FX (c₂ i) (Ξ₂ i).1) → (∀ (y : Matrix n n' k) (y' : Matrix (Z ⊕ Unit) n k), Φ₂.1 y'.toRows₁ * GlobalTheory.StepData.hat ψk ν (-1) (fun u => Φ₁.1 (fromCols y (Matrix.of fun r _ => u r))) (y' (Sum.inr ())) = ∑ i ∈ S, x i * ((Ξ₁ i).1 y * (Ξ₂ i).1 y')) → GlobalTheory.FinPl.lastBi B.o o'' τ (T₁ Φ₁) (T₂ Φ₂) = ∑ i ∈ S, x i • biComb ψ B.A W X (c₁ i) (c₂ i) (GlobalTheory.FinPl.lastBi B.o o'' τ (T₁ O₁) (T₂ O₂)) := by
  classical
  intro D k _ _ _ _ _ _ ν hν p ψ hstd ψk hchar hcond ρ B W X T L'' o'' τ hL hτ a z₀ ha hz n _ _ n' _ _ Z _ _
    FA F₀ FS FT FX hcore hFX T₁ T₂ hT₁ hT₂ Φ₁ Φ₂ O₁ O₂ hO₁ hO₂ I S x Ξ₁ Ξ₂ c₁ c₂ hc hrel
  have := hν.1
  obtain ⟨Λ, hΛ, hK⟩ := GlobalTheory.LastKerLoc.lastLoc D k p ν hν.1 ψ hstd ψk hchar ρ B W X T L'' o'' τ hL hτ a z₀ ha hz
    n n' Z FA F₀ FS FT FX hcore hFX T₁ T₂ hT₁ hT₂
  obtain ⟨Ξ, hΞ, hΞK⟩ := hK Φ₁ Φ₂
  obtain ⟨Ξ', hΞ', hΞ'K⟩ := hK O₁ O₂
  have hv1 : valuation k (-1 : k) = 1 := by simp
  haveI : T2Space (Matrix n n' k) := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField
  haveI : T2Space (Matrix (Z ⊕ Unit) n k) := GlobalTheory.FinPl.Comm.t2Space_matrix_of_isNonarchimedeanLocalField
  let P : I → SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k) := fun i =>
    ⟨fun q => (Ξ₁ i).1 q.1 * (Ξ₂ i).1 q.2,
      GlobalTheory.FinPl.Comm.prod_mem_SB (Ξ₁ i).2 (Ξ₂ i).2 continuous_fst continuous_snd continuous_id fun _ => rfl⟩
  let O₁' : SB (Matrix n n' k) := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB _ _⟩
  let O₂' : SB (Matrix (Z ⊕ Unit) n k) := ⟨_, GlobalTheory.LastTwoSteps.intInd_mem_SB _ _⟩
  have hone : ∀ q, Ξ'.1 q = O₁'.1 q.1 * O₂'.1 q.2 := fun q => by
    rw [hΞ' q, hO₂]
    have e : (fun y => O₁.1 (fromCols q.1 (Matrix.of fun r _ => y r))) = fun y =>
        Set.indicator {x : Matrix n n' k | ∀ r q, x r q ∈ 𝒪[k]}
          (fun _ => (1 : ℂ)) q.1 * cosetInd (box _ (1 : kˣ)) (Submodule.Quotient.mk 0) y := by
      funext y
      rw [hO₁]
      exact GlobalTheory.LastTwoSteps.intInd_fromCols q.1 y
    rw [e, GlobalTheory.LastTwoSteps.hat_const_mul, GlobalTheory.LastTwoSteps.hat_int hcond hν hv1]
    simp only [O₁', O₂']
    rw [GlobalTheory.LastTwoSteps.intInd_rows q.2]
    ring
  have hsum : Ξ = ∑ i ∈ S, x i • P i := by
    apply Subtype.ext
    funext q
    rw [hΞ q, hrel q.1 q.2, Submodule.coe_sum, Finset.sum_apply]
    rfl
  have key : ∀ i ∈ S, Λ (P i) = biComb ψ B.A W X (c₁ i) (c₂ i) (Λ Ξ') := fun i hi =>
    (GlobalTheory.BiComb.comb_bimodel_and_line D k p ψ n n' (Z ⊕ Unit)).1 B.A W X FA FS FX Λ (c₁ i) (c₂ i) (Ξ₁ i) O₁'
      (Ξ₂ i) O₂' (P i) Ξ' hΛ (hc i hi).1 (hc i hi).2 rfl rfl (fun _ => rfl) hone
  have e1 : GlobalTheory.FinPl.lastBi B.o o'' τ (T₁ Φ₁) (T₂ Φ₂) = Λ Ξ := funext fun u => hΞK u
  have e2 : GlobalTheory.FinPl.lastBi B.o o'' τ (T₁ O₁) (T₂ O₂) = Λ Ξ' := funext fun u => hΞ'K u
  rw [e1, e2, hsum, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_smul, key i hi]
