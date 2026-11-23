import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationTwoVariableModelAndLineExte
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatContrIntIndicator
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapBesselToFourierJacobiLocalModel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapFourierJacobiToBesselLocalModel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineContractionSplitPlaceLocalModel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergInvariantFactorsContraction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SliceColMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatThetaMapsConvergeThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapsSatisfyFlatLawsFinitePlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumLocalModelFormula
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.DblStepLoc

theorem contr_flat_expand : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), GlobalTheory.SplitWeil.IsUnitVol ν → ∀ (p : GlobalTheory.LocMod.Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ψk : AddChar k Circle), p.IsChar ψ ψk → GlobalTheory.SplitWeil.HasConductor ψk 1 → ∀ (σ : ℕ) (B : GlobalTheory.Unf.BesLev D (σ + 1)) (J : GlobalTheory.Unf.JacLev D (σ + 1)) (B' : GlobalTheory.Unf.BesLev D σ) (n₀ : Type) [Fintype n₀] [DecidableEq n₀] (n₁ : Type) [Fintype n₁] [DecidableEq n₁] (n₂ : Type) [Fintype n₂] [DecidableEq n₂] (c : ℕ) (F : GlobalTheory.LocMod.Dbl p B J B' n₀ n₁ n₂ c) (s₁ : GlobalTheory.Unf.StepBF ψ B J) (s₂ : GlobalTheory.Unf.StepFB ψ J B') (l : GlobalTheory.Unf.Link B B'.L B'.ζ) (vL : GlobalTheory.Unf.VolM D B'.L.rank J.W₀.rank) T₁ T₂, p.IsModel ψ F.G₀ F.G₁ T₁ → p.IsModel ψ F.G₁ F.G₂ T₂ → ∀ Φ₁ Φ₂ O₁ O₂, GlobalTheory.LocMod.IsOne O₁ → GlobalTheory.LocMod.IsOne O₂ → ∀ (I : Type) (S : Finset I) (x : I → ℂ) (Ξ₁ : I → GlobalTheory.SplitWeil.SB (Matrix n₁ n₀ k)) (Ξ₂ : I → GlobalTheory.SplitWeil.SB (Matrix n₂ n₁ k)) (c₁ : I → WO B.A J.W₀ →₀ ℂ) (c₂ : I → WO J.W₀ B'.A →₀ ℂ), (∀ i ∈ S, p.IsCombAt ψ F.F₀ F.F₁ (c₁ i) (Ξ₁ i).1 ∧ p.IsCombAt ψ F.F₁ F.F₂ (c₂ i) (Ξ₂ i).1) → (∀ q, GlobalTheory.LocFlat.contr ψk ν (GlobalTheory.LocFlat.flCol ψk ν (σ + 1 + 1) Φ₁.1) (GlobalTheory.LocFlat.flRow ψk ν (σ + 1) Φ₂.1) q = ∑ i ∈ S, x i * ((Ξ₁ i).1 q.1 * (Ξ₂ i).1 q.2)) → GlobalTheory.Unf.contr l J.W₀ vL (GlobalTheory.Unf.flatBF s₁ (T₁ Φ₁)) (GlobalTheory.Unf.flatFB s₂ (T₂ Φ₂)) = ∑ i ∈ S, x i • biComb ψ B.A J.W₀ B'.A (c₁ i) (c₂ i) (GlobalTheory.Unf.contr l J.W₀ vL (GlobalTheory.Unf.flatBF s₁ (T₁ O₁)) (GlobalTheory.Unf.flatFB s₂ (T₂ O₂))) := by
  intro D k _ _ _ _ _ _ ν hν p ψ hstd ψk hchar hcond σ B J B' n₀ _ _ n₁ _ _ n₂ _ _ c F s₁ s₂ l vL T₁ T₂ hT₁ hT₂
    Φ₁ Φ₂ O₁ O₂ hO₁ hO₂ I S x Ξ₁ Ξ₂ c₁ c₂ hcomb hcontr
  have hcσ : c = 2 * σ := by have := F.bes.1; omega
  have hBF := GlobalTheory.FlatBFLoc.flatBF_of_laws D (GlobalTheory.Unf.Flat.flatLaw D) (GlobalTheory.FinPl.flatLaws_all D) (GlobalTheory.LocOm.omLoc D)
  have hFB := GlobalTheory.LocMod.flatFB_holds D (GlobalTheory.Unf.Flat.flatLaw D) (GlobalTheory.FinPl.flatLaws_all D) (GlobalTheory.LocOm.omLoc D)
  have hCL := GlobalTheory.ContrLocProof.contrLoc D GlobalTheory.LocFlat.contrFactor
  have hψc : Continuous ψk := hcond.continuous
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.LocMod.GValProof.core_of_bes p B F.s F.F₀ F.G₀ F.bes
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.LocMod.GValProof.core_of_bes p B' (F.s * p.xi) F.F₂ F.G₂ F.bes'
  have hjac : p.IsJacFrame J F.s (-p.xi ^ 2 * p.hz B') F.F₁ F.G₁ := by
    rw [← GlobalTheory.LocMod.GValProof.hz_link p B B' l]; exact F.jac
  obtain ⟨U₁, hU₁, hU₁e⟩ := hBF k p ν hν.1 ψ ψk hchar (σ + 1) B J s₁ F.s F.s_ne _ _ (c + 1 + 1) F.F₀ C₀ F.G₀ F.F₁ F.G₁
    hC₀ F.bes F.jac T₁ hT₁
  obtain ⟨U₂, hU₂, hU₂e⟩ := hFB k p ν hν.1 ψ ψk hchar σ J B' s₂ F.s F.s_ne _ _ (c + 1) F.F₁ F.G₁ F.F₂ C₂ F.G₂
    hjac hC₂ F.bes' T₂ hT₂
  obtain ⟨Λ, hΛ, hΛe⟩ := hCL k p ν hν.1 ψ hstd ψk hchar (σ + 1) σ B B' l J.W₀ vL F.s F.s_ne _ _ _ F.F₀ C₀ F.F₁ F.F₂ C₂
    hC₀ hC₂ U₁ U₂ hU₁ hU₂
  have hfl := GlobalTheory.LocFlat.flat_SB_onto k ψk ν hψc hν.1
  have m₁ := fun Φ : GlobalTheory.SplitWeil.SB _ =>
    ((hfl n₁ n₀ (c + 1 + 1) (σ + 1 + 1) (by omega)).1 (by omega)).1 Φ.1 Φ.2
  have m₂ := fun Φ : GlobalTheory.SplitWeil.SB _ =>
    ((hfl n₂ n₁ (c + 1) (σ + 1) (by omega)).2 (by omega)).1 Φ.1 Φ.2
  let Ψ₁ : GlobalTheory.SplitWeil.SB _ := ⟨_, m₁ Φ₁⟩
  let Ψ₂ : GlobalTheory.SplitWeil.SB _ := ⟨_, m₂ Φ₂⟩
  let P₁ : GlobalTheory.SplitWeil.SB _ := ⟨_, m₁ O₁⟩
  let P₂ : GlobalTheory.SplitWeil.SB _ := ⟨_, m₂ O₂⟩
  rw [hU₁e Φ₁ Ψ₁ rfl, hU₂e Φ₂ Ψ₂ rfl, hU₁e O₁ P₁ rfl, hU₂e O₂ P₂ rfl]
  obtain ⟨Ξ, hΞ, e1⟩ := hΛe Ψ₁ Ψ₂
  obtain ⟨ΞO, hΞO, e2⟩ := hΛe P₁ P₂
  rw [e1, e2]
  have hun := GlobalTheory.LocFlat.flat_contr_intIndicator k ψk ν hcond hν
  let Q₁ : GlobalTheory.SplitWeil.SB (Matrix n₁ n₀ k) := ⟨_, GlobalTheory.LocMod.GValProof.one_mem_SB _ _⟩
  let Q₂ : GlobalTheory.SplitWeil.SB (Matrix n₂ n₁ k) := ⟨_, GlobalTheory.LocMod.GValProof.one_mem_SB _ _⟩
  have hP₁ : P₁.1 = Set.indicator {x : Matrix n₁ (n₀ ⊕ Unit) k | ∀ r q, x r q ∈ (ValuativeRel.valuation k).integer}
      fun _ => 1 := by
    simp only [P₁]
    rw [hO₁, (hun n₁ n₀ n₀ (c + 1 + 1) (σ + 1 + 1)).1, if_neg (by omega)]
  have hP₂ : P₂.1 = Set.indicator {x : Matrix (n₂ ⊕ Unit) n₁ k | ∀ r q, x r q ∈ (ValuativeRel.valuation k).integer}
      fun _ => 1 := by
    simp only [P₂]
    rw [hO₂, (hun n₂ n₁ n₀ (c + 1) (σ + 1)).2.1 (by omega) (by omega)]
  have hΞO' : ∀ q, ΞO.1 q = Q₁.1 q.1 * Q₂.1 q.2 := by
    intro q
    rw [hΞO, hP₁, hP₂]
    exact (hun n₁ n₀ n₂ 0 0).2.2 q
  let Pr : I → GlobalTheory.SplitWeil.SB (Matrix n₁ n₀ k × Matrix n₂ n₁ k) := fun i => GlobalTheory.LocFlat.CFac.prodSB (Ξ₁ i) (Ξ₂ i)
  have hPr : ∀ i q, (Pr i).1 q = (Ξ₁ i).1 q.1 * (Ξ₂ i).1 q.2 := fun i q => rfl
  have hΞs : Ξ = ∑ i ∈ S, x i • Pr i := by
    apply Subtype.ext
    funext q
    rw [hΞ]
    refine (hcontr q).trans ?_
    rw [Submodule.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, hPr]
  rw [hΞs, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_smul]
  congr 1
  exact (GlobalTheory.BiComb.comb_bimodel_and_line D k p ψ _ _ _).1 B.A J.W₀ B'.A F.F₀ F.F₁ F.F₂ Λ (c₁ i) (c₂ i) (Ξ₁ i) Q₁ (Ξ₂ i) Q₂
    (Pr i) ΞO hΛ (hcomb i hi).1 (hcomb i hi).2 rfl rfl (hPr i) hΞO'

end GlobalTheory.DblStepLoc
