import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.UConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedFactorEqProductAbove
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

private theorem ev_tendsto {ι : Type} (e : Ex ι) {x : ℕ → ι → ℂ} {y : ι → ℂ}
    (h : ∀ i, Tendsto (fun k => x k i) atTop (𝓝 (y i))) :
    Tendsto (fun k => e.ev (x k)) atTop (𝓝 (e.ev y)) := by
  induction e with
  | one => exact tendsto_const_nhds
  | gen i => exact h i
  | smul c a ih => exact ih.const_mul c
  | add a b iha ihb => exact iha.add ihb
  | mul a b iha ihb => exact iha.mul ihb

private theorem satEig_top_ne_zero (q n : ℕ) {C : Multiset ℂˣ} (hC : C.card = n) : satEig q n C n ≠ 0 := by
  intro h0
  have h := GlobalTheory.LFun.ConjPlace.satEig_inv_mul (q := q) hC (le_refl n)
  rw [h0, mul_zero, Nat.sub_self, GlobalTheory.LFun.ConjPlace.satEig_zero] at h
  exact zero_ne_one h

private theorem satEig_inv_eq (q n : ℕ) {B : Multiset ℂˣ} (hB : B.card = n) {i : ℕ} (hi : i ≤ n) :
    satEig q n (inv B) i = satEig q n B (n - i) / satEig q n B n := by
  rw [eq_div_iff (satEig_top_ne_zero q n hB)]
  exact GlobalTheory.LFun.ConjPlace.satEig_inv_mul hB hi

private theorem satEig_inv_tendsto (q n : ℕ) {B : ℕ → Multiset ℂˣ} {C : Multiset ℂˣ} (hB : ∀ k, (B k).card = n)
    (hC : C.card = n) (h : ∀ i : ℕ, Tendsto (fun k => satEig q n (B k) i) atTop (𝓝 (satEig q n C i)))
    {i : ℕ} (hi : i ≤ n) :
    Tendsto (fun k => satEig q n (inv (B k)) i) atTop (𝓝 (satEig q n (inv C) i)) := by
  rw [satEig_inv_eq q n hC hi]
  simp only [fun k => satEig_inv_eq q n (hB k) hi]
  exact (h (n - i)).div (h n) (satEig_top_ne_zero q n hC)

private theorem qV_cPl {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) :
    Formalism.UG.qV E (cPl w) = Formalism.UG.qV E w :=
  GlobalTheory.UnrEuler.ConjFac.absNorm_conjSrc _ w

theorem valLim : ValLim := by
  intro E _ _ _ a b T e₁ e₂ B₁ B₂ C₁ C₂ h
  unfold UpperTheory.V.Z.Tf.GlobalTraceComparison.val
  refine tendsto_finset_prod _ fun w hw => Tendsto.mul ?_ ?_
  · obtain ⟨-, -, -, h₁, h₂⟩ := h w (Or.inl hw)
    exact ev_tendsto _ fun p => (h₁ p.1).mul (h₂ p.2)
  · have hcc : cPl (cPl w) = w := ((UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm.places E).2.1 w).1
    obtain ⟨c₁, c₂, hk, h₁, h₂⟩ := h (cPl w) (Or.inr (hcc.symm ▸ hw))
    rw [qV_cPl] at h₁ h₂
    refine ev_tendsto _ fun p => Tendsto.mul ?_ ?_
    · exact satEig_inv_tendsto _ a (fun k => (hk k).1) c₁ h₁ (Nat.lt_succ_iff.1 p.1.2)
    · exact satEig_inv_tendsto _ b (fun k => (hk k).2) c₂ h₂ (Nat.lt_succ_iff.1 p.2.2)

end UpperTheory.Zero.ConvolutionTheory.EB
