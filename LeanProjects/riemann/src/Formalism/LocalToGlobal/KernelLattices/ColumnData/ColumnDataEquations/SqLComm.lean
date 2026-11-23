import Formalism.LocalToGlobal.KernelLattices.ColumnData.ColumnDataEquations.SqLLaw
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.WeightThresholdDefs

noncomputable section
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SquareSplitPairs

open Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds

open Formalism.MainNotions Formalism.L2.Ker.Cd.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq

variable {D : Car}

theorem mul_smul_mem {N : ℕ} {L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {m k : 𝓞 D.host.E}
    {v : Fin N → D.host.E} (h : (k : D.host.E) • v ∈ L₁) : ((m * k : 𝓞 D.host.E) : D.host.E) • v ∈ L₁ := by
  have e : ((m * k : 𝓞 D.host.E) : D.host.E) • v = m • ((k : D.host.E) • v) := by
    rw [osmul, smul_smul]
    norm_cast
  rw [e]
  exact L₁.smul_mem m h

theorem exists_smul_mem {N : ℕ} {L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    (hsp : Submodule.span D.host.E (L₁ : Set (Fin N → D.host.E)) = ⊤) (x : Fin N → D.host.E) :
    ∃ n : 𝓞 D.host.E, n ≠ 0 ∧ (n : D.host.E) • x ∈ L₁ := by
  first | exact UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem .. | (apply UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem <;> assumption) | (intros; apply UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem <;> assumption) | (apply @UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem <;> assumption) | (apply @UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem D N L₁ hsp x | exact @UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem D N L₁ hsp | exact @UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem D N L₁ | exact @UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem D N | exact @UpperTheory.Reformulated.B.WeightThresholdDefs.exists_smul_mem D

theorem exists_n_one {N : ℕ} {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (hL : L.FG)
    (hsp : Submodule.span D.host.E (L₁ : Set (Fin N → D.host.E)) = ⊤) :
    ∃ n : 𝓞 D.host.E, n ≠ 0 ∧ ∀ u ∈ L, (n : D.host.E) • u ∈ L₁ := by
  obtain ⟨s, hs⟩ := hL
  choose f hf0 hf using exists_smul_mem hsp
  refine ⟨∏ g ∈ s, f g, Finset.prod_ne_zero_iff.2 fun g _ => hf0 g, ?_⟩
  intro u hu
  rw [← hs] at hu
  induction hu using Submodule.span_induction with
  | mem g hg =>
    rw [← Finset.prod_erase_mul s f hg]
    exact mul_smul_mem (hf g)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact L₁.add_mem hx hy
  | smul c x _ hx =>
    rw [osmul c x, smul_comm, ← osmul]
    exact L₁.smul_mem c hx

theorem exists_n {N : ℕ} {L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} (hL : SD D L) (hL1 : SD D L₁) :
    ∃ n : 𝓞 D.host.E, n ≠ 0 ∧ (∀ u ∈ L, (n : D.host.E) • u ∈ L₁) ∧ ∀ u ∈ L₁, (n : D.host.E) • u ∈ L := by
  obtain ⟨hfg, hsp, -⟩ := hL
  obtain ⟨hfg1, hsp1, -⟩ := hL1
  obtain ⟨a, ha, h1⟩ := exists_n_one hfg hsp1
  obtain ⟨b, hb, h2⟩ := exists_n_one hfg1 hsp
  refine ⟨b * a, mul_ne_zero hb ha, fun u hu => mul_smul_mem (h1 u hu), fun u hu => ?_⟩
  rw [mul_comm]
  exact mul_smul_mem (h2 u hu)

end Formalism.L2.Ker.Cd.PairingIndexBounds.Eq.SquareSplitPairs
