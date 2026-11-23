import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FactorRapid

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc.RowLin

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem sum_sec {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (E : KMod n) (hLg : LgFacts) (hU : Unimod) (hR : RCalc) (hCl : ClsFacts) (hOps : SobOps)
    {ι : Type} (f₀ : Mat n → E.V) (h₀ : Sob μ f₀) (f : ι → Mat n → E.V) (hS : ∀ i, Sob μ (f i))
    (hI : ∀ i, IsSec E (f i)) (a : ι → ℂ) (s : Finset ι) :
    Sob μ (fun y => ∑ i ∈ s, a i • f i y) ∧ IsSec E (fun y => ∑ i ∈ s, a i • f i y) ∧
      cls μ (fun y => ∑ i ∈ s, a i • f i y) = ∑ i ∈ s, a i • cls μ (f i) := by
  classical
  have hlin := (hCl n μ E.V hU).2.1
  have hadd : ∀ (b : ℂ) (g g' : Mat n → E.V), Sob μ g → Sob μ g' → Sob μ (b • g + g') := fun b g g' hg hg' =>
    ((hOps n μ E.V hLg hU hR g hg).2.2.2.1 b g' hg').1
  have hmem : ∀ g : Mat n → E.V, Sob μ g → MemLp (fun y : G n => g y.val) 2 μ := fun g hg => hg.2 []
  induction s using Finset.induction_on with
  | empty =>
    have hz : (fun _ : Mat n => (0 : E.V)) = (-1 : ℂ) • f₀ + f₀ := by
      funext y; simp
    simp only [Finset.sum_empty]
    refine ⟨hz ▸ hadd _ _ _ h₀ h₀, fun g _ k => by simp, ?_⟩
    rw [hz, hlin _ _ _ (hmem _ h₀) (hmem _ h₀)]
    simp
  | insert i s hi ih =>
    obtain ⟨ih1, ih2, ih3⟩ := ih
    have hz : (fun y => ∑ j ∈ insert i s, a j • f j y) = a i • f i + fun y => ∑ j ∈ s, a j • f j y := by
      funext y; simp [Finset.sum_insert hi]
    rw [hz, Finset.sum_insert hi]
    refine ⟨hadd _ _ _ (hS i) ih1, fun g hg k => ?_, ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, map_add, map_smul]
      rw [hI i g hg k]
      exact congrArg (a i • (E.ρ k⁻¹) (f i g) + ·) (ih2 g hg k)
    · rw [hlin _ _ _ (hmem _ (hS i)) (hmem _ ih1), ih3]

end GlobalTheory.CompanionTheory.KerFc.RowLin

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem rowMatrix_holds : RowMatrix := by
  intro n _ _ μ _ E _ Ω T F c hstd h hrow
  obtain ⟨hLg, hU, hR, -, -, -, -, hCS, -⟩ := hstd
  obtain ⟨-, -, -, -, hCl, hOps, -⟩ := hCS
  let e := stdOrthonormalBasis ℂ E.V
  choose f hf using fun i => hrow (e i)
  obtain ⟨f₀, hf₀⟩ := hrow 0
  refine ⟨fun y => ∑ i, (innerSL ℂ (e i)).smulRight (f i y), fun v => ?_⟩
  have hA : (fun y => (∑ i, (innerSL ℂ (e i)).smulRight (f i y)) v) =
      fun y => ∑ i ∈ Finset.univ, (⟪e i, v⟫_ℂ) • f i y := by
    funext y
    simp [ContinuousLinearMap.sum_apply]
  obtain ⟨h1, h2, h3⟩ := RowLin.sum_sec μ E hLg hU hR hCl hOps f₀ hf₀.1 f (fun i => (hf i).1)
    (fun i => (hf i).2.1) (fun i => ⟪e i, v⟫_ℂ) Finset.univ
  show Row μ E F h v (fun y => (∑ i, (innerSL ℂ (e i)).smulRight (f i y)) v)
  rw [hA]
  refine ⟨h1, h2, fun φ f' hφ hφs hf' hf's hcl => ?_⟩
  rw [h3, sum_inner, ← (e.sum_inner_mul_inner v (f' 1))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, inner_conj_symm, (hf i).2.2 φ f' hφ hφs hf' hf's hcl]

end GlobalTheory.CompanionTheory.KerFc
