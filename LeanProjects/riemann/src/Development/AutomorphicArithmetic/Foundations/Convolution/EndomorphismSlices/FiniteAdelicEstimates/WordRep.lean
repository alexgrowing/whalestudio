import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.RepAlg
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.ImportsAlt

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

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem rep_sum {B : Block E} {χa : InfinitePlace E → Inf B.a} {χb : InfinitePlace E → Inf B.b}
    {ψ : Matrix B.κ B.κ (Hf E B.a B.b → ℂ)} {J : Type} [Fintype J] (c v : J → ℂ)
    (U : J → (B.Hb →L[ℂ] B.Hb)) (R : J → ℝ) (hR : ∀ j, 0 ≤ R j)
    (h : ∀ j, Rep B χa χb ψ (v j) (R j) (U j)) :
    Rep B χa χb ψ (∑ j, c j * v j) (∑ j, R j) (∑ j, c j • U j) := by
  choose C hC hv hU using h
  refine ⟨⟨Σ j, (C j).J, Finset.univ.sigma fun j => (C j).s, fun p => c p.1 * (C p.1).c p.2,
    fun p => (C p.1).t p.2⟩, ?_, ?_, ?_⟩
  · rintro ⟨j, i⟩ hi
    have hi' : i ∈ (C j).s := (Finset.mem_sigma.1 hi).2
    obtain ⟨h1, h2, h3, h4⟩ := hC j i hi'
    have hle : R j ≤ ∑ k, R k := Finset.single_le_sum (fun k _ => hR k) (Finset.mem_univ j)
    exact ⟨h1, h2, h3.trans hle, h4.trans hle⟩
  · simp only [Cmb.val]
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hv j]
    simp only [Cmb.val, Finset.mul_sum, mul_assoc]
  · simp only [Cmb.op]
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hU j]
    simp only [Cmb.op, Finset.smul_sum, mul_smul]

private theorem rep_word {B : Block E} {χa : InfinitePlace E → Inf B.a} {χb : InfinitePlace E → Inf B.b}
    (hA : ∀ v, IsHerm (χa v)) (hB : ∀ v, IsHerm (χb v)) {Γ : Type} (t : Γ → PT B) (t₀ : PT B) (h₀ : t₀.Ok)
    (ht : ∀ x, (t x).Ok ∧ (t x).ψ = t₀.ψ) (hm : mulF B.ν t₀.ψ t₀.ψ = t₀.ψ) (ha : adjF t₀.ψ = t₀.ψ)
    (w : List (Γ × Bool)) :
    ∃ R, 0 ≤ R ∧ Rep B χa χb t₀.ψ (wdVal (fun x => (t x).val χa χb) w * t₀.val χa χb) R
      (wdVal (fun x => (t x).op) w * t₀.op) := by
  obtain ⟨-, hp, -, hmul⟩ := repAlg E B χa χb
  induction w with
  | nil => exact ⟨max t₀.T t₀.r, le_max_of_le_left h₀.T, by simpa [wdVal] using hp t₀ h₀⟩
  | cons p w ih =>
    obtain ⟨R, hR, hrep⟩ := ih
    obtain ⟨x, b⟩ := p
    obtain ⟨hx, hψ⟩ := ht x
    obtain ⟨-, -, -, -, hadjOk, hadjOp, -, hadjVal⟩ :=
      PositivityTheory.Rg.BcB.F.BlockFiniteConvolution.blkOp₀ E B (t x) (t x) hx hx
    have key : ∃ R', 0 ≤ R' ∧ Rep B χa χb t₀.ψ (if b then star ((t x).val χa χb) else (t x).val χa χb) R'
        (if b then star (t x).op else (t x).op) := by
      cases b
      · refine ⟨max (t x).T (t x).r, le_max_of_le_left hx.T, ?_⟩
        have h1 := hp (t x) hx
        rw [hψ] at h1
        simpa using h1
      · refine ⟨max (t x).adj.T (t x).adj.r, le_max_of_le_left hadjOk.T, ?_⟩
        have h1 := hp _ hadjOk
        have e : (t x).adj.ψ = t₀.ψ := by
          change adjF (t x).ψ = _
          rw [hψ, ha]
        rw [hadjOp, hadjVal χa χb hA hB, e] at h1
        simpa [ContinuousLinearMap.star_eq_adjoint] using h1
    obtain ⟨R', hR', hl⟩ := key
    refine ⟨R' + R + B.c, add_nonneg (add_nonneg hR' hR) B.c_nonneg, ?_⟩
    have h2 := hmul _ _ _ _ _ _ _ _ hl hrep
    rw [hm] at h2
    have e1 : ∀ {A : Type} [Monoid A] [Star A] (g : Γ → A), wdVal g ((x, b) :: w) =
        (if b then star (g x) else g x) * wdVal g w := fun g => by simp [wdVal]
    rw [e1, e1, mul_assoc, mul_assoc]
    exact h2

theorem wordRep : WordRep := by
  intro E _ _ _ B χa χb Γ t t₀ J _ c w hA hB h₀ ht hm ha
  choose R hR hrep using fun j => rep_word hA hB t t₀ h₀ ht hm ha (w j)
  refine ⟨∑ j, R j, Finset.sum_nonneg fun j _ => hR j, ?_⟩
  have h1 := rep_sum c _ _ R hR hrep
  rw [Finset.sum_mul, Finset.sum_mul]
  simpa only [mul_assoc, smul_mul_assoc] using h1

end UpperTheory.Zero.ConvolutionTheory.EB
