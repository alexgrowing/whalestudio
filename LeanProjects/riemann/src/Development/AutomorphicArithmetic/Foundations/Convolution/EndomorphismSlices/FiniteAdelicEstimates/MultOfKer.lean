import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.ImportsAlt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.BlkGrowth

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

private theorem herm_chi {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
    (l : InfinitePlace E → DomWeight n) (v : InfinitePlace E) : IsHerm (chi l v) := by
  refine ⟨Equiv.refl _, fun i => ?_⟩
  simp [chi, infOf, Complex.conj_ofReal, map_sub, map_add, map_div₀, map_natCast, map_intCast, map_one, map_ofNat]

private theorem mult_of_ker {n : ℕ} [MeasurableSpace (G n)] {μ : Measure (G n)} {M : KMod n}
    {w : List (Bool × ℕ)} {g : ℝ → ℝ} {T : ℝ} {k : Mat n → (M.V →L[ℂ] M.V)}
    (hg : IsBump g T) (hk : IsKer μ M w g k) :
    IsMult μ M k (fun χ => zVal w χ * coshT g (cas χ)) T := by
  refine ⟨1, fun _ => 1, fun _ => w, fun _ => g, fun _ => k, fun _ => ⟨hg, hk⟩, ?_, ?_⟩
  · intro y _
    simp
  · intro χ
    simp

theorem ptOk : PtOk := by
  intro E _ _ _ a b l₁ l₂ D A
  have hsize : ∀ ψ : Matrix Unit Unit (Hf E a b → ℂ), IsFinM ψ →
      0 ≤ PositivityTheory.Rg.BcB.F.sizeOf ψ ∧ ∀ x y g, ψ x y g ≠ 0 →
        logSize (finGL E a g.1) ≤ PositivityTheory.Rg.BcB.F.sizeOf ψ ∧ logSize (finGL E b g.2) ≤ PositivityTheory.Rg.BcB.F.sizeOf ψ := by
    intro ψ hψ
    have h : ∃ r, 0 ≤ r ∧ ∀ x y g, ψ x y g ≠ 0 → logSize (finGL E a g.1) ≤ r ∧ logSize (finGL E b g.2) ≤ r :=
      (PositivityTheory.Rg.BcB.F.BlockFiniteConvolution.rtAlg' E A.blk 1 1).2.2 ψ hψ
    rw [PositivityTheory.Rg.BcB.F.sizeOf, dif_pos h]
    exact h.choose_spec
  refine ⟨herm_chi l₁, herm_chi l₂, ?_, ?_, ?_⟩
  · intro wa wb ψ hψ
    exact
      { T := A.T_nonneg
        r := (hsize ψ hψ).1
        ka := fun v => mult_of_ker A.isBump (A.kera (wa v) v)
        kb := fun v => mult_of_ker A.isBump (A.kerb (wb v) v)
        ψ := hψ
        size := (hsize ψ hψ).2 }
  · intro ψ
    have := A.one
    simpa [Ar.ptB, Ar.pt, PT.val, valA, Ar.valW, zVal] using this
  · intro wa wb ψ χa χb
    simp only [Ar.ptB, Ar.pt, PT.val, valA, Ar.valW, Finset.prod_mul_distrib]
    simp only [zVal, List.map_nil, List.prod_nil, one_mul, Finset.prod_const_one]
    ring

end UpperTheory.Zero.ConvolutionTheory.EB
