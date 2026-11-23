import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.ImportsAlt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.Imports
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.ConvTest

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

theorem repAlg : RepAlg := by
  intro E _ _ _ B χa χb
  have hop := PositivityTheory.Rg.BcB.F.BlockFiniteConvolution.blkOp₀ E B
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro C ψ R h
    exact PositivityTheory.Rg.BcB.F.blkSum E B.a B.b B.D B.I C.J C.s C.c (fun j => (C.t j).Φ) (fun j => (C.t j).op)
      fun j hj => ⟨(hop _ _ (h j hj).1 (h j hj).1).1, (hop _ _ (h j hj).1 (h j hj).1).2.1⟩
  · intro t ht
    refine ⟨⟨Unit, {()}, fun _ => 1, fun _ => t⟩, ?_, ?_, ?_⟩
    · intro j _
      exact ⟨ht, rfl, le_max_left _ _, le_max_right _ _⟩
    · simp [Cmb.val]
    · simp [Cmb.op]
  · rintro ψ v R R' U h ⟨C, hC, hv, hU⟩
    exact ⟨C, fun j hj => ⟨(hC j hj).1, (hC j hj).2.1, (hC j hj).2.2.1.trans h, (hC j hj).2.2.2.trans h⟩, hv, hU⟩
  · rintro ψ ψ' v v' R R' U U' ⟨C, hC, rfl, rfl⟩ ⟨C', hC', rfl, rfl⟩
    refine ⟨⟨C.J × C'.J, C.s ×ˢ C'.s, fun p => C.c p.1 * C'.c p.2, fun p => (C.t p.1).mul (C'.t p.2)⟩, ?_, ?_, ?_⟩
    · rintro ⟨j, j'⟩ hj
      obtain ⟨h1, h2⟩ := Finset.mem_product.1 hj
      obtain ⟨o, e, hT, hr⟩ := hC j h1
      obtain ⟨o', e', hT', hr'⟩ := hC' j' h2
      refine ⟨(hop _ _ o o').2.2.1, ?_, ?_, ?_⟩
      · change mulF B.ν (C.t j).ψ (C'.t j').ψ = _
        rw [e, e']
      · change (C.t j).T + (C'.t j').T ≤ _
        linarith [B.c_nonneg]
      · change (C.t j).r + (C'.t j').r + B.c ≤ _
        linarith
    · simp only [Cmb.val]
      rw [Finset.sum_mul_sum, Finset.sum_product]
      refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun j' hj' => ?_
      rw [(hop _ _ (hC j hj).1 (hC' j' hj').1).2.2.2.2.2.2.1 χa χb]
      ring
    · simp only [Cmb.op]
      rw [Finset.sum_mul_sum, Finset.sum_product]
      refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun j' hj' => ?_
      rw [(hop _ _ (hC j hj).1 (hC' j' hj').1).2.2.2.1, smul_mul_smul_comm]

end UpperTheory.Zero.ConvolutionTheory.EB
