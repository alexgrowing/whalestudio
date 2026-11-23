import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.ConvMul
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.ImportsAlt
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OrthogonalKeepingHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.LimitbAlg

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

private theorem conv_smul' {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} {ι : Type} [Fintype ι]
    (μ : Measure (H E a b)) (Φ : Matrix ι ι (H E a b → ℂ)) (c : ℂ) (f : ι → H E a b → ℂ) :
    PositivityTheory.Rg.BcB.E.conv μ Φ (c • f) = c • PositivityTheory.Rg.BcB.E.conv μ Φ f := by
  funext i x
  simp only [PositivityTheory.Rg.BcB.E.conv, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← integral_const_mul]
  congr 1
  funext y
  ring

set_option maxHeartbeats 1000000 in
theorem realAlg : RealAlg := by
  intro E _ _ _ B Q _ Γ _ t v 𝔄 a₀ g s hok hK hT hs hs0
  let gg : Γ → BGen B := fun x => Sum.inr (t x)
  let X : B.Hb →L[ℂ] B.Hb := (t a₀).op
  have hmem : ∀ y : 𝔄.B, 𝔄.F y ∈ StarAlgebra.adjoin ℂ (Rd.gOps gg ∪ {X}) := by
    have hle : StarAlgebra.adjoin ℂ (Set.range 𝔄.ι) ≤ (StarAlgebra.adjoin ℂ (Rd.gOps gg ∪ {X})).comap 𝔄.F := by
      refine StarAlgebra.adjoin_le ?_
      rintro _ ⟨x, rfl⟩
      show 𝔄.F (𝔄.ι x) ∈ StarAlgebra.adjoin ℂ (Rd.gOps gg ∪ {X})
      rw [𝔄.hF]
      exact StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨x, rfl⟩)
    intro y
    have hy : y ∈ StarAlgebra.adjoin ℂ (Set.range 𝔄.ι) := by
      rw [𝔄.top]
      exact StarSubalgebra.mem_top
    exact hle hy
  have hΦ : ∀ y : 𝔄.B, ∃ Φ : Matrix B.I B.I (H E B.a B.b → ℂ), IsTestM Φ ∧ IsROp B.D Φ (𝔄.F y * (t a₀).op) := fun y =>
    Rd.phiEx BlockFiniteConvolution.blkOp₀ BlockFiniteConvolution.blkWord₀ blkSum adjWords gg X (t a₀) (t a₀) (fun x => hok x) (hok a₀) rfl (hok a₀)
      ⟨𝔄.F y, hmem y⟩
  choose Φ hΦt hΦr using hΦ
  have hop : ∀ y : 𝔄.B, ∃ T : B.Hb →L[ℂ] B.Hb, IsROp B.D (Φ y) T ∧
      (∀ w : Q, T (Q.subtypeL w) = Q.subtypeL (𝔄.R (y * 𝔄.ι a₀) w)) ∧
      ∀ u, (∀ w : Q, inner ℂ (Q.subtypeL w) u = 0) → ∀ w : Q, inner ℂ (Q.subtypeL w) (T u) = 0 := by
    intro y
    have hTy : 𝔄.F y * (t a₀).op = 𝔄.F (y * 𝔄.ι a₀) := by rw [map_mul, 𝔄.hF]
    refine ⟨_, hΦr y, fun w => ?_, fun u hu w => ?_⟩
    · rw [hTy]
      exact (𝔄.hR _ w).symm
    · rw [hTy]
      have h1 : (ContinuousLinearMap.adjoint (𝔄.F (y * 𝔄.ι a₀))) (w : B.Hb) =
          Q.subtypeL (𝔄.R (star (y * 𝔄.ι a₀)) w) := by
        rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star]
        exact (𝔄.hR _ w).symm
      have h2 := hu (𝔄.R (star (y * 𝔄.ι a₀)) w)
      rw [← h1, ContinuousLinearMap.adjoint_inner_left] at h2
      exact h2
  have hC : ({1} ∪ Set.range 𝔄.ι : Set 𝔄.B).Countable :=
    (Set.countable_singleton _).union (Set.countable_range _)
  obtain ⟨M, sk, f, hlim, hk⟩ := PositivityTheory.Rg.BcB.E2.orthogonal_keeping_holds E B.a B.b B.D B.I Q Q.subtypeL (fun w => rfl) 𝔄.B 𝔄.R s
    (𝔄.ι a₀) ({1} ∪ Set.range 𝔄.ι) Φ g hs hs0 hC (Or.inl rfl) hΦt hop
    (fun j w => (Submodule.mem_orthogonal _ _).1 (hT.1 j) w w.2) hT.2
  refine ⟨fun k x => sk k (𝔄.ι x), f, fun x => hlim _ (Or.inr ⟨x, rfl⟩), fun k => ?_⟩
  obtain ⟨h0, hc, hne, hL, hW, hconv, horth⟩ := hk k
  have hO := fun x => BlockFiniteConvolution.blkOp₀ E B (t x) (t a₀) (hok x) (hok a₀)
  have ha : PositivityTheory.Rg.BcB.E.conv B.D.μ (t a₀).Φ (f k) = sk k (𝔄.ι a₀) • f k := by
    have h1 := hconv 1 (Or.inl rfl)
    rw [one_mul] at h1
    rw [← h1]
    refine PositivityTheory.Rg.BcB.E2.conv_eq_of_isROp B.D (hO a₀).1 (hΦt 1) ?_ (hΦr 1) hc hL
    rw [map_one, one_mul]
    exact (hO a₀).2.1
  have hx : ∀ x, PositivityTheory.Rg.BcB.E.conv B.D.μ (t x).Φ (f k) = sk k (𝔄.ι x) • f k := by
    intro x
    have h1 := hconv (𝔄.ι x) (Or.inr ⟨x, rfl⟩)
    have hok' := (hO x).2.2.1
    have hm := BlockFiniteConvolution.blkOp₀ E B _ _ hok' hok'
    have h2 : PositivityTheory.Rg.BcB.E.conv B.D.μ ((t x).mul (t a₀)).Φ (f k) = PositivityTheory.Rg.BcB.E.conv B.D.μ (Φ (𝔄.ι x)) (f k) := by
      refine PositivityTheory.Rg.BcB.E2.conv_eq_of_isROp B.D hm.1 (hΦt _) ?_ (hΦr _) hc hL
      rw [𝔄.hF, ← (hO x).2.2.2.1]
      exact hm.2.1
    have h3 := (UpperTheory.Zero.ConvolutionTheory.EB.convMul E B (f k) hc).1 (t x) (t a₀) (hok x) (hok a₀)
    rw [ha, conv_smul', h2, h1, map_mul] at h3
    calc PositivityTheory.Rg.BcB.E.conv B.D.μ (t x).Φ (f k)
        = (sk k (𝔄.ι a₀))⁻¹ • (sk k (𝔄.ι a₀)) • PositivityTheory.Rg.BcB.E.conv B.D.μ (t x).Φ (f k) := (inv_smul_smul₀ h0 _).symm
      _ = (sk k (𝔄.ι a₀))⁻¹ • ((sk k (𝔄.ι x) * sk k (𝔄.ι a₀)) • f k) := by rw [← h3]
      _ = sk k (𝔄.ι x) • f k := by
        rw [smul_smul]
        congr 1
        field_simp
  exact ⟨h0, ⟨hc, hne, hL, ⟨M, hW⟩, hx⟩, horth⟩

end UpperTheory.Zero.ConvolutionTheory.EB
