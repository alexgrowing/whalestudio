import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.CuspReadPTrue
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.GrowthOut
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.GlobalCharacterOfFiniteInputs
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.ImportsAlt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NontrivialInfinitePlaceOfUnramifiedStatement

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

theorem rSpec_of (h1 : PeakRun) (h2 : GenSt) (h3 : PtOk) (h4 : HkMul) (h5 : RepAlg) (h6 : PositionTest) : RSpec := by
  intro P hR E _ _ _ a b l₁ l₂ D A S Z L hS hZ X hX hXc Q _ hK hg
  obtain ⟨W, hW, hR⟩ := hR E a b l₁ l₂
  obtain ⟨J, hJ, D₁, D₂, B₁, B₂, a1, a2, a3⟩ := hR D A S Z L hS hZ X hX hXc
  obtain ⟨g, hg1, hg2⟩ := hg W hW
  refine ⟨J, hJ, D₁, D₂, B₁, B₂, a1, a2, fun T e₁ e₂ ρ hT hd hρ hv => ?_⟩
  obtain ⟨hG, hC⟩ := h2 E a b l₁ l₂ D A S Z L hS hZ T e₁ e₂
  obtain ⟨p1, p2, -, p4, -⟩ := h3 E a b l₁ l₂ D A
  obtain ⟨-, m2, m3, -, -, m6, -⟩ := h4 E a b l₁ l₂ D A S Z L hS hZ
  obtain ⟨-, r2, -, r4⟩ := h5 E A.blk (chi l₁) (chi l₂)
  obtain ⟨V, R, hR0, hV, hn⟩ := h1 E A.blk Q (chi l₁) (chi l₂) (Gam a b S Z) (A.gen S L T e₁ e₂) Gam.arch (.inl ())
    (.inr (.inr (.inr ()))) g ρ hG hK hg1 p1 p2 trivial (p4 _)
    (fun γ hγ => by rcases γ with _ | _ | _ <;> first | rfl | exact hγ.elim) m2 m3 hρ
    (fun s hs hr => by
      obtain ⟨j, hj⟩ := a3 T e₁ e₂ g s hT hd hg2 hs hr
      rw [hj]
      exact hv j)
  have hx := hG.ok (.inr (.inr (.inr ())))
  have h := r4 _ _ _ _ _ _ _ _ (r2 _ hx) hV
  have e1 : mulF A.blk.ν (A.gen S L T e₁ e₂ (.inr (.inr (.inr ())))).ψ (A.gen S L T e₁ e₂ (.inl ())).ψ = A.hk S L T e₁ e₂ :=
    (m6 T L.ln e₁ e₂ (h6 E a b S Z L hZ).1).2.1
  have e2 : (A.gen S L T e₁ e₂ (.inr (.inr (.inr ())))).val (chi l₁) (chi l₂) = 1 := p4 _
  rw [e1, e2, one_mul] at h
  exact ⟨_, _, add_nonneg (add_nonneg (le_max_of_le_left hx.T) hR0) A.c_nonneg, h, hn⟩

theorem haarEx (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) : ∃ μ : Measure (GA E n), μ.IsHaarMeasure := by
  haveI : BorelSpace (GA E n) := ⟨rfl⟩
  exact ⟨Measure.haar, inferInstance⟩

theorem rEndo_of (h1 : ArEx) (h2 : LvEx) (h3 : PowRep) (h4 : CmbTest) (h5 : CmbEll) (h6 : RepAlg) (h7 : PowNorm) : REndo := by
  intro P hSp E _ _ _ hE a b _ S hS l₁ l₂ Z hZ φ hφ hreg
  haveI : Nontrivial (InfinitePlace E) := GlobalTheory.T.nontrivial_infinite_place_of_unramified E hE
  haveI : BorelSpace (GA E a) := ⟨rfl⟩
  haveI : BorelSpace (GA E b) := ⟨rfl⟩
  obtain ⟨μ₁, hμ₁⟩ := haarEx E a
  obtain ⟨μ₂, hμ₂⟩ := haarEx E b
  obtain ⟨D, hD⟩ := PositivityTheory.Rg.BcB.E1.growthJ_holds E a b μ₁ μ₂
  obtain ⟨A⟩ := h1 E a b l₁ l₂ D
  obtain ⟨L, hL⟩ := h2 E a b Z φ hφ
  obtain ⟨u₁, hu₁⟩ := PositivityTheory.Rg.BcB.G8.translation_existence_holds E a
  obtain ⟨u₂, hu₂⟩ := PositivityTheory.Rg.BcB.G8.translation_existence_holds E b
  obtain ⟨κ, hκ, hell⟩ := h5 E hE a b l₁ l₂ D A μ₁ μ₂ hμ₁ hμ₂
  obtain ⟨c, hc, htest⟩ := h4 E a b l₁ l₂ D A S Z L hS hZ u₁ u₂ hu₁ hu₂
  haveI : CompleteSpace (⊤ : Submodule ℂ A.blk.Hb) := (isClosed_univ.completeSpace_coe : CompleteSpace (Set.univ : Set A.blk.Hb))
  obtain ⟨J, hJ, D₁, D₂, B₁, B₂, a1, a2, a3⟩ := hSp E a b l₁ l₂ D A S Z L hS hZ ∅ Set.subsingleton_empty
    (fun _ h => h.elim) ⊤ (fun _ _ _ _ _ _ => Submodule.mem_top)
    (fun W _ => ⟨fun _ => 0, ⟨fun _ => Submodule.zero_mem _, fun j i M => by
      have : ((0 : A.blk.Hb) i : H E a b → ℂ) =ᵐ[D.ν] 0 := Lp.coeFn_zero _ _ _
      rw [lintegral_congr_ae (g := fun _ => 0) (this.mono fun x hx => by
        show _ * ‖((0 : A.blk.Hb) i : H E a b → ℂ) x‖ₑ ^ 2 = 0
        rw [hx]
        simp)]
      simp⟩, fun _ _ _ _ _ _ _ _ _ h => h.elim⟩)
  refine ⟨J, hJ, D₁, D₂, B₁, B₂, fun j => (a1 j).2, a2, fun T hT hd e₁ e₂ ρ hT' hρ hv => ?_⟩
  obtain ⟨U, R, hR, hU, hn⟩ := a3 T e₁ e₂ ρ ⟨hT, hT'⟩ hd hρ hv
  obtain ⟨o₁, o₂, r₀, r₁, hr₀, hr₁, hk⟩ := h3 E a b l₁ l₂ D A S Z L hS hZ u₁ u₂ φ T e₁ e₂ U R hL hR hU
  have b₁ := BlockFiniteConvolution.blkOp₀ E A.blk _ _ o₁ o₁
  have b₂ := BlockFiniteConvolution.blkOp₀ E A.blk _ _ o₂ o₂
  obtain ⟨C, N, hb⟩ := hD A.blk.I _ _ _ _ A.tw (c * (1 + r₀)) (c * r₁) b₁.1 b₂.1 b₁.2.1 b₂.2.1 (by positivity) (by positivity)
  refine ⟨‖κ‖⁻¹ * |C|, N, fun k => ?_⟩
  obtain ⟨Cm, c1, c2, c3⟩ := hk k
  have hrk : 0 ≤ r₀ + k * r₁ := by positivity
  obtain ⟨q1, q2⟩ := (h6 E A.blk (chi l₁) (chi l₂)).1 Cm _ _ c1
  have ht := (htest φ T _ _ Cm _ hL hreg hrk c1).2
  have he := hell S Z L hS hZ u₁ u₂ hu₁ hu₂ φ T e₁ e₂ k Cm _ hL hreg ⟨hT, hT'⟩ hrk c1
  rw [c3] at q2
  have hb' := hb k (U ^ k) Cm.Φ q1 q2 (by rw [show c * (1 + r₀) + k * (c * r₁) = c * (1 + (r₀ + k * r₁)) by ring]; exact ht)
  have hp : ‖U ^ k‖ ≤ ρ ^ k := by
    have h := (h7 A.blk.Hb ⊤ U ρ (fun _ _ => Submodule.mem_top) hn.le k).2
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
    exact (((U ^ k) ∘L (⊤ : Submodule ℂ A.blk.Hb).subtypeL).le_opNorm ⟨x, Submodule.mem_top⟩).trans
      (mul_le_mul_of_nonneg_right h (norm_nonneg _))
  rw [he, c2, mul_one, norm_mul] at hb'
  have hκ' : 0 < ‖κ‖ := norm_pos_iff.2 hκ
  have h9 : C * (1 + k) ^ N * ‖U ^ k‖ ≤ |C| * (1 + k) ^ N * ρ ^ k :=
    mul_le_mul (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)) hp (norm_nonneg _) (by positivity)
  rw [mul_assoc, mul_assoc, ← mul_assoc |C|, le_inv_mul_iff₀ hκ']
  exact hb'.trans h9

end UpperTheory.Zero.ConvolutionTheory.EB
