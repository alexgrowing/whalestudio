import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ArrowFockDense

open GlobalTheory.RealWeil GlobalTheory.Mem.Lift GlobalTheory.Size GlobalTheory.ChainFr GlobalTheory.FockCompare GlobalTheory.OrientedHeis GlobalTheory.FockDensity

theorem dense_level : ∀ (D : D7) (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ (t : T) i j, i ≤ D.R.m → j < D.R.m → ∀ (U : AddSubgroup (WO (G.V i j).V (G.V i (j + 1)).V)), IsOpen (U : Set (WO (G.V i j).V (G.V i (j + 1)).V)) → ∀ Φ ∈ GlobalTheory.Size.thetaLevel R.ψ (G.V i j).V (G.V i (j + 1)).V U, ∀ (μ : Measure (WO (G.V i j).V (G.V i (j + 1)).V)) (𝓕 : Set (WO (G.V i j).V (G.V i (j + 1)).V)), IsCovolOne (ratL (G.V i (j + 1)).V (G.V i j).V) μ 𝓕 → ∀ (d : ℕ) (ε : ℝ), 0 < ε → ∃ (n : ℕ) (fs : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (ps : Fin n → PolF D (G.V i (j + 1)).V.rank (G.V i j).V.rank), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l)) ∧ (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) ∈ GlobalTheory.Size.thetaLevel R.ψ (G.V i j).V (G.V i (j + 1)).V U ∧ GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d ((∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) - Φ) < ENNReal.ofReal ε := by
  intro D G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj U hU Φ hΦ μ 𝓕 hm d ε hε
  have hω : IsWeilDatumO R.ψ (G.V i j).V (G.V i (j + 1)).V _ _ (G.th t i j).ω :=
    (GlobalTheory.Grid.isWeil_false _ _ _ _ _ _).1 (hG.arrows.th t i j hi hj).weil
  have hψ : IsStdChar D R.ψ (-1) := hω.std
  have hθ : IsInfFam R.θ := hRB.inf
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨-, i2, i3, i4, i5, -⟩ := GlobalTheory.AdelicMatrixLattice.lattice D (G.V i (j + 1)).V (G.V i j).V
  haveI : BorelSpace (WO (G.V i j).V (G.V i (j + 1)).V) := ⟨rfl⟩
  haveI : IsFiniteMeasure (μ.restrict 𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, hm.2.2]; exact ENNReal.one_lt_top⟩
  have e0 : coeL R.ψ _ _ (toB hψ Φ hΦ.1) = Φ := coe_toB hψ Φ hΦ.1
  have hF : toB hψ Φ hΦ.1 ∈ (thetaLevel R.ψ (G.V i j).V (G.V i (j + 1)).V U).comap (coeL R.ψ _ _) := by
    rw [Submodule.mem_comap, e0]
    exact hΦ
  obtain ⟨g, h1, h2, h3⟩ := dense_vec h hψ (Fr.ofModel (G.V i j).M) (Fr.ofModel (G.V i (j + 1)).M) hU
    (toL2 _ _ (μ.restrict 𝓕))
    (fun v F => by
      rw [← enorm_sq_inj, ← lintegral_norm_sq_eq_toL2, ← lintegral_norm_sq_eq_toL2]
      exact lintegral_rhoB hψ μ 𝓕 hm.1 hm.2.1 _ F)
    (fun a : D.what₂.Tau × Fin (G.V i (j + 1)).V.rank × Fin (G.V i j).V.rank × Bool =>
      atPl a.1 (Matrix.single a.2.1 a.2.2.1 (if a.2.2.2 then Complex.I else 1))) d hF
    (ENNReal.ofReal_pos.2 hε)
  have e1 : ∀ F : BB R.ψ (G.V i j).V (G.V i (j + 1)).V,
      l2O μ 𝓕 (coeL R.ψ _ _ F) = ‖toL2 _ _ (μ.restrict 𝓕) F‖ₑ := fun F =>
    (eLpNorm_congr_ae (BoundedContinuousFunction.coeFn_toLp 2 (μ.restrict 𝓕) ℂ F.1)).symm.trans (Lp.enorm_def _).symm
  have e2 : Φ - coeL R.ψ _ _ g = coeL R.ψ _ _ (toB hψ Φ hΦ.1 - g) := by rw [LinearMap.map_sub, e0]
  have hS : sobO R.ψ R.θ μ 𝓕 d (Φ - coeL R.ψ _ _ g) < ENNReal.ofReal ε := by
    refine lt_of_eq_of_lt ?_ h3
    simp only [sobO, wordSum, e2, coe_word h hψ hU _ (sub_mem hF h2), e1]

  obtain ⟨n, c, gs, hgs⟩ := Submodule.mem_span_set'.1 (Submodule.mem_comap.1 h1)
  choose f₀ P hv hl hP using fun l => (gs l).2
  refine ⟨n, f₀, fun l => c l • P l, fun l => hv l, ?_, ?_⟩
  · have e3 : (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f₀ l) (c l • P l)) = coeL R.ψ _ _ g := by
      rw [← hgs]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hP l, map_smul]
      rfl
    rw [e3]
    exact h2
  · have e3 : (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (f₀ l) (c l • P l)) - Φ =
        (-1 : ℂ) • (Φ - coeL R.ψ _ _ g) := by
      rw [← hgs, neg_one_smul, neg_sub]
      congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hP l, map_smul]
      rfl
    rw [e3, sobO_smul, enorm_neg, enorm_one, one_mul]
    exact hS

end GlobalTheory.ArrowFockDense
