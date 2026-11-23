import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RapidDecayLift
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnThetaKOMulCusp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunOfMemCusp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GrowthSobZeroNeTop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKFiniteIteratedCompactAverageApproxStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormKFiniteApproxStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
open scoped ENNReal

namespace GlobalTheory.SobolevCuspApprox

theorem sobolev_approx : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.P (i + 1)) φ → ∀ U : Subgroup (GA D (G.P (i + 1)).V), IsOpen (U : Set (GA D (G.P (i + 1)).V)) → (∀ k ∈ U, k ∈ GfC (G.P (i + 1)).V → ∀ g, φ (g * k) = φ g) → ∀ (d : ℕ) (δ : ENNReal), 0 < δ → ∃ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) ∧ (∀ k ∈ K, ∀ u ∈ U, u ∈ GfC (G.P (i + 1)).V → ∀ g, F k (v k) (g * u) = F k (v k) g) ∧ (∀ e, GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V e 0 (φ - ∑ k ∈ K, F k (v k)) ≠ ⊤) ∧ GlobalTheory.Size.growthSob R.θ (G.P (i + 1)).V d 0 (φ - ∑ k ∈ K, F k (v k)) < δ := by
  intro hP D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hRB _ i _ φ hφ U hU hlev d δ hδ
  have hθ : IsInfFam R.θ := hRB.inf
  obtain ⟨hAut, hc, -⟩ := id hφ
  have hφg : GlobalTheory.CuspApproxAll.Good R.θ (G.P (i + 1)).V φ :=
    ⟨GlobalTheory.Size.rapidDecSm_of_cuspForm hP.cuspRapidDecay hθ hAut hc, hc⟩
  obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hδ
  have hr : 0 < r := by
    by_contra h
    rw [ENNReal.ofReal_of_nonpos (not_lt.1 h)] at hr1
    exact lt_irrefl _ hr1
  obtain ⟨e, he, hgrow⟩ := GlobalTheory.T.exists_KFinite_iteratedCompactAverage_approx D R.θ hθ (G.P (i + 1)) φ hφg.1 (Finset.univ : Finset D.what₂.Tau).toList
    (Finset.nodup_toList _) d r hr
  obtain ⟨n, F, v, hF, hFlev, hsum⟩ := GlobalTheory.T.cusp_form_K_finite_approx D R.θ hθ hP (G.P (i + 1)) φ hφ U hU hlev e he
    (Finset.univ : Finset D.what₂.Tau).toList (fun τ => Finset.mem_toList.2 (Finset.mem_univ τ))
  rw [hsum] at hgrow
  let F' : ℕ → (G.P (i + 1)).Maps := fun k => if h : k < n then F ⟨k, h⟩ else 0
  let v' : ℕ → Formalism.IndefR.Links.SmT (G.P (i + 1)).M := fun k => if h : k < n then v ⟨k, h⟩ else 0
  have hval : ∀ j : Fin n, F' j (v' j) = F j (v j) := fun j => by simp [F', v', j.2]
  have hsumeq : ∑ k ∈ Finset.range n, F' k (v' k) = ∑ j, F j (v j) := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => F' k (v' k))]
    exact Finset.sum_congr rfl fun j _ => hval j
  refine ⟨Finset.range n, F', v', fun k hk => ?_, fun k hk u hu hu' g => ?_, ?_⟩
  · have hk' : k < n := Finset.mem_range.1 hk
    simpa [F', hk'] using hF ⟨k, hk'⟩
  · have hk' : k < n := Finset.mem_range.1 hk
    simpa [F', v', hk'] using hFlev ⟨k, hk'⟩ u hu hu' g
  · rw [hsumeq]
    have hsg : GlobalTheory.CuspApproxAll.Good R.θ (G.P (i + 1)).V (∑ j, F j (v j)) :=
      Finset.sum_induction _ (GlobalTheory.CuspApproxAll.Good R.θ (G.P (i + 1)).V) (fun _ _ => GlobalTheory.CuspApproxAll.good_add)
        (GlobalTheory.CuspApproxAll.good_zero R.θ (G.P (i + 1)).V) fun j _ =>
          GlobalTheory.CuspApproxAll.good_value hP.cuspRapidDecay hθ (G.P (i + 1)) (hF j) (v j)
    have hg : GlobalTheory.CuspApproxAll.Good R.θ (G.P (i + 1)).V (φ - ∑ j, F j (v j)) := by
      have := GlobalTheory.CuspApproxAll.good_add hφg (GlobalTheory.CuspApproxAll.good_smul (-1) hsg)
      rwa [neg_one_smul, ← sub_eq_add_neg] at this
    exact ⟨fun e' => GlobalTheory.CuspApproxAll.growthSob_zero_ne_top hg.1 e', lt_of_le_of_lt hgrow hr2⟩

end GlobalTheory.SobolevCuspApprox

end
