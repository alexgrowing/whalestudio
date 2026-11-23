import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GenericSectionsPolynomialDictionary
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsLtMulOfLt
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsIndepForms
import Formalism.LocalToGlobal.ProjectiveLattices.CuspMulOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.KerExistsStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.LowerBound

theorem le_finrank_of_pieces {K Z : Type} [Fintype K] [DecidableEq K] {Y : K → Type} (dom : ∀ k, Set (Y k))
    (e : Z ≃ Σ k, dom k) (d : K → ℕ) (C δ : ℕ) (en : Fin δ ≃ Σ k, Fin (d k))
    (f : ∀ k, Fin (d k * C) → Y k → ℂ)
    (hf : ∀ k (u : Fin (d k * C) → ℂ), (∀ x ∈ dom k, ∑ q, u q * f k q x = 0) → u = 0)
    (S : Submodule ℂ (Z → ℂ)) [FiniteDimensional ℂ S]
    (hS : ∀ k q, (fun z => (Pi.single k (f k q) : ∀ k, Y k → ℂ) (e z).1 (e z).2.1) ∈ S) :
    δ * C ≤ Module.finrank ℂ S := by
  let v : (Σ k, Fin (d k * C)) → S := fun p => ⟨_, hS p.1 p.2⟩
  have hv : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg p
    have key := hf p.1 (fun q => g ⟨p.1, q⟩) fun x hx => by
      have h1 := congrFun (congrArg Subtype.val hg) (e.symm ⟨p.1, x, hx⟩)
      rw [Submodule.coe_sum, Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single p.1] at h1
      · refine Eq.trans (Finset.sum_congr rfl fun q _ => ?_) h1
        show _ = g _ * (Pi.single p.1 (f p.1 q) : ∀ k, Y k → ℂ) (e (e.symm ⟨p.1, x, hx⟩)).1
          (e (e.symm ⟨p.1, x, hx⟩)).2.1
        rw [e.apply_symm_apply]
        simp
      · intro k _ hk
        refine Finset.sum_eq_zero fun q _ => ?_
        show g _ * (Pi.single k (f k q) : ∀ k, Y k → ℂ) (e (e.symm ⟨p.1, x, hx⟩)).1
          (e (e.symm ⟨p.1, x, hx⟩)).2.1 = 0
        rw [e.apply_symm_apply]
        simp [Pi.single_eq_of_ne hk.symm]
      · simp
    exact congrFun key p.2
  have h1 := hv.fintype_card_le_finrank
  have h2 := Fintype.card_congr en
  simp only [Fintype.card_sigma, Fintype.card_fin] at h1 h2
  rwa [← Finset.sum_mul, ← h2] at h1

variable {D : D7}

theorem laR_wadd (T : Top D) (j : ℕ) (u v : WeightFamilies.Wt D j) (k : (T.U j T.σ₀).Comp) :
    laR T j (wadd u v) k = laR T j u k + laR T j v k := by
  unfold laR
  rw [wtA_wadd]
  exact laU_add (T.U j T.σ₀) (wtA u) (wtA v) u.n v.n u.n_even v.n_even k

theorem laR_wsmul (T : Top D) (j : ℕ) (m : ℕ) (u : WeightFamilies.Wt D j) (k : (T.U j T.σ₀).Comp) :
    laR T j (wsmul m u) k = m • laR T j u k := by
  induction m with
  | zero =>
    funext τ a
    simp [laR, laU, wtA, wsmul, Formalism.L2.Pj.ext0]
  | succ m ih =>
    have e : wsmul (m + 1) u = wadd (wsmul m u) u := by
      simp only [wsmul, wadd, add_mul, one_mul]
    rw [e, laR_wadd, ih, succ_nsmul]

theorem lower_bound : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → ∀ (CR c : ℝ), c1 = WeightFamilies.c1 D CR Tn c j → MggOnto h j CR Tn c (addL wF wL Tn) → δ * (Tn + WeightFamilies.dimY D j).choose (WeightFamilies.dimY D j) ≤ Module.finrank ℂ (R.sp (addL wF wL Tn) (WeightFamilies.MggK n.base CR Tn c j (addL wF wL Tn))) := by
  classical
  intro D T h j hj n R e hR N wL wF w Tn c1 A t Fl δ xs en _ CR c hc hM
  have hex : ∀ k : (T.U j T.σ₀).Comp,
      ∃ f : Fin ((Fl.Fl k).δ * (Tn + WeightFamilies.dimY D j).choose (WeightFamilies.dimY D j)) → Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ,
        (∀ q, f q ∈ ((T.U j T.σ₀).X k).SSgt (laR T j (addL wF wL Tn) k) c1) ∧
        ∀ u : Fin ((Fl.Fl k).δ * (Tn + WeightFamilies.dimY D j).choose (WeightFamilies.dimY D j)) → ℂ,
          (∀ x ∈ ((T.U j T.σ₀).X k).dom, ∑ q, u q * f q x = 0) → u = 0 := by
    intro k
    obtain ⟨⟨bb, m, h1, h2, h3⟩, -, h4, h5, h6⟩ := A.mar k
    have hint := interpCStatement_holds _ _ (A.Xa k) (Fl.Fl k) (GlobalTheory.ClosedDiscontinuity.propDisc_closed _ _)
      ⟨bb, m, h1, h2, h3 _ (by simp)⟩ h4 h5 (by simpa using h6 0) (GlobalTheory.ClosedModes.modeHalf_closed _ _)
    have hmany := GlobalTheory.ManyForms.exists_indep_forms _ _ (A.Xa k) (Fl.Fl k) (A.Xa k).Fp Tn (A.Xa k).c1
      (A.Xa k).frame_theta_const_pos.le hint
    rw [A.hF k, A.hL k, A.hc k] at hmany
    rw [← A.dim k, addL, laR_wadd, laR_wsmul]
    exact hmany
  choose f hfm hfi using hex
  haveI := (GlobalTheory.Shares.PolyDict.sp_finrank R (addL wF wL Tn) (WeightFamilies.MggK n.base CR Tn c j (addL wF wL Tn))).1
  refine le_finrank_of_pieces (fun k => ((T.U j T.σ₀).X k).dom) e (fun k => (Fl.Fl k).δ) _ δ en f hfi _ fun k q => ?_
  obtain ⟨m, a, F, hF, hsum⟩ := hM (Pi.single k (f k q)) fun k' => by
    rw [← hc]
    by_cases hk : k' = k
    · subst hk
      rw [Pi.single_eq_same]
      exact hfm _ q
    · rw [Pi.single_eq_of_ne hk]
      exact (siegelSpaceAlgebra_holds _ _ _ (laR T j (addL wF wL Tn) k') c1).2.2.1.1
  have hE : (fun z => (Pi.single k (f k q) : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ) (e z).1 (e z).2.1) =
      ∑ i, a i • R.ev ((recPlusN h j hj n).inc _ (F i)) := by
    funext z
    rw [hsum _ _ (e z).2.2, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, hR.2]
  rw [hE]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨F i, hF i, rfl⟩)

end GlobalTheory.LowerBound
