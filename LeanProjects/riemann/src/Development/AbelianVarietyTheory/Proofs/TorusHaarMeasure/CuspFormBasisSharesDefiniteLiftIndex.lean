import Mathlib
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ThetaArchimedeanDataDefiniteModelsNonemptyStatement
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CuspReadingsSpanModelFormsShiftedWeightsStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PointsInterpolationGenericSections
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspFormVanishingAtPointsMulPowMemSpan
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LeadingProductsIndependentModuloDeepProducts
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ArchimedeanFlatDecompositionIndexing
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FinrankLowerBoundCuspFormVanishingLowCoeff
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspFormVanishingLowCoeffMemLeadingAddDeepSpan
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAlgIndependentCoeffsFlatDatum
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsBaseEmbeddingReadingForms
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InBasisIffPointValuesLinearIndependentSpan
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsValueBasisInSpanningForms
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShareRdOfInBasis
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShareRhoROfAnFacts
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NonemptyHeightOneSpectrumRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.InContainMROfAnFacts
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ReadingsCuspAndIndependent
import Formalism.LocalToGlobal.ProjectiveLattices.OneCusp
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR

noncomputable section

namespace GlobalTheory.SharesDefinite

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

section Lower

open GlobalTheory.LowerBound

theorem lower_bound_definite : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → ∀ (CR c : ℝ), (∀ k : (T.U j T.σ₀).Comp, ((T.U j T.σ₀).X k).p0 = 0) → MggOnto h j CR Tn c (addL wF wL Tn) → δ * (Tn + WeightFamilies.dimY D j).choose (WeightFamilies.dimY D j) ≤ Module.finrank ℂ (R.sp (addL wF wL Tn) (WeightFamilies.MggK n.base CR Tn c j (addL wF wL Tn))) := by
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
    by_cases hk : k' = k
    · subst hk
      rw [Pi.single_eq_same]
      exact ⟨(hfm _ q).1, fun ξ hξ => absurd hξ (not_isIso_of_p0_zero _ (hc _) ξ)⟩
    · rw [Pi.single_eq_of_ne hk]
      exact (siegelSpaceAlgebra_holds _ _ _ (laR T j (addL wF wL Tn) k') _).2.2.1.1
  have hE : (fun z => (Pi.single k (f k q) : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ) (e z).1 (e z).2.1) =
      ∑ i, a i • R.ev ((recPlusN h j hj n).inc _ (F i)) := by
    funext z
    rw [hsum _ _ (e z).2.2, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, hR.2]
  rw [hE]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨F i, hF i, rfl⟩)

end Lower

section Contain

open GlobalTheory.Containment

theorem containment_any : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → ∀ (CR c : ℝ), (∀ F ∈ WeightFamilies.MggK (recB h.toLawsCore) CR Tn c j (addL wF wL Tn), ∀ k : (T.U j T.σ₀).Comp, rdR h j F k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j (addL wF wL Tn) k) c1) → ∀ (m : ℕ) (θ : Fin m → R.Y → ℂ), (∀ i, θ i ∈ R.sp wF Set.univ) → Submodule.span ℂ (Set.range (vals xs θ)) = ⊤ → R.sp (addL wF wL Tn) (WeightFamilies.MggK n.base CR Tn c j (addL wF wL Tn)) ≤ Submodule.span ℂ (Set.range (R.lead w t Tn (a0 D j Tn) θ)) ⊔ R.deep w t ((recPlusN h j hj n).wF0 wL wF) (a0 D j Tn) := by
  classical
  intro D T h j hj n R e hR N wL wF w Tn c1 A t Fl δ xs en hxs hOnto CR c hMg m θ hθ hspan
  have hsp := span_readings_components D T h j hj n R e hR
  have hwt : ∀ (k : (T.U j T.σ₀).Comp) (a : ℕ), laR T j (addL wF wL a) k = (A.Xa k).Fp + a • (A.Xa k).L := fun k a => by
    rw [A.hF, A.hL]
    exact (WtDic.weights_dictionary D T h j hj k).2.2.1 wF wL a
  choose θf hθf hθe using fun i => (hsp wF).1 (θ i) (hθ i)
  have hs : ∀ (i : Fin (WeightFamilies.dimY D j + 1)) (y : R.Y),
      R.s w t i y = ∑ k, t (i, k) * rdR h j (w k) (e y).1 (e y).2.1 := fun i y => by
    unfold Rdg.s
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [Pi.smul_apply, smul_eq_mul, hR.2]
  have hs0 : ∀ y, R.s w t 0 y = (Fl.Fl (e y).1).w0 (e y).2.1 := fun y => by rw [hs, Fl.h0]
  have hs1 : ∀ (q : Fin (WeightFamilies.dimY D j)) y,
      R.s w t q.succ y = (Fl.Fl (e y).1).s (Fin.cast (A.dim _).symm q) (e y).2.1 := fun q y => by
    rw [hs, Fl.hs]; rfl
  have hfin : ∀ k : (T.U j T.σ₀).Comp, ∃ (K : ℕ) (g : Fin K → Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ),
      ∀ f ∈ ((T.U j T.σ₀).X k).SS ((A.Xa k).Fp + Tn • (A.Xa k).L),
        ∃ c : Fin K → ℂ, ∀ x ∈ ((T.U j T.σ₀).X k).dom, f x = ∑ i, c i * g i x := by
    intro k
    obtain ⟨K, g, hg⟩ := sp_le_span_fin R (addL wF wL Tn)
    refine ⟨K, fun i x => if hx : x ∈ ((T.U j T.σ₀).X k).dom then g i (e.symm ⟨k, x, hx⟩) else 0, fun f hf => ?_⟩
    have hmem := (hsp (addL wF wL Tn)).2.1 _ _ (hOnto Tn) (Pi.single k f) fun k' => by
      by_cases hk : k' = k
      · subst hk
        rw [Pi.single_eq_same, hwt]; exact hf
      · rw [Pi.single_eq_of_ne hk, hwt]
        exact (A.mar k').2.2.2.2 _ _ (BoundedSectionAlgebra.bdd_zero _ _)
    obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hg hmem)
    refine ⟨cf, fun x hx => ?_⟩
    have h1 := congrFun hcf (e.symm ⟨k, x, hx⟩)
    rw [Equiv.apply_symm_apply, Finset.sum_apply] at h1
    simp only [dif_pos hx]
    simpa using h1.symm
  have hsurj : ∀ v : (Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ) → ℂ, ∃ a : Fin m → ℂ, ∀ p,
      ∑ i, a i * θf i p.1 ((Fl.Fl p.1).xs p.2) = v p := by
    intro v
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1
      (hspan ▸ Submodule.mem_top : (fun q => v (en q)) ∈ Submodule.span ℂ (Set.range (vals xs θ)))
    refine ⟨a, fun p => ?_⟩
    obtain ⟨q, rfl⟩ := en.surjective p
    rw [← congrFun ha q, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    show _ = a i * θ i (xs q)
    rw [hθe, hxs]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨F, hF, rfl⟩
  obtain ⟨cc, g, hg, hx⟩ := division_all (T.U j T.σ₀).X A.Xa Fl.Fl A.mar A.dim A.hT hfin θf
    (fun i k => by rw [A.hF]; exact (hθf i k).1.1) hsurj (rdR h j F)
    (fun k => by rw [← hwt, A.hc]; exact hMg F hF k)
  have hdec : R.ev ((recPlusN h j hj n).inc (addL wF wL Tn) F) =
      ∑ α ∈ ReciprocityTheory.ChartRestriction.G.AR.multiLt (WeightFamilies.dimY D j) (Tn - WeightFamilies.dimY D j), ∑ i,
        cc α i • (R.mon w t α * R.s w t 0 ^ (Tn - ∑ q, α q) * θ i) +
      ∑ α ∈ Finset.Nat.antidiagonalTuple (WeightFamilies.dimY D j) (Tn - WeightFamilies.dimY D j),
        R.mon w t α * fun y => g (e y).1 α (e y).2.1 := by
    funext y
    rw [hR.2, sub_eq_iff_eq_add'.1 (hx (e y).1 (e y).2.1 (e y).2.2)]
    simp only [Rdg.mon, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.mul_apply, Finset.prod_apply,
      Pi.pow_apply, smul_eq_mul, hs0, hs1, hθe, mul_assoc]
  show R.ev ((recPlusN h j hj n).inc (addL wF wL Tn) F) ∈ _
  rw [hdec]
  refine Submodule.add_mem_sup (Submodule.sum_mem _ fun α hα => Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨(⟨α, GlobalTheory.LeadJets.mem_multiLt.1 hα⟩, i), rfl⟩))
    (Submodule.sum_mem _ fun α hα => Submodule.subset_span
      ⟨α, _, Finset.Nat.mem_antidiagonalTuple.1 hα, ?_, rfl⟩)
  exact (hsp (addL wF wL (WeightFamilies.dimY D j))).2.1 _ _ (hOnto _) (fun k => g k α) fun k => by
    rw [hwt]; exact hg k α hα

end Contain

theorem exists_anFacts_definite (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (CR c c1 : ℝ)
    (hp : ∀ k : (T.U j T.σ₀).Comp, ((T.U j T.σ₀).X k).p0 = 0) (A : ArchAt h j w wF Tn c1)
    (hOn : ∀ k : ℕ, RdOnto h j (addL wF wL k)) (hM : MggOnto h j CR Tn c (addL wF wL Tn)) :
    ∃ (R : Rdg (recPlusN h j hj n)) (t : Idx D j N → ℂ) (δ : ℕ) (xs : Fin δ → R.Y), R.Generic t ∧
      AnFacts R w t (addL wF wL Tn) wF Tn (WeightFamilies.MggK n.base CR Tn c j (addL wF wL Tn)) xs := by
  obtain ⟨R, e, hR⟩ := GlobalTheory.Shares.exists_isRdgU D T h j hj n
  obtain ⟨t, ht, ⟨Fl⟩⟩ := GlobalTheory.GenericFlat.exists_generic_flatAt D T h j hj N wL wF w Tn _ A
  classical
  let ι : Type := Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ
  have : Fintype ι := inferInstance
  let en : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let xs : Fin (Fintype.card ι) → R.Y := fun q =>
    e.symm ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩
  have hxs : ∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩ :=
    fun q => e.apply_symm_apply _
  have h1 := GlobalTheory.Shares.points_and_interp D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs hOn
  refine ⟨R, t, _, xs, ?_, h1.1, h1.2,
    GlobalTheory.Shares.VanDiv.vanishing_division D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs hOn,
    GlobalTheory.Shares.LeadDeep.main D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs,
    GlobalTheory.UpperRecord.upper D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs,
    lower_bound_definite D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs CR c hp hM,
    containment_any D T h j hj n R e hR N wL wF w Tn _ A t Fl _ xs en hxs hOn CR c ?_⟩
  · intro Q hQ
    have hσ : R.σ = T.σ₀ := RingHom.ext hR.1
    rw [hσ]
    exact ht Q hQ
  · exact fun F _ k => ⟨(GlobalTheory.ArcRead.readings_cusp_and_independent D T h j hj).1 _ F k,
      fun ξ hξ => absurd hξ (not_isIso_of_p0_zero _ (hp k) ξ)⟩

section Abstract

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

def rdgBack (X : PJ D B P j) (E : PtExt X) (hM : IntAtExt X E) (n : SecNorm B)
    (R : Rdg (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 (xplus X E hM))) : Rdg X :=
  ⟨R.Y, R.σ, R.ev, R.ev_smul, R.indep⟩

theorem anFacts_back (X : PJ D B P j) (E : PtExt X) (hM : IntAtExt X E) (n : SecNorm B)
    (R : Rdg (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 (xplus X E hM))) {N : ℕ} {ka wL wF : WeightFamilies.Wt D j}
    (w : Fin N → B.Cusp j wL) (t : Idx D j N → ℂ) (Tn : ℕ) (CR c : ℝ) {δ : ℕ} (xs : Fin δ → R.Y)
    (hg : R.Generic t) (hF : AnFacts R w t ka wF Tn (WeightFamilies.MggK n.base CR Tn c j ka) xs) :
    (rdgBack X E hM n R).Generic t ∧ AnFacts (rdgBack X E hM n R) w t ka wF Tn (WeightFamilies.MggK B CR Tn c j ka) xs :=
  ⟨hg, hF.zero, hF.interp, hF.vandiv, hF.indep, hF.upper, hF.lower, hF.contain⟩

theorem sharesAt_of_anFacts (X : PJ D B P j) {ka wL wF : WeightFamilies.Wt D j} (G₀ : GlobalFamilyData X ka wL wF) (S : Scal B) (Tn : ℕ) (c : ℝ)
    (R : Rdg X) (t : Idx D j G₀.N → ℂ) {δ : ℕ} (xs : Fin δ → R.Y) (hg : R.Generic t)
    (hF : AnFacts R G₀.w t ka wF Tn (WeightFamilies.MggK B (7 : ℝ) Tn c j ka) xs) (hka : addL wF wL Tn = ka)
    (hD : 2 ≤ WeightFamilies.dimY D j) (hT : 11 * WeightFamilies.dimY D j ^ 2 ≤ Tn) (hL : LatAt B j ka)
    (hS : ∃ β : ℝ, ShortG X (X.wF0 wL wF) (X.Thc S.s0 (X.wF0 wL wF)) β)
    (Sh : Set (B.Cusp j wF)) (hSh : Submodule.span B.KO Sh = ⊤) : GlobalTheory.RunJoin.SharesAt G₀ S Tn c Sh := by
  obtain ⟨θ, hθ, hli⟩ := GlobalTheory.Shares.exists_valueBasis_in_spanning D _ _ j X ka wL wF G₀.N G₀.w R t Tn
    _ δ xs hF Sh hSh
  refine ⟨δ, θ, hθ, ?_⟩
  intro rz alz th0 zc rq th iet et
  have hlt : WeightFamilies.dimY D j < Tn := by nlinarith
  have hB : ∀ la, InBasis (FamilyHypotheses.refill G₀ δ θ rz alz th0 zc rq th iet et) la := fun la =>
    (GlobalTheory.Shares.inBasis_iff_vals D _ _ j X ka wL wF (FamilyHypotheses.refill G₀ δ θ rz alz th0 zc rq th iet et) R t Tn _ δ xs
      hg hF hka la).2 ⟨hli, rfl⟩
  obtain ⟨β, Sg, hsub, hspan, -⟩ := hS
  refine ⟨hB, ?_, ?_, ?_, fun la => ?_⟩
  · obtain ⟨la⟩ := nonempty_heightOneSpectrum_ringOfIntegers B.KO
    exact shareRd_of_inBasis D _ _ j X ka wL wF (FamilyHypotheses.refill G₀ δ θ rz alz th0 zc rq th iet et)
      R t Tn _ δ xs hg hF hka hlt (by omega) hL ⟨la, hB la⟩
  · exact shareRhoR_of_anFacts D _ _ j X ka wL wF (FamilyHypotheses.refill G₀ δ θ rz alz th0 zc rq th iet et)
      R t Tn _ δ xs hg hF hka hD hT hL S
  · exact shareRhoP_of_anFacts D _ _ j X ka wL wF G₀.N G₀.w R t Tn 7 c δ xs hF hD hT hL
  · refine Contain.inContainMR_of_anFacts D _ _ j X ka wL wF
      (FamilyHypotheses.refill G₀ δ θ rz alz th0 zc rq th iet et) R t Tn 7 c δ xs hg hF hka hlt.le S ?_ la (hB la)
    exact top_le_iff.1 (hspan ▸ Submodule.span_mono hsub)

theorem weight_and_degree {X : PJ D B P j} {large₂ : SizeData₂ D} {H : KHyp} {C2 A2 CR CT : ℝ} {ka wL wF : WeightFamilies.Wt D j}
    {Tn nP nW : ℕ} {h0 : ℝ} (hH : FamilyHypotheses.HypPage large₂ X H C2 A2 CR CT ka wL wF Tn nP nW h0) :
    addL wF wL Tn = ka ∧ 11 * WeightFamilies.dimY D j ^ 2 ≤ Tn := by
  obtain ⟨-, hS, -, -, -⟩ := hH
  obtain ⟨hn, -, -, -, -, -, -, -, -, -, -, -, -, hnV, hL, hF, -, -, -, -, -, -, -, h11, -, -⟩ := hS
  refine ⟨?_, h11⟩
  obtain ⟨f1, f2, f3⟩ := hF
  have l1 := hL.1
  obtain ⟨aP, aM, p1, p2, n, p3⟩ := ka
  unfold addL wadd wsmul
  simp only [WeightFamilies.Wt.mk.injEq]
  simp only at hn f2 f3
  refine ⟨?_, ?_, ?_⟩
  · funext τ i
    have := f2 τ i
    zify; linarith
  · funext τ i
    have := f3 τ i
    zify; linarith
  · rw [f1, l1, hn, hnV]

theorem two_le_dimY (hj : InR D j) : 2 ≤ WeightFamilies.dimY D j := by
  have h1 := hj.1
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hf : 8 ≤ D.R.f := D.eight_le_f
  have hs : (D.R.sigW j).1 = D.R.k + j - 1 := rfl
  have h5 : 5 ≤ (D.R.sigW j).1 := by omega
  have h6 : 2 ≤ (D.R.sigW j).1 * ((D.R.sigW j).1 - 1) / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have : 5 * 4 ≤ (D.R.sigW j).1 * ((D.R.sigW j).1 - 1) := Nat.mul_le_mul h5 (by omega)
    omega
  unfold WeightFamilies.dimY
  exact le_trans (by omega) (Nat.le_mul_of_pos_left _ (by omega))

end Abstract

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem sharesDef : GlobalTheory.RunJoin.SharesDefSt := by
  intro D T h EX p hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 S nus hPar hPg hC hL G₀ hNZ Sh hSh
  obtain ⟨A⟩ := GlobalTheory.T.thetaArchimedeanData_definiteModels_nonempty D T h EX p hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 S nus hPar hPg hC G₀.N G₀.w hNZ
  obtain ⟨hOn, hM⟩ := GlobalTheory.T.cuspReadings_span_model_forms_shifted_weights D T h _ hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 EX p hPar hPg
  obtain ⟨hka, hT⟩ := weight_and_degree hPg.hyp
  have hp : ∀ k : (T.U D.R.m T.σ₀).Comp, ((T.U D.R.m T.σ₀).X k).p0 = 0 := fun k => by
    have h0 : WeightFamilies.rho D D.R.m = 0 := by
      show D.R.m - D.R.m = 0
      omega
    have hU : IsUnf (T.U D.R.m T.σ₀) := h.unf _ hj T.σ₀ T.good_σ₀
    exact ((hU.2.1 k).1).trans ((h.pins.2.2.2 _ hj).2.1.trans h0)
  have hsh : ∃ β : ℝ, ShortG (recPJ h D.R.m hj) ((recPJ h D.R.m hj).wF0 wL wF)
      ((recPJ h D.R.m hj).Thc S.s0 ((recPJ h D.R.m hj).wF0 wL wF)) β := by
    obtain ⟨_, _, _, _, _, po, hpo, _, PLam, hPL, _, _, hz, _⟩ := ((FamilyHypotheses.hypC_iff ..).1 hC).2.1
    exact ⟨_, hz⟩
  subst hka
  obtain ⟨R, t, δ, xs, hg, hF⟩ := exists_anFacts_definite D T h _ hj (SecNorm.sup _) G₀.N wL wF G₀.w Tn 7 _ 1 hp A hOn hM
  obtain ⟨hg', hF'⟩ := anFacts_back (recPJ h D.R.m hj) _ _ (SecNorm.sup _) R G₀.w t Tn 7 _ xs hg hF
  exact sharesAt_of_anFacts _ G₀ S Tn _ _ t xs hg' hF' rfl (two_le_dimY hj) hT hL hsh Sh hSh

end GlobalTheory.SharesDefinite
