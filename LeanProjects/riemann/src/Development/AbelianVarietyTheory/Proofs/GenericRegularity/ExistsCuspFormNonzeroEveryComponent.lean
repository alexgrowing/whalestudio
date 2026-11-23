import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.InnerEuclideanEmbeddingEqAverage
import Formalism.LocalToGlobal.ProjectiveLattices.CurveAsm
import Formalism.LocalToGlobal.ProjectiveLattices.CurveLocInst
import Formalism.LocalToGlobal.ProjectiveLattices.RealPtPf
import Formalism.LocalToGlobal.ProjectiveLattices.TieInst
import Formalism.LocalToGlobal.ProjectiveLattices.CombAlgOfCombBound
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Formalism.LocalToGlobal.ProjectiveLattices.FullExists
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Formalism.LocalToGlobal.ProjectiveLattices.AxHLAM
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.NonzeroDivisorOfConnected
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CompSplitRecord
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CuspEqZeroOfGenericValues
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsOpenSameModel
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.WeightsBelow
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaGeneratorReadingNeZeroAllFramesStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicGermValueChartIndependentStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin

noncomputable section

namespace GlobalTheory.RunJoin

theorem eval_ne_zero_of_nonZeroComp {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j)
    {ι : Type} (Ω : ι → Type) [∀ Z, Field (Ω Z)] [∀ Z, Algebra B.KO (Ω Z)] (gF : ∀ Z, X.Forms →ₐ[B.KO] Ω Z)
    (hinj : ∀ (u : WeightFamilies.Wt D j) (F : B.Cusp j u), (∀ Z, gF Z (X.inc u F) = 0) → F = 0)
    {u v : WeightFamilies.Wt D j} (g : B.Cusp j u) (hg : X.NonZeroComp u g) (Z : ι) (g' : B.Cusp j v)
    (h1 : gF Z (X.inc v g') ≠ 0) (h2 : ∀ Z', Z' ≠ Z → gF Z' (X.inc v g') = 0) : gF Z (X.inc u g) ≠ 0 := by
  intro h0
  obtain ⟨H, hH⟩ := X.inc_mul u v g g'
  have hz : H = 0 := by
    refine hinj _ H fun Z' => ?_
    rw [← hH, map_mul]
    by_cases e : Z' = Z
    · subst e
      rw [h0, zero_mul]
    · rw [h2 Z' e, mul_zero]
  have hg0 : g' = 0 := hg v g' (by rw [hH, hz, map_zero])
  exact h1 (by rw [hg0, map_zero, map_zero])

section Record

variable {D : D7} {T : Top D} (h : LawsP T) {j : ℕ} (hj : InR D j)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem generic_ne_zero_of_nonZeroComp (hG : GenFrEx (T.Q.Xo j) T.Q.c) {v u : WeightFamilies.Wt D j}
    (Z : Comp (T.Q.Xo j) T.Q.c) (w : (recB h.toLawsCore).Cusp j v) (hw : evC hG Z (w : T.R j) ≠ 0)
    (g : (recB h.toLawsCore).Cusp j u) (hg : (recPJ h j hj).NonZeroComp u g) : evC hG Z (g : T.R j) ≠ 0 := by
  have hT : GenFromTest (T.Q.Xo j) T.Q.c hG := fun Z => h.allTest j hj (Om Z) (genFr hG Z)
  have hV := GlobalTheory.Reg.genValInj_record D T h j hj hG
  obtain ⟨g', h1, h2⟩ := GlobalTheory.Reg.compSplit_record D T h j hj hG Z v w
  have := eval_ne_zero_of_nonZeroComp (recPlus h j hj) (fun Z : Comp (T.Q.Xo j) T.Q.c => Om Z)
    (fun Z => formsEvR j hG hT Z)
    (fun u F hF => hV u F fun Z => (formsEvR_inc h j hj hG hT Z u F).symm.trans (hF Z)) g hg Z g'
    (fun h0 => hw (h1.symm.trans ((formsEvR_inc h j hj hG hT Z v g').symm.trans h0)))
    (fun Z' e => (formsEvR_inc h j hj hG hT Z' v g').trans (h2 Z' e))
  exact fun h0 => this ((formsEvR_inc h j hj hG hT Z u g).trans h0)

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_cusp_reading_ne_zero (w : WeightFamilies.Wt D j) (σ : T.Q.c.F →+* ℂ)
    (hN : ∀ k : (T.U j σ).Comp, ∃ x ∈ ((T.U j σ).X k).dom, ∃ f ∈ cutR T.C j w, rdU (T.U j σ) f k x ≠ 0) :
    ∃ F : (recB h.toLawsCore).Cusp j w, ∀ k : (T.U j σ).Comp, ∃ x ∈ ((T.U j σ).X k).dom,
      rdU (T.U j σ) (F.1 : T.R j) k x ≠ 0 := by
  choose x hx f hc hf0 using hN
  let p : (T.U j σ).Comp → Submodule T.Q.c.F (cutR T.C j w) := fun k =>
    { carrier := {F | rdU (T.U j σ) (F.1 : T.R j) k (x k) = 0}
      zero_mem' := by
        show rdU (T.U j σ) (0 : T.R j) k (x k) = 0
        rw [map_zero]; rfl
      add_mem' := by
        intro a b ha hb
        show rdU (T.U j σ) (a.1 + b.1 : T.R j) k (x k) = 0
        rw [map_add]
        show rdU (T.U j σ) (a.1 : T.R j) k (x k) + rdU (T.U j σ) (b.1 : T.R j) k (x k) = 0
        rw [ha, hb, add_zero]
      smul_mem' := by
        intro c a ha
        show rdU (T.U j σ) (c • a.1 : T.R j) k (x k) = 0
        rw [LinearMap.map_smulₛₗ]
        show σ c * rdU (T.U j σ) (a.1 : T.R j) k (x k) = 0
        rw [ha, mul_zero] }
  have hne : ∀ k, p k ≠ ⊤ := by
    intro k htop
    have hm : (⟨f k, hc k⟩ : cutR T.C j w) ∈ p k := by rw [htop]; exact Submodule.mem_top
    exact hf0 k hm
  obtain ⟨F, hF⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hne
  exact ⟨F, fun k => ⟨x k, hx k, hF k⟩⟩

end Record

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_nonZeroComp_and_ne_zero : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (hG : GenFrEx (T.Q.Xo j) T.Q.c), PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → (∃ g0 : (recB h.toLawsCore).Cusp j wF, (recPJ h j hj).NonZeroComp wF g0 ∧ ∀ Z : Comp (T.Q.Xo j) T.Q.c, evC hG Z g0.1 ≠ 0) ∧ ∀ (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u), (recPJ h j hj).NonZeroComp u F → (∀ Z : Comp (T.Q.Xo j) T.Q.c, evC hG Z F.1 ≠ 0) ∧ ∀ σ, GoodEmb T.Q.c σ → ∀ k : (T.U j σ).Comp, ∃ x ∈ ((T.U j σ).X k).dom, rdU (T.U j σ) F.1 k x ≠ 0 := by
  intro D T h j hj large₂ H C2 A2 CT ka wL wF Tn nP nW h0 hG hOK
  have hP := hOK.hyp
  obtain ⟨hDF, -, hr, hl⟩ := (GlobalTheory.RunWeights.weights_below D _ _ j (recPJ h j hj) large₂ H C2 A2 7 CT ka wL wF Tn nP nW h0
    hj.1 hP).1 wF (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hlp := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj wF hl
  have hg : ∀ i, 2 * WeightAlgebra.DF ka + 2 < D.host.g i := hP.2.2.2.1.2.2.2.2.2
  have hM : T.Q.l.M = D.host.g 0 * D.host.g 1 := h.pins.2.1.1
  have hdeg : 3 * WeightAlgebra.DF wF + 2 ≤ T.Q.l.M := by
    have h1 : (2 * WeightAlgebra.DF ka + 3) * 3 ≤ D.host.g 0 * D.host.g 1 :=
      Nat.mul_le_mul (hg 0) (by have := hg 1; omega)
    omega
  obtain ⟨g0, hg0⟩ := exists_cusp_reading_ne_zero h wF T.σ₀ fun k => by
    obtain ⟨x, hx⟩ := (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected _ ((T.U j T.σ₀).X k)).nonempty
    obtain ⟨f, hf, hf0⟩ := GlobalTheory.T.exists_thetaGenerator_reading_ne_zero_all_frames GlobalTheory.T.harmonic_germ_value_chart_independent D T h j hj wF hr hdeg T.σ₀ T.good_σ₀ k x hx
    refine ⟨x, hx, f, ?_, hf0⟩
    rw [cutR_eq T.C hj]
    exact h.thCusp j hj _ _ (dom_wtA wF) hlp f hf
  have hZ : ∀ Z : Comp (T.Q.Xo j) T.Q.c, evC hG Z g0.1 ≠ 0 := by
    intro Z hz
    obtain ⟨k, hk⟩ := (GlobalTheory.CompModel.comp_read_on_model D T h j hj hG T.σ₀ T.good_σ₀).1 Z
    obtain ⟨x, hx, hx0⟩ := hg0 k
    exact hx0 ((hk wF g0).1 hz x hx)
  refine ⟨⟨g0, ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.nonzero_divisor_of_connected D T h j hj wF g0 T.σ₀ T.good_σ₀ hg0, hZ⟩, fun u F hF => ?_⟩
  have hFZ : ∀ Z : Comp (T.Q.Xo j) T.Q.c, evC hG Z F.1 ≠ 0 := fun Z =>
    generic_ne_zero_of_nonZeroComp h hj hG Z g0 (hZ Z) F hF
  refine ⟨hFZ, fun σ hσ k => ?_⟩
  obtain ⟨Z, hk⟩ := (GlobalTheory.CompModel.comp_read_on_model D T h j hj hG σ hσ).2 k
  by_contra hno
  refine hFZ Z ((hk u F).2 fun x hx => ?_)
  by_contra h'
  exact hno ⟨x, hx, h'⟩

end GlobalTheory.RunJoin
