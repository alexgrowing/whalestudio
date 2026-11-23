import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.WeightsBelow
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HalfLevelGeneratorNorm
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaGeneratorsNoCommonZeroOfChartIndependence
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NoCommonZeroOfReadings
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RunIn

theorem semilinear_eq_zero_of_span_smul {O K L M ι : Type} [CommRing O] [Field K] [Field L] [Algebra O K]
    [AddCommGroup M] [Module K M] [Module O M] [IsScalarTower O K M] (σ : K →+* L) (φ : M →ₛₗ[σ] L)
    (w : ι → M) (hw : ∀ i, φ (w i) = 0) (s : O) (hs : algebraMap O K s ≠ 0) (f : M)
    (hf : s • f ∈ Submodule.span O (Set.range w)) : φ f = 0 := by
  have h1 : ∀ g ∈ Submodule.span O (Set.range w), φ g = 0 := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hw i
    | zero => exact map_zero φ
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul a x _ hx => rw [← algebraMap_smul K a x, map_smulₛₗ, hx, smul_zero]
  have h2 := h1 _ hf
  rw [← algebraMap_smul K s f, map_smulₛₗ, smul_eq_mul] at h2
  exact (mul_eq_zero.1 h2).resolve_left ((map_ne_zero σ).2 hs)

theorem eq_zero_of_span_eq_WWc {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : PJ D B P j) (w : WeightFamilies.Wt D j)
    {ι : Type} (g : ι → B.Cusp j w) (s : 𝓞 B.KO) (hs : s ≠ 0)
    (hg : Submodule.span (𝓞 B.KO) (Set.range g) = X.WWc s w) (σ : B.KO →+* ℂ) (φ : B.Cusp j w → ℂ)
    (hadd : ∀ F F', φ (F + F') = φ F + φ F') (hsmul : ∀ (a : B.KO) F, φ (a • F) = σ a * φ F)
    (h0 : ∀ i, φ (g i) = 0) (F : B.Cusp j w) (hF : F ∈ X.thAll w) : φ F = 0 := by
  have hW : s • F ∈ X.WWc s w := ⟨F, hF, rfl⟩
  rw [← hg] at hW
  exact semilinear_eq_zero_of_span_smul σ ⟨⟨φ, hadd⟩, hsmul⟩ g h0 s
    (fun h' => hs (RingOfIntegers.coe_eq_zero_iff.1 h')) F hW

set_option synthInstance.maxHeartbeats 400000 in

theorem noCommonZero_of_tiedW : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (h : LawsP T) (_EX : ErrX D) (j : ℕ) (hj : InR D j) (S : Scal (recB h.toLawsCore)) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (Gc Prw : ℝ), FamilyHypotheses.HypPage large₂ (recPJ h j hj) H C2 A2 CR CT ka wL wF Tn nP nW h0 → S.sW ≠ 0 → ∀ G : EtaleWeightGaps.GlobalFamilyData (recPJ h j hj) ka wL wF, G.TiedW S Gc Prw → NoCommonZero (T.Q.Xo j) T.Q.c (fun i => (G.w i).1) := by
  intro hC D T h EX j hj S large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 Gc Prw hP hs G hG
  obtain ⟨hDF, -, hr, hl⟩ := (GlobalTheory.RunWeights.weights_below D _ _ j (recPJ h j hj) large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0
    hj.1 hP).1 wL (Set.mem_insert _ _)
  have hlp := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.lastPos_wtA h hj wL hl
  have hg : ∀ i, 2 * WeightAlgebra.DF ka + 2 < D.host.g i := hP.2.2.2.1.2.2.2.2.2
  have hM : T.Q.l.M = D.host.g 0 * D.host.g 1 := h.pins.2.1.1
  have hdeg : 4 * WeightAlgebra.DF wL + 4 ≤ T.Q.l.M := by
    have h1 : (2 * WeightAlgebra.DF ka + 3) * 3 ≤ D.host.g 0 * D.host.g 1 :=
      Nat.mul_le_mul (hg 0) (by have := hg 1; omega)
    omega
  refine GlobalTheory.FrameZero.noCommonZero_of_readings D T h j hj (wtA wL) wL.n G.N _
    (fun i => cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) _ _ (cutR_le T.C j wL (G.w i).2)) fun k x hx => ?_
  obtain ⟨f, hf, hf0⟩ := GlobalTheory.noCommonZero_of_chartIndep hC D T h j hj wL hr hlp hdeg (half_level_generator_norm D T h EX) T.σ₀ T.good_σ₀ k x hx
  have hc : f ∈ cutR T.C j wL := by
    rw [cutR_eq T.C hj]
    exact h.thCusp j hj _ _ (dom_wtA wL) hlp f hf
  have hF : (⟨f, hc⟩ : (recB h.toLawsCore).Cusp j wL) ∈ (recPJ h j hj).thAll wL := Submodule.subset_span hf
  by_contra hno
  have hno' : ∀ i, rdU (T.U j T.σ₀) (G.w i).1 k x = 0 := fun i => by
    by_contra h'
    exact hno ⟨i, h'⟩
  have hadd : ∀ F F' : T.R j, rdU (T.U j T.σ₀) (F + F') k x = rdU (T.U j T.σ₀) F k x + rdU (T.U j T.σ₀) F' k x :=
    fun F F' => by rw [map_add]; rfl
  have hsmul : ∀ (a : T.Q.c.F) (F : T.R j), rdU (T.U j T.σ₀) (a • F) k x = T.σ₀ a * rdU (T.U j T.σ₀) F k x :=
    fun a F => by rw [map_smulₛₗ]; rfl
  exact hf0 (eq_zero_of_span_eq_WWc (recPJ h j hj) wL G.w S.sW hs hG.1 T.σ₀
    (fun F => rdU (T.U j T.σ₀) F.1 k x) (fun F F' => hadd F.1 F'.1) (fun a F => hsmul a F.1) hno' ⟨f, hc⟩ hF)

end GlobalTheory.RunIn
