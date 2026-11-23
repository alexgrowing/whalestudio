import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.DataParamsT
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedFrameSumSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupremumConstantLogBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepLevelCoverPrincipalLevelLawsGaloisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemSpanCuspOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FiniteAndFinrankLeOfPointwise
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePointsOverComponentOpenSet
import Development.AbelianVarietyTheory.Definitions.Foundations.CanonicalExponents
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ClausesIffExistsUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RdZeroOfPetAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestValueEqConstMulReadingSecZ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsFiniteDimensional
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoreGoodMatch
import Formalism.LocalToGlobal.ProjectiveLattices.ReadProofs
import Formalism.LocalToGlobal.ProjectiveLattices.NormLaws
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.RankBergman

open MeasureTheory ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.AllWt (ptN petE muOn muPart framesOn bergE bergOn modelWt mem_cuspW cuspW_le_secZ cuspOn_le classesOver
  isProbabilityMeasure_muPart muPart_univ_le petE_ne_top bergE_le_iff)
open scoped ENNReal

set_option maxHeartbeats 1000000 in

theorem rkC_le_of_bergLe : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o →
    ∀ (la : AllWt.Weight (T.Q.Dw j)) (Z : Comp Y.d.Xo₂ Y.d.c₂) (β : ℝ), 0 ≤ β →
    BergLe Z Y.U (fun _ => D.sp.W j) Y.dict la β → (Y.rkC la Z : ℝ) ≤ β := by
  intro D T j Y e o hY la Z β hβ hB
  classical
  obtain ⟨G, hG⟩ : ∃ G : WTZ D.host.E, G = wtOf (T.Q.Dw j) la 0 := ⟨_, rfl⟩
  set σ : Y.d.c₂.F →+* ℂ := goodOf Y.d.c₂ Y.d.c₂.F.val.toRingHom with hσdef
  have hσ : GoodEmb Y.d.c₂ σ := goodEmb_goodOf _ _
  obtain ⟨th, hr, hth, hdU⟩ := hY.dictU σ hσ
  have hd : ∀ g, (Y.dict σ g).2 ∈ ((Y.U σ).X (Y.dict σ g).1).dom := hdU.2.2.2.1
  have hu := hY.unit σ hσ
  set Cw := cuspOn Y.U Z G with hCw
  set S : Submodule ℂ (FDSec (Y.U σ).X) := Submodule.span ℂ (rdU (Y.U σ) '' (Cw : Set (Rul Y.d.Xo₂ Y.d.c₂))) with hS
  set μ := muOn (Y.U σ) (D.sp.W j) (Y.dict σ) Z with hμdef
  set lw := modelWt (Y.U σ) G with hlw
  have hSsub : S ≤ holSub (Y.U σ).X lw :=
    Submodule.span_le.2 (by rintro _ ⟨f, hf, rfl⟩; exact (mem_cuspW.1 hf.1).2 σ hσ)
  have hoff : ∀ P ∈ S, ∀ z, z ∉ framesOn (Y.U σ) Z → P z.1 z.2 = 0 := fun P hP z hz =>
    eq_zero_of_mem_span_cuspOn hP hz
  have hμ1 : μ Set.univ ≤ 1 := muPart_univ_le _ _ _
  have hfin : ∀ P ∈ holSub (Y.U σ).X lw, petE (D.sp.W j) (Y.dict σ) μ lw P ≠ ⊤ := fun P hP =>
    petE_ne_top _ _ μ hμ1 hd hP

  have hpt : ∀ P ∈ S, ∀ z, ptN lw P z ^ 2 ≤ β * (petE (D.sp.W j) (Y.dict σ) μ lw P).toReal ^ 2 := by
    intro P hP z
    by_cases hz : z ∈ framesOn (Y.U σ) Z
    · have hzd := hz.1
      have hb := hB σ hσ ⟨z.1, z.2, hzd⟩ hz
      have hb' : bergE (D.sp.W j) (Y.dict σ) μ lw ⟨z.1, z.2, hzd⟩ ≤ ENNReal.ofReal β := by
        rw [hlw, hG]; exact hb
      have h := (bergE_le_iff (D.sp.W j) (Y.dict σ) μ hfin ⟨z.1, z.2, hzd⟩ ENNReal.ofReal_ne_top).1 hb' P (hSsub hP)
      have hf := hfin P (hSsub hP)
      have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hf)) h
      rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (GlobalTheory.AllWt.ptN_nonneg _ _ _), ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hβ, ENNReal.toReal_pow] at h2
      exact h2
    · have h0 : ptN lw P z = 0 := by
        simp only [ptN, Data.pnorm, hoff P hP z hz, norm_zero, zero_mul]
      rw [h0]
      nlinarith [sq_nonneg (petE (D.sp.W j) (Y.dict σ) μ lw P).toReal]
  have hzero : ∀ P ∈ S, petE (D.sp.W j) (Y.dict σ) μ lw P = 0 → P = 0 := by
    intro P hP h0
    funext k x
    by_cases hz : (⟨k, x⟩ : Σ k, Frame ((Y.U σ).X k).Ψ D.R.r) ∈ framesOn (Y.U σ) Z
    · have h1 := hpt P hP ⟨k, x⟩
      rw [h0, ENNReal.toReal_zero] at h1
      have h2 : ptN lw P ⟨k, x⟩ = 0 := by nlinarith [GlobalTheory.AllWt.ptN_nonneg lw P ⟨k, x⟩]
      have h3 := GlobalTheory.LevGeo.RankBd.pnorm_fac_pos ((Y.U σ).X k) (lw k) hz.1
      have h4 : ‖P k x‖ * _ = 0 := h2
      rcases mul_eq_zero.1 h4 with h5 | h5
      · simpa using h5
      · exact absurd h5 h3.ne'
    · exact hoff P hP ⟨k, x⟩ hz
  have hptd : ∀ (P : FDSec (Y.U σ).X) g, ptN lw P (Y.dict σ g) = ‖P (Y.dict σ g).1 (Y.dict σ g).2‖ := fun P g =>
    pnorm_eq_of_unit _ _ _ _ (hu g)
  have hmeasQ : ∀ P ∈ S, AEStronglyMeasurable
      (fun q : AutQ (D.sp.W j) => ‖P (Y.dict σ q.out).1 (Y.dict σ q.out).2‖) (muQ1 (D.sp.W j)) := by
    intro P hP
    have h := aesm_of_holSub (adelMeas_of_aut Y.d.Xo₂ Y.d.c₂ (U := Y.U) (σ := σ) (GlobalTheory.PetDef.adelAut_good Y hY σ hσ))
      _ (hSsub hP)
    have e : (fun q : AutQ (D.sp.W j) => ‖P (Y.dict σ q.out).1 (Y.dict σ q.out).2‖) =
        fun q => ‖onQ (D.sp.W j) (adel (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) P) q‖ := by
      funext q
      simp [onQ, adel]
    rw [e]
    exact h.norm
  have hmeas : ∀ P ∈ S, AEStronglyMeasurable
      (fun q : AutQ (D.sp.W j) => ‖P (Y.dict σ q.out).1 (Y.dict σ q.out).2‖) μ := by
    intro P hP
    rw [hμdef]
    unfold GlobalTheory.AllWt.muOn GlobalTheory.AllWt.muPart ProbabilityTheory.cond
    exact ((hmeasQ P hP).restrict).smul_measure _

  have hSfin : FiniteDimensional ℂ S ∧ (Module.finrank ℂ S : ℝ) ≤ β := by
    by_cases hA : muQ1 (D.sp.W j) (classesOver (D.sp.W j) (Y.dict σ) (framesOn (Y.U σ) Z)) = 0
    · have hμ0 : μ = 0 := ProbabilityTheory.cond_eq_zero_of_meas_eq_zero hA
      have hsub : Subsingleton S := ⟨fun a b => by
        have ha := hzero a a.2 (by rw [hμ0]; unfold GlobalTheory.AllWt.petE; exact eLpNorm_measure_zero)
        have hb := hzero b b.2 (by rw [hμ0]; unfold GlobalTheory.AllWt.petE; exact eLpNorm_measure_zero)
        exact Subtype.ext (ha.trans hb.symm)⟩
      refine ⟨inferInstance, ?_⟩
      rw [Module.finrank_zero_of_subsingleton]
      simpa using hβ
    · haveI : IsProbabilityMeasure μ := isProbabilityMeasure_muPart _ _ hA
      have hpet : ∀ P ∈ S, (petE (D.sp.W j) (Y.dict σ) μ lw P).toReal ^ 2 =
          ∫ q, ‖P (Y.dict σ q.out).1 (Y.dict σ q.out).2‖ ^ 2 ∂μ := by
        intro P hP
        obtain ⟨M, -, hM⟩ := exists_ptN_le (hSsub hP)
        have e : petE (D.sp.W j) (Y.dict σ) μ lw P =
            eLpNorm (fun q : AutQ (D.sp.W j) => ‖P (Y.dict σ q.out).1 (Y.dict σ q.out).2‖) 2 μ := by
          unfold GlobalTheory.AllWt.petE
          congr 1
          funext q
          exact hptd P _
        have h2 := GlobalTheory.LevGeo.RankBd.eLpNorm_sq_eq (μ := μ) (fun _ => norm_nonneg _) (hmeas P hP) (B := M)
          fun q => by rw [← hptd]; exact hM ⟨_, _, hd q.out⟩
        rw [← e] at h2
        rw [← ENNReal.toReal_pow, h2, ENNReal.toReal_ofReal (integral_nonneg fun _ => by positivity)]
      refine GlobalTheory.Bergman.finite_and_finrank_le_of_pointwise (μ := μ)
        (fun q (P : S) => ‖(P : FDSec (Y.U σ).X) (Y.dict σ q.out).1 (Y.dict σ q.out).2‖)
        (fun q => ⟨(LinearMap.proj (R := ℂ) (φ := fun _ : Frame ((Y.U σ).X (Y.dict σ q.out).1).Ψ D.R.r => ℂ)
          (Y.dict σ q.out).2 ∘ₗ LinearMap.proj (R := ℂ) (φ := fun k => Frame ((Y.U σ).X k).Ψ D.R.r → ℂ)
          (Y.dict σ q.out).1) ∘ₗ S.subtype, fun P => rfl⟩)
        (fun P => hmeas P P.2) ?_ hβ ?_
      · intro P hP0
        refine Subtype.ext (hzero P P.2 ?_)
        unfold GlobalTheory.AllWt.petE
        have e : (fun q : AutQ (D.sp.W j) => ptN lw (P : FDSec (Y.U σ).X) (Y.dict σ q.out)) = fun _ => 0 := by
          funext q
          rw [hptd]
          exact hP0 q
        rw [e]
        exact eLpNorm_zero
      · intro P q
        have h1 := hpt P P.2 (Y.dict σ q.out)
        rw [hptd, hpet P P.2] at h1
        exact h1

  obtain ⟨hSf, hSle⟩ := hSfin
  have hcard : ∀ s : Finset Cw, LinearIndependent Y.d.c₂.F (fun i : s => (i : Cw)) → s.card ≤ Module.finrank ℂ S := by
    intro s hs
    let eq : Fin s.card ≃ s := s.equivFin.symm
    let b : Fin s.card → Rul Y.d.Xo₂ Y.d.c₂ := fun i => ((eq i : Cw) : Rul Y.d.Xo₂ Y.d.c₂)
    have hb : LinearIndependent Y.d.c₂.F b := (hs.comp eq eq.injective).map' Cw.subtype (Submodule.ker_subtype _)
    have hrd := GlobalTheory.reading_linearIndependent_secZ GlobalTheory.abelianSchemeLaws_all.1.secBaseChange (Y.U σ) (hY.unf σ hσ)
      (exZ _ G) s.card b (fun i => cuspW_le_secZ G (cuspOn_le Y.U Z G (eq i : Cw).2)) hb
    let v : Fin s.card → S := fun i => ⟨rdU (Y.U σ) (b i), Submodule.subset_span ⟨b i, (eq i : Cw).2, rfl⟩⟩
    have hv : LinearIndependent ℂ v := LinearIndependent.of_comp S.subtype hrd
    simpa using hv.fintype_card_le_finrank
  haveI : Module.Free Y.d.c₂.F Cw := Module.Free.of_divisionRing Y.d.c₂.F Cw
  have hrank : Module.rank Y.d.c₂.F Cw ≤ ((Module.finrank ℂ S : ℕ) : Cardinal) := rank_le hcard
  haveI hCf : FiniteDimensional Y.d.c₂.F Cw :=
    Module.rank_lt_aleph0_iff.1 (lt_of_le_of_lt hrank (Cardinal.nat_lt_aleph0 _))
  have h2 : Module.finrank Y.d.c₂.F Cw ≤ Module.finrank ℂ S := Module.finrank_le_of_rank_le hrank
  have h3 : GlobalTheory.AllWt.rankOn Y.U Z G ≤ Module.finrank Y.d.c₂.F Cw := by
    unfold GlobalTheory.AllWt.rankOn Formalism.HN.rkK
    exact Submodule.finrank_le _
  show (GlobalTheory.AllWt.rankOn Y.U Z (wtOf (T.Q.Dw j) la 0) : ℝ) ≤ β
  rw [← hG]
  exact le_trans (Nat.cast_le.2 (h3.trans h2)) hSle

end GlobalTheory.RankBergman
