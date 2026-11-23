import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransferOfFundamentalDomains
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodRowsLevelSubPrincipalLevelHilbertModelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvalNormTransfer

theorem castGA_mem_GFset {I I' : AutInst} (h : I = I') (x : I.GA) :
    castGA h x ∈ I'.GFset ↔ x ∈ I.GFset := by
  subst h; exact Iff.rfl

theorem iotaX_rat {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (g : GA D (D.sp.Y 0)) : g ∈ GQ (D.sp.Y 0) ↔ (iotaX X h).toMulEquiv g ∈ X.B.I.GFset := by
  rw [Formalism.IndefR.RationalEmbedding.iota_rat D g]
  exact (castGA_mem_GFset h.symm _).symm

theorem borel_inst {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : BorelSpace X.B.I.GA := by
  obtain ⟨hT, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology X.B.I
  infer_instance

theorem exists_map_eq_smul {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (ν : Measure (GA D (D.sp.Y 0))) [ν.IsHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧
      Measure.map (iotaX X h).toMulEquiv.symm (X.B.I.muA X.B.μf) = ENNReal.ofReal c • ν := by
  obtain ⟨hT, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology X.B.I
  obtain ⟨h1, h2, h3, h4, h5⟩ := Formalism.IndefR.Eqv.ga_facts D (D.sp.Y 0)
  haveI := X.B.haar
  haveI := X.B.sf
  haveI : BorelSpace X.B.I.GA := inferInstance
  haveI : (X.B.I.muA X.B.μf).IsHaarMeasure := Measure.prod.instIsHaarMeasure _ _
  set μ' := Measure.map (iotaX X h).toMulEquiv.symm (X.B.I.muA X.B.μf) with hμ'
  haveI hH : μ'.IsHaarMeasure :=
    (iotaX X h).toMulEquiv.symm.isHaarMeasure_map _ (iotaX X h).symm.continuous (iotaX X h).continuous
  refine ⟨(Measure.haarScalarFactor μ' ν : ℝ), ?_, ?_⟩
  · exact_mod_cast Measure.haarScalarFactor_pos_of_isHaarMeasure μ' ν
  · rw [ENNReal.ofReal_coe_nnreal, ← ENNReal.smul_def]
    exact Measure.isMulLeftInvariant_eq_smul μ' ν

theorem evalTranslate_norm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ t ∈ GfC (Yc D 0), ∃ c : ℝ, 0 < c ∧ ∀ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) → ∀ S ∈ EP R F, MemLp (fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) 2 (muX X) ∧ ∫ x, ‖(fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) x‖ ^ 2 ∂(muX X) = c * (ipM (MP R) R.ν0 R.fd0 S S).re ∧ ((ipM (MP R) R.ν0 R.fd0 S S).re = 0 → S = 0) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hL hG hM t ht
  haveI hνH : R.ν0.IsHaarMeasure := hM.ν0.1.1
  obtain ⟨c, hc, hmap⟩ := @exists_map_eq_smul D X h R.ν0 hνH
  obtain ⟨hι, hιs⟩ := measurable_of_borel X (iotaX X h) (borel_inst X)
  have hTr : SquareIntegrableTransfer R.ν0 R.fd0 X (iotaX X h).toMulEquiv t c :=
    squareIntegrableTransfer_of_rational_points R.ν0 R.fd0 X _ t c hι hιs hc hmap hνH hM.ν0.2 (iotaX_rat X h)
  refine ⟨c, hc, fun v₀ hv S hS => ?_⟩
  have hI := GlobalTheory.T.goodRows_level_sub_principalLevel_hilbertModel R hM
  have hS' : S ∈ R.EEat (R.levR F true) := hS
  have hMult : S ∈ Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F true)))
      (levChi _ (R.βY 0) (R.dat0 (R.levR F true))) := hS'.1
  have hcl := Formalism.IndefR.PeterssonHilbertSpace.mult_cont_left (M := R.MY 0) (θ := R.θ) (J := _) (χ := _) hMult v₀
  have hip := hI.2.2 _ S hS' S hS'
  have := Formalism.IndefR.PeterssonHilbertSpace.borel_GA (Yc D 0)
  have hL2 : MemLp (S v₀) 2 (R.ν0.restrict R.fd0) := by
    refine (memLp_two_iff_integrable_sq_norm hcl.1.measurable.aestronglyMeasurable).2
      (((hip v₀ v₀).1).norm.congr (.of_forall fun x => ?_))
    simp only [norm_mul, norm_star, sq]
  obtain ⟨hm, hn⟩ := hTr (S v₀) hcl.1 hcl.2 hL2
  refine ⟨hm, hn.trans (congrArg (c * ·) (re_ipM_eq ⟨_, hip⟩ hv).symm), ?_⟩
  intro h0
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.1 (hI.2.1 _ hS')
  have hx : inner ℂ x x = ipM (R.MY 0) R.ν0 R.fd0 (R.HE.e x) (R.HE.e x) := hM.HE.2.2 x x
  have hre : ‖x‖ ^ 2 = (ipM (R.MY 0) R.ν0 R.fd0 (R.HE.e x) (R.HE.e x)).re := by
    rw [← hx]
    exact (inner_self_eq_norm_sq (𝕜 := ℂ) x).symm
  have h00 : ‖x‖ ^ 2 = 0 := hre.trans h0
  rw [pow_eq_zero_iff two_ne_zero, norm_eq_zero] at h00
  rw [h00]
  exact map_zero R.HE.e

end GlobalTheory.EvalNormTransfer
