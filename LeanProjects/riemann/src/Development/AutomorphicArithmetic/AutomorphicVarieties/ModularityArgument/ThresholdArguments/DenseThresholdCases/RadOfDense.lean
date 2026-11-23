import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.SubalgebraIntegrality.RadOfDense
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.NumJ
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevelRelationTwoX
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryHeckeData
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PointTheoremBaseObject
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HdEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsHeckeIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.JEnd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TJDense
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.THasAutOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLevelU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TJRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HeckePolyCoeffZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.JTwistA
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TDenseU
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PaLevel
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocalLanglandsGLOfPrints

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Z.J.D
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
private theorem coef_isCoef (l : ℕ) [hl : Fact l.Prime] (c : Coef l) : Pa.IsCoef l c.O := by
  obtain ⟨hc, hf, hlm, -, -, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  refine ⟨hc, hf, (CharP.charP_iff_prime_eq_zero hl.out).2 ?_⟩
  rw [← map_natCast (IsLocalRing.residue c.O), IsLocalRing.residue_eq_zero_iff]
  exact hlm
private theorem locP_of (P : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : _root_.UpperTheory.V.Pa.LocPAlt :=
  ⟨P.loc.bz, P.loc.geo, GlobalTheory.Published.TameLocal_of_duality P.coh.lt⟩
private theorem rad_of_dense {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : Resid V.frame c.O n} (B : UniversalOrdinaryDeterminantRing r)
    (J : Ideal B.B) (h : B.Dense J) : J.IsRadical := by
  rintro b ⟨k, hk⟩
  refine h (fun _ j _ => ((j : ℕ) : ℤ)) (fun _ _ i j hij => Int.ofNat_lt.2 hij) b fun x hx _ => ?_
  have h1 : x (b ^ k) = 0 := hx hk
  rw [map_pow] at h1
  exact IsReduced.eq_zero _ ⟨k, h1⟩
private theorem cohP_of (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : Pa.CohP :=
  ⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.gw, hN.coh.pt, GlobalTheory.Published.TameLocal_of_duality hN.coh.lt⟩
theorem UpperTheory.V.Z.J.D.modularity_n_of_num_j_printed_mult_comp :
    _root_.UpperTheory.V.Z.J.D.NumJAlt → _root_.UpperTheory.V.Af.HypothesesH' → UpperTheory.V.Z.Mult.Mult → UpperTheory.V.Z.Mult.CompOf → _root_.UpperTheory.V.J.ModNAlt := by
  intro hN P hM hC l _ L Ω _ _ _ _ _ _ s V hS hμ c _ r hv B Λ ι
  have hn : 1 ≤ 3 := by norm_num
  obtain ⟨R⟩ := _root_.UpperTheory.V.Hi.nonempty_unitaryHeckeData P l L Ω s 3 hn V (QData.empty V hS) c r ι Λ
  let K : (hset (QData.empty V hS) R.τ₀).Lev := ⟨fun q => Empty.elim q, fun q => Empty.elim q⟩
  obtain ⟨J, hJ⟩ := _root_.UpperTheory.V.Hi.exists_hecke_ideal P l L Ω s 3 hn V _ c r ι B Λ R K
  have hE := _root_.UpperTheory.Gal.projectedFormsSystemPart.decomposition_and_automorphicAway_of_isJ P l L Ω s 3 hn V _ c r ι B Λ R K hS J hJ
  haveI := coef_isCoef l c
  have hD := _root_.UpperTheory.V.Hi.dense_of_is_j_unitary_hecke_data P l L Ω s 3 hn V _ c r ι B Λ R K hS J hJ
  have hA := _root_.UpperTheory.V.Pa.has_automorphy_of_statement (locP_of P.litN) l L Ω s V c.O 3 r B J hS (_root_.UpperTheory.V.Hi.level_of_is_j_unitary_hecke_data P l L Ω s 3 hn V _ c r ι B Λ R K hS J hJ)
  obtain ⟨h1, h3⟩ := Pa.pFromAut (cohP_of P.litN) l L Ω s V c.O 3 r B J hn hS (W.locCFT P.litN.aut.art (cohP_of P.litN) l L Ω s)
    ((W.muL l L Ω s V).1 hμ) hA
  exact ⟨J, ⟨⟨_root_.UpperTheory.V.Hi.ring_props_of_is_j_unitary_hecke_data P l L Ω s 3 hn V _ c r ι B Λ R K hS J hJ, hD,
    _root_.UpperTheory.V.Hi.hecke_ideal_point_properties P l L Ω s 3 hn V _ c r ι B Λ R K hS J hJ, hE.1, hE.2, _root_.UpperTheory.V.Z.Desc.W.twistOk_of_isJ P l L Ω s 3 hn V _ c r ι B Λ R K hS J hJ⟩, h1, h3⟩,
    hN P hM hC l L Ω s 3 hn V hS (by norm_num) _ c r ι B Λ R K J hv
      (_root_.UpperTheory.V.Hi.isDomain_and_denseWt_of_isTheta P.litN l L Ω s 3 hn V _ c R.m R.τ₀ r Λ R.θ R.theta).1 hJ (rad_of_dense B J hD)⟩
end
