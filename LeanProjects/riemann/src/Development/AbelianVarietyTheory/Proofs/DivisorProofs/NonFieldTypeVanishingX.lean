import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TestFnConstTermVanishX
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicAndConstantTermStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonFieldTypeVanishingStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EllipticPartStatement

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Mult Formalism.MainNotions.S
open MeasureTheory IsDedekindDomain NumberField GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.Orb
open GlobalTheory.AutomorphicL2Unitary (starFn)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH)
open GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Proof.parabolic_and_constant_term
section Star
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}
end Star

theorem testFnConstTermVanishX : TestFnConstTermVanishX := by
  intro D V hodd S M T hH U μa _ μf _ f hf 𝔉 hP
  obtain ⟨a, ha0, ha2, hpar⟩ := parabolicAtSplitPlaces D V hodd T 𝔉 hP
  obtain ⟨v, hv⟩ := hH a ha0 (by omega)
  obtain ⟨fa, ff, hfa, hff, rfl⟩ := hf
  obtain ⟨h, hh, e⟩ := hff.2.1 v
  have hA : ∀ w, fa w ∈ CcArch D.sp.cm.sig V.gram w := hfa.mem
  have hF := hff.isFinFamily
  have he := (T.frame v).idem_mem (μf v.1) (T.τ v)
  constructor
  · refine GlobalTheory.T.unipotentIntegrals_pureTensor_vanish_of_local D V 𝔉 fa ff hA hF v.1 fun ν _ x y => ?_
    exact (GlobalTheory.T.typeIdempotent_unipotentIntegral_vanish_splitPlace D V T v a ha0 (by omega) hv 𝔉 (hpar v).1 (μf v.1) _ (conv_mem_SB he hh) (ff v.1) (Or.inr e)
      ν x y).2
  · rw [starFn_tensor]
    refine GlobalTheory.T.unipotentIntegrals_pureTensor_vanish_of_local D V 𝔉 _ _ (fun w => starFn_mem_ccArch (hA w)) (isFinFamily_starFn hF) v.1 fun ν _ x y => ?_
    have e' : starFn (ff v.1) = GlobalTheory.AutomorphicL2Unitary.conv (μf v.1) ((T.frame v).idem (μf v.1) (T.τ v))
        (GlobalTheory.AutomorphicL2Unitary.conv (μf v.1) (starFn h) ((T.frame v).idem (μf v.1) (T.τ v))) := by
      rw [e, starFn_conv, starFn_conv]
      simp only [TypeData.idem, SplitAt.starFn_idem]
    exact (GlobalTheory.T.typeIdempotent_unipotentIntegral_vanish_splitPlace D V T v a ha0 (by omega) hv 𝔉 (hpar v).1 (μf v.1) _ (conv_mem_SB (starFn_mem_SB hh) he) _
      (Or.inl e') ν x y).2

theorem parabolicAndConstTermX : ParabolicAndConstTermX := ⟨parabolicAtSplitPlaces, testFnConstTermVanishX⟩
end GlobalTheory.Proof.parabolic_and_constant_term
end
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.PsCo.Plug.parabolicT : GlobalTheory.IndefiniteRowSideFullHecke.ConstantTermVanishing.ParabolicAndConstTermX := by
  first | exact @GlobalTheory.Proof.parabolic_and_constant_term.parabolicAndConstTermX | exact GlobalTheory.Proof.parabolic_and_constant_term.parabolicAndConstTermX | (intros; apply GlobalTheory.Proof.parabolic_and_constant_term.parabolicAndConstTermX <;> assumption)
end

section
open MeasureTheory Set Filter GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms (plusAlg genAlg)
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalNoFixedVectors (HypH NoFixed radical)
open GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt
open scoped TensorProduct ENNReal
noncomputable section
namespace GlobalTheory.NonFieldType
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {V : HSp D}
set_option maxHeartbeats 4000000 in
theorem productClauseX {S : D.what₂.Tau → SPar} {M : DSModel V S} {T : TypeDataG V} {U : AuxiliaryPlaceHermitianSpace V}
    {μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)} {μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)}
    {μ : Measure (GA D V)} (hμ : IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ)
    {fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ} {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ}
    (ha : IsTestArchGX M μa fa) (hf : IsTestFin T U μf ff)
    {γ : GRat D.sp.cm.sig V.gram} (hγ : IsNonFieldAniso D.sp.cm.sig V.gram γ.1.1) :
    ProductClause μa μf μ fa ff (ratEmb D.sp.cm.sig V.gram γ) := by
  intro dta dtf dt hdt 𝓣 h𝓣
  have hreg := hγ.1
  have hcm := isCMExt_host D
  have hJ := isHermND_gram V
  obtain ⟨hta, htf, htt, -⟩ := id hdt
  have i1 : ∀ w, (dta w).IsMulRightInvariant := fun w =>
    haveI := hta w; isMulRightInvariant_cent (isMulCommutative_cent_HA (isRegSS_projArch_ratEmb hreg w)) _
  have i2 : ∀ v, (dtf v).IsMulRightInvariant := fun v =>
    haveI := htf v; isMulRightInvariant_cent (isMulCommutative_cent_HA (isRegSS_proj_ratEmb hreg v)) _
  have hvol : dt 𝓣 < ⊤ := @covol_lt_top D V γ hγ dt htt 𝓣 h𝓣
  have hfa : ∀ w, Continuous (fa w) ∧ HasCompactSupport (fa w) := fun w =>
    ⟨continuous_of_mem_ccSmooth (continuous_archCoord _ _ w) (ha.mem w), (ha.mem w).1⟩
  have hff : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff := hf.isFinFamily
  have hKv := (regular_semisimple_adelic hcm hJ (frameLat V) γ hreg).1
  have hpa : ∀ w, IsProperOrbit (cent (projArch D.sp.cm.sig V.gram w (ratEmb D.sp.cm.sig V.gram γ)))
      (projArch D.sp.cm.sig V.gram w (ratEmb D.sp.cm.sig V.gram γ)) := fun w =>
    isProperOrbit_GArch hcm hJ (isRegSS_projArch_ratEmb hreg w)
  have hpf : ∀ v, IsProperOrbit (cent (proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ)))
      (proj D.sp.cm.sig V.gram v (ratEmb D.sp.cm.sig V.gram γ)) := fun v =>
    isProperOrbit_GLoc hcm hJ (isRegSS_proj_ratEmb hreg v)
  obtain ⟨-, hoa, hob, h1, hO⟩ := @hasOrbInt_tensor _ _ _ _ _ _ _ _ _ _ (frameLat V) _ μa μf μ _ dta dtf dt fa ff
    hμ hdt i1 i2 hfa hff hKv (fun w => Or.inl (hpa w)) (fun v => Or.inl (hpf v))
  refine ⟨hvol, _, _, hoa, hob, h1, hO, fun 𝓕 h𝓕 => ?_⟩
  have hc := continuous_of_mem_ccAd (tensor_mem_ccAd ha.mem hf.isFinFamily)
  exact @GlobalTheory.T.classTerm_eq_volume_mul_orbitalIntegral (GA D V) _ _ _ _ _ _ _ _ (GQ V) _ (ratEmb D.sp.cm.sig V.gram γ) (ratEmb_mem_GQ γ)
    (isMulCommutative_cent_ratEmb hreg) μ hμ.2.2.1 dt htt 𝓣 h𝓣 hvol _ _ hc.1 hc.2 hO 𝓕 h𝓕
set_option maxHeartbeats 4000000 in

theorem nonFieldTypeVanishingX : NonFieldTypeVanishingX := by
  intro D V _ S M T U hH μa μf μ hμ fa ff ha hf γ hγ
  have hL := localClause (fun v => hμ.2.1 v) hf hγ
  have hP := productClauseX hμ ha hf hγ
  exact ⟨hL, hP, zeroClause hH hγ hL hP⟩
end GlobalTheory.NonFieldType
end
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.PsCo.Plug.nonFieldT : GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt.NonFieldTypeVanishingX := by
  first | exact @GlobalTheory.NonFieldType.nonFieldTypeVanishingX | exact GlobalTheory.NonFieldType.nonFieldTypeVanishingX | (intros; apply GlobalTheory.NonFieldType.nonFieldTypeVanishingX <;> assumption)
end

section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
noncomputable section
namespace GlobalTheory.TrEllSum

theorem ellipticPartX : GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.EllipticPartX := by
  intro D V lam S M T U μa μf μ fa ff h dta dtf dt ht
  obtain ⟨-, -, -, -, hμ, ha, hf⟩ := h
  exact elliptic_expansion (isCMExt_host D) (GlobalTheory.InertOfConj.unram D) (isHermND_gram V) (frameLat V) hμ ha.mem hf.isFinFamily
    dta dtf dt ht _ rfl _ rfl
end GlobalTheory.TrEllSum
end
end

section
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.PsCo.Plug.ellipticT : GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots.EllipticPartX := by
  first | exact @GlobalTheory.TrEllSum.ellipticPartX | exact GlobalTheory.TrEllSum.ellipticPartX | (intros; apply GlobalTheory.TrEllSum.ellipticPartX <;> assumption)
end

section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end
