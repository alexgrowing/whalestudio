import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsReductionActionChosenPlaces
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RedBasicsPf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodAtReductionConjugatedUnitaryElement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAddEquivOfCard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSelfDualHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WBEqPrimeComap
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommTensCastRSymmMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SurjectiveReductionOntoFiniteLevelGroup
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

noncomputable section

namespace GlobalTheory.SplitRes

open IsDedekindDomain

section Cast

variable {E : Type} [Field E] [NumberField E]

theorem tensCastR_comm_symm_tmul_one {F₁ F₂ : Subfield E} (h : F₁ = F₂) (y : E) :
    GlobalTheory.StdFrame.tensCastR h ((Algebra.TensorProduct.comm F₁ (FiniteAdeleRing (𝓞 F₁) F₁) E).symm
      (y ⊗ₜ[F₁] (1 : FiniteAdeleRing (𝓞 F₁) F₁))) = y ⊗ₜ[F₂] (1 : FiniteAdeleRing (𝓞 F₂) F₂) := by
  subst h
  exact (Algebra.TensorProduct.comm F₁ (FiniteAdeleRing (𝓞 F₁) F₁) E).apply_symm_apply _

theorem tensCastR_comm_symm_one_tmul {F₁ F₂ : Subfield E} (h : F₁ = F₂) (c : FiniteAdeleRing (𝓞 F₁) F₁)
    (hc : ∀ v, c v ∈ v.adicCompletionIntegers F₁) :
    ∃ c' : FiniteAdeleRing (𝓞 F₂) F₂, (∀ v, c' v ∈ v.adicCompletionIntegers F₂) ∧
      GlobalTheory.StdFrame.tensCastR h ((Algebra.TensorProduct.comm F₁ (FiniteAdeleRing (𝓞 F₁) F₁) E).symm
        ((1 : E) ⊗ₜ[F₁] c)) = (1 : E) ⊗ₜ[F₂] c' := by
  subst h
  exact ⟨c, hc, (Algebra.TensorProduct.comm F₁ (FiniteAdeleRing (𝓞 F₁) F₁) E).apply_symm_apply _⟩

end Cast

def projE (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) :
    Formalism.IndefR.Lev.EAf D →+* s.v.adicCompletion (maximalRealSubfield D.host.E) :=
  s.proj.comp (GlobalTheory.FixedConj.adeleEquiv D hF).symm.toRingHom

theorem projE_apply (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (x : Formalism.IndefR.Lev.EAf D) :
    projE D hF s x = s.proj (GlobalTheory.StdFrame.tensCastR hF
      ((Algebra.TensorProduct.comm (↥D.host.F) (FiniteAdeleRing (𝓞 ↥D.host.F) ↥D.host.F) D.host.E).symm x)) := rfl

theorem projE_adeleEquiv (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (a : ReciprocityTheory.Aut.AL D.host.E) : projE D hF s (GlobalTheory.FixedConj.adeleEquiv D hF a) = s.proj a := by
  simp [projE]

theorem projE_tmul_one (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (y : D.host.E) : projE D hF s (y ⊗ₜ[↥D.host.F] (1 : Formalism.L2.Herm.Af ↥D.host.F)) = s.i y := by
  rw [projE_apply, tensCastR_comm_symm_tmul_one]
  simp [SplitPlace.proj, Algebra.TensorProduct.lift_tmul]

theorem projE_le_one (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (z : Formalism.IndefR.Lev.EAf D) (hz : z ∈ Formalism.L2.Herm.intAf (↥D.host.F) D.host.E) : Valued.v (projE D hF s z) ≤ 1 := by
  have hle : Formalism.L2.Herm.intAf (↥D.host.F) D.host.E ≤
      (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).toSubring.comap (projE D hF s) := by
    refine Subring.closure_le.2 ?_
    rintro x (⟨⟨_, y, rfl⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩)
    · show projE D hF s _ ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, projE_tmul_one]
      exact s.split_le_one y
    · show projE D hF s _ ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)
      obtain ⟨c', hc', e⟩ := tensCastR_comm_symm_one_tmul hF c hc
      rw [projE_apply, e]
      simp only [SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      exact hc' s.v
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hle hz)

theorem projE_lt_one (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (z : Formalism.L2.Herm.intAf (↥D.host.F) D.host.E) (hz : z ∈ Formalism.L2.DIV.idS (↥D.host.F) s.w.asIdeal) :
    Valued.v (projE D hF s (z : Formalism.IndefR.Lev.EAf D)) < 1 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Formalism.L2.DIV.oToS_coe, projE_tmul_one]
    exact hy
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Subring.coe_add, map_add]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hx hy)
  | smul c x _ hx =>
    rw [smul_eq_mul, Subring.coe_mul, map_mul, map_mul]
    calc Valued.v (projE D hF s (c : Formalism.IndefR.Lev.EAf D)) * Valued.v (projE D hF s (x : Formalism.IndefR.Lev.EAf D))
        ≤ 1 * Valued.v (projE D hF s (x : Formalism.IndefR.Lev.EAf D)) := by
          gcongr
          exact projE_le_one D hF s _ c.2
      _ < 1 := by rwa [one_mul]

theorem resS_adeleEquiv_eq_natCast : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (a : ReciprocityTheory.Aut.AL D.host.E) (ha : GlobalTheory.FixedConj.adeleEquiv D hF a ∈ Formalism.L2.Herm.intAf (↥D.host.F) D.host.E) (m : ℕ), a ∈ ReciprocityTheory.Aut.ALint D.host.E → Valued.v (s.proj a - (m : s.v.adicCompletion (maximalRealSubfield D.host.E))) < 1 → Formalism.L2.DIV.resS (↥D.host.F) s.w ⟨_, ha⟩ = (m : Formalism.L2.DIV.kP s.w) := by
  intro D hF s a ha m _hA hm
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (Formalism.L2.DIV.resS (↥D.host.F) s.w ⟨_, ha⟩)
  have e1 : Formalism.L2.DIV.cmpS (↥D.host.F) s.w.asIdeal (Formalism.L2.DIV.resS (↥D.host.F) s.w ⟨_, ha⟩) =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS (↥D.host.F) s.w.asIdeal) ⟨_, ha⟩ :=
    (RingEquiv.ofBijective (Formalism.L2.DIV.cmpS (↥D.host.F) s.w.asIdeal)
      (Formalism.L2.DIV.cmpS_bij (F := ↥D.host.F) s.w.asIdeal s.w.ne_bot)).apply_symm_apply _
  have e2 : Formalism.L2.DIV.cmpS (↥D.host.F) s.w.asIdeal (Ideal.Quotient.mk s.w.asIdeal b) =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS (↥D.host.F) s.w.asIdeal) (Formalism.L2.DIV.oToS (↥D.host.F) D.host.E b) :=
    Ideal.quotientMap_mk
  have hmem : (⟨_, ha⟩ : Formalism.L2.Herm.intAf (↥D.host.F) D.host.E) - Formalism.L2.DIV.oToS (↥D.host.F) D.host.E b ∈
      Formalism.L2.DIV.idS (↥D.host.F) s.w.asIdeal := by
    refine Ideal.Quotient.eq.1 ?_
    exact e1.symm.trans ((congrArg (Formalism.L2.DIV.cmpS (↥D.host.F) s.w.asIdeal) hb.symm).trans e2)
  have h1 : Valued.v (s.proj a - s.i (algebraMap (𝓞 D.host.E) D.host.E b)) < 1 := by
    have := projE_lt_one D hF s _ hmem
    rwa [AddSubgroupClass.coe_sub, map_sub, Formalism.L2.DIV.oToS_coe, projE_tmul_one, projE_adeleEquiv] at this
  have h2 : b - (m : 𝓞 D.host.E) ∈ s.w.asIdeal := by
    show Valued.v (s.i ((b - (m : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E)) < 1
    have e : s.i ((b - (m : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E) =
        (s.proj a - (m : s.v.adicCompletion (maximalRealSubfield D.host.E))) -
          (s.proj a - s.i (algebraMap (𝓞 D.host.E) D.host.E b)) := by
      rw [RingOfIntegers.coe_eq_algebraMap, map_sub, map_sub, map_natCast, map_natCast]
      ring
    rw [e]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hm h1)
  rw [← hb, ← map_natCast (Ideal.Quotient.mk s.w.asIdeal) m, Ideal.Quotient.eq]
  exact h2

end GlobalTheory.SplitRes

end
