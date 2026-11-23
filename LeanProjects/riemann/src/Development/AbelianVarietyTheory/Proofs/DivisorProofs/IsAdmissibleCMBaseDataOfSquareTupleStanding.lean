import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsInertPlOfInertOff
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPrimeAdditiveCharacterUnramified
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.TrSumOf
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.FunKit

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.BaseGoodPlace

open GlobalTheory.Idele WithZero
open GlobalTheory.StdDual (codiff codiff_ne_zero)

theorem psiUnr_of_not_le {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : ¬ differentIdeal ℤ (𝓞 D.host.F) ≤ v.asIdeal) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PsiUnr ψ v := by
  classical
  intro x
  have hc := GlobalTheory.SplitUnram.count_codiff_eq_zero v (fun h => hv (Ideal.le_of_dvd h))
  set α : Af D.host.F := GlobalTheory.AdelicU.singleFin v x with hα
  have hαv : α v = x := GlobalTheory.AdelicU.evalV_singleFin_self v x
  have hαw : ∀ w, w ≠ v → α w = 0 := fun w hw => GlobalTheory.AdelicU.evalV_singleFin_ne hw x
  have h := GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1.1 (GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ) α
  have key : (∀ y ∈ v.adicCompletionIntegers D.host.F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v (x * y) = 1) ↔
      ∀ β : Af D.host.F, (∀ w, β w ∈ w.adicCompletionIntegers D.host.F) → ψ (pairA D.host.F 0 (β * α)) = 1 := by
    constructor
    · intro H β hβ
      have e : β * α = GlobalTheory.AdelicU.singleFin v (x * β v) := by
        apply GlobalTheory.AdelicU.af_ext
        intro u
        by_cases hu : u = v
        · subst hu
          rw [map_mul, hα, GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self]
          change β u * x = x * β u
          ring
        · rw [map_mul, hα, GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu, mul_zero]
      rw [e]
      exact H _ (hβ v)
    · intro H y hy
      have e : GlobalTheory.AdelicU.singleFin v y * α = GlobalTheory.AdelicU.singleFin v (x * y) := by
        rw [hα, ← GlobalTheory.AdelicU.singleFin_mul, mul_comm]
      have := H (GlobalTheory.AdelicU.singleFin v y) (fun w => by
        by_cases hw : w = v
        · subst hw
          change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (GlobalTheory.AdelicU.singleFin w y) ∈ _
          rw [GlobalTheory.AdelicU.evalV_singleFin_self]
          exact hy
        · change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (GlobalTheory.AdelicU.singleFin v y) ∈ _
          rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw]
          exact zero_mem _)
      rw [e] at this
      exact this
  rw [key, ← h, mem_adelicIdeal_iff codiff_ne_zero, HeightOneSpectrum.mem_adicCompletionIntegers]
  constructor
  · intro H
    have := H v
    rwa [hc, neg_zero, exp_zero, hαv] at this
  · intro H w
    by_cases hw : w = v
    · subst hw
      rw [hc, neg_zero, exp_zero, hαv]
      exact H
    · rw [hαw w hw, map_zero]
      exact zero_le

end GlobalTheory.BaseGoodPlace

namespace GlobalTheory.BaseGoodPlace

theorem trInf_eq_trace (D : D7) (x : Ainf D.host.F) :
    GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.trInf D x = Algebra.trace ℝ (mixedEmbedding.mixedSpace D.host.F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F x) := by
  classical
  rw [Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi, PI.ProdFormulaE.Tr.trace_pi,
    InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  simp only [Algebra.trace_complex_apply]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.trInf
  rw [← Fintype.sum_subtype_add_sum_subtype (fun w : InfinitePlace D.host.F => w.IsReal)]
  congr 1
  · refine Fintype.sum_congr _ _ fun w => ?_
    rw [InfinitePlace.mult_isReal, Nat.cast_one, one_mul, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply w.2,
      Complex.ofReal_re]
    simp
  · refine Fintype.sum_equiv (Equiv.subtypeEquivRight fun w => InfinitePlace.not_isReal_iff_isComplex) _ _ fun w => ?_
    have h := InfinitePlace.mult_isComplex ⟨w.1, InfinitePlace.not_isReal_iff_isComplex.1 w.2⟩
    simp only at h
    rw [h]
    push_cast
    rfl

end GlobalTheory.BaseGoodPlace

namespace GlobalTheory.BaseGoodPlace

theorem isStd_of_isStdChar {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := by
  refine ⟨hψ.1.1, hψ.1.2.2.1, fun a ha => ?_⟩
  have h2 : a.2 = 0 := by
    have h0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F (pairA D.host.F 0 1) = 0 := by
      show InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (0 : Ainf D.host.F) = 0
      exact map_zero _
    have := congrArg Prod.snd (ha (pairA D.host.F 0 1) h0)
    rw [smul_eq_mul] at this
    have e : (1 : Af D.host.F) * a.2 = 0 := this
    simpa using e
  have ha' : a = pairA D.host.F a.1 0 := Prod.ext rfl h2
  obtain ⟨θ, hθ⟩ := hψ.2.1
  have h := hψ.2.2 θ hθ a.1
  rw [GlobalTheory.DualPairCompare.sum_infFam θ hθ, trInf_eq_trace] at h
  rw [ha']
  change psiInf D.host.F ψ a.1 = _
  rw [h]
  congr 1
  push_cast
  change _ = -(2 * ↑Real.pi * Complex.I) * ((Algebra.trace ℝ (mixedEmbedding.mixedSpace D.host.F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F a.1) : ℝ) : ℂ)
  ring

end GlobalTheory.BaseGoodPlace

namespace GlobalTheory.BaseGoodPlace

theorem exists_ram_prime_of_le (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F))
    (hle : differentIdeal ℤ (𝓞 D.host.F) ≤ v.asIdeal) :
    ∃ p : ℕ, p ∣ D.host.QS * D.host.q * D.host.d ∧ (p : 𝓞 D.host.F) ∈ v.asIdeal := by
  obtain ⟨p, -, h1, h2⟩ := UpperTheory.Ram.Fun.exists_prime_of_different_le D.host v hle
  exact ⟨p, h1, h2⟩

end GlobalTheory.BaseGoodPlace

namespace GlobalTheory.FunObj

theorem base_isGood_of_standing : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (W : G.Weil) (t : T),
    SquareStanding G t → ∀ B : Base D.host.F D.host.E, B.ψ = W.ψ →
      (∀ v ∈ B.P, ∃ w ∈ locPl G t, w.under (𝓞 D.host.F) = v) → B.IsGood D.sp.cm.sig := by
  intro D T L sc G μ₀ _hL W t hS B hB hP
  have hψ : IsStdChar D B.ψ (-1) := hB ▸ W.ψ_std
  refine { cm := GlobalTheory.AdelicU.isCMExt_host D
           galois := D.host.hostE_isGalois
           unram := GlobalTheory.InertOfConj.unram D
           std := GlobalTheory.BaseGoodPlace.isStd_of_isStdChar hψ
           inert := ?_
           psiP := ?_ }
  · intro v w hw
    have hns : ¬ Formalism.MainNotions.KudlaSiegelWeil.Split D v := by
      rintro ⟨w1, w2, hne, h1, h2⟩
      apply hne
      have key : ∀ u : HeightOneSpectrum (𝓞 D.host.E), Formalism.MainNotions.KudlaSiegelWeil.Over D u v → u = w := fun u hu => by
        have hle : w.asIdeal ≤ u.asIdeal := by
          rw [← hw]
          exact Ideal.map_le_iff_le_comap.2 (le_of_eq hu.symm)
        exact HeightOneSpectrum.ext (w.isMaximal.eq_of_le u.isPrime.ne_top hle).symm
      rw [key w1 h1, key w2 h2]
    obtain ⟨h2, h3, hd, -⟩ := Formalism.MainNotions.KudlaSiegelWeil.inert_conditions_hold D v hns
    exact ⟨h2, h3, GlobalTheory.BaseGoodPlace.psiUnr_of_not_le hψ v hd⟩
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := hP v hv
    refine GlobalTheory.BaseGoodPlace.psiUnr_of_not_le hψ _ fun hle => ?_
    obtain ⟨p, hp, hpv⟩ := GlobalTheory.BaseGoodPlace.exists_ram_prime_of_le D _ hle
    have hpw : (p : 𝓞 D.host.E) ∈ w.asIdeal := by
      have h := hpv
      change (p : 𝓞 D.host.F) ∈ w.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) at h
      rwa [Ideal.mem_comap, map_natCast] at h
    apply hS.2 w hw
    obtain ⟨c, hc⟩ := hp
    rw [hc]
    push_cast
    exact w.asIdeal.mul_mem_right _ (w.asIdeal.mul_mem_right _ hpw)

end GlobalTheory.FunObj
