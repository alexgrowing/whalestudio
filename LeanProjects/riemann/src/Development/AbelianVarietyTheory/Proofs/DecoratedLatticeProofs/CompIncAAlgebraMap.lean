import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TiedAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegralPowerExpansion

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
open NumberField IsDedekindDomain
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocMod.SplitCompl

open GlobalTheory.FinPl GlobalTheory.FinPl.SplitPoint GlobalTheory.IdemModTwo GlobalTheory.SplitIdem GlobalTheory.SplitChart GlobalTheory.SplitHecke

variable {D : D7}

theorem incA_algebraMap (t : D.host.F) :
    incA D (algebraMap D.host.F D.host.E t) = algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) t) := by
  rw [← IsScalarTower.algebraMap_apply]
  exact (Algebra.TensorProduct.includeRight (R := D.host.F) (A := AF D.host.F) (B := D.host.E)).commutes t

theorem comp_incA_algebraMap {v : Pl D} {e : AE D} (he : SplitAt D v e) (t : D.host.F) :
    comp he (incA D (algebraMap D.host.F D.host.E t)) = algebraMap D.host.F (Fv D.host.F v) t := by
  rw [incA_algebraMap, comp_algebraMap]
  rfl

def emb {v : Pl D} {e : AE D} (he : SplitAt D v e) : D.host.E →ₐ[D.host.F] Fv D.host.F v :=
  { (comp he).comp (incA D) with commutes' := comp_incA_algebraMap he }

theorem comp_sec {v : Pl D} {e : AE D} (he : SplitAt D v e) (a : Fv D.host.F v) : comp he (sec D v e a) = a := by
  rw [sec_apply, map_mul, comp_fj, comp_self, mul_one, evalV_singleV_same]

theorem sec_comp {v : Pl D} {e : AE D} (he : SplitAt D v e) (x : AE D) : sec D v e (comp he x) = e * x :=
  (sc_spec he x).symm

theorem int_iff_sec {v : Pl D} {e : AE D} (he : SplitAt D v e) (a : Fv D.host.F v) :
    a ∈ 𝒪[Fv D.host.F v] ↔ finPart D (sec D v e a) ∈ intAE D := by
  have h1 := (chart_comp he).2.2.2 (sec D v e a)
  rw [← sec_comp he, comp_sec he] at h1
  rw [h1, isInt_Ov, mem_integer_iff]

def splitPt {v : Pl D} {e : AE D} (h : IsSplitIdem D e) (he : SplitAt D v e)
    (hab : ∃ ε, IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) : SplitPt D (Fv D.host.F v) where
  v := v
  e := e
  split := h
  above := hab
  pr := comp he
  sec := sec D v e
  pr_sec := comp_sec he
  sec_pr := sec_comp he
  cont_pr := continuous_comp he
  cont_sec := continuous_sec
  int_iff := int_iff_sec he

theorem emb_apply {v : Pl D} {e : AE D} (he : SplitAt D v e) (a : D.host.E) : emb he a = comp he (incA D a) := rfl

theorem splitPrime_emb {v : Pl D} {e : AE D} (he : SplitAt D v e) (PP : HeightOneSpectrum (𝓞 D.host.E))
    (h : Formalism.L2.NTheta.IsIdemAt e PP) : GlobalTheory.AdelicU.splitPrime (emb he) = PP := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  by_cases hx : x = 0
  · subst hx; simp only [Submodule.zero_mem]
  rw [GlobalTheory.AdelicU.mem_splitPrime, h.2 x hx, ← sec_comp he, ← emb_apply]
  have h0 : emb he (x : D.host.E) ≠ 0 :=
    (map_ne_zero _).2 (RingOfIntegers.coe_ne_zero_iff.2 hx)
  rw [← int_iff_sec he, mem_integer_iff, HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀, not_le,
    one_lt_inv₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0))]

theorem exists_place : ∀ (D : D7) (PP : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e PP → ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (q : GlobalTheory.FinPl.SplitPt D k), q.e = e ∧ q.v = PP.under (NumberField.RingOfIntegers D.host.F) ∧ (∀ a, (ofSplit q).pr a ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt PP a) ∧ DenseRange (ofSplit q).pr := by
  intro D PP e h
  obtain ⟨-, -, v, ε, hε, hs⟩ := h.1
  have he : SplitAt D v e := splitAt_of h.1 hε hs
  have hP := splitPrime_emb he PP h
  refine ⟨Fv D.host.F v, inferInstance, inferInstance, inferInstance, inferInstance, splitPt h.1 he ⟨ε, hε, hs⟩, rfl, ?_, ?_, ?_⟩
  · show v = _
    rw [← hP, GlobalTheory.AdelicU.splitPrime_under]
  · intro a
    change emb he a ∈ _ ↔ _
    rw [mem_integer_iff, HeightOneSpectrum.mem_adicCompletionIntegers, GlobalTheory.AdelicU.valued_apply_eq_valuation, hP,
      GlobalTheory.Proof.IntegralPowerExpansion.intAt_iff_val]
  · change DenseRange (emb he)
    refine Dense.mono ?_ (HeightOneSpectrum.denseRange_algebraMap D.host.F v)
    rintro _ ⟨t, rfl⟩
    exact ⟨algebraMap D.host.F D.host.E t, (emb he).commutes t⟩
end GlobalTheory.LocMod.SplitCompl
