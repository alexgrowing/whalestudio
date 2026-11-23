import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenPtSubset
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

namespace GlobalTheory.IdemAtPl

theorem eq_atPl_of_isIdemAt {D : D7} {e : AE D} {P : Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt e P) : e = atPl P 1 := by
  classical
  refine ae_ext ?_ fun Q => ?_
  · rw [GlobalTheory.SplitScalar.infPart_splitIdem h.1, (atPl_spec P 1).1]
  · rw [(atPl_spec P 1).2]
    by_cases hQ : Q = P
    · subst hQ
      rw [(cpt_of_isIdemAt h).1, Pi.single_eq_same]
    · rw [(cpt_of_isIdemAt h).2 Q hQ, Pi.single_eq_of_ne hQ]

theorem eq_liftV_of_isPlaceIdem {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}
    (h : IsPlaceIdem D v ε) : ε = GlobalTheory.LatVac.liftV v 1 := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  have hα : α = GlobalTheory.AdelicU.singleFin v 1 := GlobalTheory.AdelicU.af_ext fun u => by
    by_cases hu : u = v
    · subst hu
      rw [h1, GlobalTheory.AdelicU.evalV_singleFin_self]
    · rw [h0 u hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu]
  subst hα
  rfl

theorem main : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ t : T,
    (∀ w ∈ locPl G t, IsSplitIdem D (atPl w 1) ∧ atPl w 1 + cA D (atPl w 1) =
      algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV (w.under (𝓞 D.host.F)) 1)) ∧
    ∀ ε, IsIdemSum ε (locPl G t) → ε = ∑ w ∈ locPl G t, atPl w 1 ∧ ∀ w ∈ locPl G t, ε * atPl w 1 = atPl w 1 := by
  intro D T L sc G μ₀ hL t
  classical
  obtain ⟨_, ⟨es, hes, -⟩, -⟩ := GlobalTheory.FunObj.LocTensor.exists_idemSum_locPl hL G t
  refine ⟨fun w hw => ?_, fun ε hε => ?_⟩
  · have h := hes w hw
    rw [← eq_atPl_of_isIdemAt h]
    obtain ⟨v, ε, hε, he⟩ := h.1.2.2
    refine ⟨h.1, ?_⟩
    rw [he, eq_liftV_of_isPlaceIdem hε, GlobalTheory.IdemUnder.under_eq_of_isIdemAt D _ w v ε h hε he]
  · obtain ⟨⟨fs, hfs, rfl⟩, -⟩ := hε
    have hf : ∀ PP ∈ locPl G t, fs PP = atPl PP 1 := fun PP hPP => eq_atPl_of_isIdemAt (hfs PP hPP)
    refine ⟨Finset.sum_congr rfl hf, fun w hw => ?_⟩
    rw [Finset.sum_congr rfl hf]
    refine ae_ext ?_ fun Q => ?_
    · rw [map_mul, (atPl_spec w 1).1, mul_zero]
    · rw [map_mul, map_mul, (atPl_spec w 1).2, map_sum, map_sum]
      by_cases hQ : Q = w
      · subst hQ
        rw [Pi.single_eq_same, mul_one, Finset.sum_eq_single Q (fun b _ hb => by
          rw [(atPl_spec b 1).2, Pi.single_eq_of_ne (Ne.symm hb)]) (fun h => absurd hw h),
          (atPl_spec Q 1).2, Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hQ, mul_zero]

end GlobalTheory.IdemAtPl
