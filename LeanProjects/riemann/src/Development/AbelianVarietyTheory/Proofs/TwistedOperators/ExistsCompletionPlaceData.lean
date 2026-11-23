import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesSplitIdempotentSum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFiniteParts
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousSymmFinite
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil

noncomputable section

namespace GlobalTheory.PlcAtW

variable {D : D7}

open Classical in

theorem cpt_atPl_self (w : Pl D.host.E) (x : Kw w) : cpt w (toEAf D (atPl w x)) = x := by
  rw [(atPl_spec w x).2 w, Pi.single_eq_same]

theorem atPl_zero (w : Pl D.host.E) : atPl w (0 : Kw w) = 0 := by
  have h := atPl_add w 0 0
  rw [add_zero] at h
  exact (add_eq_left.1 h.symm)

def atPlHom (w : Pl D.host.E) : Kw w →+ AE D where
  toFun := atPl w
  map_zero' := atPl_zero w
  map_add' := atPl_add w

theorem atPl_cpt (w : Pl D.host.E) (a : AE D) : atPl w (cpt w (toEAf D a)) = atPl w 1 * a := by
  classical
  refine ae_ext ?_ fun Q => ?_
  · rw [(atPl_spec w _).1, map_mul, (atPl_spec w 1).1, zero_mul]
  · rw [(atPl_spec w _).2 Q, map_mul, map_mul, (atPl_spec w 1).2 Q]
    by_cases hQ : Q = w
    · subst hQ
      rw [Pi.single_eq_same, Pi.single_eq_same, one_mul]
    · rw [Pi.single_eq_of_ne hQ, Pi.single_eq_of_ne hQ, zero_mul]

theorem valuation_le_of_inv_mul {k : Type} [Field k] [ValuativeRel k] (u : kˣ) (b : k)
    (h : ValuativeRel.valuation k (((u⁻¹ : kˣ) : k) * b) ≤ 1) :
    ValuativeRel.valuation k b ≤ ValuativeRel.valuation k (u : k) := by
  have hne : ValuativeRel.valuation k (u : k) ≠ 0 := by simp
  rw [Valuation.map_mul, Units.val_inv_eq_inv_val, map_inv₀] at h
  calc ValuativeRel.valuation k b
      = ValuativeRel.valuation k (u : k) * ((ValuativeRel.valuation k (u : k))⁻¹ * ValuativeRel.valuation k b) := by
        rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    _ ≤ ValuativeRel.valuation k (u : k) * 1 := by gcongr
    _ = _ := mul_one _

theorem cpt_atPl_mul (w : Pl D.host.E) (x : Kw w) (z : AE D) :
    cpt w (toEAf D (atPl w x * z)) = x * cpt w (toEAf D z) := by
  rw [map_mul, map_mul, cpt_atPl_self]

theorem valuation_cpt_le_one (w : Pl D.host.E) (x : AE D) (h : finPart D x ∈ intAE D) :
    ValuativeRel.valuation (Kw w) (cpt w (toEAf D x)) ≤ 1 := by
  have h2 := ((GlobalTheory.StdFrames.comp_toAd D).int x).1 h w
  have h3 : cpt w (toEAf D x) ∈ (ValuativeRel.valuation (Kw w)).integer :=
    (GlobalTheory.FinPl.SplitPoint.mem_integer_iff D.host.E w _).2 h2
  exact h3

end GlobalTheory.PlcAtW

open scoped TensorProduct

namespace GlobalTheory.PlcAtW

variable {D : D7}

open scoped Topology in

theorem continuous_cpt_toEAf (w : Pl D.host.E) : Continuous fun a : AE D => cpt w (toEAf D a) := by
  letI tf : TopologicalSpace (Af D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E)
  letI ti : TopologicalSpace (Ainf D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Ainf D.host.F) (Ainf D.host.F ⊗[D.host.F] D.host.E)
  obtain ⟨e, he, hec, -⟩ : ∃ e : AE D ≃+* (Ainf D.host.F ⊗[D.host.F] D.host.E) × (Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ z, (e z).1 = infPart D z ∧ (e z).2 = finPart D z) ∧ Continuous e ∧ Continuous e.symm :=
    GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hfc : Continuous (finPart D) := by
    have : (finPart D : AE D → _) = fun z => (e z).2 := funext fun z => (he z).2.symm
    rw [this]
    exact continuous_snd.comp hec
  have h1 : IsOpen {z : Af D.host.F ⊗[D.host.F] D.host.E | z ∈ intAE D} := by
    have := GlobalTheory.IdeleParts.isOpen_nsmul_adelicCompletion_integers D.host.F D.host.E 1 one_pos
    rw [← GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers] at this
    convert this using 1
    ext z
    simp
  haveI : MulArchimedean (ValuativeRel.ValueGroupWithZero (Kw w)) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.1 inferInstance
  let f : AE D →+ Kw w := ((cpt w).comp (toEAf D)).toAddMonoidHom
  refine continuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero]
  refine (IsValuativeTopology.hasBasis_nhds_zero (Kw w)).tendsto_right_iff.2 fun γ _ => ?_
  have hϖ : ValuativeRel.valuation (Kw w) (unifAt w : Kw w) < 1 := by
    rw [isUnif_unifAt w]
    exact ValuativeRel.uniformizer_lt_one
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hϖ γ
  set u : (Kw w)ˣ := unifAt w ^ n
  have hu : ValuativeRel.valuation (Kw w) (u : Kw w) < γ := by
    simpa [u, Units.val_pow_eq_pow_val, map_pow] using hn
  have hU : {z : AE D | finPart D (atPl w ((u⁻¹ : (Kw w)ˣ) : Kw w) * z) ∈ intAE D} ∈ 𝓝 (0 : AE D) := by
    refine IsOpen.mem_nhds (h1.preimage (hfc.comp (continuous_const.mul continuous_id))) ?_
    simp only [Set.mem_setOf_eq, mul_zero, map_zero]
    exact zero_mem _
  filter_upwards [hU] with z hz
  have h3 := valuation_cpt_le_one w _ hz
  rw [cpt_atPl_mul] at h3
  exact (valuation_le_of_inv_mul u _ h3).trans_lt hu

end GlobalTheory.PlcAtW

namespace GlobalTheory.PlcAtW

variable {D : D7}

theorem continuous_atPl (w : Pl D.host.E) : Continuous (atPl (D := D) w) := by
  classical
  letI tf : TopologicalSpace (Af D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E)
  letI ti : TopologicalSpace (Ainf D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Ainf D.host.F) (Ainf D.host.F ⊗[D.host.F] D.host.E)
  obtain ⟨e, he, -, hes⟩ : ∃ e : AE D ≃+* (Ainf D.host.F ⊗[D.host.F] D.host.E) × (Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ z, (e z).1 = infPart D z ∧ (e z).2 = finPart D z) ∧ Continuous e ∧ Continuous e.symm :=
    GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hs : Function.Bijective (Formalism.IndefR.Lev.swapAE D) :=
    (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).bijective
  have ht : Function.Bijective (toAd D) :=
    ⟨GlobalTheory.AdeleBaseChange.map_injective (toAd_spec D), GlobalTheory.AdeleBaseChange.map_surjective (toAd_spec D)⟩
  let R : Af D.host.F ⊗[D.host.F] D.host.E ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
    RingEquiv.ofBijective ((toAd D).comp (Formalism.IndefR.Lev.swapAE D)) (ht.comp hs)
  have hfin : ∀ y, finPart D (e.symm (0, y)) = y := fun y => by
    rw [← (he _).2, RingEquiv.apply_symm_apply]
  have hR : Continuous R.symm := by
    refine GlobalTheory.AdeleBaseChange.continuous_symm_finite D.host.F D.host.E R fun y => ?_
    have key := (GlobalTheory.StdFrames.comp_toAd D).int (e.symm (0, y))
    rw [hfin] at key
    have e1 : ((toAd D).comp (toEAf D)) (e.symm (0, y)) = R y := by
      show toAd D (Formalism.IndefR.Lev.swapAE D (finPart D (e.symm (0, y)))) = toAd D (Formalism.IndefR.Lev.swapAE D y)
      rw [hfin]
    rw [e1] at key
    exact key
  have hform : ∀ x, atPl w x = e.symm (0, R.symm (singleV D.host.E w x)) := fun x => by
    refine ae_ext ?_ fun Q => ?_
    · rw [(atPl_spec w x).1, ← (he _).1, RingEquiv.apply_symm_apply]
    · rw [(atPl_spec w x).2 Q]
      show _ = toAd D (Formalism.IndefR.Lev.swapAE D (finPart D (e.symm (0, R.symm (singleV D.host.E w x))))) Q
      rw [hfin]
      show _ = R (R.symm (singleV D.host.E w x)) Q
      rw [RingEquiv.apply_symm_apply]
      by_cases hQ : Q = w
      · subst hQ
        rw [Pi.single_eq_same]
        exact (RestrictedProduct.single_eq_same _ _ _).symm
      · rw [Pi.single_eq_of_ne hQ]
        exact (RestrictedProduct.single_eq_of_ne _ _ hQ).symm
  rw [funext hform]
  exact hes.comp (continuous_const.prodMk (hR.comp (GlobalTheory.FinPl.SplitPoint.continuous_single_at D.host.E w)))

end GlobalTheory.PlcAtW

namespace GlobalTheory.PlcAtW

theorem exists_plc : ∀ (D : D7) (w : Pl D.host.E) (e : AE D), IsIdemSum e {w} → ∃ p : Place D (Kw w), IsPlc w p ∧ p.e = e := by
  intro D w e he
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  rw [Finset.sum_singleton]
  have h := hes w (Finset.mem_singleton_self w)
  have he1 := GlobalTheory.IdemAtPl.eq_atPl_of_isIdemAt h
  refine ⟨{ e := es w
            split := h.1
            π := (cpt w).comp (toEAf D)
            ι := atPlHom w
            π_ι := cpt_atPl_self w
            ι_π := fun a => by
              show atPl w (cpt w (toEAf D a)) = es w * a
              rw [atPl_cpt, ← he1]
            cont_π := continuous_cpt_toEAf w
            cont_ι := continuous_atPl w }, ⟨h, fun _ => rfl, fun _ => rfl⟩, rfl⟩

end GlobalTheory.PlcAtW

end
