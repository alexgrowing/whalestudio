import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementB
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionHypothesesOfLevelOne
import Formalism.GaussJetBounds.GaussJetProofs.Transfer
import Formalism.SharpRestriction.Divisibility.JetPolynomialLogs.LetterLogIntegrality

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd.StdHyp

open Formalism.DworkPowerSeriesWeights (BHyp NoLowBidegree degE degO letterLog mvExp de1 de2 Integral torus lw V2)
open Formalism.MainNotions.DIV.Bridge.LetterLogIntegrality (eV coeff_subst_scale lw_twist cobX_eq cobY_eq jetLog_rename coeff_subst_rename
  hasSubst_XeV letterLog_cc jetLogG_cc)

theorem kur_sub_wfrac (l : ℕ) [Fact l.Prime] : ∀ x ∈ MaximalUnramifiedExtension l, x ∈ product_zeroth_first_parts.Wfrac l := by
  have hS : {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ ¬ l ∣ n ∧ ζ ^ n = 1} = product_zeroth_first_parts.rootsPrimeTo l := by
    ext ζ
    simp only [Set.mem_setOf_eq, product_zeroth_first_parts.rootsPrimeTo]
    refine exists_congr fun n => and_congr_right fun _ => and_congr_left fun _ => ?_
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)]
  have halg : ∀ x ∈ product_zeroth_first_parts.rootsPrimeTo l, IsAlgebraic ℚ_[l] x := by
    rintro x ⟨n, hn, -, hx⟩
    exact (IsIntegral.of_pow hn (by rw [hx]; exact isIntegral_one)).isAlgebraic
  have hsub : (Subfield.closure (product_zeroth_first_parts.rootsPrimeTo l) : Set ℂ_[l]) ⊆ Algebra.adjoin ℚ_[l] (product_zeroth_first_parts.rootsPrimeTo l) := by
    intro x hx
    have h1 : Subfield.closure (product_zeroth_first_parts.rootsPrimeTo l) ≤
        (IntermediateField.adjoin ℚ_[l] (product_zeroth_first_parts.rootsPrimeTo l)).toSubfield :=
      Subfield.closure_le.mpr (IntermediateField.subset_adjoin _ _)
    have h2 := h1 hx
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg]
    exact h2
  intro x hx
  unfold MaximalUnramifiedExtension at hx
  rw [hS] at hx
  unfold product_zeroth_first_parts.Wfrac
  have hc : x ∈ closure (Subfield.closure (product_zeroth_first_parts.rootsPrimeTo l) : Set ℂ_[l]) := hx
  exact closure_mono hsub hc

theorem b3_of_noLowBidegree (l d : ℕ) [Fact l.Prime] [NeZero d] (be : MvPowerSeries (ZMod d) ℂ_[l])
    (h : NoLowBidegree be) : product_zeroth_first_parts.B3 l d be := by
  intro n hn
  obtain ⟨h1, h2, h3⟩ := h n hn
  have e1 : (product_zeroth_first_parts.bideg d n).1 = degE n := by
    unfold product_zeroth_first_parts.bideg degE
    simp only [Nat.even_iff]
    exact Finsupp.sum_fintype _ _ (by intro s; split_ifs <;> rfl)
  have e2 : (product_zeroth_first_parts.bideg d n).2 = degO n := by
    unfold product_zeroth_first_parts.bideg degO
    simp only [Nat.even_iff]
    exact Finsupp.sum_fintype _ _ (by intro s; split_ifs <;> rfl)
  refine ⟨by rw [e1]; exact h1.ne', by rw [e2]; exact h2.ne', ?_⟩
  intro hb
  apply h3
  have a := congrArg Prod.fst hb
  have b := congrArg Prod.snd hb
  exact ⟨e1 ▸ a, e2 ▸ b⟩

theorem b2_of_subst_torus_eq (l d : ℕ) [Fact l.Prime] [NeZero d] (ζ : ℂ_[l]) (hζ : IsPrimitiveRoot ζ (l ^ d - 1))
    (be : MvPowerSeries (ZMod d) ℂ_[l]) (h : MvPowerSeries.subst (torus l ζ) be = be) : product_zeroth_first_parts.B2 l d be := by
  intro u hu m
  haveI : NeZero (l ^ d - 1) := ⟨by
    have h1 := (Fact.out : l.Prime).one_lt
    have : 1 < l ^ d := Nat.one_lt_pow (NeZero.ne d) h1
    omega⟩
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hu
  have hm := congrArg (MvPowerSeries.coeff m) h
  have e : (torus l ζ : ZMod d → MvPowerSeries (ZMod d) ℂ_[l]) =
      fun s => MvPowerSeries.C (ζ ^ lw l s) * MvPowerSeries.X s := rfl
  rw [e, coeff_subst_scale] at hm
  by_cases hc : MvPowerSeries.coeff m be = 0
  · rw [hc, zero_mul]
  have hP : (m.prod fun s k => (ζ ^ lw l s) ^ k) = 1 :=
    mul_right_cancel₀ hc (by rw [one_mul]; exact hm)
  have hT : (m.prod fun s n => product_zeroth_first_parts.twist l d (ζ ^ i) s ^ n) = (m.prod fun s k => (ζ ^ lw l s) ^ k) ^ i := by
    unfold Finsupp.prod
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun s _ => ?_
    show product_zeroth_first_parts.twist l d (ζ ^ i) s ^ m s = ((ζ ^ lw l s) ^ m s) ^ i
    rw [← lw_twist]
    simp only [← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  rw [hT, hP, one_pow, mul_one]

theorem b4_of_coeff_subst_letterLog (l d : ℕ) [Fact l.Prime] [NeZero d] (D : MvPowerSeries (V2 d) ℂ_[l])
    (hD0 : MvPowerSeries.constantCoeff D = 0)
    (hW : ∀ n, MvPowerSeries.coeff n (MvPowerSeries.subst (letterLog (K := ℂ_[l]) l) (mvExp D)) ∈ product_zeroth_first_parts.Wint l)
    (h1 : MvPowerSeries.constantCoeff (MvPowerSeries.subst (letterLog (K := ℂ_[l]) l) (mvExp D)) = 1) :
    product_zeroth_first_parts.OverWOne l (MvPowerSeries.subst (Formalism.BasicNotions.jetLogG l d (β := Fin 2))
      (product_zeroth_first_parts.expS ℂ_[l] (MvPowerSeries.subst (fun u : Bool × ZMod d => (MvPowerSeries.X (eV d u) :
        MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) D))) := by
  have hb := hasSubst_XeV l d
  have hbs : MvPowerSeries.HasSubst (fun w : ZMod d × Fin 2 => (MvPowerSeries.X ((eV d).symm w) :
      MvPowerSeries (V2 d) ℂ_[l])) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun w => by simp)
  have hJ : MvPowerSeries.HasSubst (Formalism.BasicNotions.jetLogG l d (β := Fin 2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (jetLogG_cc l d)
  have hD : MvPowerSeries.HasSubst (fun _ : Unit => D) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hD0)
  have hLr : MvPowerSeries.HasSubst (fun v : ZMod d × Fin 2 => letterLog (K := ℂ_[l]) l ((eV d).symm v)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun v => letterLog_cc l d _)
  have hrn : (fun v : ZMod d × Fin 2 => MvPowerSeries.subst (fun w : ZMod d × Fin 2 => (MvPowerSeries.X ((eV d).symm w) :
      MvPowerSeries (V2 d) ℂ_[l])) (Formalism.BasicNotions.jetLogG l d (β := Fin 2) v)) =
      fun v => letterLog (K := ℂ_[l]) l ((eV d).symm v) := by
    funext v
    have := jetLog_rename l d ((eV d).symm v)
    rwa [Equiv.apply_symm_apply] at this
  have hexp : product_zeroth_first_parts.expS ℂ_[l] (MvPowerSeries.subst (fun u : Bool × ZMod d => (MvPowerSeries.X (eV d u) :
        MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) D) =
      MvPowerSeries.subst (fun u : Bool × ZMod d => (MvPowerSeries.X (eV d u) :
        MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) (mvExp D) := by
    unfold product_zeroth_first_parts.expS mvExp PowerSeries.subst
    rw [MvPowerSeries.subst_comp_subst_apply hD hb]
  have key : MvPowerSeries.subst (fun w : ZMod d × Fin 2 => (MvPowerSeries.X ((eV d).symm w) :
      MvPowerSeries (V2 d) ℂ_[l])) (MvPowerSeries.subst (Formalism.BasicNotions.jetLogG l d (β := Fin 2))
        (product_zeroth_first_parts.expS ℂ_[l] (MvPowerSeries.subst (fun u : Bool × ZMod d => (MvPowerSeries.X (eV d u) :
          MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) D))) =
      MvPowerSeries.subst (letterLog (K := ℂ_[l]) l) (mvExp D) := by
    rw [hexp, MvPowerSeries.subst_comp_subst_apply hJ hbs, hrn, MvPowerSeries.subst_comp_subst_apply hb hLr]
    congr 1
    funext u
    rw [MvPowerSeries.subst_X hLr, Equiv.symm_apply_apply]
  refine ⟨fun n => ?_, ?_⟩
  · have := hW (Finsupp.equivMapDomain (eV d).symm n)
    rw [← key, coeff_subst_rename, Equiv.symm_symm, ← Finsupp.equivMapDomain_trans] at this
    simpa using this
  · have e := congrArg (MvPowerSeries.coeff 0) key
    rw [coeff_subst_rename, Finsupp.equivMapDomain_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at e
    rw [e, h1]

end GlobalTheory.KerStd.StdHyp

namespace GlobalTheory.KerStd

open Formalism.DworkPowerSeriesWeights (NoLowBidegree)
open Formalism.DworkPowerSeriesWeights.Transfer (map_defectOne map_defectTwo map_logExp constantCoeff_defectOne constantCoeff_defectTwo cc_of_noLow map_torus cc_torus)

theorem bHyps_of_beStd : ∀ (l d : ℕ) [Fact l.Prime] [NeZero d] (be : MvPowerSeries (ZMod d) ℂ_[l]), 5 ≤ l → 2 ≤ d →
    Even d → BeStd l d be → product_zeroth_first_parts.B1 l d be ∧ product_zeroth_first_parts.B2 l d be ∧ product_zeroth_first_parts.B3 l d be ∧ product_zeroth_first_parts.B4 l d be := by
  intro l d _ _ be _ hd2 hde hstd
  obtain ⟨σ, F, be0, om, oms, ζ, ⟨hσ, hF, hF1, -, hO, -, hζ⟩, rfl⟩ := hstd
  obtain ⟨-, h2, h3, ⟨h4, h4'⟩, ⟨h5, h5'⟩⟩ := Formalism.L2.Th1.D.biextension_hypotheses_of_level_one (MaximalUnramifiedExtension l) l d σ hσ hd2 hde F hF be0 hF1
    (Fin (d / 2)) om oms hO ζ hζ
  have hbe : beOf l d σ be0 om oms ζ =
      MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (Formalism.L2.Th1.D.beMean (d := d) l σ be0 om oms ζ) := rfl
  rw [hbe]
  have hc := cc_of_noLow h3
  have hc' : MvPowerSeries.constantCoeff
      (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (Formalism.L2.Th1.D.beMean (d := d) l σ be0 om oms ζ)) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, hc, map_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m
    rw [MvPowerSeries.coeff_map]
    exact StdHyp.kur_sub_wfrac l _ (SetLike.coe_mem _)
  · have ht := congrArg (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype) h2
    rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (cc_torus l ζ))] at ht
    simp only [map_torus] at ht
    exact StdHyp.b2_of_subst_torus_eq l d _ (hζ.map_of_injective (MaximalUnramifiedExtension l).subtype.injective) _ ht
  · apply StdHyp.b3_of_noLowBidegree
    intro n hn
    refine h3 n ?_
    intro h0
    rw [MvPowerSeries.coeff_map, h0, map_zero] at hn
    exact hn rfl
  · unfold product_zeroth_first_parts.B4
    rw [Formalism.MainNotions.DIV.Bridge.LetterLogIntegrality.cobX_eq, Formalism.MainNotions.DIV.Bridge.LetterLogIntegrality.cobY_eq]
    constructor
    · refine StdHyp.b4_of_coeff_subst_letterLog l d _ (constantCoeff_defectOne hc') (fun n => ?_) ?_
      · rw [← map_defectOne, ← map_logExp _ l (constantCoeff_defectOne hc), MvPowerSeries.coeff_map]
        exact ⟨StdHyp.kur_sub_wfrac l _ (SetLike.coe_mem _), h4 n⟩
      · rw [← map_defectOne, ← map_logExp _ l (constantCoeff_defectOne hc), MvPowerSeries.constantCoeff_map, h4', map_one]
    · refine StdHyp.b4_of_coeff_subst_letterLog l d _ (constantCoeff_defectTwo hc') (fun n => ?_) ?_
      · rw [← map_defectTwo, ← map_logExp _ l (constantCoeff_defectTwo hc), MvPowerSeries.coeff_map]
        exact ⟨StdHyp.kur_sub_wfrac l _ (SetLike.coe_mem _), h5 n⟩
      · rw [← map_defectTwo, ← map_logExp _ l (constantCoeff_defectTwo hc), MvPowerSeries.constantCoeff_map, h5', map_one]

end GlobalTheory.KerStd
