import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
import Formalism.SharpRestriction.LevelLetterCocycles.JsetEmb
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseFont
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineCyclotomicLevelOfFinrankInvariants
import Development.AutomorphicArithmetic.ResidueCharacters.FiniteRoots

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

namespace UpperTheory.N.LocRes

variable {l : ℕ} [Fact l.Prime]

abbrev res {K K' LL : FinExt l} (hle : GK K' ≤ GK K) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) :
    LocLat ↥(GK K') ℚ_[l] ↥LL.1 ↥(OL LL) :=
  LiftingTheory.resLoc (Subgroup.inclusion hle) (continuous_subtype_val.subtype_mk _) T

theorem res_crys (LT : LocTheory) (hres : ElementDenominator.CrystallineRestrictionToExtension LT)
    (hF : ∀ K LL : FinExt l, TruncatedSeriesCountingIdentities.FontaineAt ((LT l).PD K) ↥LL.1 ↥(OL LL))
    {K K' LL : FinExt l} (hKK : K.1 ≤ K'.1) (hle : GK K' ≤ GK K) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
    (hT : IsCrys ((LT l).PD K) T.ρ) :
    IsCrys ((LT l).PD K') (res hle T).ρ ∧ ∀ (τ : ↥K'.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ),
      IsJumpV ((LT l).PD K') (res hle T).ρ τ a ↔
        IsJumpV ((LT l).PD K) T.ρ (τ.comp (IntermediateField.inclusion hKK)) a := by
  obtain ⟨h1, h2⟩ := hres l K' K hKK hle LL T hT
  refine ⟨h1, fun τ a => ?_⟩
  rw [isJumpV_iff _ _ ((hF K' LL).2.2.2 (GRep.ofLat (res hle T)) h1),
    isJumpV_iff _ _ ((hF K LL).2.2.2 (GRep.ofLat T) hT), h2]

theorem caseB (P : LocPrime l) (H : LocHW l P) {K LL : FinExt l} {s : ℕ} (h : Good K s LL) (hK : Ks K s = K.1) :
    LiftingTheory.CaseB (H.W K s LL h) := by
  refine ⟨?_, ?_⟩
  · rw [eq_top_iff]
    intro x _
    rw [GlobalTheory.Cyc.mem_GKs_iff_mem_Gj, H.W_s]
    show (x : GQ l) ∈ (Ks K s).fixingSubgroup
    rw [hK]
    exact x.2
  · have h1 := GlobalTheory.Cyc.finrank_Ks K s h.1
    rw [hK, ← Module.finrank_mul_finrank ℚ_[l] ↥(K0 K) ↥K.1] at h1
    have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
    have : FiniteDimensional ℚ_[l] ↥(K0 K) :=
      FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
        (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
    rw [P.PD_p, H.W_s]
    exact Nat.eq_of_mul_eq_mul_left Module.finrank_pos h1

theorem vdeg_le (K : FinExt l) {s m : ℕ} (hs : 1 ≤ s) (hm : 1 ≤ m) :
    padicValNat l (Module.finrank ℚ_[l] ↥(Ks K m)) - padicValNat l (Module.finrank ℚ_[l] ↥(Ks K s)) ≤ m := by
  have hp : l.Prime := Fact.out
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
  have h0 : Module.finrank ℚ_[l] ↥(K0 K) ≠ 0 := Module.finrank_pos.ne'
  have h1 : l - 1 ≠ 0 := (Nat.sub_pos_of_lt hp.one_lt).ne'
  have key : ∀ j, 1 ≤ j → padicValNat l (Module.finrank ℚ_[l] ↥(Ks K j)) =
      padicValNat l (Module.finrank ℚ_[l] ↥(K0 K)) + (padicValNat l (l - 1) + (j - 1)) := by
    intro j hj
    rw [GlobalTheory.Cyc.finrank_Ks K j hj, padicValNat.mul h0 (mul_ne_zero h1 (pow_ne_zero _ hp.ne_zero)),
      padicValNat.mul h1 (pow_ne_zero _ hp.ne_zero), padicValNat.prime_pow]
  rw [key m hm, key s hs]
  omega

theorem jset_sub (D : D7) (HW : HWOf D.loc) (hres : ElementDenominator.CrystallineRestrictionToExtension D.loc)
    (hF : ∀ K LL : FinExt l, TruncatedSeriesCountingIdentities.FontaineAt ((D.loc l).PD K) ↥LL.1 ↥(OL LL))
    {K K' LL : FinExt l} (hKK : K.1 ≤ K'.1) (hle : GK K' ≤ GK K) {s : ℕ} (h : Good K' s LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ) (U : Set ℤ)
    (hU : ∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ U) :
    LocalSituation.Jset (LocalSituation.sit D.loc HW l (D.locA l) K' s LL h) (res hle T) ⊆ U := by
  intro a ha
  obtain ⟨τ, hτ⟩ := JsetEmb.jsetSplit_all D HW l K' s LL h (res hle T) a ha
  exact hU _ a (((res_crys D.loc hres hF hKK hle T hT).2 τ a).1 hτ)

theorem pow_val_smul_mem (LL : FinExt l) {M : Type} [AddCommGroup M] [Module ↥(OL LL) M] (S : Submodule ↥(OL LL) M)
    {d : ℕ} (hd : d ≠ 0) {c : M} (hc : (d : ↥(OL LL)) • c ∈ S) :
    ((l : ↥(OL LL)) ^ padicValNat l d) • c ∈ S := by
  have hp : l.Prime := Fact.out
  have hu : IsUnit ((ordCompl[l] d : ℕ) : ↥(OL LL)) := by
    have h1 : IsUnit ((ordCompl[l] d : ℕ) : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
      exact (Nat.Prime.coprime_iff_not_dvd hp).2 (Nat.not_dvd_ordCompl hp hd)
    simpa using h1.map (algebraMap ℤ_[l] ↥(OL LL))
  obtain ⟨u, hu⟩ := hu
  have e : (d : ↥(OL LL)) = u * (l : ↥(OL LL)) ^ padicValNat l d := by
    rw [hu, ← Nat.factorization_def d hp]
    conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self d l]
    push_cast; ring
  have := S.smul_mem ((u⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL)) hc
  rwa [e, smul_smul, ← mul_assoc, Units.inv_mul, one_mul] at this

end UpperTheory.N.LocRes

end
