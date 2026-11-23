import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsReductionActionChosenPlaces
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

noncomputable section

namespace GlobalTheory.SplitUniq

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

theorem le_one_iff_frac {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (ν : Valuation K Γ) (P : Ideal R)
    [P.IsPrime] (hP0 : P ≠ ⊥) (hle : ∀ r : R, ν (algebraMap R K r) ≤ 1)
    (hlt : ∀ r : R, ν (algebraMap R K r) < 1 ↔ r ∈ P) (x : K) :
    ν x ≤ 1 ↔ ∃ y s : R, s ∉ P ∧ x = algebraMap R K y / algebraMap R K s := by
  have hunit : ∀ s : R, s ∉ P → ν (algebraMap R K s) = 1 := fun s hs =>
    le_antisymm (hle s) (not_lt.mp fun h => hs ((hlt s).1 h))
  constructor
  · intro hx
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := R) x
    have hq0 : algebraMap R K q ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
    haveI := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hP0 (Localization.AtPrime P)
    have hinj : Function.Injective (algebraMap R (Localization.AtPrime P)) :=
      IsLocalization.injective (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors
    have key : ∀ a b : R, ∀ (y : R) (s : P.primeCompl),
        algebraMap R (Localization.AtPrime P) a * IsLocalization.mk' (Localization.AtPrime P) y s =
          algebraMap R (Localization.AtPrime P) b → a * y = b * s := by
      intro a b y s h
      apply hinj
      have h2 := congrArg (· * algebraMap R (Localization.AtPrime P) (s : R)) h
      simp only [mul_assoc, IsLocalization.mk'_spec] at h2
      simpa [map_mul] using h2
    obtain ⟨c, hc⟩ := ValuationRing.cond (algebraMap R (Localization.AtPrime P) p)
      (algebraMap R (Localization.AtPrime P) q)
    obtain ⟨⟨y, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
    rcases hc with hc | hc
    ·
      have e := key p q y s hc
      by_cases hy : y ∈ P
      · by_cases hp : p = 0
        · exact ⟨0, 1, P.ne_top_iff_one.mp (Ideal.IsPrime.ne_top inferInstance), by simp [hp]⟩
        · exfalso
          have hp0 : ν (algebraMap R K p) ≠ 0 := by
            rw [Valuation.ne_zero_iff]
            exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hp
          have hq' : ν (algebraMap R K q) ≠ 0 := (Valuation.ne_zero_iff _).mpr hq0
          have e2 : ν (algebraMap R K p) * ν (algebraMap R K y) = ν (algebraMap R K q) := by
            rw [← map_mul, ← map_mul, e, map_mul, map_mul, hunit _ s.2, mul_one]
          rw [map_div₀, div_le_one₀ (zero_lt_iff.mpr hq')] at hx
          have : ν (algebraMap R K p) * ν (algebraMap R K y) < ν (algebraMap R K p) * 1 :=
            mul_lt_mul_of_pos_left ((hlt y).2 hy) (zero_lt_iff.mpr hp0)
          rw [e2, mul_one] at this
          exact absurd hx (not_le.mpr this)
      · refine ⟨s, y, hy, ?_⟩
        have hy0 : algebraMap R K y ≠ 0 := by
          intro h0
          apply hy
          rw [(map_eq_zero_iff _ (IsFractionRing.injective R K)).mp h0]
          exact P.zero_mem
        rw [div_eq_div_iff hq0 hy0, ← map_mul, ← map_mul, e, mul_comm]
    ·
      have e := key q p y s hc
      refine ⟨y, s, s.2, ?_⟩
      have hs0 : algebraMap R K (s : R) ≠ 0 := by
        intro h0
        apply s.2
        rw [(map_eq_zero_iff _ (IsFractionRing.injective R K)).mp h0]
        exact P.zero_mem
      rw [div_eq_div_iff hq0 hs0, ← map_mul, ← map_mul, ← e, mul_comm]
  · rintro ⟨y, s, hs, rfl⟩
    rw [map_div₀, hunit s hs, div_one]
    exact hle y

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "Lp" => maximalRealSubfield L

theorem exists_approx (v : HeightOneSpectrum (𝓞 Lp)) (y d : v.adicCompletion Lp) (hd : d ≠ 0) :
    ∃ a : Lp, Valued.v (y - algebraMap Lp (v.adicCompletion Lp) a) < Valued.v d := by
  have hU : IsOpen {z : v.adicCompletion Lp | Valued.v (z - y) < Valued.v d} := by
    have h := (Valued.isOpen_ball (v.adicCompletion Lp) (Valued.v.restrict d)).preimage (continuous_sub_right y)
    convert h using 2 with z
    simp [Valuation.restrict_lt_iff]
  have hy : y ∈ {z : v.adicCompletion Lp | Valued.v (z - y) < Valued.v d} := by
    simp only [Set.mem_setOf_eq, sub_self, map_zero]
    exact zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hd)
  obtain ⟨z, hz, a, rfl⟩ := mem_closure_iff_nhds.mp (denseRange_algebraMap Lp v y) _ (hU.mem_nhds hy)
  refine ⟨a, ?_⟩
  rw [← Valuation.map_neg, neg_sub]
  exact hz

theorem eq_of_le_one_iff (v : HeightOneSpectrum (𝓞 Lp)) (i i' : L →ₐ[Lp] v.adicCompletion Lp)
    (h : ∀ x : L, Valued.v (i x) ≤ 1 ↔ Valued.v (i' x) ≤ 1) : i = i' := by
  refine AlgHom.ext fun x => ?_
  by_contra hne
  set δ := i x - i' x with hδ
  have hδ0 : Valued.v δ ≠ 0 := (Valuation.ne_zero_iff _).mpr (sub_ne_zero.mpr hne)
  obtain ⟨a, ha⟩ := exists_approx v (i x) δ (sub_ne_zero.mpr hne)
  obtain ⟨b, hb⟩ := exists_approx v δ δ (sub_ne_zero.mpr hne)
  set b' := algebraMap Lp (v.adicCompletion Lp) b
  set a' := algebraMap Lp (v.adicCompletion Lp) a
  have hbv : Valued.v b' = Valued.v δ := by
    have : b' = δ - (δ - b') := by ring
    rw [this, Valuation.map_sub_eq_of_lt_left _ hb]
  have hb0 : Valued.v b' ≠ 0 := hbv ▸ hδ0
  have hbne : b' ≠ 0 := (Valuation.ne_zero_iff _).mp hb0
  set z : L := (x - algebraMap Lp L a) / algebraMap Lp L b
  have hiz : i z = (i x - a') / b' := by simp [z, a', b', map_div₀, map_sub, AlgHom.commutes]
  have hi'z : i' z = (i' x - a') / b' := by simp [z, a', b', map_div₀, map_sub, AlgHom.commutes]
  have hlt : Valued.v (i z) < 1 := by
    rw [hiz, map_div₀, div_lt_one₀ (zero_lt_iff.mpr hb0), hbv]
    exact ha
  have heq : Valued.v (i' z) = 1 := by
    have : i' x - a' = (i x - a') - δ := by rw [hδ]; ring
    rw [hi'z, map_div₀, this, Valuation.map_sub_eq_of_lt_right _ ha, hbv, div_self hδ0]
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero] at heq
    exact zero_ne_one heq
  have hinv : Valued.v (i' z⁻¹) ≤ 1 := by rw [map_inv₀, map_inv₀, heq, inv_one]
  have h2 := (h z⁻¹).2 hinv
  have h3 : Valued.v (i z) * Valued.v (i z⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hz0, map_one, map_one]
  have h4 : Valued.v (i z) * Valued.v (i z⁻¹) < 1 := mul_lt_one_of_lt_of_le hlt h2
  rw [h3] at h4
  exact lt_irrefl _ h4

theorem splitPlace_eq_of_w_eq : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L]
    (s s' : ReciprocityTheory.Aut.SplitPlace L), s.w = s'.w → s = s' := by
  intro L _ _ _ s s' h
  have hv : s.v = s'.v := by
    apply HeightOneSpectrum.ext
    rw [← s.w_under, ← s'.w_under, h]
  have hid : s.ideal = s'.ideal := congrArg HeightOneSpectrum.asIdeal h
  obtain ⟨v, i⟩ := s
  obtain ⟨v', i'⟩ := s'
  simp only at hv
  subst hv
  congr 1
  haveI : (ReciprocityTheory.Aut.SplitPlace.ideal ⟨v, i⟩).IsPrime := ReciprocityTheory.Aut.SplitPlace.ideal_isPrime _
  have hP0 := ReciprocityTheory.Aut.SplitPlace.ideal_ne_bot (⟨v, i⟩ : ReciprocityTheory.Aut.SplitPlace L)
  have H := fun (j : L →ₐ[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L))
      (hj : ReciprocityTheory.Aut.SplitPlace.ideal ⟨v, j⟩ = ReciprocityTheory.Aut.SplitPlace.ideal ⟨v, i⟩) (x : L) =>
    le_one_iff_frac (R := 𝓞 L) (Valued.v.comap (j : L →+* v.adicCompletion (maximalRealSubfield L)))
      (ReciprocityTheory.Aut.SplitPlace.ideal ⟨v, i⟩) hP0
      (fun r => ReciprocityTheory.Aut.SplitPlace.split_le_one ⟨v, j⟩ r)
      (fun r => by rw [← hj]; exact (ReciprocityTheory.Aut.SplitPlace.split_mem_ideal ⟨v, j⟩ r).symm) x
  apply eq_of_le_one_iff v i i'
  intro x
  have h1 := H i rfl x
  have h2 := H i' hid.symm x
  simp only [Valuation.comap_apply] at h1 h2
  exact h1.trans h2.symm

end GlobalTheory.SplitUniq
