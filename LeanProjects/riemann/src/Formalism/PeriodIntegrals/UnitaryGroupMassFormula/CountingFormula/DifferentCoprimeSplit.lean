import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.UnimodOneGenus
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TypedLoc
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemInvCoe

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev ddI (D : D7) : Ideal (𝓞 D.host.E) :=
  Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))

def DdOffG : Prop :=
  ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)), ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal → ¬ ddI D ≤ P.asIdeal

section LocLemmas

variable {E : Type} [Field E] [NumberField E]
variable {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

theorem mem_localization_iff' (p : Ideal (𝓞 E)) [p.IsPrime] (L : Submodule (𝓞 E) V) (x : V) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ p L ↔ ∃ s : 𝓞 E, s ∉ p ∧ s • x ∈ L := by
  exact Iff.rfl

theorem localization_le_of_le_localization' (p : Ideal (𝓞 E)) [p.IsPrime] {L L' : Submodule (𝓞 E) V} (h : L ≤ Formalism.HermitianLatticesTheory.localization₂ p L') :
    Formalism.HermitianLatticesTheory.localization₂ p L ≤ Formalism.HermitianLatticesTheory.localization₂ p L' := by
  intro x hx
  rw [mem_localization_iff'] at hx ⊢
  obtain ⟨s, hs, hsx⟩ := hx
  obtain ⟨t, ht, htx⟩ := (mem_localization_iff' p L' _).1 (h hsx)
  refine ⟨t * s, fun hm => (Ideal.IsPrime.mem_or_mem ‹_› hm).elim ht hs, ?_⟩
  rwa [mul_smul]

theorem locGen_ideal (J : Ideal (𝓞 E)) (hJ : J ≠ ⊥) (P : HeightOneSpectrum (𝓞 E)) :
    ∃ d ∈ J, d ≠ 0 ∧ ∃ t : 𝓞 E, t ∉ P.asIdeal ∧ ∀ y ∈ J, ∃ o : 𝓞 E, t * y = d * o := by
  have hP : P.asIdeal ≠ ⊤ := P.isPrime.ne_top
  have hlt : J * P.asIdeal < J := by
    refine lt_of_le_of_ne (Ideal.mul_le_inf.trans inf_le_left) ?_
    intro h
    apply hP
    have h2 : J * P.asIdeal = J * ⊤ := by rw [h, Ideal.mul_top]
    exact mul_left_cancel₀ hJ h2
  obtain ⟨d, hdJ, hdP⟩ := SetLike.exists_of_lt hlt
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hdP (zero_mem _)
  obtain ⟨I, hI⟩ := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem J).mpr hdJ)
  have hIP : ¬ I ≤ P.asIdeal := by
    intro hle
    apply hdP
    have h3 : Ideal.span {d} ≤ J * P.asIdeal := by
      rw [hI]
      exact Ideal.mul_mono_right hle
    exact h3 (Ideal.mem_span_singleton_self d)
  obtain ⟨t, htI, htP⟩ := SetLike.not_le_iff_exists.mp hIP
  refine ⟨d, hdJ, hd0, t, htP, fun y hy => ?_⟩
  have h4 : y * t ∈ J * I := Ideal.mul_mem_mul hy htI
  rw [← hI, Ideal.mem_span_singleton'] at h4
  obtain ⟨o, ho⟩ := h4
  exact ⟨o, by rw [mul_comm t y, ← ho, mul_comm]⟩

end LocLemmas

section XS

variable (D : D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

theorem aaI_eq (a : Fin D.R.rS) :
    aaI D a = (((ddI D ^ (D.R.rS - (a : ℕ)) : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))⁻¹ := by
  unfold aaI
  have h : ((D.R.rS : ℤ) - (a : ℕ)) = ((D.R.rS - (a : ℕ) : ℕ) : ℤ) := by
    have := a.isLt
    omega
  rw [h, zpow_neg, zpow_natCast, FractionalIdeal.coeIdeal_pow]
  try rfl

theorem ddI_ne_bot : ddI D ≠ ⊥ := by
  rw [ne_eq, Ideal.map_eq_bot_iff_of_injective]
  · exact differentIdeal_ne_bot
  · first
    | exact FaithfulSMul.algebraMap_injective _ _
    | exact NoZeroSMulDivisors.algebraMap_injective _ _

theorem mem_inv_coe {J : Ideal (𝓞 D.host.E)} (hJ : J ≠ ⊥) (x : D.host.E) :
    x ∈ ((J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))⁻¹ ↔
      ∀ y ∈ J, ∃ o : 𝓞 D.host.E, (o : D.host.E) = x * (y : D.host.E) := by
  have hJ' : (J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := by
    rwa [ne_eq, FractionalIdeal.coeIdeal_eq_zero]
  rw [FractionalIdeal.mem_inv_iff hJ']
  constructor
  · intro h y hy
    have h2 := h _ (by rw [FractionalIdeal.mem_coeIdeal]; exact ⟨y, hy, rfl⟩)
    rw [FractionalIdeal.mem_one_iff] at h2
    obtain ⟨o, ho⟩ := h2
    exact ⟨o, ho⟩
  · intro h y hy
    rw [FractionalIdeal.mem_coeIdeal] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    obtain ⟨o, ho⟩ := h y' hy'
    rw [FractionalIdeal.mem_one_iff]
    exact ⟨o, ho⟩

theorem localization_eq_localization_span (P : Ideal (𝓞 D.host.E)) [P.IsPrime] (c : Fin D.R.rS → D.host.E)
    (h1 : ∀ a, ∀ x ∈ aaI D a, ∃ s : 𝓞 D.host.E, s ∉ P ∧ ∃ o : 𝓞 D.host.E, (s : D.host.E) * x = c a * o)
    (h2 : ∀ a, ∃ s : 𝓞 D.host.E, s ∉ P ∧ (s : D.host.E) * c a ∈ aaI D a) :
    Formalism.HermitianLatticesTheory.localization₂ P (XS D F0) =
      Formalism.HermitianLatticesTheory.localization₂ P (Submodule.span (𝓞 D.host.E) (Set.range fun a => c a • F0.e a)) := by
  have hgen_le : XS D F0 ≤ Formalism.HermitianLatticesTheory.localization₂ P (Submodule.span (𝓞 D.host.E) (Set.range fun a => c a • F0.e a)) := by
    unfold XS
    rw [Submodule.span_le]
    rintro y ⟨a, x, hx, rfl⟩
    obtain ⟨s, hs, o, ho⟩ := h1 a x hx
    refine (mem_localization_iff' P _ _).mpr ⟨s, hs, ?_⟩
    have e1 : s • (x • F0.e a) = o • (c a • F0.e a) := by
      rw [← smul_assoc, ← smul_assoc]
      congr 1
      rw [Algebra.smul_def, Algebra.smul_def, mul_comm (algebraMap _ _ o)]
      exact ho
    rw [e1]
    exact Submodule.smul_mem _ o (Submodule.subset_span ⟨a, rfl⟩)
  have hgen_ge : Submodule.span (𝓞 D.host.E) (Set.range fun a => c a • F0.e a) ≤ Formalism.HermitianLatticesTheory.localization₂ P (XS D F0) := by
    rw [Submodule.span_le]
    rintro y ⟨a, rfl⟩
    obtain ⟨s, hs, hsc⟩ := h2 a
    refine (mem_localization_iff' P _ _).mpr ⟨s, hs, ?_⟩
    rw [← smul_assoc]
    unfold XS
    apply Submodule.subset_span
    exact ⟨a, s • c a, by rw [Algebra.smul_def]; exact hsc, rfl⟩
  exact le_antisymm (localization_le_of_le_localization' P hgen_le) (localization_le_of_le_localization' P hgen_ge)

end XS

theorem locGenXS_of (hD : DdOffG) : LocGenXS := by
  intro D u F0 P
  haveI := P.isPrime
  have hJ : ∀ a : Fin D.R.rS, (ddI D ^ (D.R.rS - (a : ℕ))) ≠ ⊥ := fun a => pow_ne_zero _ (ddI_ne_bot D)
  have h1P : (1 : 𝓞 D.host.E) ∉ P.asIdeal := (Ideal.ne_top_iff_one _).mp P.isPrime.ne_top
  by_cases hg : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
  · obtain ⟨t, htd, htP⟩ := SetLike.not_le_iff_exists.mp (hD D P hg)
    refine ⟨fun _ => 1, fun _ => one_ne_zero, fun _ _ => rfl, localization_eq_localization_span D F0 P.asIdeal _ ?_ ?_⟩
    · intro a x hx
      rw [aaI_eq, mem_inv_coe D (hJ a)] at hx
      obtain ⟨o, ho⟩ := hx (t ^ (D.R.rS - (a : ℕ))) (Ideal.pow_mem_pow htd _)
      refine ⟨t ^ (D.R.rS - (a : ℕ)), fun h => htP (P.isPrime.mem_of_pow_mem _ h), o, ?_⟩
      rw [one_mul, ho, mul_comm]
    · intro a
      refine ⟨1, h1P, ?_⟩
      rw [aaI_eq, mem_inv_coe D (hJ a)]
      intro y _
      exact ⟨y, by simp⟩
  · choose d hdJ hd0 t htP ht using fun a : Fin D.R.rS => locGen_ideal (ddI D ^ (D.R.rS - (a : ℕ))) (hJ a) P
    have hdE : ∀ a, ((d a : 𝓞 D.host.E) : D.host.E) ≠ 0 := fun a h =>
      hd0 a (NumberField.RingOfIntegers.coe_eq_zero_iff.mp h)
    refine ⟨fun a => ((d a : 𝓞 D.host.E) : D.host.E)⁻¹, fun a => inv_ne_zero (hdE a), fun h => absurd h hg,
      localization_eq_localization_span D F0 P.asIdeal _ ?_ ?_⟩
    · intro a x hx
      rw [aaI_eq, mem_inv_coe D (hJ a)] at hx
      obtain ⟨o, ho⟩ := hx (d a) (hdJ a)
      refine ⟨1, h1P, o, ?_⟩
      rw [ho]
      have := hdE a
      field_simp
      try simp
      try ring
    · intro a
      refine ⟨t a, htP a, ?_⟩
      rw [aaI_eq, mem_inv_coe D (hJ a)]
      intro y hy
      obtain ⟨o, ho⟩ := ht a y hy
      refine ⟨o, ?_⟩
      have hoE : ((t a : 𝓞 D.host.E) : D.host.E) * (y : D.host.E) = ((d a : 𝓞 D.host.E) : D.host.E) * (o : D.host.E) := by
        have := congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) ho
        simpa using this
      rw [eq_comm, mul_comm ((t a : 𝓞 D.host.E) : D.host.E) _, mul_assoc, hoE, ← mul_assoc, inv_mul_cancel₀ (hdE a),
        one_mul]

theorem different_coprime_split : DdOffG := by
  intro D P hg hle
  have hg' : ∃ i, ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    have e : ((gS D : ℕ) : 𝓞 D.host.E) = ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) := by
      simp [gS, Nat.cast_mul]
    rw [e] at hg
    rcases P.isPrime.mem_or_mem hg with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  obtain ⟨i, hi⟩ := hg'
  have hp : (D.host.g i).Prime := D.host.g_prime i
  have hvp : (P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))).IsPrime := Ideal.IsPrime.comap _
  have hpv : ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
    rw [Ideal.mem_comap, map_natCast]; exact hi
  have hvb : P.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.mem_bot] at hpv
    exact hp.ne_zero (by exact_mod_cast hpv)
  let v : HeightOneSpectrum (𝓞 D.host.F) := ⟨_, hvp, hvb⟩
  have hv : ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := hpv
  have hef := Formalism.L2.SG.Pf.TypedLoc.tower_ef D.host.F D.host.E hp (D.nd.g_split i) v hv
  have hq0 := Formalism.L2.SG.Pf.TypedLoc.span_p_ne_bot hp
  have hmap : Ideal.map (algebraMap ℤ (𝓞 D.host.F)) (Ideal.span {((D.host.g i : ℕ) : ℤ)}) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hq0
  have hcount := Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmap v.isPrime v.ne_bot
  rw [hef.1] at hcount
  have : v.asIdeal.IsMaximal := v.isMaximal
  obtain ⟨Q, hQ1, hQ2⟩ := Ideal.eq_prime_pow_mul_coprime hmap v.asIdeal
  rw [← hcount, pow_one] at hQ2
  haveI := Formalism.L2.SG.Pf.TypedLoc.span_p_maximal hp
  haveI : NeZero (D.host.g i) := ⟨hp.ne_zero⟩
  haveI : Finite (ℤ ⧸ Ideal.span {((D.host.g i : ℕ) : ℤ)}) :=
    Finite.of_equiv _ (Int.quotientSpanNatEquivZMod (D.host.g i)).symm.toEquiv
  have hnd := not_dvd_differentIdeal_of_isCoprime ℤ v.asIdeal Q (Ideal.isCoprime_iff_sup_eq.mpr hQ1) hQ2.symm
  apply hnd
  rw [Ideal.dvd_iff_le]
  exact Ideal.map_le_iff_le_comap.mp hle

theorem local_genus_exists : LocGenXS := locGenXS_of different_coprime_split

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
