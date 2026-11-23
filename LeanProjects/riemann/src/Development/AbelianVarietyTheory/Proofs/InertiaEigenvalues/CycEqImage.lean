import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousTwoCocycleMultipleOfFundamental
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicCoboundaryOfDivisible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FactorMemCocyclesPowQuot
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.LocDualInt

noncomputable section

namespace GlobalTheory.CycImage

theorem cyc_eq_image : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] {G : Type} [Group G] [TopologicalSpace G], PadicCoeff p O → ∀ (φ : ℤ_[p] →+* O) (i : G ≃ₜ* GK p K) {ε : G →* Oˣ}, IsCyc p K (carry i ε) → ∀ g : G, ((ε g : Oˣ) : O) = φ ((cyclotomicCharacter (PadicAlgCl p) p (MulSemiringAction.toRingAut (GK p K) (PadicAlgCl p) (i g)) : ℤ_[p]ˣ) : ℤ_[p]) := by
  intro p _ K O _ _ _ _ G _ _ hO φ i ε hε g
  set c : ℤ_[p] := ((cyclotomicCharacter (PadicAlgCl p) p
    (MulSemiringAction.toRingAut (GK p K) (PadicAlgCl p) (i g)) : ℤ_[p]ˣ) : ℤ_[p]) with hcdef
  have key : ∀ n : ℕ, ((ε g : Oˣ) : O) - φ c ∈ Ideal.span {(p : O) ^ n} := by
    intro n
    obtain ⟨ζ, hζ⟩ : ∃ ζ : PadicAlgCl p, IsPrimitiveRoot ζ (p ^ n) :=
      HasEnoughRootsOfUnity.exists_primitiveRoot _ _
    obtain ⟨a, ha, hmem⟩ := hε (i g) n ζ hζ.pow_eq_one
    have hcar : ((carry i ε (i g) : Oˣ) : O) = ((ε g : Oˣ) : O) := by
      simp only [carry, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
      congr 2
      exact i.symm_apply_apply g
    rw [hcar] at hmem
    have hsp := cyclotomicCharacter.spec (L := PadicAlgCl p) p (n := n)
      (MulSemiringAction.toRingAut (GK p K) (PadicAlgCl p) (i g)) ζ hζ.pow_eq_one
    have h1 : (MulSemiringAction.toRingAut (GK p K) (PadicAlgCl p) (i g)) ζ = (i g) ζ := rfl
    rw [h1, ha] at hsp
    set v : ℕ := (PadicInt.toZModPow n c).val with hv
    have hmod : a ≡ v [MOD p ^ n] := by
      have hne : ζ ≠ 0 := hζ.ne_zero (NeZero.ne _)
      have hz : ζ ^ ((a : ℤ) - (v : ℤ)) = 1 := by
        rw [zpow_sub₀ hne, zpow_natCast, zpow_natCast, hsp, div_self (pow_ne_zero _ hne)]
      have hd := (hζ.zpow_eq_one_iff_dvd _).1 hz
      exact (Nat.modEq_iff_dvd.2 (by
        have : ((p ^ n : ℕ) : ℤ) ∣ -((a : ℤ) - (v : ℤ)) := (dvd_neg).2 (by exact_mod_cast hd)
        simpa using this))
    have hc : c - (v : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ n} := by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, hv,
        ZMod.natCast_zmod_val, sub_self]
    have hφ : φ c - (v : O) ∈ Ideal.span {(p : O) ^ n} := by
      have := Ideal.mem_map_of_mem φ hc
      rw [Ideal.map_span, Set.image_singleton] at this
      simpa using this
    have hav : (a : O) - (v : O) ∈ Ideal.span {(p : O) ^ n} := by
      rw [Ideal.mem_span_singleton]
      have hd : ((p ^ n : ℕ) : ℤ) ∣ (v : ℤ) - (a : ℤ) := (Nat.modEq_iff_dvd.1 hmod)
      obtain ⟨k, hk⟩ := hd
      refine ⟨-(k : O), ?_⟩
      have hk' : ((v : ℤ) : O) - ((a : ℤ) : O) = (((p ^ n : ℕ) : ℤ) : O) * (k : O) := by
        rw [← Int.cast_sub, hk, Int.cast_mul]
      push_cast at hk'
      linear_combination -hk'
    have hsum : ((ε g : Oˣ) : O) - φ c =
        ((((ε g : Oˣ) : O) - a) + ((a : O) - v)) - (φ c - v) := by ring
    rw [hsum]
    exact Ideal.sub_mem _ (Ideal.add_mem _ hmem hav) hφ
  have hbot : ((ε g : Oˣ) : O) - φ c ∈ ⨅ n : ℕ, (IsLocalRing.maximalIdeal O) ^ n := by
    refine Ideal.mem_iInf.2 fun n => ?_
    have h := key n
    have hle : Ideal.span {(p : O) ^ n} ≤ (IsLocalRing.maximalIdeal O) ^ n := by
      rw [← Ideal.span_singleton_pow]
      exact Ideal.pow_right_mono ((Ideal.span_singleton_le_iff_mem _).2 hO.p_mem) n
    exact hle h
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal O).ne_top, Ideal.mem_bot] at hbot
  exact sub_eq_zero.1 hbot

end GlobalTheory.CycImage
