import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableRisingS
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIntegersOfMemHatO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteRingClassGroupOfConductorNeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicCompactDensity.ExistsNatLocal

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
open scoped nonZeroDivisors

namespace GlobalTheory.SteinitzOrder

variable {E : Type} [Field E] [NumberField E]

theorem exists_nat_mul_mem_lattice {c : Ideal (OF E)} (hc : c ≠ ⊥) (y : (Af E)ˣ) :
    ∃ m : ℕ, 0 < m ∧ ∀ b : 𝓞 E, (m : E) * (b : E) ∈ lattice c y := by
  obtain ⟨N, hN, hNy⟩ := PI.AdCpctDenWork.exists_nat_adele ((↑y⁻¹ : Af E))
  have hn0 : Ideal.absNorm c ≠ 0 := fun h => hc (Ideal.absNorm_eq_zero_iff.1 h)
  have hnc : ((Ideal.absNorm c : ℕ) : OF E) ∈ c := Ideal.absNorm_mem c
  refine ⟨Ideal.absNorm c * N, Nat.mul_pos (Nat.pos_of_ne_zero hn0) hN, fun b => ?_⟩
  have h := PicFin.mul_mem_hatO hnc (y := algebraMap E (Af E) (b : E) * ((N : Af E) * (↑y⁻¹ : Af E))) (fun v => ?_)
  · show algebraMap E (Af E) _ * _ ∈ hatO c
    convert h using 1
    simp only [map_mul, map_natCast, Nat.cast_mul]; ring
  · have h1 := hNy v
    have hb : ((algebraMap E (Af E)) (b : E)) v ∈ v.adicCompletionIntegers E :=
      HeightOneSpectrum.coe_mem_adicCompletionIntegers v b
    exact mul_mem hb h1

theorem exists_int_integral (z : E) : ∃ k : ℤ, k ≠ 0 ∧ IsIntegral ℤ ((k : E) * z) := by
  obtain ⟨k, hk, h⟩ := exists_integral_multiples ℤ ℚ (L := E) {z}
  exact ⟨k, hk, by simpa [zsmul_eq_mul] using h z (Finset.mem_singleton_self z)⟩

variable [IsCMField E]

local notation "𝔽" => maximalRealSubfield E
local notation "cc" => IsCMField.complexConj E

theorem conj_coe (a : 𝔽) : cc (a : E) = a := (IsCMField.complexConj E).commutes a

def lam (θ x : E) : E := (x - cc x) / (θ - cc θ)

theorem conj_lam (θ x : E) : cc (lam θ x) = lam θ x := by
  unfold lam
  rw [map_div₀, map_sub, map_sub, IsCMField.complexConj_apply_apply, IsCMField.complexConj_apply_apply,
    show cc x - x = -(x - cc x) by ring, show cc θ - θ = -(θ - cc θ) by ring, neg_div_neg_eq]

theorem lam_mem (θ x : E) : lam θ x ∈ 𝔽 := (IsCMField.complexConj_eq_self_iff E _).1 (conj_lam θ x)

theorem sub_conj_ne {θ : E} (hθ : θ ∉ 𝔽) : θ - cc θ ≠ 0 := fun h =>
  hθ ((IsCMField.complexConj_eq_self_iff E _).1 (sub_eq_zero.1 h).symm)

theorem sub_conj_eq {θ : E} (hθ : θ ∉ 𝔽) (x : E) : x - cc x = lam θ x * (θ - cc θ) := by
  unfold lam; rw [div_mul_cancel₀ _ (sub_conj_ne hθ)]

theorem lam_add (θ x x' : E) : lam θ (x + x') = lam θ x + lam θ x' := by
  unfold lam; rw [map_add]; ring

theorem lam_mul (θ : E) (a : 𝔽) (x : E) : lam θ ((a : E) * x) = a * lam θ x := by
  unfold lam; rw [map_mul, conj_coe]; ring

theorem lam_self {θ : E} (hθ : θ ∉ 𝔽) : lam θ θ = 1 := div_self (sub_conj_ne hθ)

theorem mem_of_lam_eq {θ ω : E} (hθ : θ ∉ 𝔽) (hω : lam θ ω = 1) (x : E) : x - lam θ x * ω ∈ 𝔽 := by
  refine (IsCMField.complexConj_eq_self_iff E _).1 ?_
  have h1 := sub_conj_eq hθ x
  have h2 := sub_conj_eq hθ ω
  rw [hω, one_mul] at h2
  rw [map_sub, map_mul, conj_lam]
  linear_combination -h1 + lam θ x * h2

theorem exists_of_isIntegral {z : 𝔽} (h : IsIntegral ℤ (z : E)) : ∃ r : OF E, algebraMap (OF E) 𝔽 r = z :=
  ⟨⟨z, (isIntegral_algHom_iff ((𝔽).subtype.toIntAlgHom) Subtype.val_injective).1 h⟩, rfl⟩

def latF (c : Ideal (OF E)) (y : (Af E)ˣ) : Submodule (OF E) 𝔽 where
  carrier := {a | (a : E) ∈ lattice c y}
  zero_mem' := (latticeSub c y).zero_mem
  add_mem' := fun {a b} ha hb => (latticeSub c y).add_mem ha hb
  smul_mem' := fun r a ha => by
    show ((r • a : 𝔽) : E) ∈ lattice c y
    rw [Algebra.smul_def]
    exact mul_mem_lattice (algebraMap_mem_orderC c r) ha

def latB (c : Ideal (OF E)) (y : (Af E)ˣ) (θ : E) : Submodule (OF E) 𝔽 where
  carrier := {b | ∃ x ∈ lattice c y, lam θ x = (b : E)}
  zero_mem' := ⟨0, (latticeSub c y).zero_mem, by simp [lam]⟩
  add_mem' := fun {a b} ⟨x, hx, ha⟩ ⟨x', hx', hb⟩ =>
    ⟨x + x', (latticeSub c y).add_mem hx hx', by rw [lam_add, ha, hb]; rfl⟩
  smul_mem' := fun r b ⟨x, hx, hb⟩ => ⟨algebraMap (OF E) E r * x, mul_mem_lattice (algebraMap_mem_orderC c r) hx, by
    rw [show algebraMap (OF E) E r = ((algebraMap (OF E) 𝔽 r : 𝔽) : E) from rfl, lam_mul, hb, Algebra.smul_def]; rfl⟩

theorem isFractional_latF (c : Ideal (OF E)) (y : (Af E)ˣ) : IsFractional (OF E)⁰ (latF c y) := by
  obtain ⟨n, hn, hL⟩ := Conv.exists_denominator c y
  refine ⟨(n : OF E), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn.ne'), fun a ha => ?_⟩
  obtain ⟨b, hb⟩ := hL _ ha
  refine exists_of_isIntegral ?_
  have e : (((n : OF E) • a : 𝔽) : E) = algebraMap (𝓞 E) E b := by
    rw [hb, Algebra.smul_def]; simp
  rw [e]
  exact RingOfIntegers.isIntegral_coe b

theorem isFractional_latB (c : Ideal (OF E)) (y : (Af E)ˣ) {θ : E} (hθ : θ ∉ 𝔽) :
    IsFractional (OF E)⁰ (latB c y θ) := by
  obtain ⟨n, hn, hL⟩ := Conv.exists_denominator c y
  obtain ⟨k, hk, hki⟩ := exists_int_integral (θ - cc θ)⁻¹
  have hnk : ((n * k : ℤ) : OF E) ≠ 0 := by
    have : (n * k : ℤ) ≠ 0 := mul_ne_zero (by exact_mod_cast hn.ne') hk
    exact_mod_cast this
  refine ⟨((n * k : ℤ) : OF E), mem_nonZeroDivisors_of_ne_zero hnk, fun b hb => ?_⟩
  obtain ⟨x, hx, hbx⟩ := hb
  obtain ⟨β, hβ⟩ := hL x hx
  refine exists_of_isIntegral ?_
  have e : ((((n * k : ℤ) : OF E) • b : 𝔽) : E) =
      (algebraMap (𝓞 E) E β - cc (algebraMap (𝓞 E) E β)) * ((k : E) * (θ - cc θ)⁻¹) := by
    have hδ := sub_conj_ne hθ
    rw [hβ, Algebra.smul_def]
    simp only [map_mul, map_natCast, map_intCast, map_sub]
    push_cast
    rw [← hbx]
    unfold lam
    field_simp
  rw [e]
  exact ((RingOfIntegers.isIntegral_coe β).sub (map_isIntegral_int cc (RingOfIntegers.isIntegral_coe β))).mul hki

end GlobalTheory.SteinitzOrder

namespace GlobalTheory.SteinitzOrder

theorem lattice_eq_steinitz : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
    ∀ θ : E, θ ∉ maximalRealSubfield E → ∃ (𝔞 𝔟 : Frac (maximalRealSubfield E)) (a₀ : maximalRealSubfield E),
      ∀ x : E, x ∈ lattice c y ↔ ∃ a ∈ latM 𝔞, ∃ b ∈ (𝔟 : FractionalIdeal (𝓞 (maximalRealSubfield E))⁰ (maximalRealSubfield E)),
        x = (a : E) + (b : E) * (θ + (a₀ : E)) := by
  intro E _ _ _ c y hc θ hθ
  obtain ⟨m, hm, hmL⟩ := exists_nat_mul_mem_lattice hc y
  obtain ⟨k, hk, hkθ⟩ := exists_int_integral θ
  let MI : FractionalIdeal (OF E)⁰ (maximalRealSubfield E) := ⟨latF c y, isFractional_latF c y⟩
  let BI : FractionalIdeal (OF E)⁰ (maximalRealSubfield E) := ⟨latB c y θ, isFractional_latB c y hθ⟩
  have hM0 : MI ≠ 0 := by
    intro h
    have h1 : ((m : maximalRealSubfield E)) ∈ MI := by
      show (((m : maximalRealSubfield E)) : E) ∈ lattice c y
      simpa using hmL 1
    rw [h, FractionalIdeal.mem_zero_iff] at h1
    exact hm.ne' (by exact_mod_cast h1)
  have hB0 : BI ≠ 0 := by
    intro h
    have h1 : (((m * k : ℤ) : maximalRealSubfield E)) ∈ BI := by
      refine ⟨(m : E) * ((k : E) * θ), ?_, ?_⟩
      · exact hmL ⟨_, hkθ⟩
      · have e : (m : E) * ((k : E) * θ) = (((m * k : ℤ) : maximalRealSubfield E) : E) * θ := by push_cast; ring
        rw [e, lam_mul, lam_self hθ, mul_one]
    rw [h, FractionalIdeal.mem_zero_iff] at h1
    have h2 : (m * k : ℤ) = 0 := by exact_mod_cast h1
    exact mul_ne_zero (by exact_mod_cast hm.ne') hk h2
  have key : ∀ z ∈ BI * BI⁻¹, ∃ w : E, lam θ w = (z : E) ∧ ∀ b ∈ BI, (b : E) * w ∈ lattice c y := by
    intro z hz
    refine FractionalIdeal.mul_induction_on hz ?_ ?_
    · intro i hi j hj
      obtain ⟨x, hx, hix⟩ := hi
      refine ⟨(j : E) * x, by rw [lam_mul, hix]; push_cast; ring, fun b hb => ?_⟩
      have hbj : b * j ∈ (1 : FractionalIdeal (OF E)⁰ (maximalRealSubfield E)) := by
        rw [← mul_inv_cancel₀ hB0]
        exact FractionalIdeal.mul_mem_mul hb hj
      obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 hbj
      have h1 := mul_mem_lattice (algebraMap_mem_orderC c r) hx
      have h2 : algebraMap (OF E) E r = ((b * j : maximalRealSubfield E) : E) := congrArg Subtype.val hr
      rw [h2] at h1
      convert h1 using 1
      push_cast; ring
    · rintro x x' ⟨w, hw, hwb⟩ ⟨w', hw', hwb'⟩
      exact ⟨w + w', by rw [lam_add, hw, hw']; push_cast; rfl, fun b hb => by
        rw [mul_add]; exact (latticeSub c y).add_mem (hwb b hb) (hwb' b hb)⟩
  obtain ⟨ω, hω, hωB⟩ := key 1 (by rw [mul_inv_cancel₀ hB0]; exact FractionalIdeal.one_mem_one _)
  have hω1 : lam θ ω = 1 := by simpa using hω
  have ha₀ : ω - θ ∈ maximalRealSubfield E := by
    have h := mem_of_lam_eq hθ hω1 θ
    rw [lam_self hθ, one_mul] at h
    have h' := neg_mem h
    rwa [neg_sub] at h'
  obtain ⟨a₀, ha₀'⟩ : ∃ a₀ : maximalRealSubfield E, (a₀ : E) = ω - θ := ⟨⟨ω - θ, ha₀⟩, rfl⟩
  have hθa : θ + (a₀ : E) = ω := by rw [ha₀']; ring
  let 𝔡 : FractionalIdeal (𝓞 (maximalRealSubfield E))⁰ (maximalRealSubfield E) :=
    ((differentIdeal ℤ (𝓞 (maximalRealSubfield E)) : Ideal (𝓞 (maximalRealSubfield E))) :
      FractionalIdeal (𝓞 (maximalRealSubfield E))⁰ (maximalRealSubfield E))
  have h𝔡 : 𝔡 ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot
  have h𝔡M : 𝔡 * MI ≠ 0 := mul_ne_zero h𝔡 hM0
  have hlatM : latM (Units.mk0 (𝔡 * MI) h𝔡M)⁻¹ = MI := by
    rw [latM, inv_inv, Units.val_mk0]
    exact inv_mul_cancel_left₀ h𝔡 MI
  refine ⟨(Units.mk0 (𝔡 * MI) h𝔡M)⁻¹, Units.mk0 BI hB0, a₀, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · have hb : (⟨lam θ x, lam_mem θ x⟩ : maximalRealSubfield E) ∈ BI := ⟨x, hx, rfl⟩
    refine ⟨⟨x - lam θ x * ω, mem_of_lam_eq hθ hω1 x⟩, ?_, ⟨lam θ x, lam_mem θ x⟩, by simpa using hb, ?_⟩
    · rw [hlatM]
      have h3 := hωB ⟨lam θ x, lam_mem θ x⟩ hb
      simp only at h3
      have h4 : x - lam θ x * ω ∈ latticeSub c y := (latticeSub c y).sub_mem hx h3
      exact h4
    · rw [hθa]
      simp only
      ring
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [hlatM] at ha
    rw [Units.val_mk0] at hb
    rw [hθa]
    have h3 := hωB b hb
    have h4 : (a : E) + (b : E) * ω ∈ latticeSub c y := (latticeSub c y).add_mem ha h3
    exact h4

end GlobalTheory.SteinitzOrder
