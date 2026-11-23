import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
open Pointwise

namespace GlobalTheory.GaloisLift

theorem cong_pow_of_cong_pow_int (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) {σ : G E Ω} (hdec : σ ∈ Dec (F := E) A) {q : ℕ}
    (hcong : ∀ b : Ω, IsIntegral ℤ b → A.valuation (σ b - b ^ q) < 1) :
    ∀ x, A.valuation x ≤ 1 → A.valuation (σ x - x ^ q) < 1 := by
  have hdec' : σ • A = A := hdec
  intro x hx
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den E A hx
  have hcs := hcong s hs
  have hct := hcong t ht
  have hvt : A.valuation t ≤ 1 := (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A ht)
  have hσs : A.valuation (σ s) = 1 := by
    refine le_antisymm ((A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A
      (hs.map ((σ : Ω ≃ₐ[E] Ω).toAlgHom.restrictScalars ℤ)))) ?_
    have h3 : ¬ (σ • A).valuation (σ s) < 1 := by
      rw [smul_valuation_lt_one_iff]
      have : (σ⁻¹ : Ω ≃ₐ[E] Ω) (σ s) = s := by
        show (σ⁻¹ * σ) s = s
        simp
      rw [this, hs1]
      exact lt_irrefl 1
    rw [hdec'] at h3
    exact not_lt.mp h3
  have he' : σ s * σ x = σ t := by rw [← map_mul, e]
  have key : s ^ q * σ s * (σ x - x ^ q) = s ^ q * (σ t - t ^ q) + t ^ q * (s ^ q - σ s) := by
    rw [← he', ← e]; ring
  have hv : A.valuation (s ^ q * σ s * (σ x - x ^ q)) < 1 := by
    rw [key]
    apply Valuation.map_add_lt
    · rw [Valuation.map_mul, Valuation.map_pow, hs1, one_pow, one_mul]
      exact hct
    · rw [Valuation.map_mul, Valuation.map_sub_swap]
      calc A.valuation (t ^ q) * A.valuation (σ s - s ^ q) ≤ 1 * A.valuation (σ s - s ^ q) :=
            mul_le_mul_left (by rw [Valuation.map_pow]; exact pow_le_one' hvt q) _
        _ < 1 := by rw [one_mul]; exact hcs
  rw [Valuation.map_mul, Valuation.map_mul, Valuation.map_pow, hs1, hσs, one_pow, one_mul,
    one_mul] at hv
  exact hv

theorem lift_resAut_of_fixes (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (A : ValuationSubring Ω) (K : IntermediateField E Ω) [FiniteDimensional E K]
    (σ₀ : G E Ω) (hσ₀ : σ₀ ∈ Dec (F := E) A)
    (hK : ∀ z ∈ K, A.valuation z ≤ 1 → A.valuation (σ₀ z - z) < 1) :
    ∃ ρ : G E Ω, (∀ z ∈ K, ρ z = z) ∧ ρ ∈ Dec (F := E) A ∧
      ∀ b : Ω, IsIntegral ℤ b → A.valuation (ρ b - σ₀ b) < 1 := by
  haveI : NumberField K := NumberField.of_module_finite E K
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) K⟩
  letI : TopologicalSpace (IntCl K Ω) := ⊥
  haveI : DiscreteTopology (IntCl K Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl K Ω
  haveI := isInvariant_intCl K Ω
  set Q := primeBelow (F := K) A with hQ
  set P := Q.under (𝓞 K) with hP
  haveI : Q.LiesOver P := ⟨rfl⟩

  have hint : ∀ (g : G E Ω) (b : IntCl K Ω), IsIntegral (𝓞 K) (g (b : Ω)) := fun g b =>
    ((isIntegral_int_of_isIntegral b.2).map (g.toAlgHom.restrictScalars ℤ)).tower_top
  let e : IntCl K Ω ≃+* IntCl K Ω :=
    { toFun := fun b => ⟨σ₀ b, hint σ₀ b⟩
      invFun := fun b => ⟨σ₀⁻¹ b, hint σ₀⁻¹ b⟩
      left_inv := fun b => Subtype.ext (by simp)
      right_inv := fun b => Subtype.ext (mul_inv_apply (b : Ω))
      map_mul' := fun a b => Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp) }
  have he : ∀ b : IntCl K Ω, ((e b : IntCl K Ω) : Ω) = σ₀ b := fun _ => rfl
  have hQe : Q = Q.map (e : IntCl K Ω →+* IntCl K Ω) := by
    rw [Ideal.map_comap_of_equiv]
    ext b
    rw [Ideal.mem_comap]
    show A.valuation (b : Ω) < 1 ↔ A.valuation (σ₀⁻¹ (b : Ω)) < 1
    exact (valuation_apply_lt_one_iff ((Dec (F := E) A).inv_mem hσ₀) _).symm
  let ψ₀ : (IntCl K Ω ⧸ Q) ≃+* (IntCl K Ω ⧸ Q) := Ideal.quotientEquiv Q Q e hQe
  have hψ₀ : ∀ b, ψ₀ (Ideal.Quotient.mk Q b) = Ideal.Quotient.mk Q (e b) := fun _ => rfl
  have hlin : ∀ x : 𝓞 K ⧸ P, ψ₀ (algebraMap (𝓞 K ⧸ P) (IntCl K Ω ⧸ Q) x) =
      algebraMap (𝓞 K ⧸ P) (IntCl K Ω ⧸ Q) x := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver, hψ₀, Ideal.Quotient.eq]
    have hz : ((algebraMap (𝓞 K) (IntCl K Ω) a : IntCl K Ω) : Ω) ∈ K := ((a : K)).2
    have := hK _ hz (valuation_le_one_intCl A _)
    exact this
  let ψ : (IntCl K Ω ⧸ Q) ≃ₐ[𝓞 K ⧸ P] (IntCl K Ω ⧸ Q) := AlgEquiv.ofRingEquiv (f := ψ₀) hlin
  obtain ⟨⟨ρ₀, hρ₀Q⟩, hρ₀⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := Ω ≃ₐ[K] Ω) P Q ψ
  have hρ₀Q' : ρ₀ • Q = Q := hρ₀Q
  have hcong : ∀ b : IntCl K Ω, A.valuation (ρ₀ (b : Ω) - σ₀ b) < 1 := by
    intro b
    have h1 : Ideal.Quotient.mk Q (ρ₀ • b) = Ideal.Quotient.mk Q (e b) :=
      DFunLike.congr_fun hρ₀ (Ideal.Quotient.mk Q b)
    have h2 : ρ₀ • b - e b ∈ Q := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, h1, sub_self]
    exact h2
  have hdec : ρ₀ • A = A := by
    refine eq_of_valuation_lt_one_iff K fun b hb => ?_
    let b' : IntCl K Ω := ⟨b, hb.tower_top⟩
    change b' ∈ primeBelow (F := K) (ρ₀ • A) ↔ b' ∈ Q
    rw [primeBelow_smul, hρ₀Q']
  refine ⟨ρ₀.restrictScalars E, fun z hz => ρ₀.commutes ⟨z, hz⟩, ?_, fun b hb => hcong ⟨b, hb.tower_top⟩⟩
  show (ρ₀.restrictScalars E) • A = A
  conv_rhs => rw [← hdec]
  ext x
  simp only [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rfl

theorem exists_fixing_actsAs : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (_h : IsPlaceOver A w)
    (K : IntermediateField E Ω) [FiniteDimensional E K], ∀ d ∈ Dec (F := E) A, ∀ j : ℕ,
      (∀ z ∈ K, A.valuation z ≤ 1 → A.valuation (d z - z ^ (normV w ^ j)) < 1) →
      ∃ ρ : G E Ω, (∀ z ∈ K, ρ z = z) ∧ ActsAs A (normV w) (d * ρ) j 0 := by
  intro E Ω _ _ _ _ _ A w h K _ d hd j hdK
  obtain ⟨φ, hφ⟩ := exists_isFrob h
  have hφ1 : ActsAs A (normV w) φ 1 0 := actsAs_one_iff.mpr hφ
  have hpow : ∀ n : ℕ, ActsAs A (normV w) (φ ^ n) n 0 := by
    intro n
    induction n with
    | zero => exact ⟨(Dec (F := E) A).one_mem, fun x _ => by simp⟩
    | succ n ih => simpa [pow_succ] using ih.mul hφ1
  have hφj := hpow j
  set σ₀ : G E Ω := d⁻¹ * φ ^ j with hσ₀def
  have hσ₀ : σ₀ ∈ Dec (F := E) A := (Dec (F := E) A).mul_mem ((Dec (F := E) A).inv_mem hd) hφj.1
  have hK : ∀ z ∈ K, A.valuation z ≤ 1 → A.valuation (σ₀ z - z) < 1 := by
    intro z hz hz1
    rw [← valuation_apply_lt_one_iff hd, map_sub]
    have e1 : d (σ₀ z) = (φ ^ j) z := by
      rw [hσ₀def, AlgEquiv.mul_apply, mul_inv_apply]
    rw [e1]
    have h1 := hφj.2 z hz1
    simp only [pow_zero, pow_one] at h1
    exact cong_trans h1 (cong_symm (hdK z hz hz1))
  obtain ⟨ρ, hρK, hρA, hρc⟩ := lift_resAut_of_fixes E Ω A K σ₀ hσ₀ hK
  set τ : G E Ω := σ₀⁻¹ * ρ with hτdef
  have hτ : τ ∈ Dec (F := E) A := (Dec (F := E) A).mul_mem ((Dec (F := E) A).inv_mem hσ₀) hρA
  have hτc : ∀ b : Ω, IsIntegral ℤ b → A.valuation (τ b - b ^ 1) < 1 := by
    intro b hb
    rw [pow_one, ← valuation_apply_lt_one_iff hσ₀, map_sub]
    have e3 : σ₀ (τ b) = ρ b := mul_inv_apply (ρ b)
    rw [e3]
    exact hρc b hb
  have hτI : ActsAs A (normV w) τ 0 0 :=
    ⟨hτ, fun x hx => by simpa using cong_pow_of_cong_pow_int E Ω A hτ hτc x hx⟩
  refine ⟨ρ, hρK, ?_⟩
  have e2 : d * ρ = φ ^ j * τ := by
    rw [hτdef, hσ₀def]; group
  rw [e2]
  simpa using hφj.mul hτI

end GlobalTheory.GaloisLift
