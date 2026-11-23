import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumEqTsumOfKillsStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.GcdOut

abbrev CopVec (L : ℕ) : Type := {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1}

def scl (L : ℕ) (p : ℕ+ × CopVec L) : ℤ × ℤ := (((p.1 : ℕ) : ℤ) * p.2.1.1, ((p.1 : ℕ) : ℤ) * p.2.1.2)

lemma scl_injective (L : ℕ) : Function.Injective (scl L) := by
  rintro ⟨δ, ⟨⟨a, b⟩, hab, ha⟩⟩ ⟨δ', ⟨⟨a', b'⟩, hab', ha'⟩⟩ h
  simp only [scl, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have g1 : Int.gcd a b = 1 := Int.isCoprime_iff_gcd_eq_one.1 hab
  have g2 : Int.gcd a' b' = 1 := Int.isCoprime_iff_gcd_eq_one.1 hab'
  have hd : (δ : ℕ) = (δ' : ℕ) := by
    have e1 := Int.gcd_mul_left ((δ : ℕ) : ℤ) a b
    have e2 := Int.gcd_mul_left ((δ' : ℕ) : ℤ) a' b'
    rw [h1, h2, e2, g1, g2] at e1
    simpa using e1.symm
  have hδ : δ = δ' := PNat.coe_injective hd
  subst hδ
  have hne : ((δ : ℕ) : ℤ) ≠ 0 := by exact_mod_cast δ.ne_zero
  have := mul_left_cancel₀ hne h1
  have := mul_left_cancel₀ hne h2
  subst_vars
  rfl

lemma trm_zero (j : ℕ) (s : ℝ) (hj : 2 ≤ j) : trm j s 0 = 0 := by
  simp [trm, zero_pow (by omega : j ≠ 0)]

lemma trm_smul (j : ℕ) (s : ℝ) (δ : ℕ) (z : ℂ) :
    trm j s ((δ : ℂ) * z) = (((δ : ℂ) ^ j)⁻¹ * ((((δ : ℝ) ^ (2 * s))⁻¹ : ℝ) : ℂ)) * trm j s z := by
  unfold trm
  rw [norm_mul, Complex.norm_natCast, Real.mul_rpow (Nat.cast_nonneg _) (norm_nonneg _), neg_mul,
    Real.rpow_neg (Nat.cast_nonneg _), ← neg_mul, mul_pow, mul_inv]
  push_cast
  ring

lemma cpow_split (j : ℕ) (s : ℝ) (δ : ℕ) (hδ : 0 < δ) :
    (δ : ℂ) ^ ((j : ℂ) + 2 * (s : ℂ)) = (δ : ℂ) ^ j * ((((δ : ℝ) ^ (2 * s)) : ℝ) : ℂ) := by
  rw [Complex.cpow_add _ _ (by exact_mod_cast hδ.ne'), Complex.cpow_natCast,
    Complex.ofReal_cpow (Nat.cast_nonneg _)]
  push_cast
  rfl

end GlobalTheory.EisM.GcdOut

open GlobalTheory.EisM.GcdOut in
theorem GlobalTheory.EisM.lattice_sum_gcd_out (j L : ℕ) (s : ℝ) (φ : DirichletCharacter ℂ L) (τ : ℍ)
    (hj : 2 ≤ j) (hs : 0 < s) (hL : 0 < L) :
    ∑' x : ℤ × ℤ, latF L (fun _ => 1) φ x * trm j s ((x.1 : ℂ) * τ + x.2) =
      LSeries (fun n => φ n) (j + 2 * s) *
        ∑' x : {x : ℤ × ℤ // IsCoprime x.1 x.2 ∧ (L : ℤ) ∣ x.1},
          φ (x.1.2 : ZMod L) * trm j s ((x.1.1 : ℂ) * τ + x.1.2) := by
  let F : ℤ × ℤ → ℂ := fun x => latF L (fun _ => 1) φ x * trm j s ((x.1 : ℂ) * τ + x.2)
  let f : ℕ+ → ℂ := fun δ => LSeries.term (fun n => φ n) ((j : ℂ) + 2 * (s : ℂ)) (δ : ℕ)
  let g : CopVec L → ℂ := fun x => φ (x.1.2 : ZMod L) * trm j s ((x.1.1 : ℂ) * τ + x.1.2)
  change ∑' x, F x = LSeries (fun n : ℕ => φ n) ((j : ℂ) + 2 * (s : ℂ)) * ∑' x, g x
  have hsumT := (GlobalTheory.T.regularizedEisensteinLatticeSum_eq_tsum_of_kills j L s 0 0 τ hj hs hL ⟨0, by simp⟩ (fun x => by simp [Kills])).1
  have hgs : Summable fun x => ‖g x‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun x => ?_)
      (hsumT.comp_injective Subtype.val_injective)
    simp only [g, Function.comp, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one _ _)
  have hLS : LSeriesSummable (fun n : ℕ => φ n) ((j : ℂ) + 2 * (s : ℂ)) := by
    rw [DirichletCharacter.LSeriesSummable_iff hL.ne']
    have : (2:ℝ) ≤ j := by exact_mod_cast hj
    simp
    linarith
  have hfs : Summable fun δ => ‖f δ‖ :=
    (summable_norm_iff.2 hLS).comp_injective PNat.coe_injective
  have hterm : ∀ p : ℕ+ × CopVec L, F (scl L p) = f p.1 * g p.2 := by
    rintro ⟨δ, ⟨⟨a, b⟩, hab, ha⟩⟩
    have hδ : 0 < (δ : ℕ) := δ.pos
    simp only [F, f, g, scl, latF]
    rw [if_pos (dvd_mul_of_dvd_right ha _), LSeries.term_of_ne_zero hδ.ne', cpow_split j s _ hδ]
    have e : ((((δ : ℕ) : ℤ) * a : ℤ) : ℂ) * (τ : ℂ) + ((((δ : ℕ) : ℤ) * b : ℤ) : ℂ)
        = ((δ : ℕ) : ℂ) * ((a : ℂ) * τ + b) := by push_cast; ring
    rw [e, trm_smul]
    have e2 : (((((δ : ℕ) : ℤ) * b : ℤ)) : ZMod L) = ((δ : ℕ) : ZMod L) * (b : ZMod L) := by push_cast; ring
    rw [e2, map_mul]
    have h1 : ((δ:ℕ) : ℂ) ^ j ≠ 0 := pow_ne_zero _ (by exact_mod_cast hδ.ne')
    have h2 : ((((δ : ℕ) : ℝ) ^ (2 * s) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.rpow_pos_of_pos (by exact_mod_cast hδ) _).ne'
    push_cast
    field_simp
  have hsupp : Function.support F ⊆ Set.range (scl L) := by
    rintro ⟨x1, x2⟩ hx
    simp only [Function.mem_support, F, latF] at hx
    by_cases hL1 : (L : ℤ) ∣ x1
    swap
    · simp [hL1] at hx
    rw [if_pos hL1, one_mul] at hx
    have hφ : φ (x2 : ZMod L) ≠ 0 := left_ne_zero_of_mul hx
    have ht : trm j s ((x1 : ℂ) * τ + x2) ≠ 0 := right_ne_zero_of_mul hx
    have hgpos : 0 < Int.gcd x1 x2 := by
      rw [Nat.pos_iff_ne_zero]
      intro h
      rw [Int.gcd_eq_zero_iff] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [trm_zero j s hj] at ht
    obtain ⟨a, b, hab, h1, h2⟩ := Int.exists_gcd_one hgpos
    generalize Int.gcd x1 x2 = d at h1 h2 hgpos
    have hunit : IsUnit (x2 : ZMod L) := by
      by_contra h
      exact hφ (MulChar.map_nonunit φ h)
    have hdu : IsUnit ((d : ℕ) : ZMod L) := by
      rw [h2] at hunit
      push_cast at hunit
      exact isUnit_of_mul_isUnit_right hunit
    have hcop : Nat.Coprime d L := (ZMod.isUnit_iff_coprime d L).1 hdu
    have hLa : (L : ℤ) ∣ a := by
      have hc : IsCoprime (L : ℤ) (d : ℤ) := Nat.isCoprime_iff_coprime.2 hcop.symm
      rw [h1] at hL1
      exact hc.dvd_of_dvd_mul_right hL1
    refine ⟨(⟨d, hgpos⟩, ⟨(a, b), Int.isCoprime_iff_gcd_eq_one.2 hab, hLa⟩), ?_⟩
    simp only [scl, PNat.mk_coe]
    rw [h1, h2, mul_comm a, mul_comm b]
  have hLser : ∑' δ : ℕ+, f δ = LSeries (fun n : ℕ => φ n) ((j : ℂ) + 2 * (s : ℂ)) := by
    unfold LSeries
    refine (PNat.coe_injective.tsum_eq (f := LSeries.term (fun n : ℕ => φ n) ((j : ℂ) + 2 * (s : ℂ))) ?_)
    intro n hn
    have : n ≠ 0 := by
      rintro rfl
      exact hn (LSeries.term_zero _ _)
    exact ⟨⟨n, Nat.pos_of_ne_zero this⟩, rfl⟩
  calc ∑' x, F x = ∑' p, F (scl L p) := ((scl_injective L).tsum_eq hsupp).symm
    _ = ∑' p : ℕ+ × CopVec L, f p.1 * g p.2 := tsum_congr hterm
    _ = (∑' δ, f δ) * ∑' x, g x := (tsum_mul_tsum_of_summable_norm hfs hgs).symm
    _ = _ := by rw [hLser]
