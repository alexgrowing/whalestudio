import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalBMemKummerInvariantSetStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesCoeffRingHomMapCoeff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEqExpOfRat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpUpperInt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerPadicCompletionMapEvalDependsOnLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BettiFunctionSubMemOfColumnsCongrStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntExponentCongrCyclotomicCharacterStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.GalUpper

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

theorem map_eq_zpow_of_pow_eq_one (s : Ω ≃ₐ[ℚ] Ω) {L : ℕ} (hL : 0 < L) {e : ℤ}
    (he : ∀ ζ : Ω, IsPrimitiveRoot ζ L → s ζ = ζ ^ e) {ω : Ω} (hω : ω ^ L = 1) : s ω = ω ^ e := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero L := ⟨hL.ne'⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω L
  obtain ⟨i, -, rfl⟩ := hξ.eq_pow_of_pow_eq_one hω
  rw [map_pow, he ξ hξ, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]

theorem eOm_mul_int (ε : Ω →+* ℂ) (x : ℚ) (k : ℤ) : eOm ε (x * k) = eOm ε x ^ k := by
  apply ε.injective
  rw [map_zpow₀, eOm_spec ε ε.injective, eOm_spec ε ε.injective, ← Complex.exp_int_mul]
  congr 1; push_cast; ring

theorem gal_sl_upper (ε : Ω →+* ℂ) (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (M q : ℕ) (hq : 0 < q) (e : ℤ)
    (he : ∀ ω : Ω, ω ^ (M * q) = 1 → s ω = ω ^ e) (j : ℤ) (f : X.K)
    (hf : ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) :
    X.gal s (X.sl (toGQ !![1, j; 0, (q : ℤ)]) f) = X.sl (toGQ !![1, j * e; 0, (q : ℤ)]) (X.gal s f) := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have key : ∀ (a : ℤ) (g : X.K) (t : ℚ), (X.exp (X.sl (toGQ !![1, a; 0, (q : ℤ)]) g)).coeff t =
      eOm ε (t * a) * (X.exp g).coeff (t * q) := by
    intro a g t
    have h := Tower.exp_upper_int ε X 1 a q one_pos (by exact_mod_cast hq) g (t * q)
    have e1 : t * q * ((1 : ℤ) : ℚ) / ((q : ℤ) : ℚ) = t := by push_cast; field_simp
    have e2 : t * q * (a : ℚ) / ((q : ℤ) : ℚ) = t * a := by push_cast; field_simp
    rwa [e1, e2] at h
  apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
  ext t
  change (X.exp (X.gal s _)).coeff t = (X.exp (X.sl _ _)).coeff t
  rw [X.gal_exp, key, key, X.gal_exp, map_mul]
  by_cases h0 : (X.exp f).coeff (t * q) = 0
  · rw [h0, map_zero, mul_zero, mul_zero]
  · congr 1
    have h1 := GlobalTheory.KroneckerCongruence.eOm_level X M f hf _ h0
    have h2 : eOm ε (t * j) ^ (M * q) = 1 := by
      rw [← zpow_natCast, ← eOm_mul_int,
        show t * j * (((M * q : ℕ) : ℤ) : ℚ) = t * q * M * j by push_cast; ring, eOm_mul_int, h1, _root_.one_zpow]
    rw [he _ h2, ← eOm_mul_int]
    congr 1; push_cast; ring

omit [IsAlgClosure ℚ Ω] in

theorem eval_eq_zero_of_mem {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (φ : X.K ≃+* X.K)
    {x : X.Khat l} (hx : x ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l))) :
    AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ x) = 0 := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr y _
    rw [map_smul, map_smul]
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ y))
    rw [← hz, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · intro x y hx hy
    rw [map_add, map_add, hx, hy, add_zero]

omit [IsAlgClosure ℚ Ω] in

theorem act_upper_add {ε : Ω →+* ℂ} (X : Tower Ω ε) {N l w : ℕ} [Fact l.Prime] {b : X.Fn l} (hb : b ∈ X.B N l w)
    (q : ℕ) (hq : 0 < q) (a t : ℤ) :
    X.act l !![1, a + t * q; 0, (q : ℤ)] b = X.act l !![1, a; 0, (q : ℤ)] b := by
  let γ : SL(2, ℤ) := ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩
  have hγ : γ ∈ Gam N l := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [CongruenceSubgroup.Gamma1_mem]; simp [γ]
    · rw [CongruenceSubgroup.Gamma0_mem]; simp [γ]
  have hinv : X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b := by
    induction hb using Submodule.span_induction with
    | mem x hx => exact hx.2 γ hγ
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul c x _ hx => rw [map_smul, hx]
  have hm : (!![1, a + t * q; 0, (q : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) =
      (γ : Matrix (Fin 2) (Fin 2) ℤ) * !![1, a; 0, (q : ℤ)] := by
    simp [γ]
  rw [hm, ← Tower.act_act Ω ε X l _ _ (by rw [γ.det_coe]; exact one_pos)
    (by simp [Matrix.det_fin_two]; exact hq), hinv]

theorem galB_act_upper : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ (s : Ω ≃ₐ[ℚ] Ω) (q : ℕ) (e : ℤ), 0 < q → (∀ ζ : Ω, IsPrimitiveRoot ζ q → s ζ = ζ ^ e) → ∀ (j : ℤ), ∀ b ∈ X.B N l w, X.galB l s (X.act l !![1, j; 0, (q : ℤ)] b) = X.act l !![1, j * e; 0, (q : ℤ)] (X.galB l s b) := by
  intro Ω _ _ _ ε X hε hj N l w _ hl hN hNl hw s q e hq he j b hb
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero q := ⟨hq.ne'⟩
  have hlp : l.Prime := Fact.out
  have hb' := GlobalTheory.T.galB_mem_kummer_invariant_set ε X hε hj N l w hl hN hNl hw s b hb
  funext u
  apply AdicCompletion.ext
  intro n
  set χ : ℤ_[l] := (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) with hχ
  set v : Fin 2 → ℤ_[l] := mZl l !![1, j; 0, (q : ℤ)] *ᵥ ![u 0, χ * u 1] with hv
  obtain ⟨M, hM, hred⟩ := GlobalTheory.T.towerPadicCompletionMap_eval_depends_on_level X l (b v) n
  have hL : 0 < M * q * l ^ n := Nat.mul_pos (Nat.mul_pos hM hq) (pow_pos hlp.pos n)
  obtain ⟨d, hd, hdχ⟩ := GlobalTheory.T.exists_int_exponent_congr_cyclotomicCharacter l s n (M * q * l ^ n) hL (dvd_mul_left _ _)
  have hd' : ∀ ω : Ω, ω ^ (M * q) = 1 → s ω = ω ^ d := fun ω hω =>
    map_eq_zpow_of_pow_eq_one s hL hd (by rw [pow_mul, hω, one_pow])
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω q
  have hξ0 : ξ ≠ 0 := hξ.ne_zero hq.ne'
  have hde : (q : ℤ) ∣ d - e := by
    rw [← hξ.zpow_eq_one_iff_dvd, zpow_sub₀ hξ0, ← he ξ hξ,
      ← hd' ξ (by rw [mul_comm, pow_mul, hξ.pow_eq_one, one_pow])]
    exact div_self ((map_ne_zero s).2 hξ0)
  obtain ⟨t, ht⟩ := hde
  have hjd : j * d = j * e + (j * t) * q := by linear_combination j * ht
  rw [← act_upper_add X hb' q hq (j * e) (j * t), ← hjd]
  set v' : Fin 2 → ℤ_[l] := mZl l !![1, j * d; 0, (q : ℤ)] *ᵥ u with hv'
  change AdicCompletion.eval (idl l) (X.Kl l) n
      (X.kmap l (X.gal s) (X.kmap l (X.sl (toGQ !![1, j; 0, (q : ℤ)])).toRingEquiv (b v))) =
    AdicCompletion.eval (idl l) (X.Kl l) n
      (X.kmap l (X.sl (toGQ !![1, j * d; 0, (q : ℤ)])).toRingEquiv (X.kmap l (X.gal s) (b ![v' 0, χ * v' 1])))
  rw [Tower.kmap_kmap, Tower.kmap_kmap,
    hred _ ((X.gal s).trans (X.sl (toGQ !![1, j * d; 0, (q : ℤ)])).toRingEquiv)
      (fun f hf => gal_sl_upper ε X s M q hq d hd' j f hf), ← sub_eq_zero, ← map_sub, ← map_sub]
  apply eval_eq_zero_of_mem
  refine GlobalTheory.T.bettiFunction_sub_mem_of_columns_congr X N l w b hb n _ _ ?_
  intro i
  fin_cases i
  · have h := Ideal.mul_mem_left _ (-((j : ℤ_[l]) * u 1)) hdχ
    convert h using 1
    simp [hv, hv', mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · convert Ideal.zero_mem _
    simp [hv, hv', mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

end GlobalTheory.KZ.GalUpper
