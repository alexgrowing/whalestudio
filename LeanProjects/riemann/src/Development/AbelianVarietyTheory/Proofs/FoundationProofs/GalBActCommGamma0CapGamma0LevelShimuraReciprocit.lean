import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlMulToRingEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpecialLinearGroupIntMapZmodSurjective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerPadicCompletionMapEvalDependsOnLevel
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BettiFunctionSubMemOfColumnsCongr
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntExponentCongrCyclotomicCharacter

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.GammaZeroComm

theorem act_eq_self_of_mem_B {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l w : ℕ)
    [Fact l.Prime] {b : X.Fn l} (hb : b ∈ X.B N l w) {h : SL(2, ℤ)} (hh : h ∈ Gam N l) :
    X.act l (h : Matrix (Fin 2) (Fin 2) ℤ) b = b := by
  induction hb using Submodule.span_induction with
  | mem x hx => exact hx.2 h hh
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

theorem eval_kmap_congr {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (φ : X.K ≃+* X.K) (n : ℕ) {x y : X.Khat l} (h : x - y ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l))) :
    AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ x) = AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ y) := by
  rw [← sub_eq_zero, ← map_sub, ← map_sub]
  refine Submodule.smul_induction_on h (fun r hr m _ => ?_) (fun a b ha hb => ?_)
  · rw [map_smul, map_smul]
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ m))
    rw [← hz, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · rw [map_add, map_add, ha, hb, add_zero]

theorem exists_twist (M : ℕ) (e e' : ℤ) (he : (e : ZMod M) * e' = 1) (γ : SL(2, ℤ)) :
    ∃ γ₁ : SL(2, ℤ), (en γ 0 0 : ZMod M) = en γ₁ 0 0 ∧ (en γ 0 1 : ZMod M) = e * en γ₁ 0 1 ∧
      (e : ZMod M) * en γ 1 0 = en γ₁ 1 0 ∧ (en γ 1 1 : ZMod M) = en γ₁ 1 1 := by
  have hdet : (en γ 0 0 : ZMod M) * en γ 1 1 - en γ 0 1 * en γ 1 0 = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    have h2 := congrArg (Int.cast : ℤ → ZMod M) this
    push_cast at h2
    exact h2
  obtain ⟨γ₁, hγ₁⟩ := GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective M
    ⟨!![(en γ 0 0 : ZMod M), e' * en γ 0 1; e * en γ 1 0, en γ 1 1], by
      rw [Matrix.det_fin_two_of]; linear_combination hdet - (en γ 0 1 : ZMod M) * en γ 1 0 * he⟩
  have hent : ∀ i j, (en γ₁ i j : ZMod M) =
      (!![(en γ 0 0 : ZMod M), e' * en γ 0 1; e * en γ 1 0, en γ 1 1] : Matrix (Fin 2) (Fin 2) (ZMod M)) i j :=
    fun i j => congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod M) => g.1 i j) hγ₁
  refine ⟨γ₁, ?_, ?_, ?_, ?_⟩
  · rw [hent]; rfl
  · rw [hent]
    show _ = (e : ZMod M) * (e' * en γ 0 1)
    rw [← mul_assoc, he, one_mul]
  · rw [hent]; rfl
  · rw [hent]; rfl

theorem cong_of_dvd {M K : ℕ} (hK : K ∣ M) {e : ℤ} {γ γ₁ : SL(2, ℤ)}
    (h : (en γ 0 0 : ZMod M) = en γ₁ 0 0 ∧ (en γ 0 1 : ZMod M) = e * en γ₁ 0 1 ∧
      (e : ZMod M) * en γ 1 0 = en γ₁ 1 0 ∧ (en γ 1 1 : ZMod M) = en γ₁ 1 1) :
    (en γ 0 0 : ZMod K) = en γ₁ 0 0 ∧ (en γ 0 1 : ZMod K) = e * en γ₁ 0 1 ∧
      (e : ZMod K) * en γ 1 0 = en γ₁ 1 0 ∧ (en γ 1 1 : ZMod K) = en γ₁ 1 1 := by
  obtain ⟨h00, h01, h10, h11⟩ := h
  have e00 := congrArg (ZMod.castHom hK (ZMod K)) h00
  have e01 := congrArg (ZMod.castHom hK (ZMod K)) h01
  have e10 := congrArg (ZMod.castHom hK (ZMod K)) h10
  have e11 := congrArg (ZMod.castHom hK (ZMod K)) h11
  simp only [map_mul, map_intCast] at e00 e01 e10 e11
  exact ⟨e00, e01, e10, e11⟩

theorem twist_mul_inv_mem {N l M : ℕ} (hN : N ∣ M) (hl : l ∣ M) {e : ℤ} {γ γ₁ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l)
    (h : (en γ 0 0 : ZMod M) = en γ₁ 0 0 ∧ (en γ 0 1 : ZMod M) = e * en γ₁ 0 1 ∧
      (e : ZMod M) * en γ 1 0 = en γ₁ 1 0 ∧ (en γ 1 1 : ZMod M) = en γ₁ 1 1) :
    γ₁ * γ⁻¹ ∈ Gam N l := by
  obtain ⟨a00, -, a10, a11⟩ := cong_of_dvd hN h
  obtain ⟨-, -, b10, -⟩ := cong_of_dvd hl h
  have cN : (en γ 1 0 : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.1 hγ.1
  have cl : (en γ 1 0 : ZMod l) = 0 := CongruenceSubgroup.Gamma0_mem.1 hγ.2
  have hdet : (en γ 0 0 : ZMod N) * en γ 1 1 - en γ 0 1 * en γ 1 0 = 1 := by
    have := γ.det_coe
    rw [Matrix.det_fin_two] at this
    have h2 := congrArg (Int.cast : ℤ → ZMod N) this
    push_cast at h2
    exact h2
  have m00 : (γ₁ * γ⁻¹ : SL(2, ℤ)).1 0 0 = en γ₁ 0 0 * en γ 1 1 - en γ₁ 0 1 * en γ 1 0 := by
    simp [en, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]; ring
  have m10 : (γ₁ * γ⁻¹ : SL(2, ℤ)).1 1 0 = en γ₁ 1 0 * en γ 1 1 - en γ₁ 1 1 * en γ 1 0 := by
    simp [en, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]; ring
  have m11 : (γ₁ * γ⁻¹ : SL(2, ℤ)).1 1 1 = en γ₁ 1 1 * en γ 0 0 - en γ₁ 1 0 * en γ 0 1 := by
    simp [en, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]; ring
  rw [cN] at a10 hdet
  rw [cl] at b10
  refine ⟨(CongruenceSubgroup.Gamma1_mem N _).2 ⟨?_, ?_, ?_⟩, CongruenceSubgroup.Gamma0_mem.2 ?_⟩
  · rw [m00]; push_cast; rw [← a00, cN]; linear_combination hdet
  · rw [m11]; push_cast; rw [← a11, ← a10]; linear_combination hdet
  · rw [m10]; push_cast; rw [← a10, cN]; ring
  · rw [m10]; push_cast; rw [← b10, cl]; ring

theorem twist_vec {l n M : ℕ} [Fact l.Prime] (hM : l ^ n ∣ M) {e : ℤ} {χ : ℤ_[l]} (hχ : (e : ℤ_[l]) - χ ∈ (idl l) ^ n)
    {γ γ₁ : SL(2, ℤ)}
    (h : (en γ 0 0 : ZMod M) = en γ₁ 0 0 ∧ (en γ 0 1 : ZMod M) = e * en γ₁ 0 1 ∧
      (e : ZMod M) * en γ 1 0 = en γ₁ 1 0 ∧ (en γ 1 1 : ZMod M) = en γ₁ 1 1) (u : Fin 2 → ℤ_[l]) (i : Fin 2) :
    (![(mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0, χ * (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1] :
      Fin 2 → ℤ_[l]) i - (mZl l (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![u 0, χ * u 1]) i ∈ (idl l) ^ n := by
  obtain ⟨e00, e01, e10, e11⟩ := cong_of_dvd hM h
  rw [Ideal.span_singleton_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at hχ ⊢
  rw [map_intCast] at hχ
  simp only [en] at e00 e01 e10 e11
  rw [hχ] at e01 e10
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, mZl, Matrix.map_apply, map_add, map_mul, map_intCast]
  · rw [← e00, e01]; ring
  · rw [← e10, ← e11]; ring

theorem galB_act_comm : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l → ∀ (s : Ω ≃ₐ[ℚ] Ω), ∀ b ∈ X.B N l w, X.galB l s (X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b) = X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) (X.galB l s b) := by
  intro Ω _ _ _ ε X _ _ N l w _ _ hN _ _ γ hγ s b hb
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hl : l.Prime := Fact.out
  funext u
  apply AdicCompletion.ext
  intro n
  set χ : ℤ_[l] := (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) with hχ
  obtain ⟨M0, hM0, hlev⟩ := X.eval_kmap_levelRed l
    (b ![(mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0, χ * (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1]) n
  obtain ⟨M, hM, hNM, hlM, hlnM, hM0M⟩ : ∃ M : ℕ, 0 < M ∧ N ∣ M ∧ l ∣ M ∧ l ^ n ∣ M ∧ M0 ∣ M :=
    ⟨N * l * l ^ n * M0, Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) hl.pos) (pow_pos hl.pos n)) hM0,
      ⟨l * l ^ n * M0, by ring⟩, ⟨N * l ^ n * M0, by ring⟩, ⟨N * l * M0, by ring⟩, ⟨N * l * l ^ n, by ring⟩⟩
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  obtain ⟨e, he, heχ⟩ := exists_int_exponent_cyclotomic l s n M hM hlnM
  obtain ⟨e', he', -⟩ := exists_int_exponent_cyclotomic l s.symm n M hM hlnM
  have hee : (e : ZMod M) * e' = 1 := by
    have h1 : ζ ^ (e * e') = ζ := by
      rw [_root_.zpow_mul, ← he ζ hζ, ← map_zpow₀, ← he' ζ hζ, AlgEquiv.apply_symm_apply]
    have h0 : ζ ≠ 0 := hζ.ne_zero hM.ne'
    have h2 : ζ ^ (e * e' - 1) = 1 := by rw [zpow_sub_one₀ h0, h1, mul_inv_cancel₀ h0]
    have h3 := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (e * e') M).2 ((hζ.zpow_eq_one_iff_dvd _).1 h2)
    push_cast at h3
    exact h3.symm
  obtain ⟨γ₁, hc⟩ := exists_twist M e e' hee γ
  have hpos : ∀ g : SL(2, ℤ), 0 < (g : Matrix (Fin 2) (Fin 2) ℤ).det := fun g => by rw [g.det_coe]; exact one_pos
  have hact : X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = X.act l (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) b := by
    conv_lhs => rw [← act_eq_self_of_mem_B X N l w hb (twist_mul_inv_mem hNM hlM hγ hc)]
    rw [Tower.act_act Ω ε X l _ _ (hpos _) (hpos _), ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]
  rw [hact]
  show AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l (X.gal s)
      (X.kmap l (X.sl (toGQ (γ₁ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv
        (b (mZl l (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![u 0, χ * u 1])))) =
    AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l (X.sl (toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv
      (X.kmap l (X.gal s)
        (b ![(mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 0, χ * (mZl l (γ : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ u) 1])))
  rw [Tower.kmap_kmap, Tower.kmap_kmap, Betti.toGQ_sl, Betti.toGQ_sl,
    ← eval_kmap_congr X l _ n (X.B_sub_mem N l w b hb n _ _ (twist_vec hlnM heχ hc u))]
  refine hlev _ _ fun f hf => ?_
  exact X.recip M f hM (fun g hg => hf g (LevelRed.gamma_le_of_dvd hM0M hg)) ζ hζ s e (he ζ hζ) γ₁ γ hc

end GlobalTheory.KZ.GammaZeroComm
