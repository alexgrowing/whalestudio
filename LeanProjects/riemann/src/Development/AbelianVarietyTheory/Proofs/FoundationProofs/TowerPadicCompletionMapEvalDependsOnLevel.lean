import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.LevelRed

open scoped MatrixGroups TensorProduct in
open Matrix in

theorem _root_.GlobalTheory.KZ.LevelRed.gamma_le_of_dvd {M M0 : ℕ} (h : M ∣ M0) :
    CongruenceSubgroup.Gamma M0 ≤ CongruenceSubgroup.Gamma M := by
  intro γ hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  have key : ∀ z : ℤ, ((z : ZMod M0).cast : ZMod M) = z := ZMod.cast_intCast h
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← key, h1, ZMod.cast_one h]
  · rw [← key, h2, ZMod.cast_zero]
  · rw [← key, h3, ZMod.cast_zero]
  · rw [← key, h4, ZMod.cast_one h]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

noncomputable abbrev bc (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ : X.K ≃+* X.K) : X.Kl l →ₗ[ℤ_[l]] X.Kl l :=
  LinearMap.baseChange ℤ_[l] (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map φ.toMonoidHom)))

end GlobalTheory.KZ.LevelRed

namespace GlobalTheory.KZ

open scoped MatrixGroups TensorProduct in
open Matrix in
private lemma exists_level_bc_eq_of_agree_on_level {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}
    (X : _root_.GlobalTheory.KZ.Tower Ω ε) (l : ℕ) [Fact l.Prime] (m : X.Kl l) :
    ∃ M0 : ℕ, 0 < M0 ∧ ∀ φ ψ : X.K ≃+* X.K,
      (∀ f : X.K, (∀ γ ∈ CongruenceSubgroup.Gamma M0,
        X.sl (_root_.GlobalTheory.KZ.ofSL γ) f = f) → φ f = ψ f) →
      _root_.GlobalTheory.KZ.LevelRed.bc X l φ m = _root_.GlobalTheory.KZ.LevelRed.bc X l ψ m := by
  induction m using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, fun φ ψ _ => by simp⟩
  | tmul c u =>
    obtain ⟨M, hM, hfix⟩ := X.level ((Additive.toMul u : X.Kˣ) : X.K)
    refine ⟨M, hM, fun φ ψ h => ?_⟩
    have hu : Units.map φ.toMonoidHom (Additive.toMul u) =
        Units.map ψ.toMonoidHom (Additive.toMul u) :=
      Units.ext (by simpa using h _ hfix)
    simp only [LinearMap.baseChange_tmul]
    congr 1
  | add x y hx hy =>
    obtain ⟨M1, hM1, h1⟩ := hx
    obtain ⟨M2, hM2, h2⟩ := hy
    refine ⟨M1 * M2, Nat.mul_pos hM1 hM2, fun φ ψ h => ?_⟩
    rw [map_add, map_add,
      h1 φ ψ fun f hf => h f fun γ hγ => hf γ (_root_.GlobalTheory.KZ.LevelRed.gamma_le_of_dvd (dvd_mul_right M1 M2) hγ),
      h2 φ ψ fun f hf => h f fun γ hγ => hf γ (_root_.GlobalTheory.KZ.LevelRed.gamma_le_of_dvd (dvd_mul_left M2 M1) hγ)]

open scoped MatrixGroups TensorProduct in
open Matrix in

theorem _root_.GlobalTheory.KZ.Tower.eval_kmap_levelRed : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : _root_.GlobalTheory.KZ.Tower Ω ε) (l : ℕ) [Fact l.Prime] (a : X.Khat l) (n : ℕ), ∃ M0 : ℕ, 0 < M0 ∧ ∀ φ ψ : X.K ≃+* X.K, (∀ f : X.K, (∀ γ ∈ CongruenceSubgroup.Gamma M0, X.sl (_root_.GlobalTheory.KZ.ofSL γ) f = f) → φ f = ψ f) → AdicCompletion.eval (_root_.GlobalTheory.KZ.idl l) (X.Kl l) n (X.kmap l φ a) = AdicCompletion.eval (_root_.GlobalTheory.KZ.idl l) (X.Kl l) n (X.kmap l ψ a) := by
  intro Ω _ _ ε X l _ a n
  obtain ⟨m, hm⟩ := Submodule.Quotient.mk_surjective _ (a.1 n)
  obtain ⟨M0, hM0, hlev⟩ := exists_level_bc_eq_of_agree_on_level X l m
  refine ⟨M0, hM0, fun φ ψ h => ?_⟩
  unfold _root_.GlobalTheory.KZ.Tower.kmap
  simp only [LinearMap.coe_restrictScalars, AdicCompletion.map_val_apply,
    AdicCompletion.eval_apply]
  rw [← hm]
  simp only [LinearMap.reduceModIdeal_apply]
  exact congrArg _ (hlev φ ψ h)

end GlobalTheory.KZ
