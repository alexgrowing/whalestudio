import Mathlib
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ExistsIsRegularAppendOfModDepthGE
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModDepthGETwoQuotientPowFreeOverRegularLocalRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyEtaleAwayOfEtaleOffMaximalIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteOfLeMaximalIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftSquareZeroOfFormallyEtaleAwayDepthStatement
open IsLocalRing

namespace GlobalTheory.LiftHom

theorem liftHom_of_etale_punctured : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R], IsAdicComplete (maximalIdeal R) R → 3 ≤ ringKrullDim R → ∀ f ∈ maximalIdeal R, f ≠ 0 → ∀ (A : Type) [CommRing A] [Algebra R A] [Module.Finite R A], (∀ (p : Ideal R) [p.IsPrime], p ≠ maximalIdeal R → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → ∀ (B : Type) [CommRing B] [Algebra R B] [Module.Finite R B] [Module.Free R B] (φ : A →ₐ[R] B ⧸ (Ideal.span {f}).map (algebraMap R B)), ∃ ψ : A →ₐ[R] B, (Ideal.Quotient.mkₐ R ((Ideal.span {f}).map (algebraMap R B))).comp ψ = φ := by
  intro R _ _ hcomp hdim f hf hf0 A _ _ _ he B _ _ _ _ φ
  have hfe := GlobalTheory.T.formallyEtale_away_of_etale_off_maximalIdeal R A he
  generalize hJ : (Ideal.span {f}).map (algebraMap R B) = J at φ ⊢
  rcases subsingleton_or_nontrivial B with hB | hB
  · refine ⟨default, ?_⟩
    haveI : Subsingleton (B ⧸ J) := Ideal.Quotient.subsingleton_iff.2 (Subsingleton.elim _ _)
    exact AlgHom.ext fun x => Subsingleton.elim _ _
  haveI : IsAdicComplete (Ideal.span {f}) R :=
    GlobalTheory.T.isAdicComplete_of_le_maximalIdeal' R hcomp _ ((Ideal.span_singleton_le_iff_mem _).2 hf)
  haveI : IsAdicComplete J B := hJ ▸ GlobalTheory.isAdicComplete_map_of_finite (Ideal.span {f}) B
  have hd : ∀ k : ℕ, ReciprocityTheory.CA.ModDepthGE R (B ⧸ J ^ (k + 1)) 2 := fun k =>
    hJ ▸ GlobalTheory.T.modDepthGE_two_quotient_pow_free_over_regularLocalRing R hdim f hf hf0 B (k + 1) (Nat.le_add_left 1 k)
  have hle : ∀ k : ℕ, J ^ (k + 2) ≤ J ^ (k + 1) := fun k => Ideal.pow_le_pow_right (by omega)
  have step : ∀ (k : ℕ) (φk : A →ₐ[R] B ⧸ J ^ (k + 1)),
      ∃ ψ : A →ₐ[R] B ⧸ J ^ (k + 2), (Ideal.Quotient.factorₐ R (hle k)).comp ψ = φk := by
    intro k φk
    refine GlobalTheory.T.algHom_lift_squareZero_of_formallyEtale_away_depth R A hfe (B ⧸ J ^ (k + 2)) (B ⧸ J ^ (k + 1)) (hd (k + 1))
      ((hd k).mono (by norm_num)) (Ideal.Quotient.factorₐ R (hle k))
      (Ideal.Quotient.factor_surjective (hle k)) ?_ φk
    rw [pow_two, eq_bot_iff]
    refine Ideal.mul_le.2 fun x hx y hy => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [RingHom.mem_ker] at hx hy
    change Ideal.Quotient.mk _ a = 0 at hx
    change Ideal.Quotient.mk _ b = 0 at hy
    rw [Ideal.Quotient.eq_zero_iff_mem] at hx hy
    rw [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    have : a * b ∈ J ^ (k + 1) * J ^ (k + 1) := Ideal.mul_mem_mul hx hy
    rw [← pow_add] at this
    exact Ideal.pow_le_pow_right (by omega) this
  let φs : (n : ℕ) → A →ₐ[R] B ⧸ J ^ (n + 1) := fun n => Nat.rec
    ((Ideal.quotientEquivAlgOfEq R (pow_one J).symm).toAlgHom.comp φ)
    (fun k φk => Classical.choose (step k φk)) n
  have hφs : ∀ k x, Ideal.Quotient.factor (hle k) (φs (k + 1) x) = φs k x := fun k x =>
    congrArg (fun F : A →ₐ[R] B ⧸ J ^ (k + 1) => F x) (Classical.choose_spec (step k (φs k)))

  have hcc : ∀ {a b c : ℕ} (h1 : J ^ a ≤ J ^ b) (h2 : J ^ b ≤ J ^ c) (y : B ⧸ J ^ a),
      Ideal.Quotient.factor h2 (Ideal.Quotient.factor h1 y) = Ideal.Quotient.factor (h1.trans h2) y := by
    intro a b c h1 h2 y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [Ideal.Quotient.factor_mk]
  have hchain : ∀ m n (hmn : m ≤ n) x,
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (by omega : m + 1 ≤ n + 1) : J ^ (n + 1) ≤ J ^ (m + 1))
        (φs n x) = φs m x := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base =>
      intro x
      obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (φs m x)
      rw [← hb, Ideal.Quotient.factor_mk]
    | succ n hmn ih =>
      intro x
      rw [← ih x, ← hφs n x, hcc]
  let F : (n : ℕ) → A →ₐ[R] B ⧸ J ^ n := fun n =>
    (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (Nat.le_succ n))).comp (φs n)
  have hF : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp (F n) = F m := by
    intro m n hmn
    ext x
    show Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)
        (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n)) (φs n x)) =
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ m)) (φs m x)
    rw [← hchain m n hmn x, hcc, hcc]
  refine ⟨IsAdicComplete.liftAlgHom J F hF, ?_⟩
  ext x
  have h1 := IsAdicComplete.mk_liftAlgHom J F hF 1 x
  have h2 : F 1 x = φs 0 x := hφs 0 x
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (φ x)
  have h3 : φs 0 x = Ideal.Quotient.mk (J ^ 1) b := by
    show (Ideal.quotientEquivAlgOfEq R (pow_one J).symm) (φ x) = _
    rw [← hb]
    rfl
  rw [h2, h3, Ideal.Quotient.eq, pow_one] at h1
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ← hb, Ideal.Quotient.eq]
  exact h1

end GlobalTheory.LiftHom
