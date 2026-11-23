import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyClosureHomTiltFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltGaloisActionRootOfUnityCoprimeStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc

theorem exists_pow_eq_one_algClosure_coprime (l : ℕ) [Fact l.Prime] (a : AlgebraicClosure (ZMod l))
    (ha : a ≠ 0) : ∃ m : ℕ, 0 < m ∧ ¬ l ∣ m ∧ a ^ m = 1 := by
  have hint : IsIntegral (ZMod l) a := Algebra.IsIntegral.isIntegral a
  let K := IntermediateField.adjoin (ZMod l) ({a} : Set (AlgebraicClosure (ZMod l)))
  haveI : FiniteDimensional (ZMod l) K := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite K := Module.finite_of_finite (ZMod l)
  letI : Fintype K := Fintype.ofFinite K
  let b : K := ⟨a, IntermediateField.mem_adjoin_simple_self _ a⟩
  have hb : b ≠ 0 := fun h => ha (congrArg Subtype.val h)
  have h1 : 1 < Fintype.card K := Fintype.one_lt_card
  refine ⟨Fintype.card K - 1, by omega, ?_, ?_⟩
  · intro hd
    have h0 : ((Fintype.card K - 1 : ℕ) : K) = 0 := by
      obtain ⟨c, hc⟩ := hd
      have hl : ((l : ℕ) : K) = 0 := by
        rw [← map_natCast (algebraMap (ZMod l) K), ZMod.natCast_self, map_zero]
      rw [hc, Nat.cast_mul, hl, zero_mul]
    rw [Nat.cast_sub h1.le, FiniteField.cast_card_eq_zero] at h0
    simp at h0
  · have := congrArg Subtype.val (FiniteField.pow_card_sub_one_eq_one b hb)
    simpa [b] using this

theorem exists_unit_frobenius_eq_mul (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [IsAlgClosed k]
    (u : WittVector l k) (hu : IsUnit u) :
    ∃ w : WittVector l k, IsUnit w ∧ WittVector.frobenius w = u * w := by
  have h1 : (1 : WittVector l k).coeff 0 ≠ 0 := by simp
  have h2 : u.coeff 0 ≠ 0 := (hu.map (WittVector.constantCoeff (p := l) (R := k))).ne_zero
  refine ⟨WittVector.frobeniusRotation l h1 h2, ?_, ?_⟩
  · apply WittVector.isUnit_of_coeff_zero_ne_zero
    simpa [WittVector.frobeniusRotation, WittVector.frobeniusRotationCoeff] using
      WittVector.RecursionBase.solution_nonzero l h1 h2
  · have := WittVector.frobenius_frobeniusRotation l h1 h2
    rwa [mul_one, mul_comm] at this

private theorem padicInt_ringHom_ext (l : ℕ) [Fact l.Prime] {R : Type*} [CommRing R]
    [IsHausdorff (Ideal.span {(l : R)}) R] (f g : ℤ_[l] →+* R) : f = g := by
  refine RingHom.ext fun x => ?_
  refine sub_eq_zero.1 (IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {(l : R)}) R) _ fun n => ?_)
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n x)
  have hx : x = c * (l : ℤ_[l]) ^ n + (x.appr n : ℤ_[l]) := by rw [hc]; ring
  have h : f x - g x = (f c - g c) * (l : R) ^ n := by
    rw [hx]
    simp only [map_add, map_mul, map_pow, map_natCast]
    ring
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, h]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem exists_unramified_period : ∀ (l : ℕ) [Fact l.Prime] (F : GQ l), (∀ (x : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → x ^ m = 1 → F x = x ^ l) → ∀ u : ℤ_[l]ˣ, ∃ w : Per.Ainf l, IsUnit w ∧ (∀ g ∈ (MaximalUnramifiedExtension l).fixingSubgroup, Per.σA g w = w) ∧ Per.σA F w = Per.zA l u * w ∧ Per.φA l w = Per.zA l u * w := by
  intro l _ F hF u
  obtain ⟨f⟩ := GlobalTheory.T.nonempty_closure_hom_tilt_field l
  let u' : WittVector l (AlgebraicClosure (ZMod l)) :=
    WittVector.map (ZMod.castHom (dvd_refl l) _) (WittVector.fromPadicInt l u)
  have hu' : IsUnit u' := (u.isUnit.map _).map _
  obtain ⟨w₀, hw₀, hφ⟩ := exists_unit_frobenius_eq_mul l _ u' hu'
  have hfu : WittVector.map f u' = Per.zA l u := by
    exact RingHom.congr_fun (padicInt_ringHom_ext l (R := Per.Ainf l)
      ((WittVector.map f).comp ((WittVector.map (ZMod.castHom (dvd_refl l) _)).comp
        (WittVector.fromPadicInt l))) (Per.zA l)) u
  have hact : ∀ (g : GQ l) (n : ℕ), n ≠ 0 →
      (∀ (x : Om l) (m : ℕ), 0 < m → ¬ l ∣ m → x ^ m = 1 → g x = x ^ n) →
      ∀ a, Per.σF g (f a) = f a ^ n := by
    intro g n hn hg a
    by_cases ha : a = 0
    · rw [ha, map_zero, map_zero, zero_pow hn]
    · obtain ⟨m, hm, hl, ham⟩ := exists_pow_eq_one_algClosure_coprime l a ha
      exact GlobalTheory.T.tilt_galois_action_root_of_unity_coprime l (f a) m n g hm hl (by rw [← map_pow, ham, map_one])
        fun x hx => hg x m hm hl hx
  have hφA : Per.φA l (WittVector.map f w₀) = Per.zA l u * WittVector.map f w₀ := by
    rw [← hfu, ← map_mul, ← hφ]
    refine WittVector.ext fun n => ?_
    rw [GlobalTheory.RingIface.phiA_coeff]
    simp only [WittVector.map_coeff, WittVector.coeff_frobenius_charP, map_pow]
  refine ⟨WittVector.map f w₀, hw₀.map _, fun g hg => ?_, ?_, hφA⟩
  · refine WittVector.ext fun n => ?_
    have := hact g 1 one_ne_zero (fun x m hm hl hx => by
      rw [pow_one]
      exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg x
        (IntermediateField.subset_adjoin _ _ ⟨m, hm, hl, hx⟩)) (w₀.coeff n)
    rw [pow_one] at this
    rw [GlobalTheory.RingIface.sigA_coeff, WittVector.map_coeff]
    exact this
  · rw [← hφA]
    refine WittVector.ext fun n => ?_
    rw [GlobalTheory.RingIface.sigA_coeff, GlobalTheory.RingIface.phiA_coeff, WittVector.map_coeff]
    exact hact F l (Fact.out : l.Prime).ne_zero hF (w₀.coeff n)

end GlobalTheory.MemLoc
