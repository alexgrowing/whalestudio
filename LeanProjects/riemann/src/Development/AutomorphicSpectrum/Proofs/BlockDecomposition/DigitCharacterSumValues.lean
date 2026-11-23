import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFunctionalSectionNonvanishing
import GroundTheory.AutomorphicForms.MacdonaldWhittaker

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFUDom

section CharSum

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

def negCharC (ψ : AddChar F Circle) : AddChar F ℂ where
  toFun x := ((ψ (-x) : Circle) : ℂ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by
    rw [neg_add, AddChar.map_add_eq_mul]
    simp

theorem negCharC_apply (ψ : AddChar F Circle) (x : F) :
    negCharC ψ x = ((ψ (-x) : Circle) : ℂ) := rfl

theorem std_trivial_of_mem {ψ : AddChar F Circle} (hψ : Ad3.IsStd ψ) {x : F} (hx : x ∈ 𝒪[F]) :
    ψ x = 1 := by
  obtain ⟨hc, h1, h0⟩ := hψ
  refine isTrivialOn_addCharConductor hc h1 x ?_
  rw [h0]
  exact mem_valBall_zero_iff.2 hx

theorem std_exists_ne_one {ψ : AddChar F Circle} (hψ : Ad3.IsStd ψ) :
    ∃ x : F, (GLnLocal.uniformizer F : F) * x ∈ 𝒪[F] ∧ ψ x ≠ 1 := by
  obtain ⟨hc, h1, h0⟩ := hψ
  have hnot := not_isTrivialOn_addCharConductor_sub_one hc h1
  rw [h0] at hnot
  simp only [IsTrivialOn, not_forall] at hnot
  obtain ⟨x, hx, hne⟩ := hnot
  refine ⟨x, ?_, hne⟩
  have hϖ : (GLnLocal.uniformizer F : F) ≠ 0 := Cartan.uniformizer_ne_zero F
  have hp : (GLnLocal.uniformizer F : F) ∈ valBall F 1 := by
    rw [mem_valBall_iff_le_ord hϖ, ord_uniformizer (irreducible_uniformizer F)]
  have h := mul_mem_valBall hp hx
  rw [show (1 : ℤ) + (0 - 1) = 0 by norm_num] at h
  exact mem_valBall_zero_iff.1 h

theorem sum_negCharC_residue_eq_zero {ψ : AddChar F Circle} (hψ : Ad3.IsStd ψ) :
    ∑ x : 𝓀[F], negCharC ψ ((residueLift F x : F) * (GLnLocal.uniformizer F : F)⁻¹) = 0 := by
  have h0 : ∀ x ∈ 𝒪[F], negCharC ψ x = 1 := fun x hx => by
    rw [negCharC_apply, std_trivial_of_mem hψ (neg_mem hx)]
    simp
  have h1 : ∃ x : F, (GLnLocal.uniformizer F : F) * x ∈ 𝒪[F] ∧ negCharC ψ x ≠ 1 := by
    obtain ⟨x, hx, hne⟩ := std_exists_ne_one hψ
    refine ⟨-x, by rw [mul_neg]; exact neg_mem hx, ?_⟩
    rw [negCharC_apply, neg_neg]
    intro h
    exact hne (Circle.ext (by simpa using h))
  have h := AddChar.sum_eq_zero_of_ne_one
    (GroundTheory.Automorphic.Spherical.residueChar_ne_one (negCharC ψ) h0 h1)
  rw [← h]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_comm]
  rfl

theorem digitSum_mul_zpow (j : ℕ) (c : Fin j → 𝓀[F]) (m : ℤ) :
    digitSum F j c * (GLnLocal.uniformizer F : F) ^ m =
      ∑ t : Fin j, (residueLift F (c t) : F) * (GLnLocal.uniformizer F : F) ^ (((t : ℕ) : ℤ) + m) := by
  have hϖ : (GLnLocal.uniformizer F : F) ≠ 0 := Cartan.uniformizer_ne_zero F
  rw [digitSum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [zpow_add₀ hϖ, zpow_natCast, mul_assoc]

end CharSum

theorem charsum : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), Ad3.IsStd ψ → ∀ (j : ℕ) (m : ℤ),
  (0 ≤ m → ∑ c : Fin j → 𝓀[F], ((ψ (-(digitSum F j c) * (GLnLocal.uniformizer F : F) ^ m) : Circle) : ℂ) = (qF F : ℂ) ^ j) ∧
  (m < 0 → -m ≤ j → ∑ c : Fin j → 𝓀[F], ((ψ (-(digitSum F j c) * (GLnLocal.uniformizer F : F) ^ m) : Circle) : ℂ) = 0) := by
  intro F _ _ _ _ _ _ ψ hψ j m
  constructor
  · intro hm
    lift m to ℕ using hm
    have hterm : ∀ c : Fin j → 𝓀[F],
        ((ψ (-(digitSum F j c) * (GLnLocal.uniformizer F : F) ^ (m : ℤ)) : Circle) : ℂ) = 1 := by
      intro c
      rw [std_trivial_of_mem hψ, Circle.coe_one]
      rw [zpow_natCast]
      exact mul_mem (neg_mem (digitSum_mem j c)) (pow_mem (GLnLocal.uniformizer F).2 m)
    rw [Finset.sum_congr rfl fun c _ => hterm c]
    simp [qF, Nat.card_eq_fintype_card]
  · intro hm hj
    obtain ⟨n, hn⟩ : ∃ n : ℕ, m = -((n : ℤ) + 1) := ⟨(-m - 1).toNat, by omega⟩
    have hnj : n < j := by omega
    set G : Fin j → 𝓀[F] → ℂ := fun t x => negCharC ψ
      ((residueLift F x : F) * (GLnLocal.uniformizer F : F) ^ (((t : ℕ) : ℤ) + m)) with hG
    have key := Finset.prod_univ_sum (fun _ : Fin j => (Finset.univ : Finset 𝓀[F])) G
    rw [Fintype.piFinset_univ] at key
    have hterm : ∀ c : Fin j → 𝓀[F],
        ((ψ (-(digitSum F j c) * (GLnLocal.uniformizer F : F) ^ m) : Circle) : ℂ) =
          ∏ t, G t (c t) := by
      intro c
      rw [neg_mul, ← negCharC_apply, digitSum_mul_zpow, addChar_sum_eq_prod]
    rw [Finset.sum_congr rfl fun c _ => hterm c, ← key]
    refine Finset.prod_eq_zero (Finset.mem_univ (⟨n, hnj⟩ : Fin j)) ?_
    have hexp : (((⟨n, hnj⟩ : Fin j) : ℕ) : ℤ) + m = -1 := by
      simp only [hn]
      ring
    simp only [hG, hexp, _root_.zpow_neg_one]
    exact sum_negCharC_residue_eq_zero hψ

end GlobalTheory.CompanionTheory.LFUDom
