import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA.ConjQ

section Coord

variable {F K : Type} [Field F] [Field K] [Algebra F K] {d β : F}

theorem isUnit_of_qn_ne_zero {y : Q d β K} (h : qn y ≠ 0) : IsUnit y := by
  refine isUnit_iff_exists.2 ⟨(qn y)⁻¹ • star y, ?_, ?_⟩
  · rw [mul_smul_comm, mul_star_eq, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ h, map_one]
  · rw [smul_mul_assoc, star_mul_eq, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ h, map_one]

def pureAdd (x b : Q d β K) : Q d β K := ⟨0, x.imI + b.imI, x.imJ + b.imJ, x.imK + b.imK⟩

def pureSub (x b : Q d β K) : Q d β K := ⟨0, x.imI - b.imI, x.imJ - b.imJ, x.imK - b.imK⟩

theorem pureAdd_mul (x b : Q d β K) (hre : x.re = b.re) (hq : qn x = qn b) :
    pureAdd x b * x = b * pureAdd x b := by
  unfold qn at hq
  rw [hre] at hq
  ext <;> simp only [pureAdd, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
    QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul, hre]
  · linear_combination -hq
  · ring
  · ring
  · ring

theorem pureSub_mul (x b : Q d β K) (hre : x.re = b.re) (hq : qn x = qn b) :
    pureSub x b * x = star b * pureSub x b := by
  unfold qn at hq
  rw [hre] at hq
  ext <;> simp only [pureSub, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
    QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul, QuaternionAlgebra.re_star,
    QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star, hre]
  · linear_combination -hq
  · ring
  · ring
  · ring

theorem qn_add_sub (x b : Q d β K) :
    qn (pureAdd x b) + qn (pureSub x b) = 2 * (qn x - x.re ^ 2) + 2 * (qn b - b.re ^ 2) := by
  simp only [qn, pureAdd, pureSub]
  ring

theorem mul_star_of_orth (z b : Q d β K) (hz : z.re = 0)
    (ho : algebraMap F K d * z.imI * b.imI + algebraMap F K β * z.imJ * b.imJ -
      algebraMap F K d * algebraMap F K β * z.imK * b.imK = 0) :
    z * star b = b * z := by
  ext <;> simp only [QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul,
    QuaternionAlgebra.imJ_mul, QuaternionAlgebra.imK_mul, QuaternionAlgebra.re_star,
    QuaternionAlgebra.imI_star, QuaternionAlgebra.imJ_star, QuaternionAlgebra.imK_star, hz]
  · linear_combination -2 * ho
  · ring
  · ring
  · ring

theorem exists_orth (h2 : (2 : K) ≠ 0) (hd : algebraMap F K d ≠ 0) (hβ : algebraMap F K β ≠ 0)
    (b : Q d β K) (hb : qn b - b.re ^ 2 ≠ 0) :
    ∃ z : Q d β K, z.re = 0 ∧ qn z ≠ 0 ∧
      algebraMap F K d * z.imI * b.imI + algebraMap F K β * z.imJ * b.imJ -
        algebraMap F K d * algebraMap F K β * z.imK * b.imK = 0 := by
  set a := algebraMap F K d with ha
  set c := algebraMap F K β with hc
  by_cases hA : a * b.imI ^ 2 + c * b.imJ ^ 2 = 0
  · by_cases hB : b.imI ^ 2 - c * b.imK ^ 2 = 0
    · by_cases hC : b.imJ ^ 2 - a * b.imK ^ 2 = 0
      · exfalso
        have hk : 2 * (a * c * b.imK ^ 2) = 0 := by
          linear_combination hA - a * hB - c * hC
        have hk2 : a * c * b.imK ^ 2 = 0 := (mul_eq_zero.1 hk).resolve_left h2
        apply hb
        simp only [qn, ← ha, ← hc]
        linear_combination hk2 - hA
      · refine ⟨⟨0, 0, a * b.imK, b.imJ⟩, rfl, ?_, ?_⟩
        · simp only [qn, ← ha, ← hc]
          intro h
          have : a * c * (b.imJ ^ 2 - a * b.imK ^ 2) = 0 := by linear_combination h
          exact hC ((mul_eq_zero.1 this).resolve_left (mul_ne_zero hd hβ))
        · simp only [← ha, ← hc]; ring
    · refine ⟨⟨0, c * b.imK, 0, b.imI⟩, rfl, ?_, ?_⟩
      · simp only [qn, ← ha, ← hc]
        intro h
        have : a * c * (b.imI ^ 2 - c * b.imK ^ 2) = 0 := by linear_combination h
        exact hB ((mul_eq_zero.1 this).resolve_left (mul_ne_zero hd hβ))
      · simp only [← ha, ← hc]; ring
  · refine ⟨⟨0, c * b.imJ, -(a * b.imI), 0⟩, rfl, ?_, ?_⟩
    · simp only [qn, ← ha, ← hc]
      intro h
      have : a * c * (a * b.imI ^ 2 + c * b.imJ ^ 2) = 0 := by linear_combination -h
      exact hA ((mul_eq_zero.1 this).resolve_left (mul_ne_zero hd hβ))
    · simp only [← ha, ← hc]; ring

end Coord

theorem conj_of_same_re : ∀ {F K : Type} [Field F] [Field K] [Algebra F K] (d β : F), (2 : K) ≠ 0 → d ≠ 0 → β ≠ 0 →
    ∀ x b : Q d β K, qn x = 1 → qn b = 1 → x.re = b.re → x.re ^ 2 ≠ 1 →
      ∃ y : (Q d β K)ˣ, (y : Q d β K) * x * ((y⁻¹ : (Q d β K)ˣ) : Q d β K) = b := by
  intro F K _ _ _ d β h2 hd hβ x b hx hb hre hp
  have hd' : algebraMap F K d ≠ 0 := by
    simpa using (map_ne_zero (algebraMap F K)).2 hd
  have hβ' : algebraMap F K β ≠ 0 := by
    simpa using (map_ne_zero (algebraMap F K)).2 hβ
  have hn : (1 : K) - b.re ^ 2 ≠ 0 := by
    rw [← hre]
    exact fun h => hp (by linear_combination -h)

  have key : ∀ y : (Q d β K)ˣ, (y : Q d β K) * x = b * y →
      ∃ y : (Q d β K)ˣ, (y : Q d β K) * x * ((y⁻¹ : (Q d β K)ˣ) : Q d β K) = b := by
    intro y hy
    exact ⟨y, by rw [hy, mul_assoc, Units.mul_inv, mul_one]⟩
  have hq : qn x = qn b := hx.trans hb.symm
  by_cases h₁ : qn (pureAdd x b) = 0
  · have h₂ : qn (pureSub x b) ≠ 0 := by
      intro h₂
      have hs := qn_add_sub x b
      rw [h₁, h₂, hx, hb, hre] at hs
      have : (2 * 2 : K) * (1 - b.re ^ 2) = 0 := by linear_combination -hs
      exact hn ((mul_eq_zero.1 this).resolve_left (mul_ne_zero h2 h2))
    obtain ⟨z, hz, hzn, ho⟩ := exists_orth h2 hd' hβ' b (by rwa [hb])
    obtain ⟨e, he⟩ := isUnit_of_qn_ne_zero h₂
    obtain ⟨w, hw⟩ := isUnit_of_qn_ne_zero hzn
    refine key (w * e) ?_
    rw [Units.val_mul, hw, he, mul_assoc, pureSub_mul x b hre hq, ← mul_assoc,
      mul_star_of_orth z b hz ho, mul_assoc]
  · obtain ⟨y, hy⟩ := isUnit_of_qn_ne_zero h₁
    refine key y ?_
    rw [hy, pureAdd_mul x b hre hq]

end GlobalTheory.CompanionTheory.PlaneSA.ConjQ
