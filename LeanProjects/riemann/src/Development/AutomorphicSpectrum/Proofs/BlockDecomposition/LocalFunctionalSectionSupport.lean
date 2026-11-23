import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.GaugeTopology.SSmoothW
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFSupp

open ValuativeRel NNReal

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem dg_mul_uni (a b : Fˣ) (x z : F) :
    Ad3.dg (a * b) b 1 * Ad3.uni x 0 z =
      Ad3.uni ((a : F) * x) 0 ((b : F) * z) * Ad3.dg (a * b) b 1 := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ad3.dg, Ad3.uni, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem uni_mem_congruenceSubgroup {m : ℕ} {x z : F}
    (hx : valuation F x ≤ valuation F (GLnLocal.uniformizer F : F) ^ m)
    (hz : valuation F z ≤ valuation F (GLnLocal.uniformizer F : F) ^ m) :
    Ad3.uni x 0 z ∈ GLnLocal.congruenceSubgroup F 3 m := by
  have h1 : valuation F (GLnLocal.uniformizer F : F) ^ m ≤ 1 :=
    pow_le_one' (GLnLocal.valuation_uniformizer_lt_one F).le m
  have hxO : x ∈ 𝒪[F] := (Valuation.mem_integer_iff _ _).mpr (hx.trans h1)
  have hzO : z ∈ 𝒪[F] := (Valuation.mem_integer_iff _ _).mpr (hz.trans h1)
  have hnx : -x ∈ 𝒪[F] := neg_mem hxO
  have hnz : -z ∈ 𝒪[F] := neg_mem hzO
  have hxz : x * z ∈ 𝒪[F] := mul_mem hxO hzO
  have hinv : (((Ad3.uni x 0 z)⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, -x, x * z - 0; 0, 1, -z; 0, 0, 1] := rfl
  have hval : (((Ad3.uni x 0 z) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      !![1, x, 0; 0, 1, z; 0, 0, 1] := rfl
  rw [GLnLocal.mem_congruenceSubgroup_iff]
  refine ⟨(GLnLocal.mem_integralGL_iff F 3).mpr ⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_⟩
  · rw [hval]
    fin_cases i <;> fin_cases j <;> simp [hxO, hzO, zero_mem, one_mem]
  · rw [hinv]
    fin_cases i <;> fin_cases j <;> simp [hnx, hnz, hxz, zero_mem, one_mem]
  · rw [hval]
    fin_cases i <;> fin_cases j <;> simp [hx, hz]

theorem valuation_le_of_mem_valBall {m : ℕ} {x : F}
    (hx : x ∈ valBall F (ord ((GLnLocal.uniformizer F : F) ^ m))) :
    valuation F x ≤ valuation F (GLnLocal.uniformizer F : F) ^ m := by
  have h0 : (GLnLocal.uniformizer F : F) ≠ 0 := fun h =>
    GLnLocal.valuation_uniformizer_ne_zero F (by rw [h, map_zero])
  obtain ⟨y, rfl⟩ := exists_mul_of_mem_valBall (pow_ne_zero m h0) hx
  rw [map_mul, map_pow]
  exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).mp y.2)

theorem psi_eq_one {ψ : AddChar F Circle} {W : GL (Fin 3) F → ℂ}
    (hW : ∀ x y z g, W (Ad3.uni x y z * g) = (ψ (x + z) : ℂ) * W g)
    {U : Set (GL (Fin 3) F)} (hU : ∀ g, ∀ u ∈ U, W (g * u) = W g) {m : ℕ}
    (hm : (GLnLocal.congruenceSubgroup F 3 m : Set (GL (Fin 3) F)) ⊆ U) (a b : Fˣ)
    {k : GL (Fin 3) F} (hk : k ∈ GLnLocal.integralGL F 3) {x z : F}
    (hx : valuation F x ≤ valuation F (GLnLocal.uniformizer F : F) ^ m)
    (hz : valuation F z ≤ valuation F (GLnLocal.uniformizer F : F) ^ m)
    (h : W (Ad3.dg (a * b) b 1 * k) ≠ 0) : ψ ((a : F) * x + (b : F) * z) = 1 := by
  have hc : k⁻¹ * Ad3.uni x 0 z * k ∈ GLnLocal.congruenceSubgroup F 3 m := by
    simpa using GLnLocal.conj_mem_congruenceSubgroup F 3 (inv_mem hk)
      (uni_mem_congruenceSubgroup hx hz)
  have e1 := hU (Ad3.dg (a * b) b 1 * k) _ (hm hc)
  have e2 : Ad3.dg (a * b) b 1 * k * (k⁻¹ * Ad3.uni x 0 z * k) =
      Ad3.uni ((a : F) * x) 0 ((b : F) * z) * (Ad3.dg (a * b) b 1 * k) := by
    calc Ad3.dg (a * b) b 1 * k * (k⁻¹ * Ad3.uni x 0 z * k)
        = Ad3.dg (a * b) b 1 * Ad3.uni x 0 z * k := by group
      _ = _ := by rw [dg_mul_uni, mul_assoc]
  rw [e2, hW] at e1
  have e3 : (ψ ((a : F) * x + (b : F) * z) : ℂ) = 1 :=
    mul_right_cancel₀ h (by rw [e1, one_mul])
  exact Circle.coe_eq_one.mp e3

theorem modulus_le_of_trivial {ψ : AddChar F Circle} {y : F} (hy : y ∈ valBall F (-1))
    (hy1 : ψ y ≠ 1) {n : ℤ} (c : Fˣ) (h : ∀ x ∈ valBall F n, ψ ((c : F) * x) = 1) :
    GroundTheory.LocalField.modulus (c : F) ≤ (residueCard F : ℝ≥0) ^ (n + 1) := by
  by_contra hlt
  rw [not_le, GroundTheory.LocalField.modulus_of_ne_zero c.ne_zero,
    (zpow_right_strictMono₀ one_lt_residueCard_nnreal).lt_iff_lt] at hlt
  have h1 : (c : F)⁻¹ ∈ valBall F (-ord (c : F)) := by
    rw [← ord_inv c.ne_zero]
    exact mem_valBall_ord
  have h2 : (c : F)⁻¹ * y ∈ valBall F n :=
    valBall_antitone (by omega) (mul_mem_valBall h1 hy)
  apply hy1
  simpa [c.ne_zero] using h _ h2

end GlobalTheory.CompanionTheory.LFSupp

open GlobalTheory.CompanionTheory.LFSupp in

theorem GlobalTheory.CompanionTheory.LFSupp.sSupp : Ad3.LFS.SSupp := by
  intro F _ _ _ _ _ _ ψ hψ W hW hsm
  obtain ⟨U, hU⟩ := hsm
  obtain ⟨m, -, hm⟩ := (GLnLocal.hasBasis_nhds_one F 3).mem_iff.mp
    (U.isOpen.mem_nhds (one_mem U))
  obtain ⟨hc, h1, h0⟩ := hψ
  have hnot := not_isTrivialOn_addCharConductor_sub_one hc h1
  rw [h0] at hnot
  simp only [IsTrivialOn, not_forall] at hnot
  obtain ⟨y, hy, hy1⟩ := hnot
  have hy' : y ∈ valBall F (-1) := by simpa using hy
  refine ⟨(((residueCard F : NNReal) ^ (ord ((GLnLocal.uniformizer F : F) ^ m) + 1) : NNReal) : ℝ),
    fun a b k hk h => ⟨?_, ?_⟩⟩
  · refine NNReal.coe_le_coe.mpr (modulus_le_of_trivial hy' hy1 a fun x hx => ?_)
    have := psi_eq_one hW (U := (U : Set _)) hU hm a b hk (valuation_le_of_mem_valBall hx)
      (z := 0) (by simp) h
    simpa using this
  · refine NNReal.coe_le_coe.mpr (modulus_le_of_trivial hy' hy1 b fun z hz => ?_)
    have := psi_eq_one hW (U := (U : Set _)) hU hm a b hk (x := 0) (by simp)
      (valuation_le_of_mem_valBall hz) h
    simpa using this
