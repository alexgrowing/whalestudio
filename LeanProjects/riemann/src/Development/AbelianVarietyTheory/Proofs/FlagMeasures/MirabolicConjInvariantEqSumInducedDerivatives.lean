import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicFunctionEqInducedDerivativeAddTailStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicInductionPhiPlusInductionFromBlockUniStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerTailStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsMirabolicConjInvariantTwistedTailMeanFunStatement

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.MirSum

variable {g : ℕ} [Fact g.Prime]

theorem inMir_toG {m : ℕ} {M : Mt g m} (h : InMir M) : InMir ((toG M : Gn g m) : Mt g m) := by
  unfold toG
  split_ifs with hu
  · rw [hu.unit_spec]
    exact h
  · exact inMir_one m

theorem indV_sum (ψ : AddChar (ZMod g) ℂ) (m : ℕ) (f : Gn g m → ℂ) (s : Finset ℕ) (fs : ℕ → Gn g m → ℂ)
    (h : ∀ p : Gn g m, InMir (p : Mt g m) → f p = ∑ i ∈ s, fs i p) (x : Gn g (m + 1)) :
    indV ψ m f x = ∑ i ∈ s, indV ψ m (fs i) x := by
  simp only [indV]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs with hc
  · rw [h _ (inMir_toG hc.2.2), Finset.sum_mul]
  · simp

theorem inMir_one_iff (p : Gn g 1) : InMir (p : Mt g 1) ↔ p = 1 := by
  constructor
  · intro h
    ext i j
    fin_cases i
    fin_cases j
    simpa using h 0 0 rfl
  · rintro rfl i j _
    rfl

theorem isUniUp_one_iff (p : Gn g 1) : IsUniUp (p : Mt g 1) ↔ p = 1 := by
  constructor
  · intro h
    ext i j
    fin_cases i
    fin_cases j
    simpa using (h 0 0).2 rfl
  · rintro rfl a b
    fin_cases a
    fin_cases b
    simp

theorem br_one (M : Mt g 1) : br 0 1 M = M := by
  ext i j
  obtain rfl := Subsingleton.elim i 0
  obtain rfl := Subsingleton.elim j 0
  simp [br, entN]

theorem inPar_zero {n : ℕ} (M : Mt g n) : InPar 0 M := by
  intro i j hj _
  exact absurd hj (Nat.not_lt_zero _)

theorem inR_one_iff (p : Gn g 1) : InR 0 (p : Mt g 1) ↔ p = 1 := by
  show InPar 0 (p : Mt g 1) ∧ IsUniUp (br 0 1 (p : Mt g 1)) ↔ p = 1
  rw [br_one, isUniUp_one_iff]
  exact ⟨fun h => h.2, fun h => ⟨inPar_zero _, h⟩⟩

theorem res_one (F : Gn g 1 → ℂ) (h : Gn g 0) (u : Gn g 1) : res 0 1 F h u = F u := by
  have key : ∀ x : Gn g 1, (InPar 0 (x : Mt g 1) ∧ tl 0 (x : Mt g 1) = (h : Mt g 0) ∧
      br 0 1 (x : Mt g 1) = (u : Mt g 1)) ↔ x = u := by
    intro x
    rw [br_one]
    exact ⟨fun hx => Units.ext hx.2.2, fun hx => ⟨inPar_zero _, by ext i j; exact i.elim0, by rw [hx]⟩⟩
  unfold res
  simp only [key, Finset.sum_ite_eq', Finset.mem_univ, if_true, zero_mul, pow_zero, inv_one, one_mul]

theorem eU_one (ψ : AddChar (ZMod g) ℂ) : eU g 1 ψ = MonoidAlgebra.single 1 1 := by
  have hf : (Finset.univ.filter fun u : Gn g 1 => IsUniUp (u : Mt g 1)) = {1} := by
    ext u
    simp [isUniUp_one_iff]
  simp only [eU, eDat, hf]
  simp

theorem der_one (ψ : AddChar (ZMod g) ℂ) (F : Gn g 1 → ℂ) (h : Gn g 0) : der ψ 0 F h = F 1 := by
  show wh ψ (res 0 1 F h) = F 1
  unfold wh tr
  rw [eU_one, Finset.sum_eq_single (1 : Gn g 1)]
  · rw [MonoidAlgebra.coeff_single, Finsupp.single_eq_same, one_mul, res_one]
  · intro b _ hb
    simp [MonoidAlgebra.coeff_single, Finsupp.single_apply, Ne.symm hb]
  · intro h1
    exact absurd (Finset.mem_univ _) h1

theorem base (ψ : AddChar (ZMod g) ℂ) (F : Gn g 1 → ℂ) : F 1 = indR ψ 0 1 (der ψ 0 F) 1 := by
  have hc : (Finset.univ.filter fun p : Gn g 1 => InR 0 (p : Mt g 1)) = {1} := by
    ext p
    simp [inR_one_iff]
  have hs : ∀ y : Gn g 1, (InMir (y : Mt g 1) ∧ InR 0 ((y⁻¹ * 1 * y : Gn g 1) : Mt g 1)) ↔ y = 1 := by
    intro y
    rw [inMir_one_iff, inR_one_iff]
    simp
  unfold indR
  simp only [hc, hs, Finset.card_singleton, Nat.cast_one, inv_one, one_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, der_one, supFrom]
  simp

theorem eq_sum_indR_der : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) , ψ ≠ 1 → ∀ (n : ℕ) (F : Gn g n → ℂ), 1 ≤ n → IsMirClass F → ∀ p : Gn g n, InMir (p : Mt g n) → F p = ∑ i ∈ Finset.range n, indR ψ i n (der ψ i F) p := by
  intro g _ ψ hψ n
  induction n with
  | zero =>
    intro F h
    omega
  | succ m ih =>
    intro F _ hF p hp
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have hp1 := (inMir_one_iff p).mp hp
      subst hp1
      show F 1 = ∑ i ∈ Finset.range 1, indR ψ i 1 (der ψ i F) 1
      rw [Finset.sum_range_one]
      exact base ψ F
    · have hT := GlobalTheory.T.isMirabolicConjInvariant_twistedTailMeanFun g ψ m (m + 1) F hm (Nat.le_succ m) hF
      rw [GlobalTheory.T.mirabolic_function_eq_induced_derivative_add_tail g ψ hψ m F hm hF p hp, Finset.sum_range_succ,
        add_comm (indR ψ m (m + 1) (der ψ m F) p)]
      congr 1
      refine (indV_sum ψ m (tail ψ m F) (Finset.range m)
        (fun i => indR ψ i m (der ψ i (tail ψ m F))) (fun q hq => ih (tail ψ m F) hm hT q hq) p).trans ?_
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      show indV ψ m (indR ψ i m (der ψ i (tail ψ m F))) p = _
      rw [GlobalTheory.T.mirabolicInductionPhiPlus_inductionFromBlockUni g ψ i m _ hi p hp, GlobalTheory.T.der_tail_of_lt_of_le g ψ i m (m + 1) F hi (Nat.le_succ m)]

end GlobalTheory.GLm.MirSum
