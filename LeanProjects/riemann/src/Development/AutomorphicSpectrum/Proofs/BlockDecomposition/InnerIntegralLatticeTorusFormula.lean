import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetInd
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WS
namespace InnTorus

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem rowAct_torusPow (l : Fin 2 → ℤ) (v : F × F) :
    rowAct (Iwasawa.torusPow F 2 l) v =
      (v.1 * (GLnLocal.uniformizer F : F) ^ l 0, v.2 * (GLnLocal.uniformizer F : F) ^ l 1) := by
  have h : (Iwasawa.torusPow F 2 l).val = diagonal fun i => (GLnLocal.uniformizer F : F) ^ l i :=
    Iwasawa.coe_torusPow F 2 l
  unfold rowAct
  rw [h]
  simp [Matrix.diagonal]

theorem unif_ne_zero : (GLnLocal.uniformizer F : F) ≠ 0 :=
  (Iwasawa.uniformizerUnit F).ne_zero

theorem ord_mul_unif_zpow {x : F} (hx : x ≠ 0) (k : ℤ) :
    ord (x * (GLnLocal.uniformizer F : F) ^ k) = ord x + k := by
  have h := ord_units_zpow (Iwasawa.uniformizerUnit F) k
  have hz : (((Iwasawa.uniformizerUnit F ^ k : Fˣ)) : F) = (GLnLocal.uniformizer F : F) ^ k := by
    simp [Units.val_zpow_eq_zpow_val]
  rw [hz, Iwasawa.coe_uniformizerUnit, ord_uniformizer (GLnLocal.irreducible_uniformizer F),
    mul_one] at h
  rw [ord_mul hx (zpow_ne_zero _ unif_ne_zero), h]

theorem mul_unif_zpow_mem_iff {x : F} (hx : x ≠ 0) (k : ℤ) :
    x * (GLnLocal.uniformizer F : F) ^ k ∈ valBall F 0 ↔ -k ≤ ord x := by
  rw [mem_valBall_iff_le_ord (mul_ne_zero hx (zpow_ne_zero _ unif_ne_zero)), ord_mul_unif_zpow hx]
  omega

theorem mul_mul_unif_zpow_mem_iff {u : F} (hu : u ≠ 0) (y : F) (k : ℤ) :
    u * y * (GLnLocal.uniformizer F : F) ^ k ∈ valBall F 0 ↔ y ∈ valBall F (-ord u - k) := by
  by_cases hy : y = 0
  · simp [hy, zero_mem]
  rw [mul_unif_zpow_mem_iff (mul_ne_zero hu hy), mem_valBall_iff_le_ord hy, ord_mul hu hy]
  omega

variable [MeasurableSpace F] [BorelSpace F]

theorem selfDualMeasure_eq {χ : AddChar F Circle} (hχ : IsStd χ) :
    selfDualMeasure χ = haarIntegers F := by
  unfold GroundTheory.LocalField.selfDualMeasure
  rw [hχ.2.2]
  simp

theorem integral_indicator_valBall {χ : AddChar F Circle} (hχ : IsStd χ) (m : ℤ) :
    ∫ y, (valBall F m : Set F).indicator (fun y => ((χ (-y) : Circle) : ℂ)) y ∂haarIntegers F =
      if 0 ≤ m then (residueCard F : ℂ) ^ (-m) else 0 := by
  have ht : IsTrivialOn χ 0 := by
    have := isTrivialOn_addCharConductor hχ.1 hχ.2.1
    rwa [hχ.2.2] at this
  split_ifs with hm
  · have h1 : Set.EqOn (fun y => ((χ (-y) : Circle) : ℂ)) (fun _ => (1 : ℂ)) (valBall F m : Set F) := by
      intro y hy
      have hy0 : -y ∈ valBall F 0 := neg_mem (valBall_antitone hm hy)
      simp [ht _ hy0]
    rw [integral_indicator (measurableSet_valBall m),
      setIntegral_congr_fun (measurableSet_valBall m) h1, setIntegral_const, measureReal_def,
      haarIntegers_valBall, ENNReal.coe_toReal]
    simp
  · have hnot := not_isTrivialOn_addCharConductor_sub_one hχ.1 hχ.2.1
    rw [hχ.2.2] at hnot
    unfold IsTrivialOn at hnot
    push_neg at hnot
    obtain ⟨y₀, hy₀, hne⟩ := hnot
    have hy₀m : y₀ ∈ valBall F m := valBall_antitone (by omega) hy₀
    set f : F → ℂ := (valBall F m : Set F).indicator (fun y => ((χ (-y) : Circle) : ℂ)) with hf
    have shift : ∀ y, f (y + y₀) = ((χ (-y₀) : Circle) : ℂ) * f y := by
      intro y
      by_cases hy : y ∈ valBall F m
      · have hy' : y + y₀ ∈ valBall F m := add_mem hy hy₀m
        rw [hf, Set.indicator_of_mem (show y + y₀ ∈ (valBall F m : Set F) from hy'),
          Set.indicator_of_mem (show y ∈ (valBall F m : Set F) from hy), neg_add, add_comm,
          AddChar.map_add_eq_mul, Circle.coe_mul]
      · have hy' : y + y₀ ∉ valBall F m := fun h => hy (by simpa using sub_mem h hy₀m)
        rw [hf, Set.indicator_of_notMem (show y + y₀ ∉ (valBall F m : Set F) from hy'),
          Set.indicator_of_notMem (show y ∉ (valBall F m : Set F) from hy), mul_zero]
    have hI : ∫ y, f y ∂haarIntegers F = ((χ (-y₀) : Circle) : ℂ) * ∫ y, f y ∂haarIntegers F := by
      rw [← integral_const_mul, ← integral_add_right_eq_self f y₀]
      exact integral_congr_ae (Filter.Eventually.of_forall shift)
    have hc : ((χ (-y₀) : Circle) : ℂ) ≠ 1 := by
      intro h
      apply hne
      have h' : χ (-y₀) = 1 := Circle.ext (by simpa using h)
      rw [AddChar.map_neg_eq_inv, inv_eq_one] at h'
      exact h'
    have h0 : (1 - ((χ (-y₀) : Circle) : ℂ)) * ∫ y, f y ∂haarIntegers F = 0 := by
      rw [sub_mul, one_mul, ← hI, sub_self]
    exact (mul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hc.symm)

theorem mp_one_inv (u : Fˣ) : (mp u 1)⁻¹ = (residueCard F : ℂ) ^ ord (u : F) := by
  unfold mp
  rw [Complex.cpow_one, modulus_of_ne_zero u.ne_zero]
  push_cast
  rw [_root_.zpow_neg, inv_inv]

theorem inner_integral_standard_lattice_torus : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (χ : AddChar F Circle), IsStd χ → ∀ (l : Fin 2 → ℤ) (u : Fˣ), GlobalTheory.CompanionTheory.WS.inn χ (GlobalTheory.CompanionTheory.WS.lat0 F ∘ GlobalTheory.CompanionTheory.WS.rowAct (Iwasawa.torusPow F 2 l)) u = if -(l 0) ≤ ord (u : F) ∧ ord (u : F) ≤ -(l 1) then ((Spherical.qF F : ℕ) : ℂ) ^ (l 1) * (mp u 1)⁻¹ else 0 := by
  intro F _ _ _ _ _ _ χ hχ l u
  have hpt : ∀ y : F, (lat0 F ∘ rowAct (Iwasawa.torusPow F 2 l)) ((u : F), (u : F) * y) *
      ((χ (-y) : Circle) : ℂ) = if -(l 0) ≤ ord (u : F) then
        (valBall F (-ord (u : F) - l 1) : Set F).indicator (fun y => ((χ (-y) : Circle) : ℂ)) y
        else 0 := by
    intro y
    have h1 := mul_unif_zpow_mem_iff u.ne_zero (l 0)
    have h2 := mul_mul_unif_zpow_mem_iff u.ne_zero y (l 1)
    simp only [Function.comp, rowAct_torusPow, lat0]
    by_cases hA : -(l 0) ≤ ord (u : F)
    · rw [if_pos hA]
      by_cases hy : y ∈ valBall F (-ord (u : F) - l 1)
      · rw [Set.indicator_of_mem (show ((u : F) * (GLnLocal.uniformizer F : F) ^ l 0,
            (u : F) * y * (GLnLocal.uniformizer F : F) ^ l 1) ∈ Ln F 0 from ⟨h1.2 hA, h2.2 hy⟩),
          Set.indicator_of_mem (show y ∈ (valBall F (-ord (u : F) - l 1) : Set F) from hy)]
        simp
      · rw [Set.indicator_of_notMem (show ((u : F) * (GLnLocal.uniformizer F : F) ^ l 0,
            (u : F) * y * (GLnLocal.uniformizer F : F) ^ l 1) ∉ Ln F 0 from fun h => hy (h2.1 h.2)),
          Set.indicator_of_notMem (show y ∉ (valBall F (-ord (u : F) - l 1) : Set F) from hy)]
        simp
    · rw [if_neg hA, Set.indicator_of_notMem (show ((u : F) * (GLnLocal.uniformizer F : F) ^ l 0,
          (u : F) * y * (GLnLocal.uniformizer F : F) ^ l 1) ∉ Ln F 0 from fun h => hA (h1.1 h.1))]
      simp
  unfold inn
  rw [selfDualMeasure_eq hχ]
  simp_rw [hpt]
  have hq : Spherical.qF F = residueCard F := rfl
  have hq0 : (residueCard F : ℂ) ≠ 0 := by exact_mod_cast residueCard_ne_zero
  by_cases hA : -(l 0) ≤ ord (u : F)
  · simp only [if_pos hA, integral_indicator_valBall hχ]
    by_cases hD : ord (u : F) ≤ -(l 1)
    · rw [if_pos (by omega), if_pos ⟨hA, hD⟩, mp_one_inv, hq, ← zpow_add₀ hq0]
      congr 1
      omega
    · rw [if_neg (by omega), if_neg (fun h => hD h.2)]
  · rw [if_neg (fun h => hA h.1)]
    simp [if_neg hA]

end InnTorus
end GlobalTheory.CompanionTheory.WS
