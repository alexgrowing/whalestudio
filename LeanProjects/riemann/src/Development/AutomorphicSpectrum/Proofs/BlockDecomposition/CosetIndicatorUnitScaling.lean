import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetInd

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.WS

theorem unit_mul_mem_valBall_iff {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℤ) (t : Fˣ) (ht : t ∈ unitFiltrationUnits F 0) (y : F) :
    (t : F) * y ∈ valBall F n ↔ y ∈ valBall F n := by
  have h0 : ord (t : F) = 0 := mem_unitFiltrationUnits_zero_iff_ord.1 ht
  by_cases hy : y = 0
  · simp [hy]
  rw [mem_valBall_iff_le_ord (mul_ne_zero t.ne_zero hy), mem_valBall_iff_le_ord hy,
    ord_mul t.ne_zero hy, h0, zero_add]

theorem cosetInd_unit_smul : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (n : ℤ) (x : F × F) (t : Fˣ),
    t ∈ unitFiltrationUnits F 0 →
      GlobalTheory.CompanionTheory.WS.cosetInd n ((t : F) • x) = fun v => GlobalTheory.CompanionTheory.WS.cosetInd n x (((t⁻¹ : Fˣ) : F) • v) := by
  intro F _ _ _ _ _ _ n x t ht
  have hti : t⁻¹ ∈ unitFiltrationUnits F 0 := inv_mem ht
  have hc : ∀ a b : F, a - (t : F) * b ∈ valBall F n ↔
      ((t⁻¹ : Fˣ) : F) * a - b ∈ valBall F n := by
    intro a b
    have e : ((t⁻¹ : Fˣ) : F) * (a - (t : F) * b) = ((t⁻¹ : Fˣ) : F) * a - b := by
      rw [mul_sub, ← mul_assoc, Units.inv_mul, one_mul]
    rw [← e, unit_mul_mem_valBall_iff n t⁻¹ hti]
  have hs : ∀ v : F × F, v - (t : F) • x ∈ Ln F n ↔ ((t⁻¹ : Fˣ) : F) • v - x ∈ Ln F n := by
    intro v
    simp only [Ln, Set.mem_ofPred_eq, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul, hc]
  funext v
  have hm : v ∈ {w : F × F | w - (t : F) • x ∈ Ln F n} ↔
      ((t⁻¹ : Fˣ) : F) • v ∈ {w : F × F | w - x ∈ Ln F n} := hs v
  unfold cosetInd
  by_cases h : v ∈ {w : F × F | w - (t : F) • x ∈ Ln F n}
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hm.1 h)]
    rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (hm.2 h'))]

end GlobalTheory.CompanionTheory.WS
