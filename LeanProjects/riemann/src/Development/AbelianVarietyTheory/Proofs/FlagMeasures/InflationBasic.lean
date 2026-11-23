import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CongruenceNormalFiniteIndex
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeStabiliserIsCompactIsOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCountData

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.InflBasic

open GlobalTheory.RowLev.Inhab GlobalTheory.Mem.RowsBundle

theorem finite_of_red {I : AutInst} {g : ℕ} {Q : Type} [Group Q] (ρ : Red I g Q) (hg : 1 ≤ g) : Finite Q := by
  obtain ⟨-, hK⟩ := GlobalTheory.CongTop.congruence_normal_finite_index I
  obtain ⟨-, -, -, s, hs⟩ := hK g hg
  refine Finite.of_surjective (fun t : s => ρ.toFun t) ?_
  intro q
  obtain ⟨x, hx, rfl⟩ := ρ.surj q
  obtain ⟨t, ht, htx⟩ := hs x hx
  have hk : t⁻¹ * x ∈ I.Kset := htx.1
  have htK : t ∈ I.Kset := by
    have hmem := (Ksub I).mul_mem ((mem_Ksub I x).2 hx) ((Ksub I).inv_mem ((mem_Ksub I _).2 hk))
    rw [_root_.mul_inv_rev, inv_inv, mul_inv_cancel_left] at hmem
    exact (mem_Ksub I t).1 hmem
  refine ⟨⟨t, ht⟩, ?_⟩
  show ρ.toFun t = ρ.toFun x
  calc ρ.toFun t = ρ.toFun t * ρ.toFun (t⁻¹ * x) := by rw [(ρ.ker _ hk).2 htx, mul_one]
    _ = ρ.toFun (t * (t⁻¹ * x)) := (ρ.map_mul t htK _ hk).symm
    _ = ρ.toFun x := by rw [mul_inv_cancel_left]

theorem inflation_basic : ∀ (I : AutInst) (g : ℕ) (Q : Type) [Group Q] (ρ : Red I g Q) (μf : Measure I.Gf) [μf.IsHaarMeasure], 1 ≤ g → Finite Q ∧ 0 < (μf (I.Kg g)).toReal ∧ ρ.toFun 1 = 1 ∧ (∀ x ∈ I.Kset, ρ.toFun x⁻¹ = (ρ.toFun x)⁻¹) ∧ (∀ q : Q, μf {x | x ∈ I.Kset ∧ ρ.toFun x = q} = μf (I.Kg g) ∧ IsOpen {x | x ∈ I.Kset ∧ ρ.toFun x = q}) ∧ (∀ a, Integrable (ρ.lift μf a) μf ∧ IsLocallyConstant (ρ.lift μf a) ∧ ∀ x, ∀ k ∈ I.Kg g, ∀ k' ∈ I.Kg g, ρ.lift μf a (k * x * k') = ρ.lift μf a x) ∧ (∀ a b, ρ.lift μf (a + b) = ρ.lift μf a + ρ.lift μf b) ∧ (∀ (c : ℂ) a, ρ.lift μf (c • a) = c • ρ.lift μf a) ∧ ∀ a, ρ.lift μf a 1 = a.coeff 1 / ((μf (I.Kg g)).toReal : ℂ) := by
  intro I g Q _ ρ μf _ hg
  have hQ : Finite Q := finite_of_red ρ hg
  obtain ⟨-, hK⟩ := GlobalTheory.CongTop.congruence_normal_finite_index I
  obtain ⟨-, hopen, -, -⟩ := hK g hg
  obtain ⟨hcpt, -, -, -⟩ := GlobalTheory.adelicStab_isCompact_isOpen I
  have h1K : (1 : I.Gf) ∈ I.Kset := (mem_Ksub I 1).1 (Ksub I).one_mem
  have h1 : (1 : I.Gf) ∈ I.Kg g := (ρ.ker 1 h1K).1 ρ.map_one
  have hsub : I.Kg g ⊆ I.Kset := fun x hx => hx.1
  have hpos : 0 < (μf (I.Kg g)).toReal :=
    ENNReal.toReal_pos (hopen.measure_pos μf ⟨1, h1⟩).ne'
      ((measure_mono hsub).trans_lt hcpt.measure_lt_top).ne
  refine ⟨hQ, hpos, ρ.map_one, fun x hx => ρ.map_inv hx, ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨t, ht⟩ := fibre_eq ρ q
    rw [ht]
    exact ⟨measure_preimage_mul μf t _, hopen.preimage (continuous_mul_left t)⟩
  · intro a
    refine ⟨integrable_lift ρ μf hg a, ?_, fun x k hk k' hk' => lift_biinv ρ μf a x k hk k' hk'⟩
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hnhds : (fun y => x⁻¹ * y) ⁻¹' I.Kg g ∈ nhds x :=
      (hopen.preimage (continuous_mul_left x⁻¹)).mem_nhds (by
        show x⁻¹ * x ∈ I.Kg g
        rw [inv_mul_cancel]
        exact h1)
    filter_upwards [hnhds] with y hy
    have h := lift_biinv ρ μf a x 1 h1 (x⁻¹ * y) hy
    rwa [one_mul, mul_inv_cancel_left] at h
  · intro a b
    funext x
    by_cases hx : x ∈ I.Kset
    · rw [Pi.add_apply, ρ.lift_of_mem μf _ hx, ρ.lift_of_mem μf _ hx, ρ.lift_of_mem μf _ hx,
        MonoidAlgebra.coeff_add, Finsupp.add_apply, add_div]
    · rw [Pi.add_apply, ρ.lift_of_notMem μf _ hx, ρ.lift_of_notMem μf _ hx, ρ.lift_of_notMem μf _ hx,
        add_zero]
  · intro c a
    funext x
    by_cases hx : x ∈ I.Kset
    · rw [Pi.smul_apply, ρ.lift_of_mem μf _ hx, ρ.lift_of_mem μf _ hx, MonoidAlgebra.coeff_smul,
        Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, mul_div_assoc]
    · rw [Pi.smul_apply, ρ.lift_of_notMem μf _ hx, ρ.lift_of_notMem μf _ hx, smul_zero]
  · intro a
    rw [ρ.lift_of_mem μf a h1K, ρ.map_one]

end GlobalTheory.InflBasic
