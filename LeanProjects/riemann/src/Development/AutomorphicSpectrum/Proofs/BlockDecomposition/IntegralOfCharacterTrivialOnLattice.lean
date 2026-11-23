import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KvFintype
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.Jp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Jp.DualInt

private theorem trace_single_one_mul {n : ℕ} {R : Type} [CommRing R] (i j : Fin n) (c : R)
    (T : Matrix (Fin n) (Fin n) R) : (Matrix.single j i c * T).trace = c * T i j := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq]

theorem mem_of_dual_integral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : Pl D), GoodPsi D ψ v → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) (Fv D.host.F v)), (∀ X : Matrix (Fin n) (Fin n) (Fv D.host.F v), (∀ i j, X i j ∈ v.adicCompletionIntegers D.host.F) → psiV D.host.F ψ v (Matrix.trace (X * T)) = 1) → ∀ i j, T i j ∈ v.adicCompletionIntegers D.host.F := by
  intro D ψ v hψ n T hT i j
  by_contra hx
  set O := v.adicCompletionIntegers D.host.F with hO
  have hx0 : T i j ≠ 0 := by
    intro h
    exact hx (h ▸ O.zero_mem)
  have hy : (T i j)⁻¹ ∈ O := (O.mem_or_inv_mem (T i j)).resolve_left hx
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖ0 : (ϖ : v.adicCompletion D.host.F) ≠ 0 := by
    intro h
    exact hϖ.ne_zero (Subtype.ext h)
  have hw : (T i j)⁻¹ / (ϖ : v.adicCompletion D.host.F) ∈ O := by
    rcases O.mem_or_inv_mem ((T i j)⁻¹ / (ϖ : v.adicCompletion D.host.F)) with h | h
    · exact h
    · have h' : (ϖ : v.adicCompletion D.host.F) / (T i j)⁻¹ ∈ O := by
        simpa [inv_div] using h
      have hfac : ϖ = (⟨(T i j)⁻¹, hy⟩ : O) * ⟨_, h'⟩ := by
        apply Subtype.ext
        simp only [MulMemClass.coe_mul]
        field_simp
      rcases hϖ.isUnit_or_isUnit hfac with hu | hu
      · exfalso
        apply hx
        obtain ⟨u, hu⟩ := hu
        have hmem : (((u⁻¹ : Oˣ) : O) : v.adicCompletion D.host.F) ∈ O := Subtype.property _
        have heq : (((u⁻¹ : Oˣ) : O) : v.adicCompletion D.host.F) = T i j := by
          have h1 : (((u⁻¹ : Oˣ) : O) : v.adicCompletion D.host.F) * (((u : Oˣ) : O) : v.adicCompletion D.host.F) = 1 := by
            rw [← MulMemClass.coe_mul, Units.inv_mul]
            rfl
          rw [hu] at h1
          field_simp at h1
          simpa using h1
        exact heq ▸ hmem
      · obtain ⟨u, hu⟩ := hu
        have hmem : (((u⁻¹ : Oˣ) : O) : v.adicCompletion D.host.F) ∈ O := Subtype.property _
        have heq : (((u⁻¹ : Oˣ) : O) : v.adicCompletion D.host.F) = (T i j)⁻¹ / (ϖ : v.adicCompletion D.host.F) := by
          have h1 : (((u⁻¹ : Oˣ) : O) : v.adicCompletion D.host.F) * (((u : Oˣ) : O) : v.adicCompletion D.host.F) = 1 := by
            rw [← MulMemClass.coe_mul, Units.inv_mul]
            rfl
          rw [hu] at h1
          simp only at h1
          rw [eq_div_iff hϖ0]
          rw [div_inv_eq_mul, ← mul_assoc] at h1
          exact eq_inv_of_mul_eq_one_left h1
        exact heq ▸ hmem
  obtain ⟨b, hb⟩ := hψ.2 ϖ hϖ
  have hb2 : (b : v.adicCompletion D.host.F) ∈ O := b.2
  apply hb
  have hX := hT (Matrix.single j i ((b : v.adicCompletion D.host.F) * ((T i j)⁻¹ / (ϖ : v.adicCompletion D.host.F)))) (by
    intro k l
    rw [Matrix.single_apply]
    split_ifs
    · exact mul_mem hb2 hw
    · exact O.zero_mem)
  rw [trace_single_one_mul] at hX
  convert hX using 2
  field_simp

end GlobalTheory.CompanionTheory.Jp.DualInt
