import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityNormalizedBorelJacquetUn

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

private theorem inv_int {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] [LinearOrder n] {c : GL n k}
    (hc : c ∈ GlobalTheory.SmGL.IwahoriOnto.lowerInt k n) (i j : n) : valuation k ((c⁻¹).val i j) ≤ 1 := by
  let M : Matrix n n 𝒪[k] := Matrix.of fun i j => ⟨c.val i j, hc.1 i j⟩
  have hdet : c.val.det = 1 := by
    rw [Matrix.det_of_lowerTriangular c.val fun i j hij => hc.2.1 i j hij]
    simp [hc.2.2]
  have hM : (algebraMap 𝒪[k] k).mapMatrix M = c.val := by ext i j; rfl
  have e : (c⁻¹).val = (algebraMap 𝒪[k] k).mapMatrix M.adjugate := by
    rw [RingHom.map_adjugate, hM, Matrix.coe_units_inv, Matrix.inv_def, hdet]
    simp
  rw [e]
  exact (M.adjugate i j).2

theorem UpperTheory.congruence_subgroup_eq_diagonal_unipotent_lower_iwahori :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (γ : (ValueGroupWithZero k)ˣ) (hγ : γ ≤ 1),
    ∀ g ∈ GlobalTheory.CentralExponent.cong (Fin N) γ hγ, ∃ d : Fin N → kˣ, (∀ i, valuation k ((d i : k) - 1) < γ) ∧
      ∃ x ∈ unipB k (Fin N), ∃ c ∈ GlobalTheory.SmGL.IwahoriOnto.lowerInt k (Fin N), g = diagT k (Fin N) d * x * c := by
  intro k _ _ _ _ N γ hγ g hg
  have hg' : ∀ i j, valuation k ((g.val - 1) i j) < γ := hg
  have h1 : g ∈ KOne k (Fin N) := GlobalTheory.StepData.mem_KOne.2 fun i j => (hg' i j).trans_le hγ
  have hI : g ∈ iwahori k (Fin N) := by
    refine mem_iwahori.2 ⟨GlobalTheory.StepData.KOne_le_KO h1, fun i j hij => ?_⟩
    have := (hg' i j).trans_le (show ((γ : ValueGroupWithZero k)) ≤ 1 from hγ)
    rwa [Matrix.sub_apply, Matrix.one_apply_ne hij.ne', sub_zero] at this
  obtain ⟨d, -, x, hx, c, hc, e⟩ := GlobalTheory.SmGL.IwahoriOnto.iwahori_factor k (Fin N) g hI
  refine ⟨d, fun i => ?_, x, hx, c, hc, e⟩
  have hcl : c ∈ unipBLower k (Fin N) :=
    (mem_unipB (n := (Fin N)ᵒᵈ) k).2 ⟨fun i j hij => hc.2.1 i j hij, hc.2.2⟩
  have hci : (c⁻¹).val i i = 1 := ((mem_unipB (n := (Fin N)ᵒᵈ) k).1 (inv_mem hcl)).2 i
  have h2 : (g * c⁻¹).val i i = d i := by
    rw [e, mul_inv_cancel_right, Units.val_mul, val_diagT, Matrix.diagonal_mul, ((mem_unipB k).1 hx).2 i, mul_one]
  have h3 : ((g.val - 1) * (c⁻¹).val) i i = (d i : k) - 1 := by
    rw [sub_mul, one_mul, Matrix.sub_apply, hci, ← Units.val_mul, h2]
  rw [← h3, Matrix.mul_apply]
  refine Valuation.map_sum_lt _ γ.ne_zero fun s _ => ?_
  rw [map_mul]
  exact (mul_le_of_le_one_right' (inv_int hc s i)).trans_lt (hg' i s)
