import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.RepIndep

theorem UpperTheory.V.Z.Sym.Tf.rLin :
    UpperTheory.V.Z.Sym.Tf.RLin := by
  classical
  intro Γ G V _ _ _ _ B s I S c f hf
  have hT : {x : G ⧸ B.U | ∃ i ∈ S, f i (s.θ x.out) ≠ 0}.Finite := by
    refine (Set.Finite.biUnion S.finite_toSet (fun i hi => (hf i hi).fin)).subset ?_
    rintro x ⟨i, hi, hx⟩
    exact Set.mem_biUnion (show i ∈ (S : Set I) from hi) hx
  have htest : s.IsTest (fun y => ∑ i ∈ S, c i * f i y) := by
    refine ⟨fun u y => ?_, fun u y => ?_, hT.subset ?_⟩
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [(hf i hi).left]; ring
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [(hf i hi).right]; ring
    · intro x hx
      obtain ⟨i, hi, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
      exact ⟨i, hi, right_ne_zero_of_mul h⟩
  refine ⟨htest, ?_⟩
  refine LinearMap.ext fun φ => Subtype.ext ?_
  rw [UpperTheory.V.Z.Sym.Tf.rSpec Γ G V B s _ htest φ, LinearMap.sum_apply, Submodule.coe_sum]
  funext g
  rw [Finset.sum_apply]
  have key : ∀ h : G → ℂ, (∀ x : G ⧸ B.U, h (s.θ x.out) ≠ 0 → ∃ i ∈ S, f i (s.θ x.out) ≠ 0) →
      s.opF h φ.1 g = ∑ x ∈ hT.toFinset, h (s.θ x.out) • s.Θ (φ.1 (s.θ.symm g * x.out)) := by
    intro h hh
    refine finsum_eq_sum_of_support_subset _ fun x hx => ?_
    rw [Set.Finite.coe_toFinset]
    exact hh x (left_ne_zero_of_smul hx)
  rw [key _ (fun x hx => by
    obtain ⟨i, hi, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    exact ⟨i, hi, right_ne_zero_of_mul h⟩)]
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply,
    UpperTheory.V.Z.Sym.Tf.rSpec Γ G V B s _ (hf i hi) φ, key _ (fun x hx => ⟨i, hi, hx⟩), Finset.smul_sum]
  simp only [mul_smul]
