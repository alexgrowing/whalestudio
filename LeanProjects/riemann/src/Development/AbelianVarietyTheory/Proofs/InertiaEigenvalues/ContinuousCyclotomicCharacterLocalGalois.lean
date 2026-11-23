import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfRetract
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2

namespace GlobalTheory.FunctorialityH2

theorem cyc_char_continuous {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
    {G : Type} [Group G] [TopologicalSpace G] (hO : PadicCoeff p O) (i : G ≃ₜ* GK p K)
    {ε : G →* Oˣ} (hc : IsCyc p K (carry i ε)) :
    Continuous (fun g : G => ((ε g : Oˣ) : O)) := by
  have := hO.ring
  set ε' : GK p K →* Oˣ := carry i ε with hε'
  have key : ∀ k : ℕ, ∃ H : Subgroup (GK p K), IsOpen (H : Set (GK p K)) ∧
      ∀ h ∈ H, ((ε' h : Oˣ) : O) - 1 ∈ Ideal.span {(p : O) ^ k} := by
    intro k
    have hN : 0 < p ^ k := pow_pos hp.out.pos k
    haveI : NeZero ((p ^ k : ℕ) : PadicAlgCl p) := ⟨by exact_mod_cast hN.ne'⟩
    obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (p ^ k) (PadicAlgCl p))
      (Polynomial.degree_cyclotomic_pos (p ^ k) (PadicAlgCl p) hN).ne'
    have hpr : IsPrimitiveRoot ζ (p ^ k) := Polynomial.isRoot_cyclotomic_iff.1 hζ
    have hint : IsIntegral K ζ :=
      IsIntegral.of_pow hN (by rw [hpr.pow_eq_one]; exact isIntegral_one)
    haveI := IntermediateField.adjoin.finiteDimensional hint
    refine ⟨(IntermediateField.adjoin K {ζ}).fixingSubgroup,
      IntermediateField.fixingSubgroup_isOpen _, fun h hh => ?_⟩
    have hfix : h ζ = ζ := hh ⟨ζ, IntermediateField.mem_adjoin_simple_self K ζ⟩
    obtain ⟨a, ha, hmem⟩ := hc h k ζ hpr.pow_eq_one
    have hz : ζ ≠ 0 := hpr.ne_zero hN.ne'
    have h1 : ζ ^ ((a : ℤ) - 1) = 1 := by
      rw [zpow_sub₀ hz, zpow_natCast, zpow_one, ← ha, hfix, div_self hz]
    obtain ⟨c, hcdef⟩ := (hpr.zpow_eq_one_iff_dvd _).1 h1
    have h2 : ((a : O) - 1) = ((p : O) ^ k) * (c : O) := by
      have := congrArg (fun z : ℤ => (z : O)) hcdef
      push_cast at this
      exact this
    have h3 : ((ε' h : Oˣ) : O) - 1 = (((ε' h : Oˣ) : O) - a) + ((a : O) - 1) := by ring
    rw [h3, h2]
    exact Ideal.add_mem _ hmem (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  have hcont' : Continuous (fun g : GK p K => ((ε' g : Oˣ) : O)) := by
    rw [continuous_iff_continuousAt]
    intro g0
    rw [ContinuousAt, Filter.tendsto_def]
    intro U hU
    have hV : (fun o : O => ((ε' g0 : Oˣ) : O) + o) ⁻¹' U ∈ nhds (0 : O) :=
      (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hU)
    obtain ⟨m, hm⟩ := (isAdic_iff.1 hO.adic).2 _ hV
    obtain ⟨H, hHo, hH⟩ := key m
    have hle : Ideal.span {(p : O) ^ m} ≤ IsLocalRing.maximalIdeal O ^ m :=
      (Ideal.span_singleton_le_iff_mem _).2 (Ideal.pow_mem_pow hO.p_mem m)
    refine Filter.mem_of_superset
      ((hHo.preimage (continuous_const_mul g0⁻¹)).mem_nhds (by simpa using H.one_mem)) ?_
    intro g hg
    have h1 := hH _ hg
    have h2 : ((ε' g : Oˣ) : O) - (ε' g0 : O) ∈ Ideal.span {(p : O) ^ m} := by
      have e : ((ε' g : Oˣ) : O) - (ε' g0 : O) =
          (ε' g0 : O) * (((ε' (g0⁻¹ * g) : Oˣ) : O) - 1) := by
        rw [map_mul, Units.val_mul, mul_sub, ← mul_assoc, ← Units.val_mul, ← map_mul,
          mul_inv_cancel, map_one, Units.val_one, one_mul, mul_one]
      rw [e]
      exact Ideal.mul_mem_left _ _ h1
    have h3 := hm (hle h2)
    simpa using h3
  have e : (fun g : G => ((ε g : Oˣ) : O)) = (fun g : GK p K => ((ε' g : Oˣ) : O)) ∘ i := by
    funext g
    simp only [Function.comp_apply, hε', carry, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
    first
    | rw [ContinuousMulEquiv.symm_apply_apply]
    | exact congrArg (fun x => ((ε x : Oˣ) : O)) (i.toMulEquiv.symm_apply_apply g).symm
  rw [e]
  exact hcont'.comp i.continuous

end GlobalTheory.FunctorialityH2
