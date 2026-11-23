import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.LocalRepresentationL2

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

theorem UpperTheory.ConvolutionTheory.Dp.fixedDense :
    UpperTheory.ConvolutionTheory.Dp.FixedDense := by
  intro G H X _ _ _ _ _ _ _ ρ τ J U hU hρ hτ hJ hd v hv
  refine Metric.mem_closure_iff.2 fun ε hε => ?_
  obtain ⟨x, hx⟩ := hd.exists_dist_lt v hε
  have hfin : ((fun g => τ g x) '' (U : Set G)).Finite := by
    obtain ⟨t, -, ht⟩ := hU.elim_nhds_subcover (fun g => {h | τ h x = τ g x}) fun g _ => by
      have h1 : IsOpen ((fun h => g⁻¹ * h) ⁻¹' {g | τ g x = x}) := (hτ x).preimage (by fun_prop)
      refine Filter.mem_of_superset (h1.mem_nhds (by simp)) fun h hh => ?_
      have h2 : τ (g⁻¹ * h) x = x := hh
      show τ h x = τ g x
      conv_rhs => rw [← h2]
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
    refine (t.finite_toSet.image fun g => τ g x).subset ?_
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨i, hi, h⟩ := Set.mem_iUnion₂.1 (ht hg)
    exact ⟨i, hi, (h : τ g x = τ i x).symm⟩
  classical
  set S := hfin.toFinset with hS
  have hm : ∀ y, y ∈ S ↔ ∃ g ∈ U, τ g x = y := fun y => by simp [hS]
  have hpos : 0 < S.card := Finset.card_pos.2 ⟨x, (hm x).2 ⟨1, U.one_mem, by simp⟩⟩
  have hc : (S.card : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hpos.ne'
  have hc' : (S.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hpos.ne'
  have hst : ∀ u ∈ U, ∀ y ∈ S, τ u y ∈ S := fun u hu y hy => by
    obtain ⟨g, hg, rfl⟩ := (hm y).1 hy
    exact (hm _).2 ⟨u * g, U.mul_mem hu hg, by rw [map_mul]; rfl⟩
  refine ⟨_, ⟨(S.card : ℂ)⁻¹ • ∑ y ∈ S, y, fun u hu => ?_, rfl⟩, ?_⟩
  · rw [map_smul, map_sum]
    congr 1
    refine Finset.sum_nbij' (τ u) (τ u⁻¹) (hst u hu) (hst _ (U.inv_mem hu)) (fun y _ => ?_) (fun y _ => ?_) fun _ _ => rfl
    · rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
    · rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]; rfl
  · have e : v - J ((S.card : ℂ)⁻¹ • ∑ y ∈ S, y) = (S.card : ℂ)⁻¹ • ∑ y ∈ S, (v - J y) := by
      rw [map_smul, map_sum, Finset.sum_sub_distrib, smul_sub, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
        inv_mul_cancel₀ hc', one_smul]
    have h1 : ∀ y ∈ S, ‖v - J y‖ = dist v (J x) := fun y hy => by
      obtain ⟨g, hg, rfl⟩ := (hm y).1 hy
      rw [hJ, dist_eq_norm, ← hρ g (v - J x), map_sub, hv g hg]
    rw [dist_eq_norm, e, norm_smul, norm_inv, Complex.norm_natCast]
    refine lt_of_le_of_lt ?_ hx
    rw [inv_mul_le_iff₀ (by exact_mod_cast hpos)]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
