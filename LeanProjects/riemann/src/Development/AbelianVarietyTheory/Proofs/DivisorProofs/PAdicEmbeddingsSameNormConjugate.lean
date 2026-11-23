import Mathlib
open NumberField Polynomial

noncomputable section
namespace GlobalTheory.CpAlgEmb

section Dense

variable {p : ℕ} [Fact p.Prime]

theorem denseRange_of_isAlgClosed {Ω : Type} [Field Ω] [IsAlgClosed Ω] (j : Ω →+* ℂ_[p]) :
    DenseRange j := by
  have : CharZero Ω := (RingHom.charZero_iff j.injective).2 inferInstance
  have hsub : Set.range ((↑) : PadicAlgCl p → ℂ_[p]) ⊆ closure (Set.range j) := by
    rintro _ ⟨z, rfl⟩
    rw [Metric.mem_closure_iff]
    intro δ δpos
    have hi : DenseRange (algebraMap ℚ ℚ_[p]) := Padic.denseRange_ratCast p
    have hint : IsIntegral ℚ_[p] z := Algebra.IsIntegral.isIntegral z
    set f := minpoly ℚ_[p] z with hf
    have fmon : f.Monic := minpoly.monic hint
    have fa0 : f.aeval ((z : ℂ_[p])) = 0 := by
      rw [PadicComplex.coe_eq, Polynomial.aeval_algebraMap_apply, minpoly.aeval, map_zero]
    have fnatdeg0 : f.natDegree ≠ 0 := (minpoly.natDegree_pos hint).ne'
    set a : ℂ_[p] := (z : ℂ_[p]) with ha
    have hε : (δ / (max ‖a‖ 1)) ^ f.natDegree / (f.natDegree + 1) > 0 := by positivity
    obtain ⟨g, gmon, gdeg, gcoeff⟩ :=
      exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hi fmon hε
    obtain ⟨b, hb, hab⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt (L := ℂ_[p])
        hε fa0 fmon (gmon.map _) (gdeg ▸ (g.natDegree_map _)) gcoeff (IsAlgClosed.splits _)
    have hab : ‖a - b‖ < δ := by
      rw [← Real.rpow_natCast, ← mul_comm_div, div_self, one_mul,
          ← Real.rpow_mul (div_pos δpos (by positivity)).le, mul_inv_cancel₀] at hab
      · simpa [mul_assoc, div_mul_cancel₀ _ (by positivity : (max ‖a‖ 1) > 0).ne'] using hab
      · simp [fnatdeg0]
      · positivity
    have e : (g.map (algebraMap ℚ ℚ_[p])).map (algebraMap ℚ_[p] ℂ_[p]) =
        (g.map (algebraMap ℚ Ω)).map j := by
      rw [Polynomial.map_map, Polynomial.map_map]
      congr 1
      exact Subsingleton.elim _ _
    rw [Polynomial.aroots_def, e, Splits.roots_map (IsAlgClosed.splits _), Multiset.mem_map] at hb
    obtain ⟨y, -, rfl⟩ := hb
    exact ⟨j y, ⟨y, rfl⟩, by rwa [dist_eq_norm]⟩
  exact dense_closure.mp (UniformSpace.Completion.denseRange_coe.mono hsub)

theorem exists_extend {Ω : Type} [Field Ω] (j j' : Ω →+* ℂ_[p]) (hd : DenseRange j)
    (h : ∀ x, ‖j' x‖ = ‖j x‖) :
    ∃ t : ℂ_[p] →+* ℂ_[p], Continuous t ∧ (∀ z, ‖t z‖ = ‖z‖) ∧ ∀ x, t (j x) = j' x := by
  let : NormedField Ω := NormedField.induced Ω ℂ_[p] j j.injective
  have hj : Isometry j := AddMonoidHomClass.isometry_of_norm j fun _ => rfl
  have hf : Isometry j' := AddMonoidHomClass.isometry_of_norm j' fun x => h x
  let t : ℂ_[p] →+* ℂ_[p] :=
    IsDenseInducing.extendRingHom hj.isUniformInducing hd hf.uniformContinuous
  have ht : ∀ x, t (j x) = j' x := fun x =>
    uniformly_extend_of_ind hj.isUniformInducing hd hf.uniformContinuous x
  have htc : Continuous t :=
    (uniformContinuous_uniformly_extend hj.isUniformInducing hd hf.uniformContinuous).continuous
  refine ⟨t, htc, fun z => ?_, ht⟩
  have := hd.equalizer (continuous_norm.comp htc) continuous_norm
    (funext fun x => by simp only [Function.comp_apply, ht, h])
  exact congrFun this z

end Dense

theorem exists_isometric_ringEquiv :
    ∀ (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime]
      (ι ι' : AlgebraicClosure F →+* ℂ_[p]), (∀ a, ‖ι a‖ = ‖ι' a‖) →
      ∃ σ : ℂ_[p] ≃+* ℂ_[p], (∀ z, ‖σ z‖ = ‖z‖) ∧ ∀ a, σ (ι' a) = ι a := by
  intro F _ _ p _ ι ι' h
  have hd := denseRange_of_isAlgClosed ι
  have hd' := denseRange_of_isAlgClosed ι'
  obtain ⟨t, htc, htn, ht⟩ := exists_extend ι' ι hd' (fun a => h a)
  obtain ⟨s, hsc, hsn, hs⟩ := exists_extend ι ι' hd (fun a => (h a).symm)
  have h1 : ∀ z, t (s z) = z := congrFun (hd.equalizer (htc.comp hsc) continuous_id
    (funext fun a => by simp only [Function.comp_apply, hs, ht, id]))
  have h2 : ∀ z, s (t z) = z := congrFun (hd'.equalizer (hsc.comp htc) continuous_id
    (funext fun a => by simp only [Function.comp_apply, hs, ht, id]))
  let σ : ℂ_[p] ≃+* ℂ_[p] :=
    { toFun := t, invFun := s, left_inv := h2, right_inv := h1, map_mul' := t.map_mul, map_add' := t.map_add }
  exact ⟨σ, htn, ht⟩

end GlobalTheory.CpAlgEmb
