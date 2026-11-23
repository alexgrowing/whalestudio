import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.ATrans

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.NearUnitLemmas

open scoped Classical

abbrev bU (F : Type) [Field F] [NumberField F] :=
  (NumberField.Units.basisUnitLattice F).ofZLatticeBasis ℝ (NumberField.Units.unitLattice F)

theorem abs_sg {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (v : InfinitePlace F) (x : F) :
    |sg v x| = v x := by
  simpa [Real.norm_eq_abs] using InfinitePlace.norm_embedding_of_isReal (IsTotallyReal.isReal v) x

theorem near_unit (F : Type) [Field F] [NumberField F] (a : NumberField.Units.dirichletUnitTheorem.logSpace F) :
    ∃ x : (𝓞 F)ˣ, ∀ w : {w : InfinitePlace F // w ≠ NumberField.Units.dirichletUnitTheorem.w₀},
      |a w - InfinitePlace.mult w.1 * Real.log (w.1 (x : F))| ≤ ∑ i, ‖bU F i‖ := by
  have hmem : (ZSpan.floor (bU F) a : NumberField.Units.dirichletUnitTheorem.logSpace F) ∈
      NumberField.Units.unitLattice F := by
    rw [← Module.Basis.ofZLatticeBasis_span ℝ (NumberField.Units.unitLattice F)
      (NumberField.Units.basisUnitLattice F)]
    exact (ZSpan.floor (bU F) a).2
  obtain ⟨x, -, hx⟩ := Submodule.mem_map.1 hmem
  refine ⟨x.toMul, fun w => ?_⟩
  have h1 : InfinitePlace.mult w.1 * Real.log (w.1 ((x.toMul : (𝓞 F)ˣ) : F)) =
      (ZSpan.floor (bU F) a : NumberField.Units.dirichletUnitTheorem.logSpace F) w := by
    rw [← hx]; rfl
  rw [h1]
  have h2 : a w - (ZSpan.floor (bU F) a : NumberField.Units.dirichletUnitTheorem.logSpace F) w =
      ZSpan.fract (bU F) a w := by rw [ZSpan.fract_apply]; rfl
  rw [h2, ← Real.norm_eq_abs]
  exact (norm_le_pi_norm _ w).trans (ZSpan.norm_fract_le _ _)

end UpperTheory.Esk.NearUnitLemmas

namespace UpperTheory.Esk

open UpperTheory.Esk.NearUnitLemmas in
theorem aUnit : UpperTheory.Esk.AUnit := by
  classical
  intro F _ _ _
  set M : ℝ := ∑ i, ‖bU F i‖ with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => norm_nonneg _
  refine ⟨Real.exp (2 * (Fintype.card (InfinitePlace F) * M)), Real.exp_pos _, fun y hy => ?_⟩
  set L : InfinitePlace F → ℝ := fun w => Real.log |y w|
  set m : ℝ := (∑ w, L w) / Fintype.card (InfinitePlace F)
  obtain ⟨x, hx⟩ := near_unit F (fun w => m - L w.1)
  set u : F := (x : F)
  have hmult : ∀ w : InfinitePlace F, InfinitePlace.mult w = 1 :=
    fun w => (IsTotallyReal.isReal w).mult_eq_one
  set d : InfinitePlace F → ℝ := fun w => Real.log (w u) + L w - m
  have hn : (Fintype.card (InfinitePlace F) : ℝ) ≠ 0 := by
    have : 0 < Fintype.card (InfinitePlace F) := Fintype.card_pos
    exact_mod_cast this.ne'
  have hsum : ∑ w, d w = 0 := by
    have h0 : ∑ w : InfinitePlace F, Real.log (w u) = 0 := by
      simpa [hmult] using NumberField.Units.sum_mult_mul_log x
    simp only [d, Finset.sum_sub_distrib, Finset.sum_add_distrib, h0, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, m]
    field_simp
    ring
  have hne : ∀ w : {w : InfinitePlace F // w ≠ NumberField.Units.dirichletUnitTheorem.w₀}, |d w| ≤ M := by
    intro w
    have := hx w
    rw [hmult, Nat.cast_one, one_mul] at this
    calc |d w| = |(m - L w.1) - Real.log (w.1 u)| := by
          rw [← abs_neg]; congr 1; simp only [d]; ring
      _ ≤ M := this
  have hall : ∀ w, |d w| ≤ Fintype.card (InfinitePlace F) * M := by
    intro w
    by_cases hw : w = NumberField.Units.dirichletUnitTheorem.w₀
    · subst hw
      have h := Fintype.sum_eq_add_sum_subtype_ne d NumberField.Units.dirichletUnitTheorem.w₀
      rw [hsum] at h
      have h' : d NumberField.Units.dirichletUnitTheorem.w₀ =
          -∑ w : {w : InfinitePlace F // w ≠ NumberField.Units.dirichletUnitTheorem.w₀}, d w := by
        linarith
      rw [h', abs_neg]
      calc |∑ w : {w : InfinitePlace F // w ≠ NumberField.Units.dirichletUnitTheorem.w₀}, d w|
          ≤ ∑ w : {w : InfinitePlace F // w ≠ NumberField.Units.dirichletUnitTheorem.w₀}, |d w| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _w : {w : InfinitePlace F // w ≠ NumberField.Units.dirichletUnitTheorem.w₀}, M :=
            Finset.sum_le_sum fun w _ => hne w
        _ = (Fintype.card {w : InfinitePlace F // w ≠ NumberField.Units.dirichletUnitTheorem.w₀} : ℝ) * M := by
            simp
        _ ≤ Fintype.card (InfinitePlace F) * M := by
            gcongr
            exact_mod_cast Fintype.card_subtype_le _
    · calc |d w| ≤ M := hne ⟨w, hw⟩
        _ ≤ Fintype.card (InfinitePlace F) * M := by
          have : (1 : ℝ) ≤ Fintype.card (InfinitePlace F) := by exact_mod_cast Fintype.card_pos
          nlinarith
  have hu0 : ∀ w : InfinitePlace F, 0 < w u := fun w => NumberField.Units.pos_at_place x w
  have hval : ∀ w, |sg w u * y w| = Real.exp (d w + m) := by
    intro w
    simp only [d, L]
    rw [abs_mul, abs_sg, sub_add_cancel, Real.exp_add, Real.exp_log (hu0 w),
      Real.exp_log (abs_pos.2 (hy w))]
  refine ⟨u, ?_, ?_, ?_, fun v v' => ?_⟩
  · intro h
    have := hu0 NumberField.Units.dirichletUnitTheorem.w₀
    rw [h, map_zero] at this
    exact lt_irrefl _ this
  · exact NumberField.RingOfIntegers.isIntegral_coe (x : 𝓞 F)
  · have : u⁻¹ = ((x⁻¹ : (𝓞 F)ˣ) : F) := by simp [u]
    rw [this]
    exact NumberField.RingOfIntegers.isIntegral_coe ((x⁻¹ : (𝓞 F)ˣ) : 𝓞 F)
  · rw [hval, hval, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 := (abs_le.1 (hall v)).2
    have h2 := (abs_le.1 (hall v')).1
    linarith

end UpperTheory.Esk
