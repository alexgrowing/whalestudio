import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem wcomp_self_eq_of_mem_wtPart {O σ X : Type} [CommRing O] [AddCommGroup X] {wt : σ → X} {j : X}
    {f : MvPowerSeries σ O} (hf : f ∈ wtPart O wt j) : wcomp O wt j f = f := by
  have hf' : ∀ n, Finsupp.weight wt n ≠ j → MvPowerSeries.coeff n f = 0 := hf
  ext n
  rw [coeff_wcomp]
  by_cases h1 : Finsupp.weight wt n = j
  · rw [if_pos h1]
  · rw [if_neg h1]
    exact (hf' n h1).symm

private theorem wcomp_eq_zero_of_mem_wtPart_of_ne {O σ X : Type} [CommRing O] [AddCommGroup X] {wt : σ → X} {j : X}
    {f : MvPowerSeries σ O} (hf : f ∈ wtPart O wt j) {j' : X} (hj : j' ≠ j) : wcomp O wt j' f = 0 := by
  have hf' : ∀ n, Finsupp.weight wt n ≠ j → MvPowerSeries.coeff n f = 0 := hf
  ext n
  rw [coeff_wcomp, map_zero]
  by_cases h1 : Finsupp.weight wt n = j'
  · rw [if_pos h1]
    exact hf' n (by rw [h1]; exact hj)
  · rw [if_neg h1]

private theorem aGraded_internal {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime]
    {c : Coef l} {D : Raw Ω c} (M : Model D) : DirectSum.IsInternal M.gr := by
  have key : ∀ (n : ℤ) (x : M.R), x ∈ M.aPart n → x ∈ (⨆ (m : ℤ) (_ : m ≠ n), M.aPart m) → x = 0 := by
    intro n x hx hx'
    have hle : (⨆ (m : ℤ) (_ : m ≠ n), M.aPart m) ≤
        Submodule.map M.W.π.toLinearMap
          (LinearMap.ker (M.W.π.toLinearMap ∘ₗ wcomp c.O M.W.wt ((0 : ℤ), n))) := by
      refine iSup₂_le fun m hm => ?_
      rintro y ⟨h, hh, rfl⟩
      refine ⟨h, ?_, rfl⟩
      change M.W.π (wcomp c.O M.W.wt ((0 : ℤ), n) h) = 0
      rw [wcomp_eq_zero_of_mem_wtPart_of_ne hh, map_zero]
      intro h'
      exact hm (Prod.ext_iff.mp h').2.symm
    obtain ⟨g, hg, hgx⟩ := hle hx'
    obtain ⟨f, hf, rfl⟩ := hx
    have hker : f - g ∈ RingHom.ker M.W.π := by
      rw [RingHom.mem_ker, map_sub]
      exact sub_eq_zero.mpr hgx.symm
    have h2 := M.W.homog _ hker ((0 : ℤ), n)
    rw [RingHom.mem_ker, map_sub, map_sub] at h2
    have hg' : M.W.π (wcomp c.O M.W.wt ((0 : ℤ), n) g) = 0 := hg
    have h3 : M.W.π (wcomp c.O M.W.wt ((0 : ℤ), n) f) = M.W.π f := by
      rw [wcomp_self_eq_of_mem_wtPart hf]
    change M.W.π f = 0
    calc M.W.π f = M.W.π (wcomp c.O M.W.wt ((0 : ℤ), n) f) := h3.symm
      _ = M.W.π (wcomp c.O M.W.wt ((0 : ℤ), n) g) := sub_eq_zero.mp h2
      _ = 0 := hg'
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · rw [iSupIndep_def]
    intro n
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have h1 : (x : M.R) ∈ M.aPart n := hx
    have h2 : (x : M.R) ∈ (⨆ (m : ℤ) (_ : m ≠ n), M.aPart m) := by
      have := Submodule.mem_map_of_mem (f := M.A.val.toLinearMap) hx'
      simp only [Submodule.map_iSup] at this
      exact (iSup₂_mono fun m _ => Submodule.map_comap_le _ _) this
    exact Subtype.ext (key n _ h1 h2)
  · refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨y, hy⟩ := x
    have main : ∀ (z : M.R) (hz : z ∈ ⨆ n, M.aPart n), (⟨z, hz⟩ : M.A) ∈ ⨆ n, M.gr n := by
      intro z hz
      refine Submodule.iSup_induction' M.aPart
        (motive := fun z hz => (⟨z, hz⟩ : M.A) ∈ ⨆ n, M.gr n) ?_ ?_ ?_ hz
      · intro n w hw
        exact Submodule.mem_iSup_of_mem n hw
      · exact zero_mem _
      · intro a b ha hb iha ihb
        exact add_mem iha ihb
    exact main y hy

theorem UpperTheory.V.GradeZeroInterpolatingElement.aGraded :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, Nonempty (GradedAlgebra M.gr) := by
  intro Ω _ _ _ l _ c D _ M
  exact ⟨{ (inferInstance : SetLike.GradedMonoid M.gr), (aGraded_internal M).chooseDecomposition with }⟩
