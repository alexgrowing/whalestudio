import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.PlusEq

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

private theorem wt_root : ∀ i j : Fin 4, i ≠ j → wt i j ∈ roots := by
  decide

private theorem rt_wt' {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) (g : Γ)
    (h : Φ.χ 0 g * Φ.χ 3 g = Φ.χ 1 g * Φ.χ 2 g) (i j : Fin 4) : Φ.rt (wt i j) g * Φ.χ j g = Φ.χ i g := by
  have hd : Φ.χ 3 g = (Φ.χ 0 g)⁻¹ * (Φ.χ 1 g * Φ.χ 2 g) := eq_inv_mul_of_mul_eq h
  fin_cases i <;> fin_cases j <;> simp [Fr.rt, wt, lamW, muW, hd] <;>
    apply Additive.ofMul.injective <;> simp <;> abel

theorem UpperTheory.V.Ws.Lk.cbInj :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (X : OCh T c' h), T.Ok → Function.Injective X.cb := by
  intro Ω _ _ _ l _ c D T c' h X hT i j hij
  by_contra hne
  obtain ⟨g, hgL, hg⟩ := hT.g3 _ (wt_root i j hne)
  obtain ⟨g', rfl⟩ := ((galEq T).2.2 g).1 hgL
  have hrel : (T.fr ∅).χ 0 (resLe T.F_le g') * (T.fr ∅).χ 3 (resLe T.F_le g') =
      (T.fr ∅).χ 1 (resLe T.F_le g') * (T.fr ∅).χ 2 (resLe T.F_le g') := by
    simp only [Tower.fr, MonoidHom.coe_comp, Function.comp_apply, chi]
    cases T.pr <;> simp [lab, Raw.ps, Raw.th, mul_comm]
  have key := rt_wt' (T.fr ∅) (resLe T.F_le g') hrel i j
  have hcb := congrArg (fun φ => ((φ g' : (ResidueField c'.O)ˣ) : ResidueField c'.O)) hij
  simp only [OCh.cb_val] at hcb
  simp only [Tower.rb] at hg
  set r := (T.fr ∅).rt (wt i j) (resLe T.F_le g') with hr_def
  have key' : ((r : c.O) * (chi D T.pr j (resQ T.L g') : c.O)) = (chi D T.pr i (resQ T.L g') : c.O) := by
    rw [← Units.val_mul]
    exact congrArg Units.val key
  rw [← key'] at hcb
  simp only [map_mul] at hcb
  have hu1 : residue c'.O (X.κ g' : c'.O) ≠ 0 := ((X.κ g').isUnit.map (residue c'.O)).ne_zero
  have hu2 : residue c'.O (inc h (chi D T.pr j (resQ T.L g') : c.O)) ≠ 0 :=
    (((chi D T.pr j (resQ T.L g')).isUnit.map (inc h)).map (residue c'.O)).ne_zero
  have hr : residue c'.O (inc h (r : c.O)) = 1 := by
    have h1 := mul_left_cancel₀ hu1 hcb
    exact mul_right_cancel₀ hu2 (h1.trans (one_mul _).symm)
  apply hg
  by_contra hne1
  have hmem : (r : c.O) - 1 ∉ maximalIdeal c.O := by
    intro hm
    apply hne1
    rw [← sub_eq_zero, ← map_one (residue c.O), ← map_sub]
    exact (residue_eq_zero_iff _).2 hm
  have hunit : IsUnit ((r : c.O) - 1) := by
    by_contra hn
    exact hmem ((mem_maximalIdeal _).2 hn)
  have hu := (hunit.map (inc h)).map (residue c'.O)
  rw [map_sub, map_sub, map_one, map_one, hr, sub_self] at hu
  exact not_isUnit_zero hu
