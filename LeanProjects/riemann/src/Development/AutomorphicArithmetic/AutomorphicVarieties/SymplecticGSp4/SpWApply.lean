import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.GradeZeroInterpolatingElement

private theorem prj_fst {O : Type} [CommRing O] (c : Fin 4 → O) (X : M4 (DualNumber O))
    (hX : ∀ a b, (X a b).fst = Matrix.diagonal c a b) (i a b : Fin 4) :
    (prj (fun a => algebraMap O (DualNumber O) (c a)) X i a b).fst =
      if a = i ∧ b = i then ∏ j ∈ Finset.univ.erase i, (c i - c j) else 0 := by
  have hp : (∏ j ∈ Finset.univ.erase i,
      (Polynomial.X - Polynomial.C ((fun a => algebraMap O (DualNumber O) (c a)) j))) =
      (∏ j ∈ Finset.univ.erase i, (Polynomial.X - Polynomial.C (c j))).map (algebraMap O (DualNumber O)) := by
    simp [Polynomial.map_prod]
  have hF : ∀ P : M4 (DualNumber O), (P a b).fst = ((TrivSqZeroExt.fstHom O O O).mapMatrix P) a b :=
    fun P => rfl
  have hXm : (TrivSqZeroExt.fstHom O O O).mapMatrix X = Matrix.diagonalAlgHom O c := by
    ext a b
    exact hX a b
  unfold prj
  rw [hp, Polynomial.aeval_map_algebraMap, hF, ← Polynomial.aeval_algHom_apply, hXm,
    Polynomial.aeval_algHom_apply, Matrix.diagonalAlgHom_apply, Matrix.diagonal_apply]
  simp only [map_prod, Finset.prod_apply, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Pi.sub_apply,
    Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  by_cases hab : a = b
  · subst hab
    by_cases hai : a = i
    · subst hai
      simp
    · rw [if_pos rfl, if_neg (fun h => hai h.1)]
      exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hai, Finset.mem_univ _⟩) (sub_self _)
  · rw [if_neg hab, if_neg (fun h => hab (h.1.trans h.2.symm))]

private theorem triple {O : Type} [CommRing O] (A B C : M4 (DualNumber O)) (p q : Fin 4) (α γ : O) (β : Fin 4 → O)
    (hA : ∀ a b, (A a b).fst = if a = p ∧ b = p then α else 0)
    (hC : ∀ a b, (C a b).fst = if a = q ∧ b = q then γ else 0)
    (hB : ∀ a b, (B a b).fst = Matrix.diagonal β a b) :
    ((A * B * C) p q).snd = (A p q).snd * β q * γ + α * (B p q).snd * γ + α * β p * (C p q).snd := by
  simp only [Matrix.mul_apply, Fin.sum_univ_four, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_mul,
    TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_add, hA, hB, hC, Matrix.diagonal_apply, smul_eq_mul, op_smul_eq_mul]
  fin_cases p <;> fin_cases q <;> simp <;> ring

private theorem spW_apply {O : Type} [CommRing O] {w : ℤ × ℤ} {X : M4 O} (hX : X ∈ spW O w) :
    adj X = -X ∧ ∀ i j, wt i j ≠ w → X i j = 0 := by
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hX
  refine ⟨h1, fun i j hij => ?_⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, Matrix.entryLinearMap_apply] at h2
  exact h2 i j hij

private theorem spW_neg {O : Type} [CommRing O] {X : M4 O} (hX : X ∈ spW O (-wPs)) : X = X 2 0 • Xm O := by
  obtain ⟨hadj, hz⟩ := spW_apply hX
  have h31 := congrFun (congrFun hadj 3) 1
  simp [adj_apply, sgn] at h31
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Xm, Matrix.single_apply] <;>
    first | exact h31 | exact h31.symm | exact hz _ _ (by simp [wt, lamW, muW, wPs])

end UpperTheory.V.GradeZeroInterpolatingElement

theorem UpperTheory.V.GradeZeroInterpolatingElement.tanLz :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → (∀ z ∈ D.tanSet l (fun _ _ _ ρ => D.eqL ρ) (-wPs), ∃ a m : c.O, a ≠ 0 ∧ ∀ g : D.Gp l, a • z g = (((D.Psi⁻¹ g : c.Oˣ) : c.O) * m - m) • Xm c.O) ∧ ∀ z ∈ D.tanSet l (fun _ _ _ ρ => D.eqL ρ) 0, ∀ g : D.Gp l, (g : G ℚ Ω) ∈ D.Ip l → z g = 0 := by
  intro Ω _ _ _ l _ c D hG
  obtain ⟨-, -, -, -, -, hprod, hinj, -⟩ := facts D hG
  set cs : Fin 4 → c.O := fun k => ((D.ps k ↑D.s0 : c.Oˣ) : c.O) with hcs
  have hα : ∀ i, (∏ j ∈ Finset.univ.erase i, (cs i - cs j)) ≠ 0 := by
    intro i
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    rw [sub_ne_zero]
    intro h
    exact (Finset.mem_erase.1 hj).1 (hinj h).symm
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨hzw, -, ρ, ⟨-, hord⟩, hρ⟩ := hz
    have hX : ∀ a b, (ρ D.s0 a b).fst = Matrix.diagonal cs a b := fun a b => (hρ D.s0 a b).1
    have E : ∀ g : D.Gp l,
        (0 : c.O) = (prj (fun a => algebraMap c.O (DualNumber c.O) (cs a)) (ρ D.s0) 2 2 0).snd *
            ((D.th g : c.Oˣ) : c.O) * (∏ j ∈ Finset.univ.erase 0, (cs 0 - cs j)) +
          (∏ j ∈ Finset.univ.erase 2, (cs 2 - cs j)) * (z g 2 0 * ((D.th g : c.Oˣ) : c.O)) *
            (∏ j ∈ Finset.univ.erase 0, (cs 0 - cs j)) +
          (∏ j ∈ Finset.univ.erase 2, (cs 2 - cs j)) * ((D.al g : c.Oˣ) : c.O) *
            (prj (fun a => algebraMap c.O (DualNumber c.O) (cs a)) (ρ D.s0) 0 2 0).snd := by
      intro g
      have hs : prj (fun a => algebraMap c.O (DualNumber c.O) (cs a)) (ρ D.s0) 2 * ρ g *
          prj (fun a => algebraMap c.O (DualNumber c.O) (cs a)) (ρ D.s0) 0 = 0 :=
        hord.stable g 0 2 (by decide)
      have ht := triple (prj (fun a => algebraMap c.O (DualNumber c.O) (cs a)) (ρ D.s0) 2) (ρ g)
        (prj (fun a => algebraMap c.O (DualNumber c.O) (cs a)) (ρ D.s0) 0) 2 0 _ _
        (fun k => ((D.ps k g : c.Oˣ) : c.O)) (prj_fst cs (ρ D.s0) hX 2) (prj_fst cs (ρ D.s0) hX 0)
        (fun a b => (hρ g a b).1)
      rw [hs, (hρ g 2 0).2, show D.r0 ↑g = Matrix.diagonal fun k => ((D.ps k g : c.Oˣ) : c.O) from rfl,
        Matrix.mul_diagonal, Matrix.zero_apply, TrivSqZeroExt.snd_zero] at ht
      exact ht
    have hx1 : z 1 2 0 = 0 := by
      have h := (hρ 1 2 0).2
      simp only [map_one, OneMemClass.coe_one, mul_one, Matrix.one_apply_ne (by decide : (2 : Fin 4) ≠ 0),
        TrivSqZeroExt.snd_zero] at h
      exact h.symm
    have E1 := E 1
    simp only [map_one, OneMemClass.coe_one, Units.val_one, hx1] at E1
    refine ⟨(∏ j ∈ Finset.univ.erase 2, (cs 2 - cs j)) * (∏ j ∈ Finset.univ.erase 0, (cs 0 - cs j)),
      -((∏ j ∈ Finset.univ.erase 2, (cs 2 - cs j)) *
        (prj (fun a => algebraMap c.O (DualNumber c.O) (cs a)) (ρ D.s0) 0 2 0).snd),
      mul_ne_zero (hα 2) (hα 0), fun g => ?_⟩
    rw [spW_neg (hzw g), smul_smul]
    congr 1
    have huv : ((D.Psi g : c.Oˣ) : c.O) * ((D.Psi⁻¹ g : c.Oˣ) : c.O) = 1 := by
      rw [MonoidHom.inv_apply, Units.mul_inv]
    have hth : ((D.th g : c.Oˣ) : c.O) = ((D.Psi g : c.Oˣ) : c.O) * ((D.al g : c.Oˣ) : c.O) := by
      have h := congrArg (fun f : G ℚ Ω →* c.Oˣ => ((f g : c.Oˣ) : c.O)) (hprod 1)
      simp only [show (1 : Fin 4).rev = 2 from rfl, MonoidHom.mul_apply, Units.val_mul] at h
      exact h.symm
    apply mul_left_cancel₀ (Units.ne_zero (D.th g))
    linear_combination (-1 : c.O) * E g +
      (((D.Psi⁻¹ g : c.Oˣ) : c.O) * (∏ j ∈ Finset.univ.erase 2, (cs 2 - cs j)) *
        (prj (fun a => algebraMap c.O (DualNumber c.O) (cs a)) (ρ D.s0) 0 2 0).snd) * hth +
      (((D.al g : c.Oˣ) : c.O) * (∏ j ∈ Finset.univ.erase 2, (cs 2 - cs j)) *
        (prj (fun a => algebraMap c.O (DualNumber c.O) (cs a)) (ρ D.s0) 0 2 0).snd) * huv +
      ((D.th g : c.Oˣ) : c.O) * E1
  · intro z hz g hg
    obtain ⟨hzw, -, ρ, ⟨-, hord⟩, hρ⟩ := hz
    have hX : ∀ a b, (ρ D.s0 a b).fst = Matrix.diagonal cs a b := fun a b => (hρ D.s0 a b).1
    have hr0 : D.r0 ↑g = Matrix.diagonal fun k => ((D.ps k g : c.Oˣ) : c.O) := rfl
    refine Matrix.ext fun i j => ?_
    by_cases hij : i = j
    · subst hij
      have hs := hord.inert g (Subgroup.mem_subgroupOf.2 hg) i
      set x := algebraMap c.O (DualNumber c.O) ((D.ps i ↑g : c.Oˣ) : c.O) with hx
      have hB : ∀ a b, ((ρ g - x • 1) a b).fst =
          Matrix.diagonal (fun k => ((D.ps k g : c.Oˣ) : c.O) - ((D.ps i g : c.Oˣ) : c.O)) a b := by
        intro a b
        rw [Matrix.sub_apply, TrivSqZeroExt.fst_sub, (hρ g a b).1, hr0, Matrix.smul_apply, Matrix.one_apply]
        simp only [Matrix.diagonal_apply, hx]
        split_ifs with h
        · simp [TrivSqZeroExt.algebraMap_eq_inl]
        · simp
      have ht := triple _ _ _ i i _ _ _ (prj_fst cs (ρ D.s0) hX i) (prj_fst cs (ρ D.s0) hX i) hB
      have hs' : prj (fun a => algebraMap c.O (DualNumber c.O) (cs a)) (ρ D.s0) i * (ρ g - x • 1) *
          prj (fun a => algebraMap c.O (DualNumber c.O) (cs a)) (ρ D.s0) i = 0 := hs
      rw [hs', Matrix.sub_apply, TrivSqZeroExt.snd_sub, (hρ g i i).2, hr0, Matrix.mul_diagonal,
        Matrix.smul_apply, Matrix.one_apply_eq] at ht
      simp [hx, TrivSqZeroExt.algebraMap_eq_inl] at ht
      rw [Matrix.zero_apply]
      rcases ht with (h | h) | h
      · exact absurd h (hα i)
      · exact h
      · exact absurd h (hα i)
    · rw [Matrix.zero_apply]
      exact (spW_apply (hzw g)).2 i j (by rw [Ne, wt_eq_zero]; exact hij)
