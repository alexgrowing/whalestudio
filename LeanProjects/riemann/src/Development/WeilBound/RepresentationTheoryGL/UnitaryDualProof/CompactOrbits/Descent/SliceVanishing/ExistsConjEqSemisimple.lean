import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.Descent.SliceVanishing.T2SpaceCentralizerGroup

noncomputable section

open Matrix Polynomial GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.T.Desc.SLF

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

section Hyp

variable {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {F : Set (Matrix (Fin n) (Fin n) k)} {P : k[X]}
  {s : Matrix (Fin n) (Fin n) k}
  (hFinv : ∀ g ∈ Gz Z, ∀ x ∈ F, g.val * x * g⁻¹.val ∈ F)
  (hP : ∀ x ∈ F, aeval x P ∈ F ∧ Module.End.IsSemisimple (Matrix.toLin' (aeval x P)) ∧ IsNilpotent (x - aeval x P) ∧
    ∃ g ∈ Gz Z, g.val * aeval x P * g⁻¹.val = s)

include hP in
theorem P_idem [CharZero k] {x} (hx : x ∈ F) : aeval (aeval x P) P = aeval x P := by
  set y := aeval x P with hydef
  obtain ⟨hyF, hyS, -, -⟩ := hP x hx
  obtain ⟨-, hzS, hzN, -⟩ := hP y hyF
  have e : ∀ M : Matrix (Fin n) (Fin n) k, Matrix.toLinAlgEquiv' M = Matrix.toLin' M := fun M => rfl
  have hc : Commute y (aeval y P) := by
    have := (Commute.all (X : k[X]) P).map (aeval y)
    rwa [aeval_X] at this
  have hc' : Commute (Matrix.toLin' y) (Matrix.toLin' (aeval y P)) := by
    have := hc.map (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) k ≃ₐ[k] _)
    rwa [e, e] at this
  have hS : Module.End.IsSemisimple (Matrix.toLin' (y - aeval y P)) := by
    rw [map_sub]
    exact Module.End.IsSemisimple.sub_of_commute hc' hyS hzS
  have hN : IsNilpotent (Matrix.toLin' (y - aeval y P)) := by
    rw [← e]
    exact hzN.map _
  have h0 := Module.End.eq_zero_of_isNilpotent_isSemisimple hN hS
  rw [← e, map_eq_zero_iff _ (AlgEquiv.injective _), sub_eq_zero] at h0
  exact h0.symm

include hP in
theorem P_mem_Tset [CharZero k] {x} (hx : x ∈ F) : aeval x P ∈ Tset F P := ⟨(hP x hx).1, P_idem hP hx⟩

include hP in
theorem exists_conj_eq_semisimple {x} (hx : x ∈ Tset F P) : ∃ g ∈ Gz Z, cj g x = s := by
  obtain ⟨hxF, hxP⟩ := hx
  obtain ⟨-, -, -, g, hg, hgs⟩ := hP x hxF
  rw [hxP] at hgs
  exact ⟨g, hg, hgs⟩

theorem continuousSMul_actT : @ContinuousSMul (GzS Z) (Tset F P) (actT hFinv).toSMul _ _ := by
  refine @ContinuousSMul.mk _ _ (actT hFinv).toSMul _ _ ?_
  exact (((Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst)).matrix_mul
    (continuous_subtype_val.comp continuous_snd)).matrix_mul
    (Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_fst))).subtype_mk _

include hP in
theorem isPretransitive_actT (hsT : s ∈ Tset F P) : @MulAction.IsPretransitive (GzS Z) (Tset F P) (actT hFinv).toSMul := by
  refine @MulAction.IsPretransitive.mk _ _ (actT hFinv).toSMul ?_
  intro x y
  obtain ⟨a, ha, hax⟩ := exists_conj_eq_semisimple hP x.2
  obtain ⟨b, hb, hby⟩ := exists_conj_eq_semisimple hP y.2
  refine ⟨⟨b⁻¹ * a, (GzS Z).mul_mem ((GzS Z).inv_mem hb) ha⟩, Subtype.ext ?_⟩
  show cj (b⁻¹ * a) x.1 = y.1
  simp only [cj] at hax hby ⊢
  simp only [_root_.mul_inv_rev, inv_inv, Units.val_mul]
  calc (b⁻¹ : GL (Fin n) k).val * a.val * x.1 * (a⁻¹.val * b.val)
      = (b⁻¹ : GL (Fin n) k).val * (a.val * x.1 * a⁻¹.val) * b.val := by
        simp only [Matrix.mul_assoc]
    _ = (b⁻¹ : GL (Fin n) k).val * (b.val * y.1 * b⁻¹.val) * b.val := by rw [hax, hby]
    _ = y.1 := by simp [Matrix.mul_assoc]

end Hyp

end PositivityTheory.RgUd.T.Desc.SLF
