import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : ℕ} (G : Grp k n)

namespace P_Jinv

def CcUm : Prop :=
  ∀ a b c : Fin G.s, cc G.μ a a = 0 ∧ cc G.μ a b = cc G.μ b a ∧ cc G.μ a c ≤ max (cc G.μ a b) (cc G.μ b c)

def fe (i j : Fin n) : ℕ := if G.bl j < G.bl i then cc G.μ (G.bl j) (G.bl i) else 0

theorem fe_self (i : Fin n) : fe G i i = 0 := by simp [fe]

theorem fe_tri (hU : CcUm G) (i l j : Fin n) : fe G i j ≤ fe G i l + fe G l j := by
  by_cases hij : G.bl j < G.bl i
  · have e1 : fe G i j = cc G.μ (G.bl j) (G.bl i) := if_pos hij
    rw [e1]
    rcases le_or_gt (G.bl l) (G.bl j) with hlj | hjl
    · have e2 : fe G i l = cc G.μ (G.bl l) (G.bl i) := if_pos (lt_of_le_of_lt hlj hij)
      rw [e2]
      exact le_add_right (G.ball _ _ _ _ hlj hij le_rfl)
    · rcases le_or_gt (G.bl i) (G.bl l) with hil | hli
      · have e3 : fe G l j = cc G.μ (G.bl j) (G.bl l) := if_pos hjl
        rw [e3]
        exact le_add_left (G.ball _ _ _ _ le_rfl hij hil)
      · have e2 : fe G i l = cc G.μ (G.bl l) (G.bl i) := if_pos hli
        have e3 : fe G l j = cc G.μ (G.bl j) (G.bl l) := if_pos hjl
        rw [e2, e3]
        have := (hU (G.bl j) (G.bl l) (G.bl i)).2.2
        omega
  · have e1 : fe G i j = 0 := if_neg hij
    omega

def S (hU : CcUm G) : Subalgebra 𝒪[k] (Matrix (Fin n) (Fin n) 𝒪[k]) where
  carrier := {A | ∀ i j, A i j ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ fe G i j}
  mul_mem' := by
    intro A B hA hB i j
    simp only [Set.mem_ofPred_eq] at hA hB
    rw [Matrix.mul_apply]
    refine Ideal.sum_mem _ fun l _ => ?_
    refine Ideal.pow_le_pow_right (fe_tri G hU i l j) ?_
    rw [pow_add]
    exact Ideal.mul_mem_mul (hA i l) (hB l j)
  one_mem' := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs with h
    · subst h
      rw [fe_self, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    · exact zero_mem _
  add_mem' := by
    intro A B hA hB i j
    simp only [Set.mem_ofPred_eq] at hA hB
    exact Ideal.add_mem _ (hA i j) (hB i j)
  zero_mem' := fun _ _ => zero_mem _
  algebraMap_mem' := by
    intro r i j
    rw [Matrix.algebraMap_matrix_apply]
    split_ifs with h
    · subst h
      rw [fe_self, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    · exact zero_mem _

theorem mem_S (hU : CcUm G) (A : Matrix (Fin n) (Fin n) 𝒪[k]) :
    A ∈ S G hU ↔ ∀ i j, A i j ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ fe G i j := Iff.rfl

theorem inv_mem (hU : CcUm G) (h : GL (Fin n) 𝒪[k])
    (hh : (h : Matrix (Fin n) (Fin n) 𝒪[k]) ∈ S G hU) :
    ((h⁻¹ : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) ∈ S G hU := by
  set A : Matrix (Fin n) (Fin n) 𝒪[k] := (h : Matrix (Fin n) (Fin n) 𝒪[k]) with hAdef
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp h.isUnit
  rw [Matrix.det_eq_sign_charpoly_coeff] at hdet
  obtain ⟨u, hu⟩ := isUnit_of_mul_isUnit_right hdet
  have h0 := Matrix.aeval_self_charpoly A
  rw [← Polynomial.X_mul_divX_add A.charpoly, map_add, map_mul, Polynomial.aeval_X,
    Polynomial.aeval_C] at h0
  have h1 : A * Polynomial.aeval A A.charpoly.divX = -algebraMap 𝒪[k] _ (A.charpoly.coeff 0) :=
    eq_neg_of_add_eq_zero_left h0
  have key : A * (-((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) • Polynomial.aeval A A.charpoly.divX) = 1 := by
    rw [mul_smul_comm, h1, neg_smul_neg, ← hu, Algebra.smul_def, ← map_mul, Units.inv_mul, map_one]
  have hinv := Units.eq_inv_of_mul_eq_one_left key
  rw [← hinv]
  refine Subalgebra.smul_mem _ ?_ _
  have hval : Polynomial.aeval A A.charpoly.divX =
      (S G hU).val (Polynomial.aeval (⟨A, hh⟩ : S G hU) A.charpoly.divX) :=
    (Polynomial.aeval_algHom_apply (S G hU).val (⟨A, hh⟩ : S G hU) A.charpoly.divX)
  rw [hval]
  exact Subtype.prop _

end P_Jinv

open P_Jinv in
theorem step_Jinv : JacquetInverseProp G := by
  intro hU0 hB g hg
  have hU : CcUm G := hU0 G.s G.μ (fun a b => ⟨_, hB.2.2.2 a b⟩)
  obtain ⟨hK, hJ⟩ := hg
  obtain ⟨h, rfl⟩ := hK
  have hinj : Function.Injective (algebraMap 𝒪[k] k) := Subtype.val_injective
  have hmem : (h : Matrix (Fin n) (Fin n) 𝒪[k]) ∈ S G hU := by
    intro a b
    by_cases hab : G.bl b < G.bl a
    · obtain ⟨y, hy, hyx⟩ := hJ a b hab
      have hy' : y = (h : Matrix (Fin n) (Fin n) 𝒪[k]) a b := hinj hyx
      have e1 : fe G a b = cc G.μ (G.bl b) (G.bl a) := if_pos hab
      rw [e1, ← hy']
      exact hy
    · have e1 : fe G a b = 0 := if_neg hab
      rw [e1, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
  have hi := inv_mem G hU h hmem
  refine ⟨⟨h⁻¹, (map_inv _ h)⟩, fun i j hij => ?_⟩
  refine ⟨((h⁻¹ : GL (Fin n) 𝒪[k]) : Matrix (Fin n) (Fin n) 𝒪[k]) i j, ?_, ?_⟩
  · have := hi i j
    have e1 : fe G i j = cc G.μ (G.bl j) (G.bl i) := if_pos hij
    rwa [e1] at this
  · rw [← map_inv]
    rfl

end UpperTheory.TNZ.Grp
