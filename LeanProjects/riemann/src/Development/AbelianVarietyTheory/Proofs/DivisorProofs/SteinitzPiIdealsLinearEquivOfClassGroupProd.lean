import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitelyManyIsoClassesProjectiveNumberField
open scoped nonZeroDivisors

namespace GlobalTheory.SteinitzProd

variable {R : Type} [CommRing R] [IsDedekindDomain R]

def coprimeEquiv (I J : Ideal R) (u v : R) (hu : u ∈ I) (hv : v ∈ J) (h : u + v = 1) :
    (I × J) ≃ₗ[R] ((⊤ : Ideal R) × (I * J : Ideal R)) where
  toFun p := (⟨p.1 + p.2, Submodule.mem_top⟩,
    ⟨v * p.1 - u * p.2, Ideal.sub_mem _ (mul_comm (p.1 : R) v ▸ Ideal.mul_mem_mul p.1.2 hv)
      (Ideal.mul_mem_mul hu p.2.2)⟩)
  invFun q := (⟨u * q.1 + q.2, add_mem (Ideal.mul_mem_right _ I hu)
      ((Ideal.mul_le_left (I := I) (J := J)) q.2.2)⟩,
    ⟨v * q.1 - q.2, Ideal.sub_mem _ (Ideal.mul_mem_right _ J hv)
      ((Ideal.mul_le_right (I := I) (J := J)) q.2.2)⟩)
  map_add' p q := by
    ext <;> simp <;> ring
  map_smul' c p := by
    ext <;> simp <;> ring
  left_inv p := by
    ext
    · simp only; linear_combination (p.1 : R) * h
    · simp only; linear_combination (p.2 : R) * h
  right_inv q := by
    ext
    · simp only; linear_combination (q.1 : R) * h
    · simp only; linear_combination (q.2 : R) * h

theorem classGroup_exists_integral_ideal_coprime {m : Ideal R} (hm : m ≠ ⊥) (c : ClassGroup R) :
    ∃ I : (Ideal R)⁰, (I : Ideal R) ⊔ m = ⊤ ∧ ClassGroup.mk0 I = c := by
  by_cases ht : m = ⊤
  · obtain ⟨I, hI⟩ := ClassGroup.mk0_surjective c
    exact ⟨I, by rw [ht, sup_top_eq], hI⟩
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective c⁻¹
  have hJ0 : (J : Ideal R) ≠ 0 := nonZeroDivisors.coe_ne_zero J
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq (I := (J : Ideal R) * m) (J := J)
    Ideal.mul_le_left (mul_ne_zero hJ0 hm)
  obtain ⟨M, hM⟩ : (J : Ideal R) ∣ Ideal.span {a} := Ideal.dvd_iff_le.2 (ha ▸ le_sup_right)
  have h1 : m ⊔ M = ⊤ := by
    apply mul_left_cancel₀ hJ0
    rw [Ideal.mul_sup, ← hM, ha, Ideal.mul_top]
  have hM0 : M ≠ 0 := by
    rintro rfl
    exact ht (by simpa using h1)
  refine ⟨⟨M, mem_nonZeroDivisors_of_ne_zero hM0⟩, by rw [sup_comm]; exact h1, ?_⟩
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hJ0 hM0 (by simpa using hM.symm)
  rw [← inv_inv c, ← hJ, ClassGroup.mk0_eq_mk0_inv_iff]
  exact ⟨a, ha0, by rw [hM, mul_comm]⟩

theorem exists_prod_equiv (I J : (Ideal R)⁰) :
    ∃ L : (Ideal R)⁰, ClassGroup.mk0 L = ClassGroup.mk0 I * ClassGroup.mk0 J ∧
      Nonempty ((↥(I : Ideal R) × ↥(J : Ideal R)) ≃ₗ[R] (R × ↥(L : Ideal R))) := by
  have hJ0 : (J : Ideal R) ≠ ⊥ := by simpa using nonZeroDivisors.coe_ne_zero J
  obtain ⟨I', hcop, hcl⟩ := classGroup_exists_integral_ideal_coprime hJ0 (ClassGroup.mk0 I)
  have h1 : (1 : R) ∈ (I' : Ideal R) ⊔ J := by rw [hcop]; exact Submodule.mem_top
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 h1
  refine ⟨I' * J, by rw [map_mul, hcl], ⟨?_⟩⟩
  have e1 := (GlobalTheory.ProjModFinIso.nonempty_equiv_of_mk0_eq hcl.symm).some
  exact (e1.prodCongr (LinearEquiv.refl R _)) ≪≫ₗ coprimeEquiv _ _ u v hu hv huv ≪≫ₗ
    (Submodule.topEquiv.prodCongr (LinearEquiv.ofEq _ _ (Submonoid.coe_mul _ _ _).symm))

theorem exists_prod_pi_equiv (n : ℕ) : ∀ (I : Fin n → (Ideal R)⁰) (K : (Ideal R)⁰),
    ∃ L : (Ideal R)⁰, ClassGroup.mk0 L = ClassGroup.mk0 K * ∏ i, ClassGroup.mk0 (I i) ∧
      Nonempty ((↥(K : Ideal R) × ((i : Fin n) → ↥(I i : Ideal R))) ≃ₗ[R]
        (↥(L : Ideal R) × (Fin n → R))) := by
  induction n with
  | zero =>
    intro I K
    exact ⟨K, by simp, ⟨(LinearEquiv.refl R _).prodCongr (LinearEquiv.ofSubsingleton _ _)⟩⟩
  | succ n ih =>
    intro I K
    obtain ⟨L₁, hL₁, ⟨e₁⟩⟩ := exists_prod_equiv K (I 0)
    obtain ⟨L, hL, ⟨e₂⟩⟩ := ih (fun i => I i.succ) L₁
    refine ⟨L, by rw [hL, hL₁, Fin.prod_univ_succ, mul_assoc], ⟨?_⟩⟩
    exact (LinearEquiv.refl R _).prodCongr (Fin.consLinearEquiv R (fun i => ↥(I i : Ideal R))).symm ≪≫ₗ
      (LinearEquiv.prodAssoc R _ _ _).symm ≪≫ₗ e₁.prodCongr (LinearEquiv.refl R _) ≪≫ₗ
      LinearEquiv.prodAssoc R _ _ _ ≪≫ₗ (LinearEquiv.refl R R).prodCongr e₂ ≪≫ₗ
      (LinearEquiv.prodAssoc R _ _ _).symm ≪≫ₗ
      (LinearEquiv.prodComm R _ _).prodCongr (LinearEquiv.refl R _) ≪≫ₗ
      LinearEquiv.prodAssoc R _ _ _ ≪≫ₗ
      (LinearEquiv.refl R _).prodCongr (Fin.consLinearEquiv R (fun _ => R))

theorem exists_pi_equiv {ι : Type} [Fintype ι] {n : ℕ} (e : ι ≃ Fin (n + 1))
    (I : ι → (Ideal R)⁰) :
    ∃ L : (Ideal R)⁰, ClassGroup.mk0 L = ∏ i, ClassGroup.mk0 (I i) ∧
      Nonempty (((i : ι) → ↥(I i : Ideal R)) ≃ₗ[R] (↥(L : Ideal R) × (Fin n → R))) := by
  let I' : Fin (n + 1) → (Ideal R)⁰ := fun j => I (e.symm j)
  obtain ⟨L, hL, ⟨f⟩⟩ := exists_prod_pi_equiv n (fun j => I' j.succ) (I' 0)
  refine ⟨L, ?_, ⟨?_⟩⟩
  · rw [hL, ← Fin.prod_univ_succ (f := fun j => ClassGroup.mk0 (I' j))]
    exact Equiv.prod_comp e.symm (fun i => ClassGroup.mk0 (I i))
  · exact LinearEquiv.piCongrLeft' R (fun i => ↥(I i : Ideal R)) e ≪≫ₗ
      (Fin.consLinearEquiv R (fun j => ↥(I' j : Ideal R))).symm ≪≫ₗ f

theorem steinitz : ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (ι : Type) [Fintype ι]
    (I J : ι → (Ideal R)⁰), ∏ i, ClassGroup.mk0 (I i) = ∏ i, ClassGroup.mk0 (J i) →
    Nonempty (((i : ι) → (I i : Ideal R)) ≃ₗ[R] ((i : ι) → (J i : Ideal R))) := by
  intro R _ _ ι _ I J h
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := ι))
  let e : ι ≃ Fin (n + 1) := (Fintype.equivFin ι).trans (finCongr hn)
  obtain ⟨L, hL, ⟨f⟩⟩ := exists_pi_equiv e I
  obtain ⟨L', hL', ⟨f'⟩⟩ := exists_pi_equiv e J
  obtain ⟨g⟩ := GlobalTheory.ProjModFinIso.nonempty_equiv_of_mk0_eq (R := R) (I := L) (J := L')
    (by rw [hL, hL', h])
  exact ⟨f ≪≫ₗ g.prodCongr (LinearEquiv.refl R _) ≪≫ₗ f'.symm⟩

end GlobalTheory.SteinitzProd
