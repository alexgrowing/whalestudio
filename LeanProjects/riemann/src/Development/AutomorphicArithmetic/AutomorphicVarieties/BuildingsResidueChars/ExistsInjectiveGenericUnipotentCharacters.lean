import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.KirCusp

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.Z.Desc.V0

namespace UpperTheory.UnipChar

variable {F : Type} [Field F] {n : ℕ}

private abbrev SD (n : ℕ) := {p : Fin n × Fin n // (p.2 : ℕ) = p.1 + 1}

private theorem SD.ne (p : SD n) : p.1.1 ≠ p.1.2 := by
  intro h
  have hp := p.2
  rw [h] at hp
  omega

private theorem super_mul {x y : Matrix (Fin n) (Fin n) F}
    (hx : ∀ i j, j < i → x i j = 0) (hx1 : ∀ i, x i i = 1)
    (hy : ∀ i j, j < i → y i j = 0) (hy1 : ∀ i, y i i = 1)
    {i j : Fin n} (h : (j : ℕ) = i + 1) : (x * y) i j = x i j + y i j := by
  rw [Matrix.mul_apply]
  have hij : i ≠ j := by
    intro e
    rw [e] at h
    omega
  rw [Fintype.sum_eq_add i j hij]
  · rw [hx1, hy1, one_mul, mul_one, add_comm]
  · rintro k ⟨hki, hkj⟩
    rcases lt_or_gt_of_ne hki with hk | hk
    · rw [hx i k hk, zero_mul]
    · have h1 := Fin.lt_iff_val_lt_val.mp hk
      have h2 : (k : ℕ) ≠ j := fun e => hkj (Fin.ext e)
      have hjk : j < k := Fin.lt_iff_val_lt_val.mpr (by omega)
      rw [hy k j hjk, mul_zero]

private def sup (f : SD n → Fˣ) (x : Matrix (Fin n) (Fin n) F) : F :=
  ∑ p, (f p : F) * x p.1.1 p.1.2

private theorem sup_one (f : SD n → Fˣ) : sup f (1 : Matrix (Fin n) (Fin n) F) = 0 := by
  unfold sup
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [Matrix.one_apply_ne (SD.ne p), mul_zero]

private theorem sup_mul (f : SD n → Fˣ) {x y : GL (Fin n) F}
    (hx : x ∈ unipB F (Fin n)) (hy : y ∈ unipB F (Fin n)) :
    sup f ((x * y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      sup f (x : Matrix (Fin n) (Fin n) F) + sup f (y : Matrix (Fin n) (Fin n) F) := by
  obtain ⟨a, b⟩ := (mem_unipB F).1 hx
  obtain ⟨c, d⟩ := (mem_unipB F).1 hy
  unfold sup
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Units.val_mul, super_mul a b c d p.2, mul_add]

private noncomputable def chi (φ : AddChar F Circle) (f : SD n → Fˣ) : unipB F (Fin n) →* ℂˣ :=
  MonoidHom.toHomUnits
    { toFun := fun x => (φ (sup f ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) : ℂ)
      map_one' := by simp [sup_one]
      map_mul' := fun x y => by
        rw [Subgroup.coe_mul, sup_mul f x.2 y.2, AddChar.map_add_eq_mul, Circle.coe_mul] }

private theorem chi_apply (φ : AddChar F Circle) (f : SD n → Fˣ) (x : unipB F (Fin n)) :
    ((chi φ f x : ℂˣ) : ℂ) = (φ (sup f ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) : ℂ) := rfl

private noncomputable def tv (i j : Fin n) (h : i ≠ j) (c : F) : GL (Fin n) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection i j c)
    (by rw [Matrix.det_transvection_of_ne i j h c]; exact one_ne_zero)

private theorem tv_apply (i j : Fin n) (h : i ≠ j) (c : F) (a b : Fin n) :
    ((tv i j h c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a b =
      (1 : Matrix (Fin n) (Fin n) F) a b + Matrix.single i j c a b := rfl

private theorem tv_mem (p : SD n) (c : F) : tv p.1.1 p.1.2 (SD.ne p) c ∈ unipB F (Fin n) := by
  rw [mem_unipB]
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [tv_apply, Matrix.one_apply_ne (ne_of_gt hab), Matrix.single_apply, if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    have h1 := p.2
    have h2 := Fin.lt_iff_val_lt_val.mp hab
    omega
  · rw [tv_apply, Matrix.one_apply_eq, Matrix.single_apply, if_neg, add_zero]
    rintro ⟨rfl, h⟩
    exact SD.ne p h.symm

private theorem sup_tv (f : SD n → Fˣ) (p : SD n) (c : F) :
    sup f ((tv p.1.1 p.1.2 (SD.ne p) c : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = f p * c := by
  simp only [sup]
  rw [Finset.sum_eq_single p]
  · rw [tv_apply, Matrix.one_apply_ne (SD.ne p), zero_add, Matrix.single_apply, if_pos ⟨rfl, rfl⟩]
  · intro q _ hq
    rw [tv_apply, Matrix.one_apply_ne (SD.ne q), zero_add, Matrix.single_apply, if_neg, mul_zero]
    rintro ⟨h1, h2⟩
    exact hq (Subtype.ext (Prod.ext h1.symm h2.symm))
  · intro h
    exact absurd (Finset.mem_univ p) h

private theorem chi_inj (φ : AddChar F Circle) (hφ : φ ≠ 1) :
    Function.Injective (chi (n := n) φ) := by
  intro f g hfg
  funext p
  by_contra hne
  apply hφ
  ext a
  have hd : ((f p : F) - g p) ≠ 0 := sub_ne_zero.mpr (fun e => hne (Units.ext e))
  have key := congrArg (fun χ => ((χ ⟨tv p.1.1 p.1.2 (SD.ne p) (((f p : F) - g p)⁻¹ * a), tv_mem p _⟩ : ℂˣ) : ℂ)) hfg
  simp only [chi_apply, sup_tv] at key
  have key' : φ ((f p : F) * (((f p : F) - g p)⁻¹ * a)) = φ ((g p : F) * (((f p : F) - g p)⁻¹ * a)) :=
    Circle.coe_injective key
  have ha : a = (f p : F) * (((f p : F) - g p)⁻¹ * a) - g p * (((f p : F) - g p)⁻¹ * a) := by
    rw [← sub_mul, ← mul_assoc, mul_inv_cancel₀ hd, one_mul]
  rw [AddChar.one_apply, ha, AddChar.map_sub_eq_div, key', div_self']

private noncomputable def psi (φ : AddChar F Circle) : AddChar F ℂ where
  toFun a := (φ a : ℂ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by rw [AddChar.map_add_eq_mul, Circle.coe_mul]

private theorem psi_prim {φ : AddChar F Circle} (hφ : φ ≠ 1) : (psi φ).IsPrimitive := by
  apply AddChar.IsPrimitive.of_ne_one
  intro h
  apply hφ
  ext a
  have e := congrArg (fun ψ : AddChar F ℂ => ψ a) h
  simp only [AddChar.one_apply] at e ⊢
  exact e.trans Circle.coe_one.symm

private theorem sum_units_eq [Fintype F] [DecidableEq F] (h : F → ℂ) :
    ∑ a : Fˣ, h a = ∑ a : F, h a - h 0 := by
  rw [← Finset.sum_erase_eq_sub (Finset.mem_univ 0),
    Finset.sum_subtype (Finset.univ.erase 0) (p := fun a => a ≠ 0) (fun a => by simp)]
  exact Fintype.sum_equiv unitsEquivNeZero _ _ (fun _ => rfl)

private theorem sum_units_psi [Fintype F] [DecidableEq F] {φ : AddChar F Circle} (hφ : φ ≠ 1) (b : F) :
    ∑ a : Fˣ, psi φ (-((a : F) * b)) =
      (((Fintype.card F : ℤ) * (if b = 0 then 1 else 0) - 1 : ℤ) : ℂ) := by
  rw [sum_units_eq (fun a : F => psi φ (-(a * b)))]
  simp only [zero_mul, neg_zero, AddChar.map_zero_eq_one, ← mul_neg]
  rw [AddChar.sum_mulShift (-b) (psi_prim hφ)]
  by_cases hb : b = 0 <;> simp [hb]

private theorem psi_sum {ι : Type} (φ : AddChar F Circle) (s : Finset ι) (g : ι → F) :
    psi φ (∑ i ∈ s, g i) = ∏ i ∈ s, psi φ (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

private theorem chi_inv [Fintype F] [DecidableEq F] (φ : AddChar F Circle) (f : SD n → Fˣ)
    (x : unipB F (Fin n)) :
    (((chi φ f x)⁻¹ : ℂˣ) : ℂ) =
      ∏ p, psi φ (-((f p : F) * ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) p.1.1 p.1.2)) := by
  rw [Units.val_inv_eq_inv_val, chi_apply, ← psi_sum, Finset.sum_neg_distrib]
  simp only [sup]
  show _ = ((φ (-_) : Circle) : ℂ)
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv]

end UpperTheory.UnipChar

open UpperTheory.UnipChar in
theorem UpperTheory.exists_injective_generic_unipotent_characters :
    ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] (n : ℕ) (φ : AddChar F Circle), φ ≠ 1 →
        ∃ χ : ({p : Fin n × Fin n // (p.2 : ℕ) = p.1 + 1} → Fˣ) → (unipB F (Fin n) →* ℂˣ),
          Function.Injective χ ∧
          (∀ f x, ((χ f x : ℂˣ) : ℂ) = (φ (∑ p, (f p : F) * ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) p.1.1 p.1.2) : ℂ)) ∧
          ∃ c : unipB F (Fin n) → ℤ, ∀ x, (c x : ℂ) = ∑ f, (((χ f x)⁻¹ : ℂˣ) : ℂ) := by
  intro F _ _ _ n φ hφ
  refine ⟨chi φ, chi_inj φ hφ, fun f x => chi_apply φ f x, ?_⟩
  refine ⟨fun x => ∏ p : SD n, ((Fintype.card F : ℤ) *
    (if ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) p.1.1 p.1.2 = 0 then 1 else 0) - 1), fun x => ?_⟩
  simp only [Int.cast_prod, chi_inv]
  refine Eq.trans ?_ (Fintype.prod_sum (κ := fun _ : SD n => Fˣ)
    (fun p (a : Fˣ) => psi φ (-((a : F) * ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) p.1.1 p.1.2))))
  exact Finset.prod_congr rfl fun p _ => (sum_units_psi hφ _).symm
