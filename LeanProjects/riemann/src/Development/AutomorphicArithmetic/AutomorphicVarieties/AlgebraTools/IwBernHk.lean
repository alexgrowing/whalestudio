import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwUnitHk
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwThetaEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwBernRel
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwSimpleQuad
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwPermMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwDomMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkNorm
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

namespace UpperTheory.V.AlgebraTools

private theorem exists_algHom_of_comm {σ A H : Type} [CommRing A] [Ring H] [Algebra A H] (y : σ → H)
    (hy : ∀ i j, y i * y j = y j * y i) :
    ∃ th : MvPolynomial σ A →ₐ[A] H, ∀ i, th (MvPolynomial.X i) = y i := by
  have hc : ∀ a ∈ Set.range y, ∀ b ∈ Set.range y, a * b = b * a := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact hy i j
  have : IsMulCommutative (Algebra.adjoin A (Set.range y)) := Algebra.isMulCommutative_adjoin A hc
  letI : CommRing (Algebra.adjoin A (Set.range y)) :=
    { (inferInstance : Ring (Algebra.adjoin A (Set.range y))) with mul_comm := fun a b => this.is_comm.comm a b }
  refine ⟨(Algebra.adjoin A (Set.range y)).val.comp
    (MvPolynomial.aeval fun i => ⟨y i, Algebra.subset_adjoin ⟨i, rfl⟩⟩), fun i => ?_⟩
  simp

private theorem anti_fund' (n m : ℕ) : Antitone (fund n m) := by
  intro i j hij
  have : (i : ℕ) ≤ j := hij
  simp only [fund]
  split_ifs <;> omega

private theorem dom_pw' {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    {x : kˣ} (hx : IsUnif x) {c : Fin n → ℤ} (hc : Antitone c) : Dom fun i => x ^ c i := by
  obtain ⟨p, -, hp⟩ := hx
  intro i j hij
  have h1 : valuation k (x : k) ≤ 1 := by rw [← hp]; exact p.2
  have h0 : 0 < valuation k (x : k) := by simp [zero_lt_iff]
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀]
  exact zpow_le_zpow_right_of_le_one₀ h0 h1 (hc hij)

private theorem single_mul_fund {G : Type} [CommGroup G] {n : ℕ} (x : G) (i : Fin n) :
    (Pi.mulSingle i x * fun l => x ^ fund n i l : Fin n → G) = fun l => x ^ fund n ((i : ℕ) + 1) l := by
  ext l
  by_cases h : l = i
  · subst h
    simp [fund]
  · have h' : (l : ℕ) ≠ i := fun e => h (Fin.ext e)
    have : fund n ((i : ℕ) + 1) l = fund n i l := by
      simp only [fund]
      split_ifs <;> omega
    simp [Pi.mulSingle_eq_of_ne h, this]

private theorem abs_bern {n : ℕ} {A E G : Type} [CommRing A] [Ring E] [Algebra A E] [CommGroup G] (S : Subalgebra A E)
    (q : A) (hq : IsUnit q) (T : Equiv.Perm (Fin n) → S) (D : ℕ → S) (θ : G →* Eˣ) (s : Fin n → G) (d : ℕ → G)
    (hsd : ∀ i : Fin n, s i * d i = d ((i : ℕ) + 1)) (hval : ∀ m, (D m : E) = θ (d m)) (hD : ∀ m, IsUnit (D m))
    (h1 : (T 1 : E) = 1)
    (hmul : ∀ a b : Fin n, a.val + 1 = b.val → ∀ w : Equiv.Perm (Fin n), w⁻¹ a < w⁻¹ b →
      (T (Equiv.swap a b) : E) * T w = T (Equiv.swap a b * w))
    (hsq : ∀ a b : Fin n, a.val + 1 = b.val →
      (T (Equiv.swap a b) : E) * T (Equiv.swap a b) = (q - 1) • (T (Equiv.swap a b) : E) + q • 1)
    (hb : ∀ a b : Fin n, a.val + 1 = b.val →
      (θ (s a) : E) = T (Equiv.swap a b) * (θ (s b) : E) * T (Equiv.swap a b) ∧
        ∀ l : Fin n, l ≠ a → l ≠ b → Commute (T (Equiv.swap a b) : E) (θ (s l) : E)) :
    ∃ b : Hk.Bern n q S, (∀ w, b.T w = T w) ∧
      ∀ i : Fin n, b.th (MvPolynomial.X i) * D i = (q ^ (i : ℕ)) • D ((i : ℕ) + 1) := by
  have hy : ∀ i : Fin n, ∃ y : S, (y : E) = θ (s i) := by
    intro i
    obtain ⟨u, hu⟩ := hD i
    refine ⟨D ((i : ℕ) + 1) * (u⁻¹ : Sˣ), ?_⟩
    apply (θ (d i)).isUnit.mul_right_cancel
    rw [← Units.val_mul, ← map_mul, hsd, ← hval, ← hval, ← hu, ← MulMemClass.coe_mul, mul_assoc,
      Units.inv_mul, mul_one]
  choose y hy using hy
  obtain ⟨th, hth⟩ := exists_algHom_of_comm (A := A) (fun i : Fin n => (q ^ (i : ℕ)) • y i) (by
    intro i j
    have : y i * y j = y j * y i := by
      apply Subtype.ext
      rw [MulMemClass.coe_mul, MulMemClass.coe_mul, hy, hy, ← Units.val_mul, ← map_mul, mul_comm, map_mul, Units.val_mul]
    simp only [smul_mul_assoc, mul_smul_comm, this]
    rw [smul_comm])
  have hsq' : ∀ a b : Fin n, a.val + 1 = b.val →
      T (Equiv.swap a b) * T (Equiv.swap a b) = (q - 1) • T (Equiv.swap a b) + q • 1 := fun a b hab =>
    Subtype.ext (hsq a b hab)
  have hrel : ∀ a b : Fin n, a.val + 1 = b.val →
      T (Equiv.swap a b) * th (MvPolynomial.X b) * T (Equiv.swap a b) = q • th (MvPolynomial.X a) := by
    intro a b hab
    have h : T (Equiv.swap a b) * y b * T (Equiv.swap a b) = y a := by
      apply Subtype.ext
      rw [MulMemClass.coe_mul, MulMemClass.coe_mul, hy, hy]
      exact (hb a b hab).1.symm
    rw [hth, hth, mul_smul_comm, smul_mul_assoc, h, smul_smul, ← hab, pow_succ']
  refine ⟨{ th := th
            T := T
            T_one := Subtype.ext h1
            T_mul := fun a b hab w hw => Subtype.ext (hmul a b hab w hw).symm
            T_sq := hsq'
            comm := fun a b hab j ha hb' => ?_
            relA := fun a b hab => (Hk.Bern.rel_of_quad hq _ _ _ (hsq' a b hab) (hrel a b hab)).1
            relB := fun a b hab => (Hk.Bern.rel_of_quad hq _ _ _ (hsq' a b hab) (hrel a b hab)).2 },
    fun w => rfl, fun i => ?_⟩
  · have h : T (Equiv.swap a b) * y j = y j * T (Equiv.swap a b) := by
      apply Subtype.ext
      rw [MulMemClass.coe_mul, MulMemClass.coe_mul, hy]
      exact ((hb a b hab).2 j ha hb').eq
    rw [hth, mul_smul_comm, smul_mul_assoc, h]
  · change th _ * _ = _
    rw [hth, smul_mul_assoc]
    congr 1
    apply Subtype.ext
    rw [MulMemClass.coe_mul, hy, hval, hval, ← Units.val_mul, ← map_mul, hsd]

end UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.bernHk :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (A : Type) [CommRing A] (x : kˣ), IsUnif x → IsUnit (resCard k : A) → ∃ b : UpperTheory.V.AlgebraTools.Hk.Bern n (resCard k : A) (HkAlg A (iwC k n ⊤)), (∀ w, b.T w = hT A (iwC k n ⊤) (pm k n w)) ∧ ∀ i : Fin n, b.th (MvPolynomial.X i) * hT A (iwC k n ⊤) (pw x (fund n i)) = ((resCard k : A) ^ (i : ℕ)) • hT A (iwC k n ⊤) (pw x (fund n ((i : ℕ) + 1))) := by
  intro k _ _ _ _ n A _ x hx hq
  refine (thetaEx k n ⊤ A _ (permRep A (iwC k n ⊤)) hq).exists.elim fun θ hθ => ?_
  have hd : ∀ m, Dom fun i : Fin n => x ^ fund n m i := fun m => dom_pw' hx (anti_fund' n m)
  have h1 : hk (permRep A (iwC k n ⊤)) (iwC k n ⊤) (pm k n 1) = 1 := by
    rw [map_one]
    exact (hkNorm A _ _ (permRep A (iwC k n ⊤)) _ 1 (heckePairIwC k n ⊤).1 (one_mem _)).2.1
  have h := abs_bern (HkAlg A (iwC k n ⊤)) (resCard k : A) hq (fun w => hT A (iwC k n ⊤) (pm k n w))
    (fun m => hT A (iwC k n ⊤) (pw x (fund n m))) θ (fun i => Pi.mulSingle i x) (fun m i => x ^ fund n m i)
    (single_mul_fund x) (fun m => (hθ _ (hd m)).symm) (fun m => (unitHk k n A hq).2 _ (hd m)) h1
    (fun a b hab w hw => permMul k n ⊤ A _ (permRep A (iwC k n ⊤)) w a b hab.symm hw)
    (fun a b hab => (simpleQuad k n ⊤ A _ (permRep A (iwC k n ⊤)) a b hab.symm).2 rfl)
    (fun a b hab => bernRel k n A _ (permRep A (iwC k n ⊤)) x hx hq θ hθ a b hab.symm)
  exact h
