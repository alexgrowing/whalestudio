import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle

open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

section

variable {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O]

end

theorem UpperTheory.V.Th.Coc.starFacts :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) {O R : Type} [CommRing O] [Algebra ℤ_[l] O] [CommRing R] [Algebra O R] {n : ℕ}, (∀ a b, F.star O R n (a * b) = F.star O R n b * F.star O R n a) ∧ (∀ a b, F.star O R n (a + b) = F.star O R n a + F.star O R n b) ∧ (∀ (r : R) a, F.star O R n (r • a) = r • F.star O R n a) ∧ (∀ a, F.star O R n (F.star O R n a) = a) ∧ (∀ g, F.star O R n (MonoidAlgebra.single g 1) = MonoidAlgebra.single (F.conj g)⁻¹ (algebraMap O R ((F.eps O O g ^ (1 - (n : ℤ)) : Oˣ) : O))) ∧ ∀ (x : R →ₐ[O] O) (ρ : F.G₀ →* GL (Fin n) O) (P : GL (Fin n) O), F.IsForm O n ρ P → ∀ a, repR x (mat ρ) (F.star O R n a) = ((P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * (repR x (mat ρ) a)ᵀ * (P : Matrix (Fin n) (Fin n) O) := by
  intro l _ F O R _ _ _ _ n
  have hmul : ∀ a b, F.star O R n (a * b) = F.star O R n b * F.star O R n a := by
    intro a b
    simp [GFrame.star, map_mul]
  have hadd : ∀ a b, F.star O R n (a + b) = F.star O R n a + F.star O R n b := by
    intro a b
    simp [GFrame.star, map_add]
  have hsmul : ∀ (r : R) a, F.star O R n (r • a) = r • F.star O R n a := by
    intro r a
    simp [GFrame.star, map_smul]
  have hzero : F.star O R n 0 = 0 := by
    simp [GFrame.star]
  have hsingle : ∀ g (r : R), F.star O R n (MonoidAlgebra.single g r)
      = MonoidAlgebra.single (F.conj g)⁻¹ (r * ((F.eps O R g ^ (1 - (n : ℤ)) : Rˣ) : R)) := by
    intro g r
    simp [GFrame.star, GFrame.starOp, MonoidAlgebra.lift_single]
  have hepsR : ∀ g (k : ℤ), ((F.eps O R g ^ k : Rˣ) : R)
      = algebraMap O R ((F.eps O O g ^ k : Oˣ) : O) := by
    intro g k
    have h : F.eps O R g = Units.map (algebraMap O R).toMonoidHom (F.eps O O g) := by
      ext
      simp [GFrame.eps, pushCh]
    rw [h, ← map_zpow]
    rfl
  have hci : F.c⁻¹ = F.c := inv_eq_of_mul_eq_one_right F.c_sq
  have hcc : ∀ g, F.conj (F.conj g) = g := by
    intro g
    apply Subtype.ext
    show F.c * (F.c * (g : F.Γ) * F.c⁻¹) * F.c⁻¹ = g
    rw [hci, ← mul_assoc, ← mul_assoc, F.c_sq, one_mul, mul_assoc, F.c_sq, mul_one]
  have hepsc : ∀ g, F.eps O R (F.conj g) = F.eps O R g := by
    intro g
    have h : F.ε ((F.conj g : F.G₀) : F.Γ) = F.ε (g : F.Γ) := by
      show F.ε (F.c * (g : F.Γ) * F.c⁻¹) = _
      rw [map_mul, map_mul, map_inv, mul_comm (F.ε F.c), mul_assoc, mul_inv_cancel, mul_one]
    simp [GFrame.eps, pushCh, h]
  refine ⟨hmul, hadd, hsmul, ?_, ?_, ?_⟩
  · intro a
    induction a using MonoidAlgebra.induction_linear with
    | zero => rw [hzero, hzero]
    | add f g hf hg => rw [hadd, hadd, hf, hg]
    | single g r =>
      rw [hsingle, hsingle]
      simp only [map_inv, hcc, inv_inv, hepsc]
      congr 1
      rw [mul_assoc, ← Units.val_mul, _root_.inv_zpow', ← _root_.zpow_add, add_neg_cancel, _root_.zpow_zero,
        Units.val_one, mul_one]
  · intro g
    rw [hsingle, one_mul, hepsR]
  · intro x ρ P hP a
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp [hzero]
    | add f g hf hg =>
      rw [hadd, map_add, hf, hg, map_add, transpose_add, Matrix.mul_add, Matrix.add_mul]
    | single g r =>
      have key : ((P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * (mat ρ g)ᵀ * (P : Matrix (Fin n) (Fin n) O)
          = ((F.eps O O g ^ (1 - (n : ℤ)) : Oˣ) : O) • mat ρ (F.conj g)⁻¹ := by
        have h := hP g
        have hm : mat ρ (F.conj g) * mat ρ (F.conj g)⁻¹ = 1 := by
          rw [← map_mul, mul_inv_cancel, map_one]
        calc ((P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * (mat ρ g)ᵀ * (P : Matrix (Fin n) (Fin n) O)
            = ((P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) * (mat ρ g)ᵀ * (P : Matrix (Fin n) (Fin n) O)
              * (mat ρ (F.conj g) * mat ρ (F.conj g)⁻¹) := by rw [hm, mul_one]
          _ = ((P⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O)
              * ((mat ρ g)ᵀ * (P : Matrix (Fin n) (Fin n) O) * mat ρ (F.conj g)) * mat ρ (F.conj g)⁻¹ := by
            simp only [mul_assoc]
          _ = _ := by
            rw [h, Matrix.mul_smul, Units.inv_mul, Matrix.smul_mul, one_mul]
      rw [hsingle, repR_single, repR_single, map_mul, hepsR, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
        transpose_smul, Matrix.mul_smul, Matrix.smul_mul, key, mul_smul]
