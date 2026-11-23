import Development.DiscreteGroups.GlobalIrreducibility.LConvBigB

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocLanglands GlobalTheory.Whittaker

namespace DiscreteGroups.sglob.LConv

variable {k : Type} [Field k] {m : ℕ} {ψ : AddChar k Circle} {V₁ V₂ : Type} [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] {π₁ : Representation ℂ (GL (Fin (m + 1)) k) V₁}
  {π₂ : Representation ℂ (GL (Fin (m + 1)) k) V₂} {l₁ : Module.Dual ℂ V₁} {l₂ : Module.Dual ℂ V₂}

theorem agree_of_entry_one (hl₁ : IsFunctional ψ π₁ l₁) (hl₂ : IsFunctional ψ π₂ l₂)
    (hW : ∀ (v₁ : V₁) (v₂ : V₂), (∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) →
      l₁ (π₁ (longElt (m + 1) k) v₁) = l₂ (π₂ (longElt (m + 1) k) v₂)) {v₁ : V₁} {v₂ : V₂}
    (hX : ∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) (g : GL (Fin (m + 1)) k)
    (hg : ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) 0 = 1) :
    l₁ (π₁ g v₁) = l₂ (π₂ g v₂) := by
  set r : Fin (m + 1) → k := fun j => ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j
  set M : Matrix (Fin (m + 1)) (Fin (m + 1)) k :=
    Matrix.of fun i j => if i = 0 then r j else (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) i j
  have hMtri : ∀ i j : Fin (m + 1), j < i → M i j = 0 := by
    intro i j hij
    have hi : i ≠ 0 := fun e => by subst e; exact (Fin.not_lt_zero j) hij
    simp [M, hi, Matrix.one_apply_ne hij.ne']
  have hMdiag : ∀ i, M i i = 1 := by
    intro i
    by_cases hi : i = 0
    · subst hi; simpa [M, r] using hg
    · simp [M, hi]
  have hdet : M.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (fun i j hij => hMtri i j hij)]
    simp [hMdiag]
  set n : GL (Fin (m + 1)) k := Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact one_ne_zero)
  have hnv : (n : Matrix (Fin (m + 1)) (Fin (m + 1)) k) = M := rfl
  have hn : n ∈ unipB k (Fin (m + 1)) := (mem_unipB k).2 ⟨fun i j hij => by rw [hnv]; exact hMtri i j hij,
    fun i => by rw [hnv]; exact hMdiag i⟩
  have hwn : ∀ b, ((longElt (m + 1) k : Matrix (Fin (m + 1)) (Fin (m + 1)) k) * (n : Matrix (Fin (m + 1)) (Fin (m + 1)) k))
      (Fin.last m) b = r b := by
    intro b
    rw [hnv, Matrix.mul_apply, Finset.sum_eq_single (0 : Fin (m + 1))]
    · rw [longElt_last, if_pos rfl, one_mul]
      simp [M, r]
    · intro a _ ha
      rw [longElt_last, if_neg ha, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  set p : GL (Fin (m + 1)) k := longElt (m + 1) k * n * g
  have hP : IsP p := by
    intro j
    show ((longElt (m + 1) k * n * g : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) j = _
    rw [Units.val_mul, Units.val_mul, Matrix.mul_apply]
    calc _ = ∑ b, r b * (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) b j :=
          Finset.sum_congr rfl fun b _ => by rw [hwn b]
      _ = _ := by
        simp only [r]
        rw [← Matrix.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hg' : g = n⁻¹ * (longElt (m + 1) k)⁻¹ * p := by
    simp only [p, mul_assoc, inv_mul_cancel_left]
  rw [hg', longElt_inv]
  simp only [map_mul, Module.End.mul_apply]
  rw [hl₁ _ (inv_mem hn), hl₂ _ (inv_mem hn), hW _ _ (agree_translate hl₁ hl₂ hX hP)]

theorem val_scalar (z : kˣ) :
    ((Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) z : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) =
      Matrix.diagonal fun _ => (z : k) := by
  first
  | rfl
  | (ext i j; simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply])

theorem agree_scalar {ω₁ ω₂ : kˣ →* ℂˣ} (h₁ : HasCentralChar π₁ ω₁) (h₂ : HasCentralChar π₂ ω₂)
    (hl₁ : IsFunctional ψ π₁ l₁) (hl₂ : IsFunctional ψ π₂ l₂)
    (hW : ∀ (v₁ : V₁) (v₂ : V₂), (∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) →
      l₁ (π₁ (longElt (m + 1) k) v₁) = l₂ (π₂ (longElt (m + 1) k) v₂)) {v₁ : V₁} {v₂ : V₂}
    (hX : ∀ g : GL (Fin m) k, l₁ (π₁ (corner g) v₁) = l₂ (π₂ (corner g) v₂)) (g : GL (Fin (m + 1)) k) (u : kˣ)
    (hg : ((g⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) 0 = u) :
    (ω₁ u : ℂ) * l₁ (π₁ g v₁) = (ω₂ u : ℂ) * l₂ (π₂ g v₂) := by
  have hent : (((Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) u * g)⁻¹ : GL (Fin (m + 1)) k) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) k) (Fin.last m) 0 = 1 := by
    rw [mul_inv_rev, ← map_inv, Units.val_mul, val_scalar, Matrix.mul_diagonal, hg, Units.mul_inv]
  have := agree_of_entry_one hl₁ hl₂ hW hX _ hent
  rwa [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, h₁, h₂, map_smul, map_smul,
    smul_eq_mul, smul_eq_mul] at this

end DiscreteGroups.sglob.LConv

end
