import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.JPred

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.LbElem.ConjMonomial

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stdBlocks_ones (N : ℕ) (a : Fin N) (i : Fin (ones N a)) :
    stdBlocks (ones N) (sum_ones N) ⟨a, i⟩ = a := by
  apply Fin.ext
  rw [stdBlocks_val]
  have hi : (i : ℕ) = 0 := by
    have := i.2
    simp only [ones] at this
    omega
  simp [ones, hi]

theorem tor_offDiag {N : ℕ} {x : GL (Fin N) k} (hx : x ∈ Tor k N) {i j : Fin N} (hij : i ≠ j) :
    (x : Matrix (Fin N) (Fin N) k) i j = 0 := by
  obtain ⟨s, rfl⟩ := hx
  have h := leviEmb_apply_ne k (stdBlocks (ones N) (sum_ones N)) s hij
    (⟨0, by simp [ones]⟩ : Fin (ones N i)) (⟨0, by simp [ones]⟩ : Fin (ones N j))
  rwa [stdBlocks_ones, stdBlocks_ones] at h

theorem mem_tor_of_offDiag {N : ℕ} (x : GL (Fin N) k)
    (h : ∀ i j : Fin N, i ≠ j → (x : Matrix (Fin N) (Fin N) k) i j = 0) : x ∈ Tor k N := by
  have hd : ∀ i, (x : Matrix (Fin N) (Fin N) k) i i ≠ 0 := by
    intro i h0
    have h1 := congrArg (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i i) (mul_inv_cancel x)
    simp only [Units.val_mul, Units.val_one, Matrix.mul_apply, Matrix.one_apply_eq] at h1
    rw [Finset.sum_eq_zero] at h1
    · exact zero_ne_one h1
    · intro l _
      by_cases hl : i = l
      · subst hl
        rw [h0, zero_mul]
      · rw [h i l hl, zero_mul]
  refine ⟨fun a => Units.map (algebraMap k (Matrix (Fin (ones N a)) (Fin (ones N a)) k)).toMonoidHom
    (Units.mk0 _ (hd a)), ?_⟩
  apply Units.ext
  ext i j
  by_cases hij : i = j
  · subst hij
    have h1 := leviEmb_apply_same k (stdBlocks (ones N) (sum_ones N))
      (fun a => Units.map (algebraMap k (Matrix (Fin (ones N a)) (Fin (ones N a)) k)).toMonoidHom
        (Units.mk0 _ (hd a))) i (⟨0, by simp [ones]⟩ : Fin (ones N i)) (⟨0, by simp [ones]⟩ : Fin (ones N i))
    rw [stdBlocks_ones] at h1
    rw [h1]
    simp [Matrix.algebraMap_matrix_apply]
  · have h1 := leviEmb_apply_ne k (stdBlocks (ones N) (sum_ones N))
      (fun a => Units.map (algebraMap k (Matrix (Fin (ones N a)) (Fin (ones N a)) k)).toMonoidHom
        (Units.mk0 _ (hd a))) hij (⟨0, by simp [ones]⟩ : Fin (ones N i)) (⟨0, by simp [ones]⟩ : Fin (ones N j))
    rw [stdBlocks_ones, stdBlocks_ones] at h1
    rw [h i j hij]
    exact h1

theorem eq_diagonal_of_offDiag {N : ℕ} (M : Matrix (Fin N) (Fin N) k)
    (h : ∀ i j : Fin N, i ≠ j → M i j = 0) : M = Matrix.diagonal fun i => M i i := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · rw [h i j hij, Matrix.diagonal_apply_ne _ hij]

theorem monomial_of_conj_torus : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], ∀ (N : ℕ) (y D D' : GL (Fin N) k), D ∈ PositivityTheory.Lbc.Tor k N →
    D' ∈ PositivityTheory.Lbc.Tor k N →
    (∀ i j : Fin N, i ≠ j →
      (D' : Matrix (Fin N) (Fin N) k) i i ≠ (D' : Matrix (Fin N) (Fin N) k) j j) →
    y⁻¹ * D * y = D' →
    ∃ (σ : Equiv.Perm (Fin N)) (w : GL (Fin N) k), (w : Matrix (Fin N) (Fin N) k) = σ.permMatrix k ∧
      ∃ s ∈ PositivityTheory.Lbc.Tor k N, y = w * s := by
  intro k _ _ _ _ N y D D' hD hD' hdist hconj
  have hcomm : D * y = y * D' := by
    rw [← hconj]
    group
  have hmat : (D : Matrix (Fin N) (Fin N) k) * (y : Matrix (Fin N) (Fin N) k) =
      (y : Matrix (Fin N) (Fin N) k) * (D' : Matrix (Fin N) (Fin N) k) := by
    simpa using congrArg (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k)) hcomm
  have hent : ∀ i j, (D : Matrix (Fin N) (Fin N) k) i i * (y : Matrix (Fin N) (Fin N) k) i j =
      (y : Matrix (Fin N) (Fin N) k) i j * (D' : Matrix (Fin N) (Fin N) k) j j := by
    intro i j
    have h1 := congrFun (congrFun hmat i) j
    rw [eq_diagonal_of_offDiag (D : Matrix (Fin N) (Fin N) k) (fun a b hab => tor_offDiag hD hab),
      eq_diagonal_of_offDiag (D' : Matrix (Fin N) (Fin N) k) (fun a b hab => tor_offDiag hD' hab),
      Matrix.diagonal_mul, Matrix.mul_diagonal] at h1
    simpa using h1

  have hsupp : ∀ i j, (y : Matrix (Fin N) (Fin N) k) i j ≠ 0 →
      (D : Matrix (Fin N) (Fin N) k) i i = (D' : Matrix (Fin N) (Fin N) k) j j := by
    intro i j hij
    have h1 := hent i j
    rw [mul_comm] at h1
    exact mul_left_cancel₀ hij h1

  have hcol : ∀ j, ∃ i, (y : Matrix (Fin N) (Fin N) k) i j ≠ 0 := by
    intro j
    by_contra hc
    push_neg at hc
    have h1 := congrArg (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) j j) (inv_mul_cancel y)
    simp only [Units.val_mul, Units.val_one, Matrix.mul_apply, Matrix.one_apply_eq] at h1
    rw [Finset.sum_eq_zero (fun l _ => by rw [hc l, mul_zero])] at h1
    exact zero_ne_one h1
  choose f hf using hcol
  have hinj : Function.Injective f := by
    intro a b hab
    by_contra hne
    apply hdist a b hne
    rw [← hsupp _ _ (hf a), ← hsupp _ _ (hf b), hab]
  have hbij : Function.Bijective f := Finite.injective_iff_bijective.1 hinj
  let τ : Equiv.Perm (Fin N) := Equiv.ofBijective f hbij
  have hτ : ∀ j, τ j = f j := fun j => rfl

  have hzero : ∀ i j, i ≠ f j → (y : Matrix (Fin N) (Fin N) k) i j = 0 := by
    intro i j hij
    by_contra hne
    obtain ⟨b, rfl⟩ := hbij.2 i
    have hbj : b ≠ j := fun e => hij (by rw [e])
    apply hdist b j hbj
    rw [← hsupp _ _ (hf b), ← hsupp _ _ hne]
  have hdet : (τ⁻¹.permMatrix k).det ≠ 0 := by
    rw [Matrix.det_permutation]
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ⁻¹) with h | h <;> simp [h]
  let w : GL (Fin N) k := Matrix.GeneralLinearGroup.mkOfDetNeZero (τ⁻¹.permMatrix k) hdet
  have hw : (w : Matrix (Fin N) (Fin N) k) = τ⁻¹.permMatrix k := rfl
  refine ⟨τ⁻¹, w, hw, w⁻¹ * y, ?_, by group⟩
  apply mem_tor_of_offDiag
  intro a b hab
  have hprod : (w : Matrix (Fin N) (Fin N) k) * ((w⁻¹ * y : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      (y : Matrix (Fin N) (Fin N) k) := by
    rw [← Units.val_mul, mul_inv_cancel_left]
  rw [hw, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul] at hprod
  have h1 := congrFun (congrFun hprod (τ a)) b
  simp only [Matrix.submatrix_apply, id] at h1
  have h2 : τ⁻¹ (τ a) = a := by simp
  rw [h2] at h1
  rw [h1]
  apply hzero
  rw [← hτ]
  exact fun e => hab (τ.injective e)

end GlobalTheory.CompanionTheory.LbElem.ConjMonomial

end
