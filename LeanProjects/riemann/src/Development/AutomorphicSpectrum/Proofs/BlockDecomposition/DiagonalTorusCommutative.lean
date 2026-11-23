import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.JPred

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.LbElem.TorComm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stdBlocks_ones_eq (N : ℕ) (a : Fin N) (i : Fin (ones N a)) :
    stdBlocks (ones N) (sum_ones N) ⟨a, i⟩ = a := by
  have hi : (i : ℕ) = 0 := by
    have := i.isLt
    simp only [ones] at this
    omega
  apply Fin.ext
  rw [stdBlocks_val]
  simp [ones, hi]

theorem offDiag_of_mem {N : ℕ} {x : GL (Fin N) k} (hx : x ∈ Tor k N) {i j : Fin N} (hij : i ≠ j) :
    (x : Matrix (Fin N) (Fin N) k) i j = 0 := by
  rw [Tor, MonoidHom.mem_range] at hx
  obtain ⟨s, rfl⟩ := hx
  obtain ⟨⟨a, p⟩, rfl⟩ := (stdBlocks (ones N) (sum_ones N)).surjective i
  obtain ⟨⟨b, q⟩, rfl⟩ := (stdBlocks (ones N) (sum_ones N)).surjective j
  have hab : a ≠ b := by
    rintro rfl
    apply hij
    have hp : (p : ℕ) = 0 := by
      have := p.isLt
      simp only [ones] at this
      omega
    have hq : (q : ℕ) = 0 := by
      have := q.isLt
      simp only [ones] at this
      omega
    have hpq : p = q := Fin.ext (hp.trans hq.symm)
    rw [hpq]
  exact leviEmb_apply_ne k _ s hab p q

theorem diag_ne_zero {N : ℕ} (x : GL (Fin N) k)
    (h : ∀ i j : Fin N, i ≠ j → (x : Matrix (Fin N) (Fin N) k) i j = 0) (i : Fin N) :
    (x : Matrix (Fin N) (Fin N) k) i i ≠ 0 := by
  have hM : (x : Matrix (Fin N) (Fin N) k) =
      Matrix.diagonal fun l => (x : Matrix (Fin N) (Fin N) k) l l := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp
    · rw [Matrix.diagonal_apply_ne _ hab]
      exact h a b hab
  have hdet : (x : Matrix (Fin N) (Fin N) k).det ≠ 0 := (Matrix.isUnits_det_units x).ne_zero
  rw [hM, Matrix.det_diagonal] at hdet
  exact Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ i)

theorem mem_of_offDiag {N : ℕ} (x : GL (Fin N) k)
    (h : ∀ i j : Fin N, i ≠ j → (x : Matrix (Fin N) (Fin N) k) i j = 0) : x ∈ Tor k N := by
  rw [Tor, MonoidHom.mem_range]
  refine ⟨(fun a => Matrix.GeneralLinearGroup.scalar _
    (Units.mk0 ((x : Matrix (Fin N) (Fin N) k) a a) (diag_ne_zero x h a)) : Levi k (Bl (ones N))), ?_⟩
  apply Units.ext
  ext i j
  obtain ⟨⟨a, p⟩, rfl⟩ := (stdBlocks (ones N) (sum_ones N)).surjective i
  obtain ⟨⟨b, q⟩, rfl⟩ := (stdBlocks (ones N) (sum_ones N)).surjective j
  by_cases hab : a = b
  · subst hab
    have hpq : p = q := by
      apply Fin.ext
      have hp := p.isLt
      have hq := q.isLt
      simp only [ones] at hp hq
      omega
    subst hpq
    refine (leviEmb_apply_same (m := fun c => Fin (ones N c)) k _ _ a p p).trans ?_
    rw [stdBlocks_ones_eq N a p]
    simp [Matrix.GeneralLinearGroup.scalar]
  · rw [h _ _ (fun heq => hab (congrArg Sigma.fst ((stdBlocks (ones N) (sum_ones N)).injective heq)))]
    exact leviEmb_apply_ne (m := fun c => Fin (ones N c)) k _ _ hab p q

theorem eq_diagonal {N : ℕ} (M : Matrix (Fin N) (Fin N) k)
    (h : ∀ i j : Fin N, i ≠ j → M i j = 0) : M = Matrix.diagonal fun i => M i i := by
  ext a b
  by_cases hab : a = b
  · subst hab
    simp
  · rw [Matrix.diagonal_apply_ne _ hab]
    exact h a b hab

theorem mul_comm_of_mem {N : ℕ} {a b : GL (Fin N) k} (ha : a ∈ Tor k N) (hb : b ∈ Tor k N) :
    a * b = b * a := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul,
    eq_diagonal (a : Matrix (Fin N) (Fin N) k) (fun i j hij => offDiag_of_mem ha hij),
    eq_diagonal (b : Matrix (Fin N) (Fin N) k) (fun i j hij => offDiag_of_mem hb hij),
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem tor_comm_and_mem_iff : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], ∀ (N : ℕ),
    (∀ a ∈ PositivityTheory.Lbc.Tor k N, ∀ b ∈ PositivityTheory.Lbc.Tor k N, a * b = b * a) ∧
      ∀ x : GL (Fin N) k, x ∈ PositivityTheory.Lbc.Tor k N ↔
        ∀ i j : Fin N, i ≠ j → (x : Matrix (Fin N) (Fin N) k) i j = 0 := by
  intro k _ _ _ _ N
  exact ⟨fun a ha b hb => mul_comm_of_mem ha hb,
    fun x => ⟨fun hx i j hij => offDiag_of_mem hx hij, mem_of_offDiag x⟩⟩

end GlobalTheory.CompanionTheory.LbElem.TorComm

end
