import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResAlgSplitTwo
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianVectorValuesCardStatement

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens

namespace GlobalTheory.CompanionTheory.UnrDens.OrthCount

variable {E : Type} [CommRing E] {τ : E →+* E} {V : Type} [AddCommGroup V] [Module E V]

abbrev Tuples (B : HermSp E τ V) (n : ℕ) : Type :=
  {x : Fin n → V // ∀ i j, B.h (x i) (x j) = if i = j then 1 else 0}

theorem isUnit_norm (B : HermSp E τ V) (w : {w : V // B.h w w = 1}) : IsUnit (B.h w.1 w.1) := by
  rw [w.2]; exact isUnit_one

noncomputable def consEquiv (B : HermSp E τ V) (n : ℕ) :
    Tuples B (n + 1) ≃
      Σ w : {w : V // B.h w w = 1}, Tuples (B.perpForm (isUnit_norm B w)) n where
  toFun x := ⟨⟨x.1 0, by simpa using x.2 0 0⟩,
    ⟨fun j => ⟨x.1 j.succ, by
      show B.h (x.1 j.succ) (x.1 0) = 0
      simpa [Fin.succ_ne_zero] using x.2 j.succ 0⟩, fun i j => by
      simpa using x.2 i.succ j.succ⟩⟩
  invFun p := ⟨Fin.cons p.1.1 (fun j => (p.2.1 j : V)), by
    obtain ⟨⟨w, hw⟩, ⟨y, hy⟩⟩ := p
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hw
    · have h0 : B.h (y j : V) w = 0 := (y j).2
      simp [B.symm (y j : V) w, h0, (Fin.succ_ne_zero j).symm]
    · have h0 : B.h (y i : V) w = 0 := (y i).2
      simp [h0, Fin.succ_ne_zero i]
    · simpa using hy i j⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    refine Fin.cases rfl (fun j => rfl) i
  right_inv p := by
    obtain ⟨⟨w, hw⟩, ⟨y, hy⟩⟩ := p
    rfl

end GlobalTheory.CompanionTheory.UnrDens.OrthCount

namespace GlobalTheory.CompanionTheory.UnrDens

open OrthCount in

theorem card_orthonormal_tuples : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (n m : ℕ), n ≤ m → ∀ (V : Type) [AddCommGroup V] [Module E V] (B : HermSp E τ V), Nat.card V = q ^ (2 * m) → (Nat.card {x : Fin n → V // ∀ i j, B.h (x i) (x j) = if i = j then 1 else 0} : ℝ) = ∏ i : Fin n, ((q : ℝ) ^ (2 * (m - (i : ℕ))) / q * (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ)))) := by
  intro E _ τ q ε hR n
  induction n with
  | zero =>
    intro m _ V _ _ B _
    have h1 : Nat.card {x : Fin 0 → V // ∀ i j, B.h (x i) (x j) = if i = j then 1 else 0} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => Subtype.ext (funext fun i => i.elim0)⟩,
        ⟨⟨fun i => i.elim0, fun i => i.elim0⟩⟩⟩
    simp [h1]
  | succ n ih =>
    intro m hnm V _ _ B hc
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hq : 1 < q := hR.one_lt
    have hq0 : q ≠ 0 := by omega
    haveI : Finite V := Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hq0)
    haveI : Finite E := Nat.finite_of_card_ne_zero (by rw [hR.card]; exact pow_ne_zero _ hq0)
    haveI : Nontrivial E := Finite.one_lt_card_iff_nontrivial.1 (by rw [hR.card]; nlinarith)
    have hsph := (GlobalTheory.T.hermitian_vector_values_card E τ q ε hR (m' + 1) V B hc).1 1 (map_one τ) one_ne_zero
    have hperp : ∀ w : {w : V // B.h w w = 1}, Nat.card (B.perp w.1) = q ^ (2 * m') := by
      intro w
      have h1 := Nat.card_congr (B.perpEquiv (isUnit_norm B w))
      rw [Nat.card_prod, hR.card, hc] at h1
      have h2 : q ^ (2 * (m' + 1)) = q ^ 2 * q ^ (2 * m') := by ring
      rw [h2] at h1
      exact Nat.eq_of_mul_eq_mul_left (pow_pos (by omega) 2) h1
    have hfib : ∀ w : {w : V // B.h w w = 1},
        (Nat.card (Tuples (B.perpForm (isUnit_norm B w)) n) : ℝ) =
          ∏ i : Fin n, ((q : ℝ) ^ (2 * (m' - (i : ℕ))) / q * (1 - ((ε : ℝ) / q) ^ (m' - (i : ℕ)))) :=
      fun w => ih m' (by omega) (B.perp w.1) (B.perpForm (isUnit_norm B w)) (hperp w)
    haveI : Fintype {w : V // B.h w w = 1} := Fintype.ofFinite _
    have hcard : (Nat.card (Tuples B (n + 1)) : ℝ) =
        (Nat.card {w : V // B.h w w = 1} : ℝ) *
          ∏ i : Fin n, ((q : ℝ) ^ (2 * (m' - (i : ℕ))) / q * (1 - ((ε : ℝ) / q) ^ (m' - (i : ℕ)))) := by
      rw [Nat.card_congr (consEquiv B n), Nat.card_sigma]
      push_cast
      rw [Finset.sum_congr rfl (fun w _ => hfib w), Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Nat.card_eq_fintype_card]
    change (Nat.card (Tuples B (n + 1)) : ℝ) = _
    rw [hcard, hsph, Fin.prod_univ_succ]
    simp [Nat.add_sub_add_right]

end GlobalTheory.CompanionTheory.UnrDens
