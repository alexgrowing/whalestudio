import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction

open Matrix

namespace Formalism.L2.NX

section UCard

variable {r : ℕ}

theorem IsUniTri.det_eq_one {R : Type} [CommRing R] {M : Matrix (Fin r) (Fin r) R} (hM : IsUniTri r M) :
    M.det = 1 := by
  rw [Matrix.det_of_isUpperTriangular hM.1]
  simp [hM.2]

abbrev SUp (r : ℕ) : Type := {q : Fin r × Fin r // q.1 < q.2}

def uniTriEquiv (R : Type) [CommRing R] :
    {M : Matrix (Fin r) (Fin r) R // IsUniTri r M} ≃ (SUp r → R) where
  toFun M q := M.1 q.1.1 q.1.2
  invFun f := ⟨Matrix.of fun a b => if h : a < b then f ⟨(a, b), h⟩ else if a = b then 1 else 0,
    fun a b hba => by
      have h1 : ¬ a < b := not_lt.2 (le_of_lt hba)
      have h2 : a ≠ b := ne_of_gt hba
      simp [Matrix.of_apply, h1, h2],
    fun a => by simp⟩
  left_inv M := by
    apply Subtype.ext
    ext a b
    simp only [Matrix.of_apply]
    rcases lt_trichotomy a b with h | rfl | h
    · simp [h]
    · simp [M.2.2 a]
    · have h1 : ¬ a < b := not_lt.2 (le_of_lt h)
      have h2 : a ≠ b := ne_of_gt h
      have h3 : M.1 a b = 0 := M.2.1 h
      simp [h1, h2, h3]
  right_inv f := by
    funext q
    simp [q.2]

theorem card_SUp (r : ℕ) : Nat.card (SUp r) = r * (r - 1) / 2 := by
  have e : SUp r ≃ Σ b : Fin r, {a : Fin r // a < b} :=
    { toFun := fun q => ⟨q.1.2, q.1.1, q.2⟩
      invFun := fun s => ⟨(s.2.1, s.1), s.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h : ∀ b : Fin r, Fintype.card {a : Fin r // a < b} = (b : ℕ) := by
    intro b
    rw [Fintype.card_subtype, Finset.filter_gt_eq_Iio, Fin.card_Iio]
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [h]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) r, Finset.sum_range_id]

variable {ι : Type} [Fintype ι]

noncomputable def uupEquiv (p : ι → ℕ) (r : ℕ) :
    Uup p r ≃ ∀ x, {M : Matrix (Fin r) (Fin r) (ZMod (p x)) // IsUniTri r M} where
  toFun g x := ⟨((g.1 x : GL (Fin r) (ZMod (p x))) : Matrix (Fin r) (Fin r) (ZMod (p x))), g.2 x⟩
  invFun M := ⟨fun x => Matrix.nonsingInvUnit (M x).1 (by rw [(M x).2.det_eq_one]; exact isUnit_one),
    fun x => (M x).2⟩
  left_inv g := by
    apply Subtype.ext
    funext x
    apply Units.ext
    rfl
  right_inv M := by
    funext x
    rfl

theorem card_Uup (p : ι → ℕ) (r : ℕ) : Nat.card (Uup p r) = ∏ x, p x ^ (r * (r - 1) / 2) := by
  rw [Nat.card_congr (uupEquiv p r), Nat.card_pi]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [Nat.card_congr (uniTriEquiv (ZMod (p x))), Nat.card_fun, card_SUp, Nat.card_zmod]

example : Nat.card (Uup (fun _ : Fin 1 => 3) 3) = 27 := by
  rw [card_Uup]; rfl

example : Nat.card (Uup (fun x : Fin 2 => if x = 0 then 2 else 5) 2) = 10 := by
  rw [card_Uup]; decide

end UCard

end Formalism.L2.NX

namespace Formalism.L2

open Formalism.BasicNotions NX

theorem NExpTied.uCard {D : D7} (T : NExpTied D) :
    Nat.card D.nexp.U = (D.host.g 0 * D.host.g 1) ^ (D.R.f * (D.R.r * (D.R.r - 1) / 2)) := by
  rw [T.U_eq, card_Uup, Fintype.prod_sigma]
  simp only [Finset.prod_const, Finset.card_univ, D.nd.card_PlG, Fin.prod_univ_two]
  rw [← pow_mul, ← pow_mul, ← mul_pow, mul_comm (D.R.r * (D.R.r - 1) / 2)]

end Formalism.L2
