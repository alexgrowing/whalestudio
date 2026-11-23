import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChainIndependenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSymmetryStatement

open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open ReciprocityTheory.Ty.Fin

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFinRow

def posFn {m : ℕ} (j o : ℕ) : Fin m ⊕ Fin j → ℕ
  | .inl a => if (a : ℕ) < o then a else a + j
  | .inr w => o + w

theorem posFn_lt {m j N o : ℕ} (h : m + j = N) (ho : o ≤ m) (x : Fin m ⊕ Fin j) : posFn j o x < N := by
  rcases x with a | w
  · have := a.2
    simp only [posFn]
    split_ifs <;> omega
  · have := w.2
    simp only [posFn]
    omega

theorem posFn_injective {m j o : ℕ} (ho : o ≤ m) :
    Function.Injective (posFn j o : Fin m ⊕ Fin j → ℕ) := by
  rintro (a | w) (b | w') hxy <;> simp only [posFn] at hxy
  · have : (a : ℕ) = b := by split_ifs at hxy <;> omega
    exact congrArg _ (Fin.ext this)
  · have := w'.2
    exfalso
    split_ifs at hxy <;> omega
  · have := w.2
    exfalso
    split_ifs at hxy <;> omega
  · exact congrArg _ (Fin.ext (by omega))

def eo {m j N o : ℕ} (h : m + j = N) (ho : o ≤ m) : Fin m ⊕ Fin j ≃ Fin N :=
  Equiv.ofBijective (fun x => ⟨posFn j o x, posFn_lt h ho x⟩) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun x y hxy => posFn_injective ho (congrArg Fin.val hxy), ?_⟩
    simp [h])

theorem eo_val {m j N o : ℕ} (h : m + j = N) (ho : o ≤ m) (x : Fin m ⊕ Fin j) :
    ((eo h ho x : Fin N) : ℕ) = posFn j o x := rfl

section Pull

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

theorem col_pat {m j N : ℕ} (h : m + j = N) (ho : 0 ≤ m) :
    (fun x y => colPat N j (eo h ho x) (eo h ho y)) = chainPat m j 0 := by
  funext x y
  apply propext
  rcases x with a | w <;> rcases y with b | w' <;>
    simp only [colPat, Fin.lt_def, eo_val, posFn, chainPat] <;>
    (try have := a.2) <;> (try have := b.2) <;> (try have := w.2) <;> (try have := w'.2) <;>
    (try split_ifs) <;> omega

theorem col_E {m j N : ℕ} (h : m + j = N) (ho : 0 ≤ m) :
    (fun x y => cutE K N j (eo h ho x) (eo h ho y)) = chainE K m j := by
  funext x y
  rcases x with a | w <;> rcases y with b | w' <;>
    simp only [cutE, eo_val, posFn, chainE] <;>
    (try have := a.2) <;> (try have := b.2) <;> (try have := w.2) <;> (try have := w'.2) <;>
    first
      | exact if_congr (by omega) rfl rfl
      | (split_ifs <;> first | rfl | (exfalso; omega))

theorem row_pat {m j N k a : ℕ} (h : m + j = N) (ho : a + 1 ≤ m) (hk : k = a + 1 + j) :
    (fun x y => rowPat N k a (eo h ho x) (eo h ho y)) = chainPat m j a := by
  funext x y
  apply propext
  rcases x with x | w <;> rcases y with b | w' <;>
    simp only [rowPat, Fin.lt_def, eo_val, posFn, chainPat] <;>
    (try have := x.2) <;> (try have := b.2) <;> (try have := w.2) <;> (try have := w'.2) <;>
    (try split_ifs) <;> omega

theorem row_E {m j N k a : ℕ} (h : m + j = N) (ho : a + 1 ≤ m) (hk : k = a + 1 + j) :
    (fun x y => rowE K N k a (eo h ho x) (eo h ho y)) = chainE K m j := by
  funext x y
  rcases x with x | w <;> rcases y with b | w' <;>
    simp only [rowE, eo_val, posFn, chainE] <;>
    (try have := x.2) <;> (try have := b.2) <;> (try have := w.2) <;> (try have := w'.2) <;>
    first
      | exact if_congr (by omega) rfl rfl
      | (split_ifs <;> first | rfl | (exfalso; omega))

theorem j_pat {m kk N s : ℕ} (h : m + kk = N) (ho : s ≤ m) :
    (fun x y => jPat N kk s (eo h ho x) (eo h ho y)) = chainPat m kk s := by
  funext x y
  apply propext
  rcases x with x | w <;> rcases y with b | w' <;>
    simp only [jPat, Fin.lt_def, eo_val, posFn, chainPat] <;>
    (try have := x.2) <;> (try have := b.2) <;> (try have := w.2) <;> (try have := w'.2) <;>
    (try split_ifs) <;> omega

theorem j_E {m kk N s : ℕ} (h : m + kk = N) (ho : s ≤ m) :
    (fun x y => jE K N kk s (eo h ho x) (eo h ho y)) = chainE K m kk := by
  funext x y
  rcases x with x | w <;> rcases y with b | w' <;>
    simp only [jE, eo_val, posFn, chainE] <;>
    (try have := x.2) <;> (try have := b.2) <;> (try have := w.2) <;> (try have := w'.2) <;>
    first
      | exact if_congr (by omega) rfl rfl
      | (split_ifs <;> first | rfl | (exfalso; omega))

theorem wh_eq_col (hS : St.WhSym) (hC : St.ChainIndep) {m j N o t : ℕ} (h : m + j = N) (ho : o ≤ m)
    (ht : t < m) (ψ₀ : AddChar K ℂ) (hψ : ψ₀ ≠ 1) (χ : GL (Fin N) K → ℂ)
    (hχ : ∀ x g, χ (x * g * x⁻¹) = χ g) {Φ : Fin N → Fin N → Prop} {E : Fin N → Fin N → K}
    (hΦ : (fun x y => Φ (eo h ho x) (eo h ho y)) = chainPat m j t)
    (hE : (fun x y => E (eo h ho x) (eo h ho y)) = chainE K m j) :
    wh Φ E ψ₀ χ = wh (colPat N j) (cutE K N j) ψ₀ χ := by
  have h0 : 0 ≤ m := Nat.zero_le m
  have s1 := (hS K (Fin m ⊕ Fin j) (Fin N) Φ E ψ₀ χ).1 (eo h ho)
  have s2 := (hS K (Fin m ⊕ Fin j) (Fin N) (colPat N j) (cutE K N j) ψ₀ χ).1 (eo h h0)
  have c := ((hS K (Fin m ⊕ Fin j) (Fin N) Φ E ψ₀ χ).2 hχ).1 (eo h ho) (eo h h0)
  rw [hΦ, hE] at s1
  rw [col_pat h h0, col_E K h h0] at s2
  rw [← s1, ← s2, show (fun x => χ (glEquiv K (eo h ho) x)) = fun x => χ (glEquiv K (eo h h0) x)
    from funext c]
  refine hC K m j t ψ₀ _ hψ (fun x g => ?_) ht
  simp only [map_mul, map_inv]
  exact hχ _ _

theorem rowToCol_of (hS : St.WhSym) (hC : St.ChainIndep) : St.RowToCol := by
  intro K _ _ _ N ψ₀ χ hψ hχ
  refine ⟨fun k a hak hkN => ?_, fun kk s hN => ?_⟩
  · have h : (N - (k - 1 - a)) + (k - 1 - a) = N := by omega
    have ho : a + 1 ≤ N - (k - 1 - a) := by omega
    have hk : k = a + 1 + (k - 1 - a) := by omega
    exact wh_eq_col K hS hC h ho (t := a) (by omega) ψ₀ hψ χ hχ (row_pat h ho hk) (row_E K h ho hk)
  · have h : (2 * s + 1) + kk = N := by omega
    have ho : s ≤ 2 * s + 1 := by omega
    exact wh_eq_col K hS hC h ho (t := s) (by omega) ψ₀ hψ χ hχ (j_pat h ho) (j_E K h ho)

end Pull

theorem rowToCol : St.RowToCol := rowToCol_of GlobalTheory.T.whittaker_symmetry GlobalTheory.T.chain_independence

end GlobalTheory.CompanionTheory.TyFinRow
