import Formalism.LocalToGlobal.CharacterGerms.RowTiePProjLie
import Lemmata.PowMulVecEigen.PowMulVecEig

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKey

open PartialDerivEval RowTiePE0 RowTiePProj RowTiePLSmall RowTiePLie

structure KeyData (C : Type) [Field C] (V : VF C) (O : Type) [CommRing O] (n d : ℕ) where
  ρ : O →+* Matrix (Fin n) (Fin n) C
  ρ_int : ∀ x i j, V.Ge 0 (ρ x i j)
  P : Matrix (Fin n) (Fin n) C
  em : ZMod d → (O →+* C)
  em_int : ∀ a x, V.Ge 0 (em a x)
  em_frob : ∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)
  ε : O
  ε_idem : ∃ y, ε * ε - ε = (V.l : O) * y
  ε_one : ∀ a, V.MM (em a ε - 1)
  ε_ann : ∀ x : O, (∀ a, V.MM (em a x)) → ∃ y, ε * x = (V.l : O) * y
  P_lim : ∀ (N : ℕ) i j, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (P i j - ρ (ε ^ V.l ^ n) i j)

def KeyEigSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C), IsAlgClosed C →
    (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) →
    ∀ (O : Type) [CommRing O] (n d : ℕ) [NeZero d] (K : KeyData C V O n d) (v : Fin n → C),
      ∃ (m : ℕ) (w : Fin m → Fin n → C) (χ : Fin m → (O →+* C)),
        Matrix.mulVec K.P v = ∑ j, w j ∧ ∀ j, Matrix.mulVec K.P (w j) = w j ∧
          ∀ x, Matrix.mulVec (K.ρ x) (w j) = χ j x • w j

def KeyResSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] (n d : ℕ) [NeZero d]
    (K : KeyData C V O n d) (χ : O →+* C), (∀ y, V.Ge 0 (χ y)) →
    (∀ z, (∀ a, V.MM (K.em a z)) → V.MM (χ z)) → ∃ c, ∀ y, V.MM (χ y - K.em c y)

def KeyDeltaSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] (n d : ℕ) [NeZero d]
    (K : KeyData C V O n d) (χ : O →+* C) (c : ZMod d), (∀ y, V.Ge 0 (χ y)) →
    (∀ y, V.MM (χ y - K.em c y)) → ∀ y, χ y = K.em c y

section Lemmas

variable {C : Type} [Field C] {V : VF C}

theorem aeval_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) C) (w : Fin n → C) (lam : C)
    (h : Matrix.mulVec A w = lam • w) (f : Polynomial C) :
    Matrix.mulVec (Polynomial.aeval A f) w = f.eval lam • w := by
  first | exact Bl.PowMulVecEigen.goal1 .. | (apply Bl.PowMulVecEigen.goal1 <;> assumption) | (intros; apply Bl.PowMulVecEigen.goal1 <;> assumption) | (apply @Bl.PowMulVecEigen.goal1 <;> assumption) | (intros; apply @Bl.PowMulVecEigen.goal1 <;> assumption) | (apply @Bl.PowMulVecEigen.goal1 <;> first | assumption | infer_instance)

theorem eig_int {n : ℕ} (A : Matrix (Fin n) (Fin n) C) (hA : ∀ i j, V.Ge 0 (A i j)) (w : Fin n → C) (hw : w ≠ 0)
    (lam : C) (h : Matrix.mulVec A w = lam • w) : V.Ge 0 lam := by
  obtain ⟨i0, hi0⟩ : ∃ i, w i ≠ 0 := by
    by_contra hc; push_neg at hc; exact hw (funext hc)

  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun i => V.v (w i)) ⟨i0, Finset.mem_univ _⟩
  have hwi : w i ≠ 0 := by
    intro h0
    have := hi i0 (Finset.mem_univ _)
    rw [h0, AddValuation.map_zero, top_le_iff, AddValuation.top_iff] at this
    exact hi0 this
  have hrow : lam * w i = ∑ j, A i j * w j := by
    have := congrFun h i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    exact this.symm
  have hge : V.v (w i) ≤ V.v (lam * w i) := by
    rw [hrow]
    refine AddValuation.map_le_sum V.v fun j _ => ?_
    rw [AddValuation.map_mul]
    have h1 := hA i j
    unfold VF.Ge at h1
    calc V.v (w i) ≤ V.v (w j) := hi j (Finset.mem_univ _)
      _ = 0 + V.v (w j) := (zero_add _).symm
      _ ≤ V.v (A i j) + V.v (w j) := add_le_add (by exact_mod_cast h1) le_rfl
  rw [AddValuation.map_mul] at hge
  unfold VF.Ge
  have hne : V.v (w i) ≠ ⊤ := (AddValuation.ne_top_iff V.v).mpr hwi
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
  rw [← hr] at hge
  by_contra hlt
  push_neg at hlt
  have h2 : V.v lam + (r : WithTop ℝ) < 0 + (r : WithTop ℝ) := by
    exact WithTop.add_lt_add_right (WithTop.coe_ne_top) hlt
  rw [zero_add] at h2
  exact absurd (lt_of_le_of_lt hge h2) (lt_irrefl _)

end Lemmas

end RowTiePKey

end Formalism.L2.FormalSeriesBounds
