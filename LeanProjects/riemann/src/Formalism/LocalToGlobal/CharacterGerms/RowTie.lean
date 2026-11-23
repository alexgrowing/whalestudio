import Formalism.LocalToGlobal.CharacterGerms.RowTieDefs

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace RawChart

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
  (X : RawChart C d I κ) {V : VF C}

theorem pairK_int (g : Fin 2) (q : JJ I g) (c : I (1 - g)) : V.Ge 0 (X.pairK g q c) := by
  unfold pairK
  split_ifs
  · exact (VF.ge_natCast X.k).neg
  · exact VF.Ge.zero 0

theorem k_ne_zero (hk : V.v (X.k : C) = 0) : (X.k : C) ≠ 0 := by
  intro h
  rw [h, V.v.map_zero] at hk
  exact WithTop.top_ne_zero hk

theorem k_inv_int (hk : V.v (X.k : C) = 0) : V.Ge 0 ((X.k : C)⁻¹) := by
  have h1 : V.v ((X.k : C) * (X.k : C)⁻¹) = 0 := by
    rw [mul_inv_cancel₀ (X.k_ne_zero hk), V.v.map_one]
  rw [V.v.map_mul, hk, zero_add] at h1
  unfold VF.Ge
  rw [h1]
  rfl

theorem pairK_onto (hk : V.v (X.k : C) = 0) (g : Fin 2) :
    ∃ s : I (1 - g) → JJ I g → C, (∀ c q, V.Ge 0 (s c q)) ∧
      ∀ q q' : JJ I g, ∑ c, X.pairK g q c * s c q' = if q = q' then 1 else 0 := by
  refine ⟨fun c q => if c = q then -(X.k : C)⁻¹ else 0, ?_, ?_⟩
  · intro c q
    dsimp only
    split_ifs
    · exact (X.k_inv_int hk).neg
    · exact VF.Ge.zero 0
  · intro q q'
    have hk0 := X.k_ne_zero hk
    simp only [pairK, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    split_ifs
    · field_simp
    · simp

theorem rk_fil (H : X.RankHyp) (g : Fin 2) (a : ZMod d) :
    (Finset.univ.filter fun q : I (1 - g) => X.ty (1 - g) q = a).card + 0 +
      (Finset.univ.filter fun c : I g => X.ty g c = a).card = X.n + X.j + X.j' := by
  by_cases hb : X.big g a
  · have h1 : ¬ X.big (1 - g) a := fun h => (H.big_compl g a).1 h hb
    rw [H.rk_big g a hb, H.rk_small (1 - g) a h1]
    omega
  · have h1 : X.big (1 - g) a := (H.big_compl g a).2 hb
    rw [H.rk_small g a hb, H.rk_big (1 - g) a h1]
    omega

theorem hLf_axes (H : X.AxesSt) (g : Fin 2) (a a' : ZMod d) (μ : WV I →₀ ℕ)
    (h : (∀ w ∈ μ.support, w.1 = g) ∨ (∀ w ∈ μ.support, w.1 = 1 - g)) :
    MvPowerSeries.coeff μ (X.hLf g a a') = 0 := by
  have h2 : (∀ w ∈ μ.support, w.1 = 0) ∨ (∀ w ∈ μ.support, w.1 = 1) := by
    fin_cases g
    · exact h
    · exact h.symm
  show (if ∀ w ∈ μ.support, X.OnLf g a a' w then MvPowerSeries.coeff μ X.hRow else 0) = 0
  rw [H μ h2]
  simp

def rowData [NeZero d] (H : X.Hyps V) : RowData C V d I (JJ I) where
  charZero := H.charZero
  algClosed := H.algClosed
  l_odd := H.l_odd
  G := fun g => cart (H.cartH g)
  n := X.n
  j := X.j
  j' := X.j'
  rh := 0
  r := X.n + X.j + X.j'
  r_eq := rfl
  big := X.big
  big_compl := H.rank.big_compl
  rk_big := H.rank.rk_big
  rk_small := H.rank.rk_small
  rk_fil := X.rk_fil H.rank
  pair := X.pairK
  pair_int := X.pairK_int
  pair_type := by
    intro g q c h
    unfold pairK
    rw [if_neg]
    rintro rfl
    exact h rfl
  pair_onto := X.pairK_onto H.k_unit
  R2 := H.R2
  R1 := fun hA g a hb N w x h1 h2 h3 => by simpa using H.R1 hA g a hb N w x h1 h2 h3
  G0 := H.G0
  hL := X.hLf
  hL_leaf := X.hLf_leaf
  hL_swap := X.hLf_swap
  hL_axes := X.hLf_axes H.axes
  C_eq := H.CEq
  CH := H.CH

end RawChart

end Formalism.L2.FormalSeriesBounds
