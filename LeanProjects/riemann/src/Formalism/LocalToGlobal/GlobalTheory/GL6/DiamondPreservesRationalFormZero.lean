import Formalism.LocalToGlobal.GlobalTheory.GL6.Statement

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Classical

variable (D : D7) (u : D.what₂.Word)

def t1A : Prop :=
  (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ (D.fm u).Fi i,
    Uop D u i v φ ∈ (D.fm u).Fi i ∧ Dop D u i v φ ∈ (D.fm u).Fi i ∧ ∀ a, dia D u i v a φ ∈ (D.fm u).Fi i) ∧
  (∀ i, i ≤ D.R.m → ∀ v v', v ≠ v' → ∀ φ ∈ (D.fm u).Fi i,
    Uop D u i v (Uop D u i v' φ) = Uop D u i v' (Uop D u i v φ)) ∧
  (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ (D.fm u).Fi i, ∀ ψ ∈ (D.fm u).Fi i,
    (D.fm u).ipC i (Uop D u i v φ) ψ = (D.fm u).ipC i φ (Dop D u i v ψ)) ∧
  (∀ i, i ≤ D.R.m → ∀ w, OverT D u w → (D.fm u).seenP w = true → ∀ v,
    Into D u w (Uop D u i v) ((D.fm u).Bw i w v) ((D.fm u).S i w) ∧
    Into D u w (Dop D u i v) ((D.fm u).S i w) ((D.fm u).Bw i w v)) ∧
  (∀ i, i ≤ D.R.m → ∀ w, ¬ OverT D u w → ∀ v,
    Into D u w (Uop D u i v) ((D.fm u).S i w) ((D.fm u).S i w) ∧ Into D u w (Dop D u i v) ((D.fm u).S i w) ((D.fm u).S i w)) ∧
  (∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ (D.fm u).Fi i, Dop D u i v (Uop D u i v φ) =
    ((D.mem u).A.T : ℂ) ^ (D.R.N i - 1) • φ - ((D.mem u).A.T : ℂ) ^ (D.R.N i - 2) • Nm D u i v φ
      + ((D.mem u).A.T : ℂ) ^ (D.R.N i - 2) • trp D u i v φ)

def t1c7 : Prop :=
  ∀ v, ∀ x ∈ (D.fm u).ramSub,
    (∃ y ∈ (D.fm u).ramSub, (D.fm u).emb 0 y = Uop D u 0 v ((D.fm u).emb 0 x)) ∧
    (∃ y ∈ (D.fm u).ramSub, (D.fm u).emb 0 y = Dop D u 0 v ((D.fm u).emb 0 x)) ∧
    ∀ a, ∃ y ∈ (D.fm u).ramSub, (D.fm u).emb 0 y = dia D u 0 v a ((D.fm u).emb 0 x)

def t1c8 : Prop :=
  ∀ w, ¬ OverT D u w → ∀ v,
    Into D u w (Uop D u 0 v) (Sram D u w) (Sram D u w) ∧
    Into D u w (Dop D u 0 v) (Sram D u w) (Sram D u w) ∧
    ∀ a, Into D u w (dia D u 0 v a) (Sram D u w) (Sram D u w)

def t1c9 : Prop :=
  ∀ i, i ≤ D.R.m → ∀ v, ∀ φ ∈ MramI D u i,
    Uop D u i v φ ∈ MramI D u i ∧ Dop D u i v φ ∈ MramI D u i ∧
    (∀ a, dia D u i v a φ ∈ MramI D u i) ∧ trp D u i v φ = 0 ∧
    Dop D u i v (Uop D u i v φ) = ((D.mem u).A.T : ℂ) ^ (D.R.N i - 1) • φ ∧
    Uop D u i v (Dop D u i v φ) = ((D.mem u).A.T : ℂ) ^ (D.R.N i - 1) • φ

def DiamondCommutesHecke : Prop :=
  ∀ i, i ≤ D.R.m → ∀ v v' (a : ((D.mem u).A.Fv v')ˣ), ∀ φ ∈ (D.fm u).Fi i,
    dia D u i v' a (Uop D u i v φ) = Uop D u i v (dia D u i v' a φ) ∧
    dia D u i v' a (Dop D u i v φ) = Dop D u i v (dia D u i v' a φ) ∧
    ∀ b : ((D.mem u).A.Fv v)ˣ, dia D u i v' a (dia D u i v b φ) = dia D u i v b (dia D u i v' a φ)

def TraceDiamondInvariant : Prop :=
  ∀ i, i ≤ D.R.m → ∀ v (a : ((D.mem u).A.Fv v)ˣ), ∀ φ ∈ (D.fm u).Fi i,
    trp D u i v (dia D u i v a φ) = trp D u i v φ

def HeckeRationalLevelZero : Prop :=
  ∀ v x, (∃ y, (D.fm u).emb 0 y = Uop D u 0 v ((D.fm u).emb 0 x)) ∧
    (∃ y, (D.fm u).emb 0 y = Dop D u 0 v ((D.fm u).emb 0 x))

theorem norm_eq_sum_diamond (i : ℕ) (v : (D.mem u).A.vT) (φ : Fn D u i) :
    Nm D u i v φ = ∑ a : ((D.mem u).A.Fv v)ˣ, dia D u i v a φ := by
  unfold Nm; rw [LinearMap.sum_apply]

theorem mem_ramified_forms_iff {i : ℕ} (φ : Fn D u i) :
    φ ∈ MramI D u i ↔ φ ∈ (D.fm u).Fi i ∧ ∀ v, Nm D u i v φ = 0 := by
  unfold MramI
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]

theorem U_D_of_D_U_on_finite_dim {V : Type*} [AddCommGroup V] [Module ℂ V] (W : Submodule ℂ V) [FiniteDimensional ℂ W]
    (U Dm : V →ₗ[ℂ] V) (c : ℂ) (hc : c ≠ 0) (hU : ∀ x ∈ W, U x ∈ W)
    (hDU : ∀ x ∈ W, Dm (U x) = c • x) : ∀ x ∈ W, U (Dm x) = c • x := by
  intro x hx
  have hinj : Function.Injective (U.restrict hU) := by
    intro a b hab
    have h1 : U a = U b := congrArg Subtype.val hab
    have h2 : c • (a : V) = c • (b : V) := by rw [← hDU a a.2, ← hDU b b.2, h1]
    exact Subtype.ext (smul_right_injective V hc h2)
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.1 hinj) ⟨x, hx⟩
  have hy' : U y = x := congrArg Subtype.val hy
  rw [← hy', hDU y y.2, map_smul]

theorem forms_finite_dimensional (i : ℕ) : FiniteDimensional ℂ ((D.fm u).Fi i) := by
  have h := FiniteDimensional.span_of_finite ℂ
    (Set.finite_range (fun a => (D.fm u).emb i (((D.fm u).lat i).b a)))
  rwa [((D.fm u).emb_basis i).2] at h

theorem ramified_forms_finite_dimensional (i : ℕ) : FiniteDimensional ℂ (MramI D u i) := by
  have := forms_finite_dimensional D u i
  exact Submodule.finiteDimensional_of_le (inf_le_left : MramI D u i ≤ (D.fm u).Fi i)

theorem two_le_rank_of_level (i : ℕ) : 2 ≤ D.R.N i := by
  have := D.R.m_add_three_le_k; unfold Ranks.N; omega

def HeckeRelationsInputs : Prop :=
  ∀ (D : D7) (u : D.what₂.Word), FormsCompatible D u → HidaSetting D u →
    t1A D u ∧ DiamondCommutesHecke D u ∧ TraceDiamondInvariant D u ∧ HeckeRationalLevelZero D u

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
