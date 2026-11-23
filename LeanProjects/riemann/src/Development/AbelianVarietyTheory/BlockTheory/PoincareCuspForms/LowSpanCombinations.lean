import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement

namespace GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def OnQuot {α : Type*} (X : Data E r) (φ : Frame X.Ψ r → α) : Prop :=
  (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) ∧
  ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, φ (lact γ x) = φ x

def SamePt (X : Data E r) (x y : Frame X.Ψ r) : Prop :=
  ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r, y = lact γ (rmul x b)

def levi (X : Data E r) (x0 : Frame X.Ψ r) (φ : Frame X.Ψ r → ℝ) (z : V (nd X))
    (ξ : Fin (nd X) → ℂ) : ℝ :=
  (leviV (nd X) (fun w => ((φ (cpt X x0 w) : ℝ) : ℂ)) z ξ).re

def hf (X : Data E r) (ξ : Fin r → E) (x : Frame X.Ψ r) (τ : X.Ψ) : ℝ :=
  X.c τ * X.maj x τ (Data.emb τ.1 ξ)

def ExtraBounds (X : Data E r) (ps : Frame X.Ψ r → ℝ) (a : ℝ) : Prop :=
  ∃ A : ℝ,
    (∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ x ∈ X.dom, ∀ ξ : Fin r → E, X.IsIso ξ → (∀ τ, hf X ξ x τ ≤ 1) →
      ps x ≤ C + A * Real.log (1 + 1 / X.la1 x) -
        8 * Real.pi * (1 - 2 * η) * a * ⨅ τ, X.tt ξ x τ) ∧
    ∃ C : ℝ, ∀ x ∈ X.dom, ps x ≤ C + A * Real.log (1 + 1 / X.la1 x)

def Admissible (X : Data E r) (ps : Frame X.Ψ r → ℝ) (a : ℝ) : Prop :=
  0 ≤ a ∧ OnQuot X ps ∧ ExtraBounds X ps a

def famNorm (X : Data E r) (L : Wt X.Ψ r) {ι : Type} [Fintype ι] (g : ι → Frame X.Ψ r → ℂ)
    (x : Frame X.Ψ r) : ℝ :=
  Real.sqrt (∑ j, X.pnorm L (g j) x ^ 2)

def IsComb (X : Data E r) {N : ℕ} (w : Fin N → Frame X.Ψ r → ℂ) (f : Frame X.Ψ r → ℂ) : Prop :=
  ∃ c : Fin N → ℂ, ∀ x ∈ X.dom, f x = ∑ j, c j * w j x

def zMap (X : Data E r) (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ)
    (x0 : Frame X.Ψ r) (u : V (nd X)) : V (nd X) :=
  WithLp.toLp 2 fun i => s i (cpt X x0 u) / w0 (cpt X x0 u)

structure IsFlat (X : Data E r) (L : Wt X.Ψ r) {N : ℕ} (w : Fin N → Frame X.Ψ r → ℂ)
    (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ) {del : ℕ}
    (P : Fin del → Frame X.Ψ r) : Prop where
  w_sec : ∀ j, X.IsSec L (w j)
  base_weight_isComb : IsComb X w w0
  s_comb : ∀ i, IsComb X w (s i)
  w_pos : ∀ x ∈ X.dom, 0 < famNorm X L w x
  del_pos : 0 < del
  rep_mem : ∀ k, P k ∈ X.dom
  rep_inj : ∀ k k', SamePt X (P k) (P k') → k = k'
  zero_iff : ∀ x ∈ X.dom, (∀ i, s i x = 0) ↔ ∃ k, SamePt X (P k) x
  w0_ne : ∀ k, w0 (P k) ≠ 0
  coord : ∀ k, ∃ T : V (nd X) ≃L[ℂ] V (nd X),
    HasFDerivAt (zMap X w0 s (P k)) (T : V (nd X) →L[ℂ] V (nd X)) 0
  family_le_coords : ∀ U : Set (Frame X.Ψ r), IsOpen U → (∀ k, P k ∈ U) → ∃ C : ℝ, ∀ x ∈ X.dom,
    (∀ u ∈ U, u ∈ X.dom → ¬ SamePt X u x) → famNorm X L w x ≤ C * famNorm X L s x
  weight_le_base_weight : ∃ C : ℝ, ∀ x ∈ X.dom,
    famNorm X L w x ≤ C * famNorm X L (fun o : Option (Fin (nd X)) => o.elim w0 s) x

def lowIdx (D T : ℕ) : Finset (Fin D → ℕ) :=
  (Fintype.piFinset fun _ : Fin D => Finset.range T).filter fun al => ∑ i, al i + D < T

theorem mem_lowIdx {D T : ℕ} {al : Fin D → ℕ} : al ∈ lowIdx D T ↔ ∑ i, al i + D < T := by
  simp only [lowIdx, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range, and_iff_right_iff_imp]
  intro h i
  have := Finset.single_le_sum (f := al) (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

def gen {α : Type*} {D : ℕ} (T : ℕ) (w0 : α → ℂ) (s : Fin D → α → ℂ) (t : α → ℂ) (al : Fin D → ℕ)
    (x : α) : ℂ :=
  (∏ i, s i x ^ al i) * w0 x ^ (T - ∑ i, al i) * t x

def lowComb {α : Type*} {D del : ℕ} (T : ℕ) (w0 : α → ℂ) (s : Fin D → α → ℂ) (t : Fin del → α → ℂ)
    (c : (Fin D → ℕ) → Fin del → ℂ) (x : α) : ℂ :=
  ∑ al ∈ lowIdx D T, ∑ k, c al k * gen T w0 s (t k) al x

def InLowSpan (X : Data E r) (T : ℕ) (w0 : Frame X.Ψ r → ℂ) (s : Fin (nd X) → Frame X.Ψ r → ℂ)
    {del : ℕ} (t : Fin del → Frame X.Ψ r → ℂ) (f : Frame X.Ψ r → ℂ) : Prop :=
  ∃ c : (Fin (nd X) → ℕ) → Fin del → ℂ, ∀ x ∈ X.dom, f x = lowComb T w0 s t c x

theorem nonempty_cmType (X : Data E r) : Nonempty X.Ψ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : τ ∈ X.Ψ
  · exact ⟨⟨τ, h⟩⟩
  · have := (X.cmType τ).not.1 h
    exact ⟨⟨_, not_not.1 this⟩⟩

theorem tt_eq (X : Data E r) (ξ : Fin r → E) (x : Frame X.Ψ r) (τ : X.Ψ) :
    X.tt ξ x τ = 1 / hf X ξ x τ := rfl

theorem admissible_zero (X : Data E r) : Admissible X (fun _ => 0) 0 :=
  ⟨le_rfl, ⟨fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩, 0,
    fun _ _ => ⟨0, fun _ _ _ _ _ => by simp⟩, 0, fun _ _ => by simp⟩

theorem cpt_zero (X : Data E r) (x0 : Frame X.Ψ r) : cpt X x0 0 = x0 := by
  funext τ
  have h : mat (nmat X 0) τ = 1 := by
    ext a b
    simp only [mat, nmat, Matrix.of_apply, Matrix.one_apply]
    split_ifs with h1 h2
    · exact absurd h2 h1.ne'
    all_goals first | rfl | simp
  simp only [cpt, rmul, h, Matrix.mul_one]
  rfl

theorem isFlat_rank_one (X : Data E 1) (x0 : Frame X.Ψ 1) (h0 : x0 ∈ X.dom) :
    IsFlat X 0 (fun _ : Fin 1 => fun _ => 1) (fun _ => 1) (fun _ _ => 0) (fun _ : Fin 1 => x0) := by
  have hE : IsEmpty (Ent X) := ⟨fun p => absurd p.2.2 (by rw [Subsingleton.elim p.2.1.2 p.2.1.1]; exact lt_irrefl _)⟩
  have hnd : nd X = 0 := Fintype.card_eq_zero
  have hF : IsEmpty (Fin (nd X)) := by rw [hnd]; infer_instance
  have hV : Subsingleton (V (nd X)) := ⟨fun u v => by ext i; exact hF.elim i⟩
  have hsame : ∀ x ∈ X.dom, SamePt X x0 x := by
    intro x hx
    have ha : ∀ τ, x0 τ 0 0 ≠ 0 := fun τ => by simpa [mat] using (h0 τ).1
    have hb : ∀ τ, x τ 0 0 ≠ 0 := fun τ => by simpa [mat] using (hx τ).1
    refine ⟨1, X.Γ.one_mem, fun τ _ _ => x τ 0 0 / x0 τ 0 0, fun τ => ⟨?_, fun a c h => ?_⟩, ?_⟩
    · simpa [mat] using ⟨hb τ, ha τ⟩
    · exact absurd h (by rw [Subsingleton.elim c a]; exact lt_irrefl _)
    · funext τ a c
      rw [Subsingleton.elim a 0, Subsingleton.elim c 0]
      have := ha τ
      simp [lact, rmul, mat, Matrix.mul_apply]
      change x τ 0 0 = ∑ j : Fin 1, x0 τ 0 j * (x τ 0 0 / x0 τ 0 0)
      simp only [Finset.univ_unique, Finset.sum_singleton, Fin.default_eq_zero]
      field_simp
  have hχ : ∀ γ ∈ X.Γ, X.χ 0 γ = 1 := by
    intro γ hγ
    obtain ⟨n, hn, h⟩ := X.χ_fin 0
    have hne : X.χ 0 γ ≠ 0 := fun e => by
      have := h γ hγ
      rw [e, zero_pow hn.ne'] at this
      exact zero_ne_one this
    have h2 := X.χ_add 0 0 γ hγ
    rw [add_zero] at h2
    exact (mul_right_eq_self₀.1 h2.symm).resolve_right hne
  have hp : ∀ x, X.pnorm 0 (fun _ => 1) x = 1 := fun x => by simp [Data.pnorm]
  refine ⟨fun _ => ⟨differentiableOn_const _, fun x _ b _ => by simp [bchar],
      fun γ hγ x _ => by simp [hχ γ hγ]⟩, ⟨fun _ => 1, fun _ _ => by simp⟩,
    fun _ => ⟨fun _ => 0, fun _ _ => by simp⟩, fun x _ => by simp [famNorm, hp], Nat.one_pos,
    fun _ => h0, fun _ _ _ => Subsingleton.elim _ _,
    fun x hx => ⟨fun _ => ⟨0, hsame x hx⟩, fun _ _ => rfl⟩, fun _ => one_ne_zero,
    fun _ => ⟨ContinuousLinearEquiv.refl ℂ _, ?_⟩,
    fun U _ hU => ⟨0, fun x hx h => absurd (hsame x hx) (h x0 (hU 0) h0)⟩,
    1, fun x _ => ?_⟩
  · have := hasFDerivAt_of_subsingleton (𝕜 := ℂ) (zMap X (fun _ => 1) (fun _ _ => 0) x0) 0
    convert this using 1
    ext v i
    exact hF.elim i
  · unfold famNorm
    rw [Fintype.sum_option]
    simp [hp]

example : lowIdx 1 3 = {![0], ![1]} := by decide

end

end GlobalTheory.IndefiniteRowSideFullHecke.LowSpanCombinations
