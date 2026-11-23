import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

namespace Formalism.MainNotions.Pk

open Formalism.BasicNotions

def EvD {eps : ℝ} (Fm : FamP eps) (P : D7 → Prop) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, P (Fm.D x i)

theorem EvD.and {eps : ℝ} {Fm : FamP eps} {P Q : D7 → Prop} (hP : EvD Fm P) (hQ : EvD Fm Q) :
    EvD Fm fun D => P D ∧ Q D := by
  obtain ⟨x1, h1⟩ := hP
  obtain ⟨x2, h2⟩ := hQ
  exact ⟨max x1 x2, fun x hx i => ⟨h1 x (le_trans (le_max_left _ _) hx) i, h2 x (le_trans (le_max_right _ _) hx) i⟩⟩

theorem EvD.mono {eps : ℝ} {Fm : FamP eps} {P Q : D7 → Prop} (hP : EvD Fm P) (h : ∀ D, P D → Q D) : EvD Fm Q := by
  obtain ⟨x0, h0⟩ := hP
  exact ⟨x0, fun x hx i => h _ (h0 x hx i)⟩

theorem EvD.of_all {eps : ℝ} (Fm : FamP eps) {P : D7 → Prop} (h : ∀ D, P D) : EvD Fm P := ⟨0, fun _ _ _ => h _⟩

def DGamSmooth {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word) (p : ℕ), p.Prime → p ∣ ((Fm.D x i).mem u).C.DGam →
    p ≤ 2 * (Fm.D x i).R.f * (Fm.D x i).R.N (Fm.D x i).R.m + 1

theorem Closed.sub {𝒞 𝒞' : FamClass} {P : ∀ {eps : ℝ}, FamP eps → ℝ → Prop} (h : Closed 𝒞 P)
    (hs : ∀ {eps : ℝ} (Fm : FamP eps), 𝒞' Fm → 𝒞 Fm) : Closed 𝒞' P := by
  obtain ⟨e1, he1, h1⟩ := h
  refine ⟨e1, he1, fun eps h0 hle => ?_⟩
  obtain ⟨K, hK⟩ := h1 eps h0 hle
  exact ⟨K, fun Fm CH hc hL => hK Fm CH (hs Fm hc) hL⟩

theorem Closed.of_class {𝒞 : FamClass} {P : ∀ {eps : ℝ}, FamP eps → ℝ → Prop}
    (hs : ∀ {eps : ℝ} (Fm : FamP eps) (CH : ℝ), 𝒞 Fm → P Fm CH) : Closed 𝒞 P :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH hc _ => hs Fm CH hc⟩⟩

theorem Closed.large {𝒞 : FamClass} {P Q : ∀ {eps : ℝ}, FamP eps → ℝ → Prop} (K0 : TransportedAlt) (hP : Closed 𝒞 P)
    (h : ∀ {eps : ℝ} (Fm : FamP eps) (CH : ℝ), Fm.Large K0 CH → P Fm CH → Q Fm CH) : Closed 𝒞 Q := by
  obtain ⟨e1, he1, h1⟩ := hP
  refine ⟨e1, he1, fun eps h0 hle => ?_⟩
  obtain ⟨K1, hK1⟩ := h1 eps h0 hle
  refine ⟨⟨max K0.pre K1.pre, fun l => max (K0.t l) (K1.t l), fun l => max (K0.mid l) (K1.mid l),
    fun l => max (K0.last l) (K1.last l)⟩, fun Fm CH hc hL => ?_⟩
  unfold FamP.Large at hL
  obtain ⟨hA, -, hC, hD⟩ := hL
  have hL0 : Fm.Large K0 CH := by
    unfold FamP.Large
    exact ⟨fun c hc' => le_trans (le_max_left _ _) (hA c hc'), trivial,
      fun c hc' => le_trans (le_max_left _ _) (hC c hc'), fun c hc' => le_trans (le_max_left _ _) (hD c hc')⟩
  have hL1 : Fm.Large K1 CH := by
    unfold FamP.Large
    exact ⟨fun c hc' => le_trans (le_max_right _ _) (hA c hc'), trivial,
      fun c hc' => le_trans (le_max_right _ _) (hC c hc'), fun c hc' => le_trans (le_max_right _ _) (hD c hc')⟩
  exact h Fm CH hL0 (hK1 Fm CH hc hL1)

end Formalism.MainNotions.Pk

end
