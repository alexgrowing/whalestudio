import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.LocGL

theorem exists_isL_of_unitary_twists (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [CharZero k] (hS : GlobalTheory.Published.StandardCosocleGL)
    (hP : ∀ (δ δ' : IrrGL k) (Δ Δ' : Segment k), IsLSeg Δ δ.rep → IsUnitarisable δ.rep → IsLSeg Δ' δ'.rep →
      IsUnitarisable δ'.rep → ∀ x y : ℝ, (Δ.nu x).Precedes (Δ'.nu y) → x + 1 ≤ y)
    (𝔫 : Multiset (Segment k))
    (h𝔫 : ∀ Δ ∈ 𝔫, ∃ (δ : IrrGL k) (Γ : Segment k) (t : ℝ), IsLSeg Γ δ.rep ∧
      IsUnitarisable δ.rep ∧ Δ = Γ.nu (t : ℂ)) : ∃ y : IrrGL k, IsL 𝔫 y.rep := by
  classical
  have h' : ∀ Δ ∈ 𝔫, ∃ (t : ℝ) (δ : IrrGL k) (Γ : Segment k), IsLSeg Γ δ.rep ∧
      IsUnitarisable δ.rep ∧ Δ = Γ.nu (t : ℂ) := fun Δ h =>
    let ⟨δ, Γ, t, h⟩ := h𝔫 Δ h
    ⟨t, δ, Γ, h⟩
  choose! t ht using h'
  let r : Segment k → Segment k → Prop := fun a b => t b ≤ t a
  haveI : IsTrans (Segment k) r := ⟨fun a b c h1 h2 => le_trans h2 h1⟩
  haveI : Std.Total r := ⟨fun a b => le_total _ _⟩
  obtain ⟨l, hl, hs⟩ : ∃ l : List (Segment k), (l : Multiset (Segment k)) = 𝔫 ∧ l.Pairwise r :=
    ⟨𝔫.toList.insertionSort r,
      (Multiset.coe_eq_coe.2 (List.perm_insertionSort r _)).trans (Multiset.coe_toList 𝔫),
      List.pairwise_insertionSort r _⟩
  have hm : ∀ i : Fin l.length, l.get i ∈ 𝔫 := fun i => by
    rw [← hl]; exact List.get_mem l i
  choose δ Γ hL hU hE using fun i : Fin l.length => ht _ (hm i)
  have hF : LFactors 𝔫 (fun i : Fin l.length => (δ i).nu (t (l.get i))) := by
    refine ⟨fun i => (Γ i).nu (t (l.get i)), ⟨?_, fun i j hij h => ?_⟩, fun i => ?_⟩
    · rw [← hl, ← funext hE]
      simp
    · have h1 : t (l.get j) ≤ t (l.get i) := List.pairwise_iff_get.1 hs i j hij
      have := hP _ _ _ _ (hL i) (hU i) (hL j) (hU j) _ _ h
      linarith
    · exact ((hL i).tw _ (isSmoothChar_absPow _)).of_equiv ((δ i).twEquiv _ _)
  obtain ⟨π, hπ⟩ := hS k 𝔫 _ _ _ rfl hF
  exact ⟨IrrGL.of π.ρ π.smooth π.irr, _, _, rfl, hF, hπ.of_equiv (IrrGL.equivOf _ _ _) (.refl _)⟩

end GlobalTheory.LocGL
