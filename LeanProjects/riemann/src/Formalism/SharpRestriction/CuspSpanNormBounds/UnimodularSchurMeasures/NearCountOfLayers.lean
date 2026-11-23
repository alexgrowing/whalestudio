import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.CnMeasurablePsi

noncomputable section

namespace Formalism.MainNotions.LeviCoordinates

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace ComplexOrder ENNReal
open Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData Formalism.MainNotions.BridgeLemma

def cn_isNear (X : CData) (εN : ℝ) (x : X.I.GA) (γ : X.I.GFset) : Prop :=
  (γ ≠ X.one' ∧ ∀ v, X.dist x γ v ≤ εN) ∧ X.φ (x⁻¹ * (γ : X.I.GA) * x) ≠ 0

def CSize.NearLayers {X : CData} (S : CSize X) (εN δ : ℝ) : Prop :=
  (∀ x ∈ S.I0, ∀ γ : X.I.GFset, γ ≠ X.one' → (∀ v, X.dist x γ v ≤ εN) → X.φ (x⁻¹ * (γ : X.I.GA) * x) = 0) ∧
    ∀ (J : ℕ) (c : Composition J), ∀ x ∈ S.str J c, S.tau J c x ∈ cn_Reg c.length ∧
      ∃ (e : Fin (Fintype.card (cn_Root c.length)) ≃ cn_Root c.length) (β : ℕ → Type) (π : ∀ i, X.I.GFset → β i),
        (∀ γ γ', cn_isNear X εN x γ → cn_isNear X εN x γ' → π 0 γ = π 0 γ') ∧
        (∀ γ γ', cn_isNear X εN x γ → cn_isNear X εN x γ' →
          π (Fintype.card (cn_Root c.length)) γ = π (Fintype.card (cn_Root c.length)) γ' → γ = γ') ∧
        ∀ (i : Fin (Fintype.card (cn_Root c.length))) (T : Finset X.I.GFset), (∀ γ ∈ T, cn_isNear X εN x γ) →
          (∀ y ∈ T, ∀ z ∈ T, π i y = π i z) → (∀ y ∈ T, ∀ z ∈ T, π (i + 1) y = π (i + 1) z → y = z) →
          ∃ laM : ℝ, cn_la (S.tau J c x) (e i) / 2 ≤ laM ∧
            (T.card : ℝ) ≤ (1 + 2 * (∏ _v : InfinitePlace X.I.F, 3 * δ) ^ (1 / (Fintype.card (InfinitePlace X.I.F) : ℝ)) / laM) ^
              (cn_dim c.blocksFun (X.I.n - 2 * J) (e i) * Fintype.card (InfinitePlace X.I.F))

theorem CSize.nearCount_of_layers {X : CData} (S : CSize X) {εN δ : ℝ} (hδ : 0 ≤ δ) (h : S.NearLayers εN δ) :
    S.NearCount εN δ := by
  refine ⟨h.1, fun J c x hx T hT => ?_⟩
  obtain ⟨hreg, e, β, π, h0, hr, hl⟩ := h.2 J c x hx
  set b : cn_Root c.length → ℝ := fun ρ =>
    (1 + 12 * δ / cn_la (S.tau J c x) ρ) ^ (cn_dim c.blocksFun (X.I.n - 2 * J) ρ * X.I.f) with hb
  have hb0 : ∀ ρ, 0 ≤ b ρ := fun ρ => by
    have := (cn_la_mem hreg ρ).1
    positivity
  set cc : ℕ → ℝ := fun i => if hi : i < Fintype.card (cn_Root c.length) then b (e ⟨i, hi⟩) else 1 with hcc
  have hcc0 : ∀ i, 0 ≤ cc i := fun i => by
    simp only [hcc]
    split_ifs
    · exact hb0 _
    · norm_num
  have key := Formalism.HermitianLatticeCounting.Final.S7.fibreCount X.I.GFset T (Fintype.card (cn_Root c.length)) β π cc hcc0 (fun y hy z hz => h0 y z (hT y hy) (hT z hz))
    (fun y hy z hz => hr y z (hT y hy) (hT z hz)) (fun i hi T' hT' ha hd => by
      obtain ⟨laM, hla, hc⟩ := hl ⟨i, hi⟩ T' (fun γ hγ => hT γ (hT' hγ)) ha hd
      have hpos := (cn_la_mem hreg (e ⟨i, hi⟩)).1
      have h1 := Formalism.HermitianLatticeCounting.Final.NearFarVolumeBounds.layerCount (InfinitePlace X.I.F) (cn_dim c.blocksFun (X.I.n - 2 * J) (e ⟨i, hi⟩)) δ
        (cn_la (S.tau J c x) (e ⟨i, hi⟩)) laM hδ hpos hla
      refine le_trans hc (le_trans h1 ?_)
      simp only [hcc, dif_pos hi, hb]
      refine pow_le_pow_right₀ ?_ (Nat.mul_le_mul_left _ (card_infinite_places_le_degree X.I))
      have : 0 ≤ 12 * δ / cn_la (S.tau J c x) (e ⟨i, hi⟩) := by positivity
      linarith)
  refine le_trans key (le_of_eq ?_)
  rw [Finset.prod_range]
  have : ∀ i : Fin (Fintype.card (cn_Root c.length)), cc i = b (e i) := fun i => by simp only [hcc, dif_pos i.2]
  rw [Finset.prod_congr rfl fun i _ => this i, Equiv.prod_comp e b]
  rfl

end Formalism.MainNotions.LeviCoordinates

end
