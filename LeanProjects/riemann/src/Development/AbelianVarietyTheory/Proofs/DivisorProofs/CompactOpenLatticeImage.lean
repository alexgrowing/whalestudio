import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDotProductRepresentationCompactCharacterLo
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.HeisUniqLoc

theorem eigen_unique : ∀ {F : Type} [Field F] [NumberField F] (v : Pl F) {κ G : Type} [Fintype κ] [AddCommGroup G]
    (ψ₀ : AddChar (Fv F v) ℂ), Continuous ψ₀ → ψ₀ ≠ 1 →
    ∀ (ℓ : G →+ (κ → Fv F v) × (κ → Fv F v)) (Γ : AddSubgroup G),
      IsOpen ((Γ.map ℓ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) : Set ((κ → Fv F v) × (κ → Fv F v))) →
      IsCompact ((Γ.map ℓ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) : Set ((κ → Fv F v) × (κ → Fv F v))) →
      (∀ w : (κ → Fv F v) × (κ → Fv F v), (∀ γ ∈ Γ, ψ₀ ((ℓ γ).1 ⬝ᵥ w.2 - w.1 ⬝ᵥ (ℓ γ).2) = 1) → w ∈ Γ.map ℓ) →
      ∀ (χ : G → ℂ) (φ φ' : (κ → Fv F v) → ℂ), φ ≠ 0 →
        (∀ γ ∈ Γ, schr ψ₀ (ℓ γ) φ = χ γ • φ) → (∀ γ ∈ Γ, schr ψ₀ (ℓ γ) φ' = χ γ • φ') → ∃ c : ℂ, φ' = c • φ := by
  intro F _ _ v κ G _ _ ψ₀ hc hne ℓ Γ hopen hcpt hdual χ φ φ' hφ hE hE'
  set Λ := Γ.map ℓ with hΛ
  have hψne : ∀ z, ψ₀ z ≠ 0 := fun z h => by
    have h0 := AddChar.map_zero_eq_one ψ₀
    rw [← add_neg_cancel z, AddChar.map_add_eq_mul, h, zero_mul] at h0
    exact zero_ne_one h0
  have hpt : ∀ (f : (κ → Fv F v) → ℂ), (∀ γ ∈ Γ, schr ψ₀ (ℓ γ) f = χ γ • f) →
      ∀ γ ∈ Γ, ∀ x, ψ₀ (x ⬝ᵥ (ℓ γ).2 + ⅟(2 : Fv F v) * ((ℓ γ).1 ⬝ᵥ (ℓ γ).2)) * f (x + (ℓ γ).1)
        = χ γ * f x := by
    intro f hf γ hγ x
    exact congrFun (hf γ hγ) x
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, φ x₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ (funext h)
  have horth0 : ∀ f : (κ → Fv F v) → ℂ, (∀ γ ∈ Γ, schr ψ₀ (ℓ γ) f = χ γ • f) → ∀ x, f x ≠ 0 →
      ∀ γ ∈ Γ, (ℓ γ).1 = 0 → ψ₀ (x ⬝ᵥ (ℓ γ).2) = χ γ := by
    intro f hf x hx γ hγ h1
    have e := hpt f hf γ hγ x
    rw [h1, zero_dotProduct, mul_zero, add_zero, add_zero] at e
    exact mul_right_cancel₀ hx e
  have horth : ∀ x, (φ x ≠ 0 ∨ φ' x ≠ 0) → ∀ y, ((0 : κ → Fv F v), y) ∈ Λ → ψ₀ ((x - x₀) ⬝ᵥ y) = 1 := by
    intro x hx y hy
    obtain ⟨γ, hγ, hℓ⟩ := AddSubgroup.mem_map.1 hy
    have h1γ : (ℓ γ).1 = 0 := by rw [hℓ]
    have h0 := horth0 φ hE x₀ hx₀ γ hγ h1γ
    have h1 : ψ₀ (x ⬝ᵥ (ℓ γ).2) = χ γ := by
      rcases hx with hx | hx
      · exact horth0 φ hE x hx γ hγ h1γ
      · exact horth0 φ' hE' x hx γ hγ h1γ
    rw [hℓ] at h0 h1
    rw [sub_dotProduct, AddChar.map_sub_eq_div, h0, h1, div_self]
    rw [← h0]
    exact hψne _
  have hmem : ∀ x, (φ x ≠ 0 ∨ φ' x ≠ 0) → ∃ u₂, (x - x₀, u₂) ∈ Λ := by
    intro x hx
    have ht := horth x hx
    have hwd : ∀ a ∈ Λ, ∀ b ∈ Λ, a.1 = b.1 → ψ₀ ((x - x₀) ⬝ᵥ a.2) = ψ₀ ((x - x₀) ⬝ᵥ b.2) := by
      intro a ha b hb hab
      have hd : ((0 : κ → Fv F v), a.2 - b.2) ∈ Λ := by
        have hs := Λ.sub_mem ha hb
        convert hs using 1
        ext <;> simp [hab]
      have e := ht _ hd
      rw [dotProduct_sub, AddChar.map_sub_eq_div, div_eq_one_iff_eq (hψne _)] at e
      exact e
    classical
    let L : AddSubgroup (κ → Fv F v) := Λ.map (AddMonoidHom.fst _ _)
    let L' : AddSubgroup (κ → Fv F v) := Λ.comap (AddMonoidHom.inl _ _)
    let c' : (κ → Fv F v) → ℂ := fun p =>
      if h : ∃ a ∈ Λ, a.1 = p then ψ₀ ((x - x₀) ⬝ᵥ (Classical.choose h).2) else 1
    have hc' : ∀ a ∈ Λ, c' a.1 = ψ₀ ((x - x₀) ⬝ᵥ a.2) := by
      intro a ha
      have h : ∃ b ∈ Λ, b.1 = a.1 := ⟨a, ha, rfl⟩
      simp only [c', dif_pos h]
      obtain ⟨hb, hb1⟩ := Classical.choose_spec h
      exact hwd _ hb _ ha hb1
    have hLc : IsCompact (L : Set (κ → Fv F v)) := by
      simp only [L, AddSubgroup.coe_map]
      exact hcpt.image continuous_fst
    have hinl : Continuous (fun p : κ → Fv F v => (p, (0 : κ → Fv F v))) := by fun_prop
    have hL'o : IsOpen (L' : Set (κ → Fv F v)) := by
      simp only [L', AddSubgroup.coe_comap]
      exact hopen.preimage hinl
    have hmul : ∀ y ∈ L, ∀ y' ∈ L, c' (y + y') = c' y * c' y' := by
      intro y hy y' hy'
      obtain ⟨a, ha, rfl⟩ := AddSubgroup.mem_map.1 hy
      obtain ⟨b, hb, rfl⟩ := AddSubgroup.mem_map.1 hy'
      have e := hc' (a + b) (Λ.add_mem ha hb)
      simp only [AddMonoidHom.coe_fst, Prod.fst_add, Prod.snd_add] at e ⊢
      rw [e, hc' a ha, hc' b hb, dotProduct_add, AddChar.map_add_eq_mul]
    have htriv : ∀ y ∈ L, y ∈ L' → c' y = 1 := by
      intro y _ hy'
      have hy'' : (y, (0 : κ → Fv F v)) ∈ Λ := hy'
      have e := hc' _ hy''
      rw [e, dotProduct_zero, AddChar.map_zero_eq_one]
    obtain ⟨u₂, hu₂⟩ :=
      GlobalTheory.CompactCharDual.exists_dotProduct_eq_local v ψ₀ hc hne L hLc L' hL'o c' hmul htriv
    refine ⟨u₂, hdual _ ?_⟩
    intro γ hγ
    have hlam : ℓ γ ∈ Λ := AddSubgroup.mem_map_of_mem ℓ hγ
    have h1 := hu₂ (ℓ γ).1 (AddSubgroup.mem_map_of_mem (AddMonoidHom.fst _ _) hlam)
    rw [hc' _ hlam] at h1
    show ψ₀ ((ℓ γ).1 ⬝ᵥ u₂ - (x - x₀) ⬝ᵥ (ℓ γ).2) = 1
    rw [AddChar.map_sub_eq_div, dotProduct_comm, ← h1, div_self (hψne _)]
  refine ⟨φ' x₀ / φ x₀, funext fun x => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hx : φ x ≠ 0 ∨ φ' x ≠ 0
  · obtain ⟨u₂, hu⟩ := hmem x hx
    obtain ⟨γ, hγ, hℓ⟩ := AddSubgroup.mem_map.1 hu
    have e1 := hpt φ hE γ hγ x₀
    have e2 := hpt φ' hE' γ hγ x₀
    simp only [hℓ] at e1 e2
    rw [show x₀ + (x - x₀) = x by abel] at e1 e2
    rw [div_mul_eq_mul_div, eq_div_iff hx₀]
    apply mul_left_cancel₀ (hψne (x₀ ⬝ᵥ u₂ + ⅟(2 : Fv F v) * ((x - x₀) ⬝ᵥ u₂)))
    linear_combination (φ x₀) * e2 - (φ' x₀) * e1
  · push_neg at hx
    rw [hx.1, hx.2, mul_zero]

end GlobalTheory.HeisUniqLoc
