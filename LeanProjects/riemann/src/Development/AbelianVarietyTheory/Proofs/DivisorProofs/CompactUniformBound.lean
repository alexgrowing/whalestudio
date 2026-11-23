import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Definitions.Divisors.KerInfIntegrableOfMemRspan

namespace GlobalTheory.CompactUniformHeightBound

open Filter Topology

theorem height_one_le {E : Type} [Field E] [NumberField E] {a : ℕ}
    (y : GL (Fin a) (GlobalTheory.CuspRep.Cinf E)) : 1 ≤ GlobalTheory.CuspRep.height y := by
  unfold GlobalTheory.CuspRep.height
  exact le_add_of_le_of_nonneg (le_add_of_nonneg_right (norm_nonneg _)) (norm_nonneg _)

theorem compact_uniform_bound : (let d1 : {E : Type} → [inst : Field E] → [inst_1 : NumberField E] → [NumberField.IsTotallyComplex E] → {a : ℕ} → (GlobalTheory.CuspRep.GA E a → ℂ) → Prop := @(fun {E : Type} [Field E] [NumberField E] [NumberField.IsTotallyComplex E] {a : ℕ} (F : GlobalTheory.CuspRep.GA E a → ℂ) ↦ ∀ (g₀ : GlobalTheory.CuspRep.GA E a), ∃ (C : ℝ) (N : ℕ), (0 : ℝ) ≤ C ∧ ∀ᶠ (g : GlobalTheory.CuspRep.GA E a) in nhds g₀, ∀ (y : GL (Fin a) (GlobalTheory.CuspRep.Cinf E)), ‖F (g * (GlobalTheory.CuspRep.infGL E a : GL (Fin a) (GlobalTheory.CuspRep.Cinf E) → GlobalTheory.CuspRep.GA E a) y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ N); ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsTotallyComplex E] {a : ℕ} {F : GlobalTheory.CuspRep.GA E a → ℂ}, d1 F → ∀ {K : Set (GlobalTheory.CuspRep.GA E a)}, IsCompact K → ∃ (C : ℝ) (N : ℕ), (0 : ℝ) ≤ C ∧ ∀ g ∈ K, ∀ (y : GL (Fin a) (GlobalTheory.CuspRep.Cinf E)), ‖F (g * (GlobalTheory.CuspRep.infGL E a : GL (Fin a) (GlobalTheory.CuspRep.Cinf E) → GlobalTheory.CuspRep.GA E a) y)‖ ≤ C * GlobalTheory.CuspRep.height y ^ N) := by
  intro d1 E _ _ _ a F hF K hK
  have hb : ∀ g₀ : GlobalTheory.CuspRep.GA E a, ∃ (C : ℝ) (N : ℕ), (0 : ℝ) ≤ C ∧
      {g : GlobalTheory.CuspRep.GA E a | ∀ (y : GL (Fin a) (GlobalTheory.CuspRep.Cinf E)),
        ‖F (g * (GlobalTheory.CuspRep.infGL E a : GL (Fin a) (GlobalTheory.CuspRep.Cinf E) → GlobalTheory.CuspRep.GA E a) y)‖
          ≤ C * GlobalTheory.CuspRep.height y ^ N} ∈ 𝓝 g₀ := fun g₀ => hF g₀
  choose C N hC hU using hb
  obtain ⟨t, -, hKt⟩ := hK.elim_nhds_subcover _ (fun x _ => hU x)
  refine ⟨∑ x ∈ t, C x, t.sup N, Finset.sum_nonneg (fun x _ => hC x), ?_⟩
  intro g hg y
  obtain ⟨x, hx, hgx⟩ := Set.mem_iUnion₂.mp (hKt hg)
  have h1 := height_one_le y
  calc _ ≤ C x * GlobalTheory.CuspRep.height y ^ N x := hgx y
    _ ≤ (∑ i ∈ t, C i) * GlobalTheory.CuspRep.height y ^ t.sup N :=
      mul_le_mul (Finset.single_le_sum (fun i _ => hC i) hx)
        (pow_le_pow_right₀ h1 (Finset.le_sup hx))
        (pow_nonneg (zero_le_one.trans h1) _) (Finset.sum_nonneg fun i _ => hC i)

end GlobalTheory.CompactUniformHeightBound
