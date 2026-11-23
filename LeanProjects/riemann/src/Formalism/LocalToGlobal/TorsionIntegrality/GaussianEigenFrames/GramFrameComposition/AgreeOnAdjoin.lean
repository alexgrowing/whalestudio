import Formalism.LocalToGlobal.TorsionIntegrality.GaussianEigenFrames.StatementE

noncomputable section
open NumberField

namespace Formalism.L2.Th1.GD

open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

namespace CharacterSeparation

theorem norm_p_lt (p : ℕ) [Fact p.Prime] : ‖(p : ℂ_[p])‖ < 1 := by
  have h := PadicComplex.norm_extends' p (p : ℚ_[p])
  have h2 : (((p : ℚ_[p]) : ℂ_[p])) = (p : ℂ_[p]) := map_natCast (algebraMap ℚ_[p] ℂ_[p]) p
  rw [h2] at h
  rw [h]
  exact Padic.norm_p_lt_one

theorem sqrt_norm_p_lt (p : ℕ) [Fact p.Prime] : ‖(p : ℂ_[p])‖ ^ (1 / 2 : ℝ) < 1 :=
  Real.rpow_lt_one (norm_nonneg _) (norm_p_lt p) (by norm_num)

theorem agree_on_adjoin {E L : Type*} [Field E] [CharZero E] [Field L] (ψ₁ ψ₂ : E →+* L) (δ : E)
    (h : ψ₁ δ = ψ₂ δ) : ∀ x ∈ IntermediateField.adjoin ℚ ({δ} : Set E), ψ₁ x = ψ₂ x := by
  intro x hx
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    rw [hx, h]
  | algebraMap q =>
    rw [eq_ratCast, map_ratCast, map_ratCast]
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | inv x _ hx => rw [map_inv₀, map_inv₀, hx]
  | mul x y _ _ hx hy => rw [map_mul, map_mul, hx, hy]

end CharacterSeparation

open CharacterSeparation

theorem SepPairs_of (hE : EmbSep) (hI : InertiaRam) : SepPairs := by
  intro p _ hp E _ _ _ c s δ hδ hc hs hcc hss hsc H emb hinj hemb hpart hKur τ ρ hρ
  obtain ⟨hn, hin, hun⟩ := hI p hp E s δ (emb τ) hδ hs hss (hKur τ)
  have hδint : IsIntegral ℤ δ := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (p : ℤ), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_add_C _ (by norm_num)
    · simp [hδ]
  let K : IntermediateField ℚ E := IntermediateField.adjoin ℚ ({δ} : Set E)
  have hδK : δ ∈ K := IntermediateField.mem_adjoin_simple_self ℚ δ
  have hδK' : IsIntegral ℤ (⟨δ, hδK⟩ : K) := by
    rw [← isIntegral_algebraMap_iff (B := E) (algebraMap K E).injective]
    exact hδint
  let π : 𝓞 K := ⟨⟨δ, hδK⟩, hδK'⟩
  have hπ : algebraMap K E (π : K) = δ := rfl
  obtain ⟨y, hy⟩ := hE p K E (emb τ) ((emb ρ).comp (c : E →+* E)) ((emb τ).comp (s : E →+* E))
    ⟨π, by rw [hπ, hn]; exact sqrt_norm_p_lt p, by rw [hπ]; exact hun⟩
    (fun x => agree_on_adjoin _ _ δ (by
      simp only [RingHom.comp_apply, RingHom.coe_coe, hc, hs, map_neg, hemb ρ τ]) _ x.2)
    (fun y => lt_of_le_of_lt (hin y) (sqrt_norm_p_lt p))
    (by
      intro heq
      apply hρ
      have h1 : ∀ z, emb ρ z = emb τ (s (c z)) := by
        intro z
        have := RingHom.congr_fun heq (c z)
        simpa only [RingHom.comp_apply, RingHom.coe_coe, hcc] using this
      obtain ⟨b, t⟩ := τ
      apply hinj
      ext z
      cases b with
      | false => exact (h1 z).trans (hpart t z).symm
      | true =>
        show emb ρ z = emb (false, t) z
        rw [h1 z, hpart t (s (c z)), hsc (s (c z)), hss, hcc])
  exact ⟨y, hy⟩

end Formalism.L2.Th1.GD
