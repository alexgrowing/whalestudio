import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegelZeroFront
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BalancedEntriesBoundedSiegelReducedStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraceBoundedOfAevalMonicEqZeroStatement

open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RedTh

theorem finite_balanced_actions : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (n : ℕ),
    {ρ : 𝓞 E →+* Matrix (Fin n) (Fin n) ℤ | ∃ (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ), IsSiegel d u ∧
      (∀ i, 0 < d i) ∧ ∀ c, ((ρ c).map (Int.cast : ℤ → ℝ))ᵀ * gram d u = gram d u *
        (ρ (H.bar c)).map (Int.cast : ℤ → ℝ)}.Finite := by
  intro E _ _ _ H n
  classical
  set S := {ρ : 𝓞 E →+* Matrix (Fin n) (Fin n) ℤ | ∃ (d : Fin n → ℝ) (u : Matrix (Fin n) (Fin n) ℝ), IsSiegel d u ∧
      (∀ i, 0 < d i) ∧ ∀ c, ((ρ c).map (Int.cast : ℤ → ℝ))ᵀ * gram d u = gram d u *
        (ρ (H.bar c)).map (Int.cast : ℤ → ℝ)} with hSdef

  have hK : ∀ c : 𝓞 E, ∃ K : ℝ, ∀ ρ : 𝓞 E →+* Matrix (Fin n) (Fin n) ℤ,
      (((ρ (H.bar c) * ρ c).trace : ℤ) : ℝ) ≤ K := by
    intro c
    obtain ⟨p, hpm, hp⟩ := Algebra.IsIntegral.isIntegral (R := ℤ) (H.bar c * c)
    obtain ⟨K, hK⟩ := GlobalTheory.T.trace_bounded_of_aeval_monic_eq_zero p hpm n
    refine ⟨K, fun ρ => ?_⟩
    apply hK
    have h0 : Polynomial.aeval (ρ.toIntAlgHom (H.bar c * c)) p = 0 := by
      rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_def, hp, map_zero]
    simpa using h0
  choose K hK using hK

  have hC : ∀ c : 𝓞 E, ∃ N : ℤ, ∀ ρ ∈ S, ∀ i j, ρ c i j ∈ Set.Icc (-N) N := by
    intro c
    obtain ⟨C, hC⟩ := GlobalTheory.T.balanced_entries_bounded_siegelReduced n (K c)
    refine ⟨⌈C⌉, fun ρ hρ i j => ?_⟩
    obtain ⟨d, u, hs, hpos, hrel⟩ := hρ
    have h1 := hC (ρ c) (ρ (H.bar c)) d u hs hpos (hrel c) (hK c ρ) i j
    have h2 : ((|ρ c i j| : ℤ) : ℝ) ≤ ((⌈C⌉ : ℤ) : ℝ) := h1.trans (Int.le_ceil C)
    have h3 : |ρ c i j| ≤ ⌈C⌉ := by exact_mod_cast h2
    exact abs_le.mp h3
  choose N hN using hC
  let b := RingOfIntegers.basis E
  let F : (𝓞 E →+* Matrix (Fin n) (Fin n) ℤ) → (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → Fin n → Fin n → ℤ) :=
    fun ρ l => ρ (b l)
  let T : Set (Module.Free.ChooseBasisIndex ℤ (𝓞 E) → Fin n → Fin n → ℤ) :=
    Set.pi Set.univ fun l => Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Set.Icc (-N (b l)) (N (b l))
  have hT : T.Finite :=
    Set.Finite.pi fun l => Set.Finite.pi fun _ => Set.Finite.pi fun _ => Set.finite_Icc _ _
  refine Set.Finite.of_injOn (f := F) (t := T) ?_ ?_ hT
  · intro ρ hρ l _ i _ j _
    exact hN (b l) ρ hρ i j
  · intro ρ₁ _ ρ₂ _ h
    have hl : ∀ l, ρ₁ (b l) = ρ₂ (b l) := fun l => congrFun h l
    have hlin : ρ₁.toAddMonoidHom.toIntLinearMap = ρ₂.toAddMonoidHom.toIntLinearMap :=
      b.ext fun l => by simpa using hl l
    ext1 x
    simpa using LinearMap.congr_fun hlin x

end GlobalTheory.RedTh
