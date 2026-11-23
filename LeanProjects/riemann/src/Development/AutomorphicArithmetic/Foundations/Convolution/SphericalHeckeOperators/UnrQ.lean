import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum
import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.Match
import GroundTheory.LocalFields.UnramifiedDefs

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

open ValuativeRel in
theorem UpperTheory.ConvolutionTheory.H.unrQ :
    ∀ (k E : Type) [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
      [Algebra k E] [ValuativeExtension k E] [FiniteDimensional k E] [IsGalois k E], PositivityTheory.Rg.Tf.Loc.IsUnramifiedLoc k E →
      qF E = qF k ^ Module.finrank k E ∧
      ∀ ϖ : kˣ, PositivityTheory.Rg.Tf.Loc.IsUniformiser (ϖ : k) → PositivityTheory.Rg.Tf.Loc.IsUniformiser (algebraMap k E (ϖ : k)) := by
  intro k E _ _ _ _ _ _ _ _ _ _ _ _ _ ⟨π, hπ1, hπ2⟩
  have hlt : ∀ a : k, valuation E (algebraMap k E a) < 1 ↔ valuation k a < 1 := fun a =>
    Valuation.HasExtension.val_map_lt_one_iff (valuation k) (valuation E) a
  have hπk : valuation k π < 1 := (hlt π).1 hπ1
  refine ⟨?_, fun ϖ ⟨h1, h2, h3⟩ => ⟨(hlt _).2 h1, (map_ne_zero _).2 h2, fun x hx => (hπ2 x hx).trans ?_⟩⟩
  · have hmem : ∀ {F : Type} [Field F] [ValuativeRel F] (x : 𝒪[F]),
        x ∈ IsLocalRing.maximalIdeal 𝒪[F] ↔ valuation F (x : F) < 1 := fun x =>
      Valuation.mem_maximalIdeal_iff _ _
    let p : 𝒪[k] := ⟨π, hπk.le⟩
    have hle : IsLocalRing.maximalIdeal 𝒪[E] ≤
        (IsLocalRing.maximalIdeal 𝒪[k]).map (algebraMap 𝒪[k] 𝒪[E]) := by
      intro x hx
      have hd : algebraMap 𝒪[k] 𝒪[E] p ∣ x :=
        (Valuation.integer.integers (valuation E)).le_iff_dvd.1 (hπ2 x ((hmem x).1 hx))
      obtain ⟨c, rfl⟩ := hd
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ((hmem p).2 hπk))
    rw [GroundTheory.LocalField.map_maximalIdeal] at hle
    have he : GroundTheory.LocalField.ramificationIndex k E = 1 := by
      have hpos := GroundTheory.LocalField.ramificationIndex_pos k E
      by_contra hne
      have h2 : 2 ≤ GroundTheory.LocalField.ramificationIndex k E := by omega
      have h3 := hle.trans (Ideal.pow_le_pow_right h2)
      have h4 := Ideal.pow_succ_lt_pow (GroundTheory.LocalField.maximalIdeal_ne_bot E) 1
      rw [pow_one] at h4
      exact not_le_of_gt h4 h3
    have hf := (GroundTheory.LocalField.isUnramified_iff_finrank_residueField k E).1 ⟨he⟩
    rw [← hf]
    exact Module.natCard_eq_pow_finrank (K := 𝓀[k]) (V := 𝓀[E])
  · exact (Valuation.HasExtension.val_map_le_iff (valuation k) (valuation E) _ _).2 (h3 π hπk)
