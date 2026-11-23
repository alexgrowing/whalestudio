import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.PrimeLocalization

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsLocalRing

noncomputable section

variable {L : Type*} [Field L] [NumberField L]

theorem eventually_exists_map_eq (E : WeierstrassCurve L) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ∃ W : WeierstrassCurve (localizationAt L v),
        W.map (algebraMap (localizationAt L v) L) = E := by
  filter_upwards [eventually_mem_localizationAt E.a₁, eventually_mem_localizationAt E.a₂,
    eventually_mem_localizationAt E.a₃, eventually_mem_localizationAt E.a₄,
    eventually_mem_localizationAt E.a₆] with v h₁ h₂ h₃ h₄ h₆
  exact ⟨⟨⟨_, h₁⟩, ⟨_, h₂⟩, ⟨_, h₃⟩, ⟨_, h₄⟩, ⟨_, h₆⟩⟩, rfl⟩

theorem isElliptic_of_map_eq {v : HeightOneSpectrum (𝓞 L)} {E : WeierstrassCurve L} [E.IsElliptic]
    {W : WeierstrassCurve (localizationAt L v)} (h : W.map (algebraMap (localizationAt L v) L) = E)
    (hΔ : E.Δ⁻¹ ∈ localizationAt L v) : W.IsElliptic := by
  have hW : algebraMap (localizationAt L v) L W.Δ = E.Δ := by
    rw [← WeierstrassCurve.map_Δ, h]
  rw [WeierstrassCurve.isElliptic_iff]
  refine isUnit_iff_exists_inv.mpr ⟨⟨E.Δ⁻¹, hΔ⟩, Subtype.ext ?_⟩
  change algebraMap (localizationAt L v) L W.Δ * E.Δ⁻¹ = 1
  rw [hW]
  exact mul_inv_cancel₀ E.isUnit_Δ.ne_zero

theorem eventually_exists_model (E : WeierstrassCurve L) [E.IsElliptic] :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ∃ W : WeierstrassCurve (localizationAt L v),
        W.IsElliptic ∧ W.map (algebraMap (localizationAt L v) L) = E := by
  filter_upwards [eventually_exists_map_eq E, eventually_mem_localizationAt E.Δ⁻¹] with v ⟨W, h⟩ hΔ
  exact ⟨W, isElliptic_of_map_eq h hΔ, h⟩

theorem algebraMap_j_of_map_eq {v : HeightOneSpectrum (𝓞 L)} {E : WeierstrassCurve L}
    [E.IsElliptic] {W : WeierstrassCurve (localizationAt L v)} [W.IsElliptic]
    (h : W.map (algebraMap (localizationAt L v) L) = E) :
    algebraMap (localizationAt L v) L W.j = E.j := by
  subst h
  exact (W.map_j _).symm

theorem eventually_residue_j_ne {E E' : WeierstrassCurve L} [E.IsElliptic] [E'.IsElliptic]
    (hj : E.j ≠ E'.j) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ∀ (W W' : WeierstrassCurve (localizationAt L v)) [W.IsElliptic] [W'.IsElliptic],
        W.map (algebraMap (localizationAt L v) L) = E →
          W'.map (algebraMap (localizationAt L v) L) = E' →
            residue (localizationAt L v) W.j ≠ residue (localizationAt L v) W'.j := by
  filter_upwards [eventually_isUnit_localizationAt (sub_ne_zero.mpr hj)] with v ⟨hmem, hu⟩
    W W' _ _ h h'
  have hsub : W.j - W'.j = ⟨E.j - E'.j, hmem⟩ :=
    Subtype.ext (congrArg₂ (· - ·) (algebraMap_j_of_map_eq h) (algebraMap_j_of_map_eq h'))
  intro heq
  refine (residue_ne_zero_iff_isUnit (W.j - W'.j)).mpr (hsub ▸ hu) ?_
  rw [map_sub, heq, sub_self]

theorem j_map_residue {R : Type*} [CommRing R] [IsLocalRing R] (W : WeierstrassCurve R)
    [W.IsElliptic] : (W.map (residue R)).j = residue R W.j :=
  W.map_j _

theorem eventually_goodReduction {ι : Type*} [Finite ι] (E : ι → WeierstrassCurve L)
    [∀ i, (E i).IsElliptic] (hE : Pairwise fun i k => (E i).j ≠ (E k).j) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ∃ (W : ι → WeierstrassCurve (localizationAt L v)) (_ : ∀ i, (W i).IsElliptic),
        (∀ i, (W i).map (algebraMap (localizationAt L v) L) = E i) ∧
        (∀ i, algebraMap (localizationAt L v) L (W i).j = (E i).j) ∧
        Pairwise fun i k => residue (localizationAt L v) (W i).j ≠
          residue (localizationAt L v) (W k).j := by
  have hd : ∀ i k, ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite, i ≠ k →
      ∀ (W W' : WeierstrassCurve (localizationAt L v)) [W.IsElliptic] [W'.IsElliptic],
        W.map (algebraMap (localizationAt L v) L) = E i →
          W'.map (algebraMap (localizationAt L v) L) = E k →
            residue (localizationAt L v) W.j ≠ residue (localizationAt L v) W'.j := by
    intro i k
    by_cases hik : i = k
    · exact Filter.Eventually.of_forall fun _ h => (h hik).elim
    · exact (eventually_residue_j_ne (hE hik)).mono fun _ h _ => h
  filter_upwards [Filter.eventually_all.mpr fun i => eventually_exists_model (E i),
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr (hd i)] with v hm hdv
  choose W hWe hWm using hm
  exact ⟨W, hWe, hWm, fun i => algebraMap_j_of_map_eq (hWm i),
    fun i k hik => hdv i k hik (W i) (W k) (hWm i) (hWm k)⟩

end

end GroundTheory.Global
