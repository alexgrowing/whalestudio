import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.FamilySeparationBoundOfNorms

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S
open scoped nonZeroDivisors NumberField

theorem szf_finrankE (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.der.finrank_E]
  simp only [Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
  omega

theorem szf_finrankF (D : D7) : Module.finrank ℚ D.host.F = D.R.f := by
  rw [D.host.der.finrank_F]
  simp only [Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]

theorem szf_normG (D : D7) : SzfNormG D := by
  unfold SzfNormG
  rw [FractionalIdeal.absNorm_span_singleton]
  have hE := szf_finrankE D
  have hg : Formalism.MainNotions.S.gE D = algebraMap ℚ D.host.E ((D.host.g 0 * D.host.g 1 : ℕ) : ℚ) := by
    simp [Formalism.MainNotions.S.gE]
  rw [hg, Algebra.norm_algebraMap, hE]
  simp only [Formalism.MainNotions.S.gg]
  push_cast
  rw [abs_of_nonneg (by positivity), ← pow_mul, mul_comm D.R.f 2]

theorem szf_finrankFE (D : D7) : Module.finrank D.host.F D.host.E = 2 := by
  have h1 := D.host.der.finrank_E
  have h2 := D.host.der.finrank_F
  have h3 : Module.finrank ℚ D.host.F * Module.finrank D.host.F D.host.E = Module.finrank ℚ D.host.E :=
    Module.finrank_mul_finrank ℚ D.host.F D.host.E
  have hpos : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
  rw [h1, h2] at h3
  rw [h1] at hpos
  have h4 : 2 * D.R.ord * Module.finrank D.host.F D.host.E = 2 * D.R.ord * 2 := by rw [h3]; ring
  exact Nat.eq_of_mul_eq_mul_left (by omega) h4

theorem szf_rd_pow (D : D7) : (D.host.rdE ^ D.R.f) ^ 2 = |(NumberField.discr D.host.E : ℝ)| := by
  have hE := szf_finrankE D
  have hpos : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
  have hf : 0 < D.R.f := by omega
  have hx0 : (0 : ℝ) ≤ |(NumberField.discr D.host.E : ℝ)| := abs_nonneg _
  unfold Formalism.BasicNotions.Host.rdE
  rw [hE, ← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
  have hc : (1 : ℝ) / ((2 * D.R.f : ℕ) : ℝ) * ((D.R.f * 2 : ℕ) : ℝ) = 1 := by
    rw [mul_comm D.R.f 2]
    exact one_div_mul_cancel (Nat.cast_ne_zero.mpr (by omega))
  rw [hc, Real.rpow_one]

theorem szf_normDD (D : D7) (hd : NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2) : SzfNormDD D := by
  unfold SzfNormDD
  rw [szf_rd_pow D, hd]
  have hFE := szf_finrankFE D
  have gen : ∀ I : Ideal (𝓞 D.host.F), Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) I) =
      Ideal.absNorm I ^ Module.finrank (𝓞 D.host.F) (𝓞 D.host.E) := by
    intro I
    rw [← Ideal.absNorm_relNorm (𝓞 D.host.F), Ideal.relNorm_algebraMap, map_pow]
  have n2 : ∀ (K : Type) [Field K] [NumberField K],
      (Algebra.norm ℤ (2 : 𝓞 K)).natAbs = 2 ^ Module.finrank ℚ K := by
    intro K _ _
    rw [show (2 : 𝓞 K) = algebraMap ℤ (𝓞 K) 2 from (map_ofNat _ 2).symm, Algebra.norm_algebraMap,
      NumberField.RingOfIntegers.rank, Int.natAbs_pow]
    rfl
  have hR : Module.finrank (𝓞 D.host.F) (𝓞 D.host.E) = 2 := by
    have h2 := gen (Ideal.span {(2 : 𝓞 D.host.F)})
    rw [Ideal.map_span, Set.image_singleton, map_ofNat, Ideal.absNorm_span_singleton,
      Ideal.absNorm_span_singleton, n2, n2, szf_finrankE D, szf_finrankF D, ← pow_mul] at h2
    have h3 := Nat.pow_right_injective (le_refl 2) h2
    have hpos : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    rw [szf_finrankE D] at hpos
    have h4 : D.R.f * Module.finrank (𝓞 D.host.F) (𝓞 D.host.E) = D.R.f * 2 := by
      rw [← h3]; ring
    exact Nat.eq_of_mul_eq_mul_left (by omega) h4
  have key : Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
      (differentIdeal ℤ (𝓞 D.host.F))) = Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.F)) ^ 2 := by
    rw [gen, hR]
  have hc : FractionalIdeal.absNorm (Formalism.MainNotions.S.ddE D) =
      (Ideal.absNorm (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
        (differentIdeal ℤ (𝓞 D.host.F))) : ℚ) := by
    first
    | exact FractionalIdeal.coeIdeal_absNorm _
    | exact FractionalIdeal.absNorm_coeIdeal _
    | exact FractionalIdeal.coe_absNorm _
  have hd2 : Ideal.absNorm (differentIdeal ℤ (𝓞 D.host.F)) = (NumberField.discr D.host.F).natAbs := by
    exact NumberField.absNorm_differentIdeal D.host.F (𝓞 D.host.F)
  rw [hc, key, hd2]
  push_cast
  first
  | simp [abs_pow, Nat.cast_natAbs]
  | rw [Nat.cast_natAbs, Int.cast_abs, abs_pow]

theorem separation_bound (CA c5 C4 C0 cT : ℝ) (hCA : 1 ≤ CA) (hcT : 0 < cT) :
    ∃ K0 Cl0 : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu CT : ℝ),
      K0 ≤ D.R.k → Cl0 ≤ Cl → LocalBesselAndTopKernel.MassRatioTheoremTwo D large₂ C0 C' Cl Cg cb Cu cT CT C4 c5 CA := by
  obtain ⟨K0, Cl0, h⟩ := separation_bound_of_norms CA c5 C4 C0 cT hCA hcT
  refine ⟨K0, Cl0, fun D large₂ C' Cl Cg cb Cu CT hK hCl => ?_⟩
  intro hh
  have hd : NumberField.discr D.host.E = NumberField.discr D.host.F ^ 2 := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hd, -⟩ := hh.1
    exact hd
  exact h D large₂ C' Cl Cg cb Cu CT (szf_normDD D hd) (szf_normG D) hK hCl hh

theorem family_separation_bound (CA c5 C4 C0 cT : ℝ) (hCA : 1 ≤ CA) (hcT : 0 < cT) :
    ∃ Cl0 : ℝ, ∀ {eps : ℝ} (Fm : FamP eps) (Cg cb Cu CT : ℝ), Cl0 ≤ sCl Fm →
      LocalBesselAndTopKernel.FamilyBesselBoundFirstPart Fm C0 Cg cb Cu cT CT → LocalBesselAndTopKernel.SchurOrthogonalityRealPlace Fm C0 Cg cb Cu cT CT C4 →
      LocalBesselAndTopKernel.FamilyLocalBesselBoundWithCharacter Fm C0 Cg cb Cu cT CT c5 CA := by
  obtain ⟨K0, Cl0, h⟩ := separation_bound CA c5 C4 C0 cT hCA hcT
  refine ⟨max Cl0 (max 1 K0), fun {eps} Fm Cg cb Cu CT hCl hA hE => ?_⟩
  simp only [LocalBesselAndTopKernel.FamilyLocalBesselBoundWithCharacter, LocalBesselAndTopKernel.FamilyBesselBoundFirstPart, LocalBesselAndTopKernel.SchurOrthogonalityRealPlace, LocalBesselAndTopKernel.UnderF, OwnEv] at hA hE ⊢
  obtain ⟨xa, hxa⟩ := hA
  obtain ⟨xe, hxe⟩ := hE
  refine ⟨max xa xe, fun x hx i hh => ?_⟩
  have hCl0 : Cl0 ≤ sCl Fm := le_trans (le_max_left _ _) hCl
  have h1 : (1 : ℝ) ≤ sCl Fm := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCl
  have hK0 : K0 ≤ sCl Fm := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hCl
  have hK : K0 ≤ ((Fm.D x i).R.k : ℝ) := by
    obtain ⟨-, hS, -⟩ := hh
    obtain ⟨-, -, h3, h4, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hClm, -⟩ := hS
    have hk4 : ((Fm.D x i).R.m : ℝ) ^ 4 ≤ ((Fm.D x i).R.k : ℝ) := by exact_mod_cast h3.trans h4
    have hm1 : (1 : ℝ) ≤ (Fm.D x i).R.m := le_trans h1 hClm
    have hm4 : ((Fm.D x i).R.m : ℝ) ≤ ((Fm.D x i).R.m : ℝ) ^ 4 := le_self_pow₀ hm1 (by norm_num)
    linarith
  exact h (Fm.D x i) (Fm.L x i) (sC' Fm) (sCl Fm) Cg cb Cu CT hK hCl0 hh
    (hxa x (le_trans (le_max_left _ _) hx) i hh) (hxe x (le_trans (le_max_right _ _) hx) i hh)

end Formalism.MainNotions.BridgeLemma

end
