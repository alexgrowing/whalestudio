import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.JordanRankOneLine

open NumberField Module
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

open Formalism.HermitianLattices.Ext.L3 GluedLatticeMass OrbitSumPf
open Formalism.L2.SG.Pf.Cnt (cMass)

namespace GluedLatticeMass

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V1 : Type} [AddCommGroup V1] [Module K V1] [FiniteDimensional K V1] [Module (𝓞 K) V1]
  [IsScalarTower (𝓞 K) K V1]

theorem sum_reps_eq {h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K} {z : V1} {s s' : Finset (Submodule (𝓞 K) V1)}
    (hs : IsHzReps h1 z s) (hs' : IsHzReps h1 z s') :
    ∑ M ∈ s, ((Nat.card (stabZ h1 z M) : ℕ) : ℝ)⁻¹ = ∑ M ∈ s', ((Nat.card (stabZ h1 z M) : ℕ) : ℝ)⁻¹ := by
  have ex : ∀ {A B : Finset (Submodule (𝓞 K) V1)}, IsHzReps h1 z A → IsHzReps h1 z B →
      ∀ M ∈ A, ∃ M' ∈ B, ∃ σ ∈ hz h1 z, Formalism.HermitianLatticesTheory.gmap σ M' = M := by
    intro A B hA hB M hM
    obtain ⟨M', ⟨hM', σ, hσ, e⟩, -⟩ := hB.2 M (hA.1 M hM)
    exact ⟨M', hM', σ, hσ, e⟩
  choose i hi σi hσi ei using ex hs hs'
  choose j hj σj hσj ej using ex hs' hs
  refine Finset.sum_bij' i j hi hj ?_ ?_ ?_
  · intro M hM
    have hu := hs.2 (i M hM) (hs'.1 _ (hi M hM))
    refine hu.unique ⟨hj _ (hi M hM), σj _ (hi M hM), hσj _ _, ej _ _⟩
      ⟨hM, (σi M hM)⁻¹, inv_mem_hz (hσi M hM),
        (congrArg (Formalism.HermitianLatticesTheory.gmap (σi M hM)⁻¹) (ei M hM)).symm.trans (gmap_inv_gmap' _ _)⟩
  · intro M hM
    have hu := hs'.2 (j M hM) (hs.1 _ (hj M hM))
    refine hu.unique ⟨hi _ (hj M hM), σi _ (hj M hM), hσi _ _, ei _ _⟩
      ⟨hM, (σj M hM)⁻¹, inv_mem_hz (hσj M hM),
        (congrArg (Formalism.HermitianLatticesTheory.gmap (σj M hM)⁻¹) (ej M hM)).symm.trans (gmap_inv_gmap' _ _)⟩
  · intro M hM
    rw [← card_stabZ_conj (hσi M hM) (i M hM), ei M hM]

theorem alphaStd_ratio (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {k : ℕ} (hk : 1 ≤ k) :
    alphaStd K 𝔭 k / alphaStd K 𝔭 (k - 1) = 1 - etaF K F 𝔭 ^ k * (Ideal.absNorm 𝔭 : ℝ) ^ (-(k : ℤ)) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hpos := alphaStd_pos hK hF h𝔭 j
  rw [Nat.add_sub_cancel]
  unfold alphaStd at hpos ⊢
  rw [Finset.prod_Icc_succ_top (by omega), mul_div_cancel_left₀ _ hpos.ne']

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem glued_lattice_mass_formula {h1 : V1 →ₗ⋆[K] V1 →ₗ[K] K} {z : V1} {t : ℕ} (hH : GlueHyp K F h1 z t)
    (hk : 1 ≤ finrank K (wPerp h1 z)) (hne : ∃ M, IsGlueLat h1 z M) {s : Finset (Submodule (𝓞 K) V1)}
    (hs : IsHzReps h1 z s) :
    ∑ M ∈ s, ((Nat.card (stabZ h1 z M) : ℕ) : ℝ)⁻¹ =
      cMass K F (finrank K (wPerp h1 z)) * (t : ℝ) ^ (finrank K (wPerp h1 z) * finrank ℚ F) *
        ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
          (if ((t : ℕ) : 𝓞 F) ∈ 𝔭.1 then
            1 - etaF K F 𝔭.1 ^ finrank K (wPerp h1 z) *
              (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(finrank K (wPerp h1 z) : ℤ)) else 1) := by
  have hH' := hH
  obtain ⟨hK, hF, hsym, hzz, ht, hd⟩ := hH'
  have hz0 : h1 z z ≠ 0 := by
    rw [hzz, neg_ne_zero]
    exact_mod_cast ht.ne'
  have hz : z ≠ 0 := z_ne_zero hz0
  set k := finrank K (wPerp h1 z) with hkdef
  have hC : IsCompl (Submodule.span K {z}) (Formalism.L2.SG.Pf.Cnt.orthK h1 (Submodule.span K {z})) := by
    rw [orthK_span]
    exact isCompl_span hz0
  have hP : Formalism.L2.SG.Pf.Cnt.PosDefOn h1 (Formalism.L2.SG.Pf.Cnt.orthK h1 (Submodule.span K {z})) := by
    rw [orthK_span]
    intro x hx hx0 φ
    exact hd ⟨x, hx⟩ (fun h => hx0 (congrArg Subtype.val h)) φ
  have hLat : Formalism.L2.SG.Pf.Cnt.IsLatIn (Submodule.span K {z}) (Submodule.span (𝓞 K) {z}) :=
    ⟨Submodule.fg_span_singleton z, Submodule.span_span_of_tower (𝓞 K) K {z}⟩
  have hInt : Formalism.HermitianLatticesTheory.IsIntegralLat h1 (Submodule.span (𝓞 K) {z}) := by
    intro x hx y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [Formalism.HermitianLatticesTheory.locDual_h_smul_left, Formalism.HermitianLatticesTheory.locDual_h_smul_right, hzz]
    obtain ⟨c, hc⟩ := Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range (K := K) a
    rw [← hc]
    refine Formalism.HermitianLatticesTheory.locDual_one_mul (Formalism.HermitianLatticesTheory.locDual_alg_mem c)
      (Formalism.HermitianLatticesTheory.locDual_one_mul (Formalism.HermitianLatticesTheory.locDual_alg_mem b) ?_)
    rw [Submodule.mem_one]
    exact ⟨-((t : ℕ) : 𝓞 K), by simp⟩
  have hGS : (Formalism.L2.SG.Pf.Cnt.GlueSet h1 (Submodule.span K {z}) (Submodule.span (𝓞 K) {z})).Nonempty := by
    obtain ⟨M, hM⟩ := hne
    exact ⟨M, (glueSet_iff hz0 M).2 hM⟩
  have hMC : MassConst K F (finrank K (Formalism.L2.SG.Pf.Cnt.orthK h1 (Submodule.span K {z}))) (cMass K F k) := by
    rw [orthK_span]
    exact massConst_cMass hK hF k hk
  obtain ⟨s', hs'1, hs'2, -, hsum⟩ := Formalism.L2.SG.Pf.Cnt.gluing_mass_holds K F V1 hK hF h1 hsym (nondeg hH)
    _ hC hP _ hLat hInt hGS (cMass K F k) hMC
  have hs' : IsHzReps h1 z s' := by
    refine ⟨fun M hM => (glueSet_iff hz0 M).1 (hs'1 M hM), fun M hM => ?_⟩
    obtain ⟨Λ₁, ⟨h1s, g, hg, e⟩, hu⟩ := hs'2 M ((glueSet_iff hz0 M).2 hM)
    exact ⟨Λ₁, ⟨h1s, g, (isomFix_iff h1 z g).1 hg, e⟩,
      fun Λ₂ ⟨h2s, g2, hg2, e2⟩ => hu Λ₂ ⟨h2s, g2, (isomFix_iff h1 z g2).2 hg2, e2⟩⟩
  rw [sum_reps_eq hs hs']
  simp only [stabFix_eq] at hsum
  rw [hsum, orthK_span]

  have hJ : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
      Formalism.L2.SG.Pf.Cnt.vJ h1 (Submodule.span K {z}) (Submodule.span (𝓞 K) {z}) 𝔭.1 = vT F t 𝔭.1 ∧
      Formalism.L2.SG.Pf.Cnt.cJ h1 (Submodule.span K {z}) (Submodule.span (𝓞 K) {z}) 𝔭.1 =
        if ((t : ℕ) : 𝓞 F) ∈ 𝔭.1 then 1 else 0 := by
    intro 𝔭
    have h1r : finrank K (Submodule.span K {z}) = 1 := finrank_span_singleton hz
    obtain ⟨e1, e2⟩ := Formalism.L2.SG.Pf.G9.vJ_cJ_eq Formalism.L2.SG.Pf.Cnt.jordan_invariants_holds hK hF hsym hLat 𝔭.2
      (jordan_rank_one_line hzz ht hz 𝔭.1)
    have hv : vF 𝔭.1 (-((t : ℕ) : 𝓞 F)) = vT F t 𝔭.1 := by rw [vF_neg, vF_eq_vT 𝔭.2 ht]
    refine ⟨?_, ?_⟩
    · rw [e1]
      unfold Formalism.L2.SG.Pf.Cnt.vJof
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, h1r, one_smul, hv]
    · rw [e2]
      unfold Formalism.L2.SG.Pf.Cnt.cJof
      have ht0 : ((t : ℕ) : 𝓞 F) ≠ 0 := by exact_mod_cast ht.ne'
      have hiff : vF 𝔭.1 (-((t : ℕ) : 𝓞 F)) ≠ 0 ↔ ((t : ℕ) : 𝓞 F) ∈ 𝔭.1 := by
        rw [vF_neg, ← Nat.one_le_iff_ne_zero, ← Formalism.L2.SG.Pf.G1.mem_pow_iff 𝔭.2 ht0 1, pow_one]
      by_cases h : ((t : ℕ) : 𝓞 F) ∈ 𝔭.1
      · rw [if_pos h, Finset.filter_true_of_mem (fun i _ => hiff.2 h), Finset.card_univ,
          Fintype.card_fin, h1r]
      · rw [if_neg h, Finset.filter_false_of_mem (fun i _ => fun hh => h (hiff.1 hh)),
          Finset.card_empty]
  have hnM : Formalism.L2.SG.Pf.Cnt.nM F h1 (Submodule.span K {z}) (Submodule.span (𝓞 K) {z}) =
      (t : ℝ) ^ finrank ℚ F := by
    unfold Formalism.L2.SG.Pf.Cnt.nM
    have e := tprod_supT (F := F) ht (fun P => (Ideal.absNorm P : ℝ) ^ vT F t P)
    beta_reduce at e
    rw [← prod_absNorm_pow ht, ← e]
    refine tprod_congr fun 𝔭 => ?_
    rw [(hJ 𝔭).1]
    by_cases h : ((t : ℕ) : 𝓞 F) ∈ 𝔭.1
    · rw [if_pos h]
    · rw [if_neg h, ← vF_eq_vT 𝔭.2 ht, Formalism.L2.SG.Pf.G1.vF_of_notMem 𝔭.2 h, pow_zero]
  have hratio : (∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, alphaStd K 𝔭.1 k /
      alphaStd K 𝔭.1 (k - Formalism.L2.SG.Pf.Cnt.cJ h1 (Submodule.span K {z}) (Submodule.span (𝓞 K) {z}) 𝔭.1)) =
      ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, (if ((t : ℕ) : 𝓞 F) ∈ 𝔭.1 then
        1 - etaF K F 𝔭.1 ^ k * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(k : ℤ)) else 1) := by
    refine tprod_congr fun 𝔭 => ?_
    rw [(hJ 𝔭).2]
    by_cases h : ((t : ℕ) : 𝓞 F) ∈ 𝔭.1
    · rw [if_pos h, if_pos h, alphaStd_ratio hK hF 𝔭.2 hk]
    · rw [if_neg h, if_neg h, Nat.sub_zero, div_self (alphaStd_pos hK hF 𝔭.2 k).ne']
  rw [hnM, hratio, ← pow_mul, mul_comm (finrank ℚ F) k]

end GluedLatticeMass

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
