import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorusUOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralBoundLtTop
import GroundTheory.AutomorphicForms.ReductionDirichlet
import GroundTheory.AutomorphicForms.ReductionIdele
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

open scoped nonZeroDivisors in
private theorem nat_den (K : Type) [Field K] [NumberField K] (L : FractionalIdeal (𝓞 K)⁰ K) :
    ∃ m : ℕ, 0 < m ∧ ∀ x ∈ L, IsIntegral ℤ ((m : K) * x) := by
  obtain ⟨a, ha, hL⟩ := L.isFractional
  have ha0 : a ≠ 0 := nonZeroDivisors.ne_zero ha
  refine ⟨Ideal.absNorm (Ideal.span {a}), Nat.pos_of_ne_zero ?_, fun x hx => ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact ha0
  · obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
    obtain ⟨y, hy⟩ := hL x hx
    have h1 : ((Ideal.absNorm (Ideal.span {a}) : ℕ) : K) * x = algebraMap (𝓞 K) K (b * y) := by
      rw [map_mul, hy, Algebra.smul_def, ← mul_assoc, ← map_mul, hb, map_natCast]
    rw [h1]
    exact RingOfIntegers.isIntegral_coe _

open GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic.Reduction in
private theorem adelic (K : Type) [Field K] [NumberField K] (D : Set (AdeleRing (𝓞 K) K)) (hD : IsCompact D) :
    ∃ (m : ℕ) (B : ℝ), 0 < m ∧ ∀ t : IdeleGroup K, ∃ (ξ : Kˣ) (ρ : ℝ), 0 < ρ ∧
      (ideleModule K t : ℝ) = ρ ^ Module.finrank ℚ K ∧
      ∀ x : K, (t : AdeleRing (𝓞 K) K) * algebraMap K (AdeleRing (𝓞 K) K) x ∈ D →
        IsIntegral ℤ ((m : K) * ((ξ : K) * x)) ∧ ∀ φ : K →+* ℂ, ρ * ‖φ ((ξ : K) * x)‖ ≤ B := by
  obtain ⟨S, hS, hSm⟩ := exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := K) one_pos 1
  set D' := (fun p : IdeleGroup K × AdeleRing (𝓞 K) K =>
    ((p.1⁻¹ : IdeleGroup K) : AdeleRing (𝓞 K) K) * p.2) '' (S ×ˢ D) with hD'def
  have hD' : IsCompact D' := (hS.prod hD).image
    ((Units.continuous_val.comp (continuous_inv.comp continuous_fst)).mul continuous_snd)
  obtain ⟨L, hL⟩ := exists_subset_idealFiniteAdeles (hD'.image continuous_snd)
  obtain ⟨m, hm, hmL⟩ := nat_den K L.1
  have hc : Continuous fun y : AdeleRing (𝓞 K) K => ∑ w : InfinitePlace K, ‖y.1 w‖ :=
    continuous_finsetSum _ fun w _ => continuous_norm.comp ((continuous_apply w).comp continuous_fst)
  obtain ⟨B, hB⟩ := hD'.bddAbove_image hc.continuousOn
  refine ⟨m, B, hm, fun t => ?_⟩
  have hn : Module.finrank ℚ K ≠ 0 := Module.finrank_pos.ne'
  have ht : 0 < (ideleModule K t : ℝ) := (ideleModule K t).2
  set ρ : ℝ := (ideleModule K t : ℝ) ^ ((Module.finrank ℚ K : ℝ)⁻¹) with hρdef
  have hρ : 0 < ρ := Real.rpow_pos_of_pos ht _
  have hρn : ρ ^ Module.finrank ℚ K = (ideleModule K t : ℝ) := Real.rpow_inv_natCast_pow ht.le hn
  set z : IdeleGroup K := posIdele ρ hρ with hz
  have hzt : ideleModule K z = ideleModule K t := Subtype.ext ((ideleModule_posIdele ρ hρ).trans hρn)
  have h1 : (ideleModule K (t * z⁻¹) : ℝ) = 1 := by
    rw [map_mul, map_inv, hzt, mul_inv_cancel]; rfl
  obtain ⟨c, hcS⟩ := hSm (t * z⁻¹) h1.ge h1.le
  refine ⟨c⁻¹, ρ, hρ, hρn.symm, fun x hx => ?_⟩
  have hmem : (z : AdeleRing (𝓞 K) K) * algebraMap K (AdeleRing (𝓞 K) K) (((c⁻¹ : Kˣ) : K) * x) ∈ D' := by
    refine ⟨(_, _), ⟨hcS, hx⟩, ?_⟩
    have e : (diagonal K c * (t * z⁻¹))⁻¹ * t = z * diagonal K c⁻¹ := by
      rw [map_inv, mul_inv, mul_inv, inv_inv, mul_assoc, mul_right_comm, inv_mul_cancel, one_mul, mul_comm]
    show (((diagonal K c * (t * z⁻¹))⁻¹ : IdeleGroup K) : AdeleRing (𝓞 K) K) * (_ * _) = _
    rw [← mul_assoc, ← Units.val_mul, e, Units.val_mul, coe_diagonal, map_mul, mul_assoc]
  generalize ((c⁻¹ : Kˣ) : K) * x = y at hmem
  constructor
  · apply hmL
    rw [← algebraMap_mem_idealFiniteAdeles_iff]
    have h2 := hL ⟨_, hmem, rfl⟩
    have h3 : ((z : AdeleRing (𝓞 K) K) * algebraMap K (AdeleRing (𝓞 K) K) y).2 =
        algebraMap K (FiniteAdeleRing (𝓞 K) K) y := by
      ext v
      rw [adele_snd_mul_apply, hz, posIdele_finite, one_mul]
      rfl
    rw [← h3]
    exact h2
  · intro φ
    have h2 := hB ⟨_, hmem, rfl⟩
    refine le_trans ?_ ((Finset.single_le_sum (f := fun w : InfinitePlace K =>
      ‖((z : AdeleRing (𝓞 K) K) * algebraMap K (AdeleRing (𝓞 K) K) y).1 w‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ (InfinitePlace.mk φ))).trans h2)
    rw [adele_fst_mul_apply, norm_mul, hz, norm_posIdele_infinite]
    refine le_of_eq (congrArg _ ?_)
    rw [← InfinitePlace.apply]
    exact (NumberField.InfinitePlace.Completion.norm_coe (InfinitePlace.mk φ) (WithAbs.toAbs _ y)).symm

theorem UpperTheory.compact_integral_vector_height :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (d : ℕ) (C : Set (Fin d → AE F E)), IsCompact C → ∃ (m : ℕ) (c : ℝ), 0 < m ∧
        ∀ (w : Fin d → E) (t : (AE F E)ˣ), t.1 • incV F w ∈ C → ∃ ξ : Eˣ, (∀ i, IsIntegral ℤ ((m : E) * ((ξ : E) * w i))) ∧
          (absE F E t : ℝ) * (∑ i, ∑ φ : E →+* ℂ, ‖φ ((ξ : E) * w i)‖) ^ Module.finrank ℚ E ≤ c := by
  intro F E _ _ _ _ _ d C hC
  have hD : IsCompact (⋃ i : Fin d, (fun y : Fin d → AE F E => GlobalTheory.TateConv.tens F E (y i)) '' C) :=
    isCompact_iUnion fun i => hC.image ((GlobalTheory.TateConv.continuous_tens F E).comp (continuous_apply i))
  obtain ⟨m, B, hm, h⟩ := adelic E _ hD
  refine ⟨m, (∑ _i : Fin d, ∑ _φ : E →+* ℂ, B) ^ Module.finrank ℚ E, hm, fun w t ht => ?_⟩
  obtain ⟨ξ, ρ, hρ, hmod, hx⟩ := h (GlobalTheory.TateConv.idl F E t)
  have hw := fun i => hx (w i) (Set.mem_iUnion.2 ⟨i, _, ht, by
    have e : GlobalTheory.TateConv.tens F E (incV F w i) = algebraMap E (AdeleRing (𝓞 E) E) (w i) := by
      refine (GroundTheory.Global.AdeleBaseChange.adeleTensorAlgEquivLeft_tmul (K := F) 1 (w i)).trans ?_
      rw [map_one, mul_one]
    show GlobalTheory.TateConv.tens F E (t.1 * incV F w i) = _
    rw [map_mul, e, GlobalTheory.TateConv.idl_val]⟩)
  refine ⟨ξ, fun i => (hw i).1, ?_⟩
  rw [GlobalTheory.TateConv.absE_eq, hmod, ← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ _
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun φ _ => (hw i).2 φ
