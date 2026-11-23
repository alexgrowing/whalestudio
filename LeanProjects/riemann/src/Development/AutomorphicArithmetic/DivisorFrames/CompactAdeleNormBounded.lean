import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorusUOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralBoundLtTop
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

open GroundTheory.Global GroundTheory.Global.IdeleGroup in
open scoped nonZeroDivisors in
private theorem finiteModule_le_of_mem {K : Type} [Field K] [NumberField K]
    (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x : IdeleGroup K)
    (hx : (x : AdeleRing (𝓞 K) K).2 ∈ idealFiniteAdeles L) :
    finiteModule x ≤ zetaWeight 1 (countFinsupp L) := by
  have h1 : finiteModule x = finiteModule (ofFinite (IdeleGroup.toFinite K x)) := rfl
  have h2 := (mem_idealFiniteAdeles_iff_ord L (IdeleGroup.toFinite K x)).1 hx
  set y := ofFinite (IdeleGroup.toFinite K x)
  have h3 := finiteModule_rpow_eq y 1
  rw [Real.rpow_one] at h3
  rw [h1, h3]
  set n : HeightOneSpectrum (𝓞 K) →₀ ℤ := ordFinsupp K y with hn
  have h4 : n = (n - countFinsupp L) + countFinsupp L := (sub_add_cancel _ _).symm
  have hk : ∀ v, 0 ≤ (n - countFinsupp L) v := fun v => by
    have : (n - countFinsupp L) v =
      ord v y - FractionalIdeal.count K v (L : FractionalIdeal (𝓞 K)⁰ K) := rfl
    rw [this]
    exact sub_nonneg.2 (h2 v)
  rw [h4, zetaWeight_add]
  refine mul_le_of_le_one_left (zetaWeight_nonneg _ _) ?_
  refine Finset.prod_le_one (fun v _ => (Real.rpow_pos_of_pos (absNorm_asIdeal_pos v) _).le) fun v _ => ?_
  refine Real.rpow_le_one_of_one_le_of_nonpos ?_ ?_
  · exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v).le
  · have : (0 : ℝ) ≤ (((n - countFinsupp L) v : ℤ) : ℝ) := by exact_mod_cast hk v
    linarith

open GroundTheory.Global GroundTheory.Global.IdeleGroup in
private theorem ideleModule_bdd {K : Type} [Field K] [NumberField K]
    {C : Set (AdeleRing (𝓞 K) K)} (hC : IsCompact C) :
    ∃ c : ℝ, ∀ x : IdeleGroup K, (x : AdeleRing (𝓞 K) K) ∈ C → (ideleModule K x : ℝ) ≤ c := by
  have hs : Continuous fun y : AdeleRing (𝓞 K) K => (y.2 : FiniteAdeleRing (𝓞 K) K) := continuous_snd
  obtain ⟨L, hL⟩ := exists_subset_idealFiniteAdeles (hC.image hs)
  have hf : Continuous fun y : AdeleRing (𝓞 K) K =>
      ∏ w : InfinitePlace K, ‖(y.1 : InfiniteAdeleRing K) w‖ ^ w.mult :=
    continuous_finsetProd _ fun w _ =>
      (continuous_norm.comp ((continuous_apply w).comp continuous_fst)).pow _
  obtain ⟨b, hb⟩ := (hC.image hf).bddAbove
  refine ⟨b * zetaWeight 1 (countFinsupp L), fun x hx => ?_⟩
  rw [ideleModule_apply]
  have h1 : infiniteModule x ≤ b := hb ⟨_, hx, rfl⟩
  have h2 := finiteModule_le_of_mem L x (hL ⟨_, hx, rfl⟩)
  exact mul_le_mul h1 h2 (finiteModule_pos x).le ((infiniteModule_pos x).le.trans h1)

theorem UpperTheory.compact_adele_norm_bounded :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (C : Set (AE F E)), IsCompact C → ∃ c : ℝ, ∀ u : (AE F E)ˣ, (u : AE F E) ∈ C → (absE F E u : ℝ) ≤ c := by
  intro F E _ _ _ _ _ C hC
  obtain ⟨c, hc⟩ := ideleModule_bdd (hC.image (GlobalTheory.TateConv.continuous_tens F E))
  refine ⟨c, fun u hu => ?_⟩
  rw [GlobalTheory.TateConv.absE_eq]
  exact hc _ ⟨_, hu, (GlobalTheory.TateConv.idl_val F E u).symm⟩
