import Mathlib
import Formalism.MeanHeightDescent.MuMaxMinkowski
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtGram
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.MuChar
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HNStep
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SatBasic
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.ExistsSmulMemOfFinrankEq
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.FinSup
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.RatioMax
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DegSupermod

open Module NumberField

noncomputable section

namespace Formalism.ExtensionFiltration

open Formalism.HN

section

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
  [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]

theorem majAt_self_re (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x : V) : (Formalism.HermitianLatticesTheory.majAt b X v x x).re = Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 := by
  unfold Formalism.HermitianLatticesTheory.majAt Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => by positivity)), Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re] <;> ring

theorem rkK_span_singleton (x : V) (hx : x ≠ 0) :
    rkK (K := K) (Submodule.span (𝓞 K) ({x} : Set V)) = 1 := by
  unfold rkK
  rw [Submodule.span_span_of_tower, finrank_span_singleton hx]

theorem muDef_line (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (x : V) (hx : x ≠ 0) (Λ : ℝ)
    (hn : ∀ v, Formalism.HermitianLatticesTheory.normAt b X v x ≤ Real.exp Λ) :
    -(2 * Λ) ≤ muDef b X (Submodule.span (𝓞 K) ({x} : Set V)) := by
  classical
  set L := Submodule.span (𝓞 K) ({x} : Set V) with hLdef
  have hFG : L.FG := Submodule.fg_span_singleton x
  have hne : L ≠ ⊥ := by
    rw [hLdef, Ne, Submodule.span_singleton_eq_bot]
    exact hx
  obtain ⟨-, -, hpos⟩ := Formalism.HN.place_lattice_structure K V ι b X hX L hFG
  have hmu := (Formalism.HN.size_maximal_slope K V ι b X hX L hFG hne).2.1
  have hli : LinearIndependent K ![x] := linearIndependent_unique_iff.mpr (by simpa using hx)
  have hr : Set.range ![x] = ({x} : Set V) := by
    rw [Set.range_unique]
    simp
  obtain ⟨hht, -⟩ := Formalism.HN.height_gram_determinant K V ι b X hX 1 ![x] hli
  rw [hr] at hht
  have hg : ∀ v, (gramPl b X v ![x]).det.re = Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 := by
    intro v
    rw [Matrix.det_unique]
    exact majAt_self_re b X v x
  simp only [hg] at hht
  have hrk : rkK (K := K) L = 1 := rkK_span_singleton x hx
  have hnPl : 0 < nPl K := Fintype.card_pos
  have hle : ht b X L ≤ (Real.exp Λ ^ 2) ^ nPl K := by
    rw [hht]
    calc ∏ v, Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 ≤ ∏ _v : InfinitePlace K, Real.exp Λ ^ 2 :=
          Finset.prod_le_prod (fun v _ => by positivity)
            (fun v _ => pow_le_pow_left₀ (by unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm; exact Real.sqrt_nonneg _)
              (hn v) 2)
      _ = (Real.exp Λ ^ 2) ^ nPl K := by rw [Finset.prod_const, Finset.card_univ]; rfl
  have hlog : Real.log (ht b X L) ≤ (nPl K : ℝ) * (2 * Λ) := by
    have h1 := Real.log_le_log hpos hle
    rwa [Real.log_pow, Real.log_pow, Real.log_exp] at h1
  rw [hmu]
  unfold size
  rw [hrk, Real.log_rpow hpos]
  have hn' : (0 : ℝ) < nPl K := by exact_mod_cast hnPl
  have key : 1 / (2 * (nPl K : ℝ) * ((1 : ℕ) : ℝ)) * Real.log (ht b X L) ≤ Λ := by
    rw [Nat.cast_one, mul_one, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

theorem muMin_line (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (x : V) (hx : x ≠ 0) (θ : ℝ)
    (hθ : θ ≤ slope (Formalism.HermitianLatticesTheory.realize b X) (Submodule.span (𝓞 K) ({x} : Set V))) :
    θ ≤ muMin (Formalism.HermitianLatticesTheory.realize b X) (Submodule.span (𝓞 K) ({x} : Set V)) := by
  classical
  have hFG : (Submodule.span (𝓞 K) ({x} : Set V)).FG := Submodule.fg_span_singleton x
  obtain ⟨hLat, hrkL, -⟩ := Formalism.HN.place_lattice_structure K V ι b X hX _ hFG
  have hne : Submodule.span (𝓞 K) ({x} : Set V) ≠ ⊥ := by
    rw [Ne, Submodule.span_singleton_eq_bot]
    exact hx
  obtain ⟨-, hmin, -, -, -⟩ := Formalism.HN.slope_characterization (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) _ hLat hne
  rw [hmin]
  intro N hN
  obtain ⟨-, hmono, -, hzero, hdeg0, -⟩ := Formalism.HN.saturation_basic_properties (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) _ hLat
  have hK : 0 < Module.finrank ℚ K := Module.finrank_pos
  rw [rkK_span_singleton x hx, mul_one] at hrkL
  by_cases hN0 : N = ⊥
  · subst hN0
    rw [hdeg0, (hzero ⊥ bot_le).mpr rfl]
    have hpos : (0 : ℝ) < (rk (Formalism.HermitianLatticesTheory.realize b X) (Submodule.span (𝓞 K) ({x} : Set V)) : ℝ) := by
      rw [hrkL]; exact_mod_cast hK
    have hθ' : θ ≤ deg (Formalism.HermitianLatticesTheory.realize b X) (Submodule.span (𝓞 K) ({x} : Set V)) /
        (rk (Formalism.HermitianLatticesTheory.realize b X) (Submodule.span (𝓞 K) ({x} : Set V)) : ℝ) := hθ
    rw [le_div_iff₀ hpos] at hθ'
    simpa using hθ'
  · have hNoeth : IsNoetherian (𝓞 K) (Submodule.span (𝓞 K) ({x} : Set V)) :=
      isNoetherian_of_fg_of_noetherian _ hFG
    have hNFG : N.FG := by
      have h1 := (IsNoetherian.noetherian (N.comap (Submodule.span (𝓞 K) ({x} : Set V)).subtype)).map
        (Submodule.span (𝓞 K) ({x} : Set V)).subtype
      rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hN] at h1
    obtain ⟨-, hrkN, -⟩ := Formalism.HN.place_lattice_structure K V ι b X hX N hNFG
    haveI : FiniteDimensional K V := Module.Finite.of_basis b
    have hkN : rkK (K := K) N = 1 := by
      have hle : Submodule.span K (N : Set V) ≤ Submodule.span K ({x} : Set V) := by
        rw [Submodule.span_le]
        intro y hy
        have hy' := hN hy
        rw [Submodule.mem_span_singleton] at hy'
        obtain ⟨a, rfl⟩ := hy'
        rw [SetLike.mem_coe, ← algebraMap_smul K a x]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
      have h1 : rkK (K := K) N ≤ 1 := by
        unfold rkK
        calc Module.finrank K (Submodule.span K (N : Set V))
            ≤ Module.finrank K (Submodule.span K ({x} : Set V)) := Submodule.finrank_mono hle
          _ = 1 := finrank_span_singleton hx
      have h2 : 0 < rkK (K := K) N := by
        unfold rkK
        apply Module.finrank_pos_iff_exists_ne_zero.mpr
        obtain ⟨y, hyN, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN0
        exact ⟨⟨y, Submodule.subset_span hyN⟩, fun h => hy0 (congrArg Subtype.val h)⟩
      omega
    rw [hkN, mul_one] at hrkN
    have hrkNL : rk (Formalism.HermitianLatticesTheory.realize b X) N = rk (Formalism.HermitianLatticesTheory.realize b X) (Submodule.span (𝓞 K) ({x} : Set V)) := by
      rw [hrkN, hrkL]
    rw [hrkNL, sub_self, mul_zero, sub_nonneg]
    exact (hmono N _ hN le_rfl).2 hrkNL

end

theorem span_min_slope : SpanMuMin := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX B Λ hB hB0 hs
  obtain ⟨s, hsB, hsn, hspan⟩ := hs
  set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ
  set θ : ℝ := (-(2 * Λ) + Real.log 2 - logDisc K / (Module.finrank ℚ K : ℝ)) / 2 with hθ
  obtain ⟨hlat, hrkB, -⟩ := place_lattice_structure K V ι b X hX B hB
  obtain ⟨hsat, hmin, hcont, -⟩ :=
    hnStep_of degree_supermodular slope_characterization maximal_slope_ratio finite_supremum_slopes real_saturation_property saturation_basic_properties
      (𝓞 K) V _ ρ B hlat θ
  set S := hnStep ρ B θ with hS
  have hmem : ∀ x ∈ s, x ∈ S := by
    intro x hx
    by_cases hx0 : x = 0
    · rw [hx0]; exact S.zero_mem
    · have hle : Submodule.span (𝓞 K) ({x} : Set V) ≤ B :=
        (Submodule.span_singleton_le_iff_mem x B).2 (hsB hx)
      have hne : Submodule.span (𝓞 K) ({x} : Set V) ≠ ⊥ := fun h =>
        hx0 ((Submodule.span_singleton_eq_bot).1 h)
      have hmu := muDef_line b X hX x hx0 Λ (hsn x hx)
      have hsl : θ ≤ slope ρ (Submodule.span (𝓞 K) ({x} : Set V)) := by
        unfold muDef at hmu
        rw [hθ]
        linarith
      exact hcont _ hle hne (muMin_line b X hX x hx0 θ hsl) (Submodule.mem_span_singleton_self x)
  have hSfg : S.FG := Submodule.FG.of_le hB hsat.1
  have hrkS := (place_lattice_structure K V ι b X hX S hSfg).2.1
  have hspanEq : Submodule.span K (S : Set V) = Submodule.span K (B : Set V) := by
    refine le_antisymm (Submodule.span_mono hsat.1) (Submodule.span_le.2 ?_)
    intro y hy
    exact Submodule.span_mono (fun x hx => hmem x hx) (hspan hy)
  have hrkK : rkK (K := K) S = rkK (K := K) B := by
    unfold rkK
    rw [hspanEq]
  have hBS : B = S :=
    (saturation_basic_properties (𝓞 K) V _ ρ B hlat).2.2.1 S B hsat hsat.1 le_rfl (by rw [hrkB, hrkS, hrkK])
  have hfin : θ ≤ muMin ρ B := by
    have := hmin (by rw [← hBS]; exact hB0)
    rwa [← hBS] at this
  unfold muMinDef
  rw [hθ] at hfin
  linarith

end Formalism.ExtensionFiltration
