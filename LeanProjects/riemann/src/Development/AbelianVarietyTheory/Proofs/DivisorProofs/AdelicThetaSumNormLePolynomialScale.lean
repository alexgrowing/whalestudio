import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
namespace GlobalTheory.LatScaleSum

open mixedEmbedding

theorem evI_algebraMap (F : Type) [Field F] [NumberField F] (x : F) :
    evI F (algebraMap F (AF F) x) = mixedEmbedding F x := by
  unfold evI
  simp [InfiniteAdeleRing.ringEquiv_mixedSpace]
  rfl

noncomputable abbrev latPi (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    Submodule ℤ (κ → mixedSpace F) :=
  Submodule.span ℤ (Set.range (Pi.basis (fun _ : κ => latticeBasis F)))

theorem mem_latPi (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (y : κ → F)
    (hy : ∀ i, IsIntegral ℤ (y i)) : (fun i => mixedEmbedding F (y i)) ∈ latPi F κ := by
  rw [Module.Basis.mem_span_iff_repr_mem]
  intro ji
  rw [Pi.basis_repr]
  have h1 : mixedEmbedding F (y ji.1) ∈ mixedEmbedding.integerLattice F := by
    exact ⟨⟨y ji.1, hy ji.1⟩, rfl⟩
  have h2 := (mem_span_latticeBasis F).mpr h1
  exact (Module.Basis.mem_span_iff_repr_mem ℤ _ _).mp h2 ji.2

theorem summable_inv_one_add_pow (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    Summable fun z : latPi F κ =>
      ((1 + ‖(z : κ → mixedSpace F)‖) ^ (Module.finrank ℤ (latPi F κ) + 1))⁻¹ := by
  set N : ℕ := Module.finrank ℤ (latPi F κ) + 1 with hN
  have h0 := ZLattice.summable_norm_rpow (latPi F κ) (-(N : ℝ)) (by rw [hN]; push_cast; linarith)
  have h1 : Summable fun z : latPi F κ => (if z = 0 then (1 : ℝ) else 0) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro z hz
    have : z ≠ 0 := by simpa using hz
    simp [this]
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_) (h0.add h1)
  have hr : 0 ≤ ‖z‖ ^ (-(N : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
  by_cases hz : z = 0
  · subst hz
    simp
  · simp only [hz, if_false, add_zero]
    have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    rw [Real.rpow_neg hpos.le, Real.rpow_natCast]
    have : ‖z‖ = ‖(z : κ → mixedSpace F)‖ := rfl
    rw [← this]
    gcongr
    linarith

end GlobalTheory.LatScaleSum

namespace GlobalTheory.LatScaleSum

open mixedEmbedding

theorem thetaSum_norm_le_pow :
    ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ], ∃ (N₀ k : ℕ) (C : ℝ), ∀ (A : ℝ) (m : ℕ) (Ψ : (κ → AF F) → ℂ), 1 ≤ m →
    (∀ ξ : κ → F, ‖Ψ (fun i => algebraMap F (AF F) (ξ i))‖ * (1 + ‖fun i => evI F (algebraMap F (AF F) (ξ i))‖) ^ N₀ ≤ A) →
    (∀ ξ : κ → F, Ψ (fun i => algebraMap F (AF F) (ξ i)) ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i)) →
    ‖thetaSum F Ψ‖ ≤ C * A * (m : ℝ) ^ k := by
  intro F _ _ κ _
  set L := latPi F κ with hL
  set N₀ : ℕ := Module.finrank ℤ L + 1 with hN
  set H : (κ → mixedSpace F) → ℝ := fun v => ((1 + ‖v‖) ^ N₀)⁻¹ with hH
  have hHs : Summable fun z : L => H z := summable_inv_one_add_pow F κ
  refine ⟨N₀, N₀, ∑' z : L, H z, ?_⟩
  intro A m Ψ hm hb hint
  set f : (κ → F) → ℂ := fun ξ => Ψ (fun i => algebraMap F (AF F) (ξ i)) with hf
  set ψ : (κ → F) → (κ → mixedSpace F) := fun ξ i => mixedEmbedding F (ξ i) with hψdef
  have hψ : ∀ ξ : κ → F, (fun i => evI F (algebraMap F (AF F) (ξ i))) = ψ ξ :=
    fun ξ => funext fun i => evI_algebraMap F (ξ i)
  set g : (κ → F) → (κ → mixedSpace F) := fun ξ => ψ (fun i => (m : F) * ξ i) with hgdef
  have hm0 : (m : F) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hm)
  have hginj : Function.Injective g := by
    intro ξ η h
    funext i
    have := congrFun h i
    simp only [hgdef, hψdef] at this
    exact mul_left_cancel₀ hm0 (mixedEmbedding_injective F this)
  have hgsmul : ∀ ξ, g ξ = m • ψ ξ := by
    intro ξ
    funext i
    simp only [hgdef, hψdef, Pi.smul_apply]
    rw [← nsmul_eq_mul, map_nsmul]
  set Lind : (κ → mixedSpace F) → ℝ := (L : Set (κ → mixedSpace F)).indicator H with hLind
  have hLs : Summable Lind := summable_subtype_iff_indicator.mp hHs
  have hLnn : ∀ v, 0 ≤ Lind v := fun v => Set.indicator_nonneg (fun v _ => by positivity) v
  have hA : 0 ≤ A := le_trans (by positivity) (hb 0)
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have key : ∀ ξ, ‖f ξ‖ ≤ A * (m : ℝ) ^ N₀ * Lind (g ξ) := by
    intro ξ
    by_cases h : f ξ = 0
    · rw [h, norm_zero]
      have := hLnn (g ξ)
      positivity
    · have hi := hint ξ h
      have hmem : g ξ ∈ L := mem_latPi F κ _ hi
      rw [hLind, Set.indicator_of_mem hmem]
      have hb' := hb ξ
      rw [hψ ξ] at hb'
      have hpos : 0 < (1 + ‖ψ ξ‖) ^ N₀ := by positivity
      have e1 : ‖f ξ‖ ≤ A * ((1 + ‖ψ ξ‖) ^ N₀)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ hpos]; exact hb'
      have hgn : ‖g ξ‖ ≤ m * ‖ψ ξ‖ := by rw [hgsmul]; exact norm_nsmul_le
      have hmpos : (0 : ℝ) < m := by linarith
      have e2 : ((1 + ‖ψ ξ‖) ^ N₀)⁻¹ ≤ (m : ℝ) ^ N₀ * H (g ξ) := by
        simp only [hH]
        calc ((1 + ‖ψ ξ‖) ^ N₀)⁻¹ = (m : ℝ) ^ N₀ * (((m : ℝ) * (1 + ‖ψ ξ‖)) ^ N₀)⁻¹ := by
              rw [mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hmpos.ne'), one_mul]
          _ ≤ (m : ℝ) ^ N₀ * ((1 + ‖g ξ‖) ^ N₀)⁻¹ := by
              gcongr
              nlinarith [norm_nonneg (ψ ξ)]
      calc ‖f ξ‖ ≤ A * ((1 + ‖ψ ξ‖) ^ N₀)⁻¹ := e1
        _ ≤ A * ((m : ℝ) ^ N₀ * H (g ξ)) := mul_le_mul_of_nonneg_left e2 hA
        _ = _ := by ring
  have hu : Summable fun ξ => A * (m : ℝ) ^ N₀ * Lind (g ξ) :=
    (hLs.comp_injective hginj).mul_left _
  have hfs : Summable fun ξ => ‖f ξ‖ := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) key hu
  have hcomp : ∑' ξ, Lind (g ξ) ≤ ∑' v, Lind v := tsum_comp_le_tsum_of_inj hLs hLnn hginj
  have hsub : ∑' v, Lind v = ∑' z : L, H z := (tsum_subtype (L : Set (κ → mixedSpace F)) H).symm
  have hmk : 0 ≤ A * (m : ℝ) ^ N₀ := by positivity
  calc ‖thetaSum F Ψ‖ = ‖∑' ξ, f ξ‖ := rfl
    _ ≤ ∑' ξ, ‖f ξ‖ := norm_tsum_le_tsum_norm hfs
    _ ≤ ∑' ξ, A * (m : ℝ) ^ N₀ * Lind (g ξ) := hfs.tsum_le_tsum key hu
    _ = A * (m : ℝ) ^ N₀ * ∑' ξ, Lind (g ξ) := tsum_mul_left
    _ ≤ A * (m : ℝ) ^ N₀ * ∑' z : L, H z := by
        rw [← hsub]; exact mul_le_mul_of_nonneg_left hcomp hmk
    _ = (∑' z : L, H z) * A * (m : ℝ) ^ N₀ := by ring

end GlobalTheory.LatScaleSum
