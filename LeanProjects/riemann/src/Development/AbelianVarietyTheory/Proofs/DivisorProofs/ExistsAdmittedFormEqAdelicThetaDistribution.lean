import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

open scoped Classical

namespace GlobalTheory.ThetaAdmitted

theorem summable_one_add_norm_inv_pow {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] {k : ℕ} (hk : Module.finrank ℤ L < k) :
    Summable fun z : L => ((1 + ‖z‖)⁻¹) ^ k := by
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_)
    ((ZLattice.summable_norm_pow_inv L k hk).add (hasSum_ite_eq (0 : L) (1 : ℝ)).summable)
  by_cases hz : z = 0
  · subst hz
    simp only [if_pos rfl, norm_zero, add_zero, inv_one, one_pow]
    exact le_add_of_nonneg_left (by positivity)
  · have h0 : 0 < ‖z‖ := norm_pos_iff.2 hz
    simp only [hz, if_false, add_zero]
    gcongr
    linarith

variable (F : Type) [Field F] [NumberField F]

theorem norm_thetaSum_pureA_le {κ : Type} [Fintype κ] {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 ≤ C ∧ ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.pureA F f g)‖ ≤
        C * (s.sup (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ)) f := by
  obtain ⟨B, hB⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  obtain ⟨N, hN, hK⟩ := GlobalTheory.WeilM.exists_nat_mul_integral_of_isCompact F hg.2.isCompact
  haveI := GlobalTheory.WeilM.discreteTopology_denomLattice F κ hN
  set L := GlobalTheory.WeilM.denomLattice F κ N with hLdef
  set k := Module.finrank ℤ L + 1 with hkdef
  have hu : Summable fun z : L => ((1 + ‖z‖)⁻¹) ^ k := summable_one_add_norm_inv_pow L (Nat.lt_succ_self _)
  set M := ∑' z : L, ((1 + ‖z‖)⁻¹) ^ k with hMdef
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0)
  have hM0 : 0 ≤ M := tsum_nonneg fun z => by positivity
  refine ⟨Finset.Iic (k, 0), B * 2 ^ k * M, by positivity, fun f => ?_⟩
  set S := (Finset.Iic (k, 0)).sup (schwartzSeminormFamily ℂ (κ → mixedEmbedding.mixedSpace F) ℂ) f with hSdef
  have hS0 : 0 ≤ S := apply_nonneg _ _
  have hf : ∀ x, ‖f x‖ ≤ 2 ^ k * S * ((1 + ‖x‖)⁻¹) ^ k := by
    intro x
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, 0)) le_rfl le_rfl f x
    rw [norm_iteratedFDeriv_zero] at h
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
    exact h
  let Sset : Set (κ → F) := {ξ | (fun i => mixedEmbedding F (ξ i)) ∈ L}
  have hsupp : ∀ ξ, ξ ∉ Sset → g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) = 0 := by
    intro ξ hξ
    by_contra h0
    apply hξ
    refine fun i => ?_
    obtain ⟨y, hy⟩ := (IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun v => by
      rw [map_mul, map_natCast]
      exact hK _ (subset_tsupport _ h0) i v
    refine ⟨y, ?_⟩
    have h2 := congrArg (mixedEmbedding F) hy
    rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
    exact h2.symm
  have hΦ : GlobalTheory.WeilM.pureA F f g ∈ GlobalTheory.WeilM.schA F κ := Submodule.subset_span ⟨f, g, hg, rfl⟩
  have hsn := GlobalTheory.WeilM.summable_norm_of_mem_schA F hΦ
  let a : (κ → F) → ℂ := fun ξ => GlobalTheory.WeilM.pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))
  have ha : ∀ ξ, a ξ = f (fun i => mixedEmbedding F (ξ i)) *
      g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) := fun ξ => GlobalTheory.WeilM.pureA_algebraMap F f g ξ
  have hsupa : Function.support (fun ξ => ‖a ξ‖) ⊆ Sset := by
    intro ξ hξ
    by_contra h
    apply hξ
    simp only [ha, hsupp ξ h, mul_zero, norm_zero]
  let j : Sset → L := fun ξ => ⟨_, ξ.2⟩
  have hj : Function.Injective j := fun a b h => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
  have hle : ∀ ξ : Sset, ‖a ξ‖ ≤ B * 2 ^ k * S * ((1 + ‖j ξ‖)⁻¹) ^ k := by
    intro ξ
    have h1 := hB (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ.1 i))
    have h2 : ‖f (fun i => mixedEmbedding F (ξ.1 i))‖ ≤ 2 ^ k * S * ((1 + ‖j ξ‖)⁻¹) ^ k := hf (j ξ)
    rw [ha, norm_mul]
    calc ‖f (fun i => mixedEmbedding F (ξ.1 i))‖ * ‖g (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ.1 i))‖
        ≤ (2 ^ k * S * ((1 + ‖j ξ‖)⁻¹) ^ k) * B := mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
      _ = B * 2 ^ k * S * ((1 + ‖j ξ‖)⁻¹) ^ k := by ring
  have hsumS : Summable fun ξ : Sset => B * 2 ^ k * S * ((1 + ‖j ξ‖)⁻¹) ^ k :=
    (hu.comp_injective hj).mul_left _
  calc ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.pureA F f g)‖ = ‖∑' ξ, a ξ‖ := rfl
    _ ≤ ∑' ξ, ‖a ξ‖ := norm_tsum_le_tsum_norm hsn
    _ = ∑' ξ : Sset, ‖a ξ‖ := (tsum_subtype_eq_of_support_subset hsupa).symm
    _ ≤ ∑' ξ : Sset, B * 2 ^ k * S * ((1 + ‖j ξ‖)⁻¹) ^ k :=
        Summable.tsum_le_tsum hle (hsn.subtype _) hsumS
    _ = B * 2 ^ k * S * ∑' ξ : Sset, ((1 + ‖j ξ‖)⁻¹) ^ k := tsum_mul_left
    _ ≤ B * 2 ^ k * S * M := by
        gcongr
        exact tsum_comp_le_tsum_of_inj hu (fun z => by positivity) hj
    _ = B * 2 ^ k * M * S := by ring

theorem exists_admitted_form_eq_adelicThetaDistribution_alt : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ l ∈ (GlobalTheory.WeilM.adeleClass F).adm κ, ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, l Φ = GlobalTheory.WeilM.thetaSum F Φ := by
  intro F _ _ κ _
  obtain ⟨l, hl⟩ := LinearMap.exists_extend (GlobalTheory.WeilM.thetaLin F κ)
  have hl' : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, l Φ = GlobalTheory.WeilM.thetaSum F Φ := fun Φ hΦ => by
    have := LinearMap.congr_fun hl ⟨Φ, hΦ⟩
    simpa using this
  refine ⟨l, ?_, hl'⟩
  intro g hg
  have hmem : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      GlobalTheory.WeilM.pureA F f g ∈ GlobalTheory.WeilM.schA F κ := fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩
  refine ⟨SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℂ)
    (fun f => GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.pureA F f g)) ?_ ?_ (norm_thetaSum_pureA_le F hg), fun f => ?_⟩
  · intro f₁ f₂
    have : GlobalTheory.WeilM.pureA F (f₁ + f₂) g = GlobalTheory.WeilM.pureA F f₁ g + GlobalTheory.WeilM.pureA F f₂ g := by
      funext x; simp [GlobalTheory.WeilM.pureA, add_mul]
    rw [this, GlobalTheory.WeilM.thetaSum_add F (hmem f₁) (hmem f₂)]
  · intro c f
    have : GlobalTheory.WeilM.pureA F (c • f) g = c • GlobalTheory.WeilM.pureA F f g := by
      funext x; simp [GlobalTheory.WeilM.pureA, mul_assoc]
    rw [this, GlobalTheory.WeilM.thetaSum_smul]
    rfl
  · rw [hl' _ (hmem f)]
    rfl

end GlobalTheory.ThetaAdmitted
