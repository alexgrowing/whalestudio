import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasWitness
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerThetaFunctionsReadingTestFunctionFrames
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionTranslatesThetaByUnitScalar

open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.FrameEquiv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameEquiv.RealChar

variable {D : D7} {S T : HSp D} (C : GlobalTheory.Ker.Ctx S T)

theorem xB_mem_dom {B : C.Bas} (hB : C.IsB B) : C.xB B ∈ C.X.dom :=
  GlobalTheory.Ker.ONBasis.mem_dom C.X (GlobalTheory.Ker.ONBasis.isONFr_xB C hB)

theorem Th_ne_zero {x : Frame C.X.Ψ T.rank} (hx : x ∈ C.X.dom) {φ : TF S.rank C.g} (hφ : GlobalTheory.SW.IsSB φ)
    (h0 : φ ≠ 0) : C.Th x φ ≠ 0 := by
  intro h
  obtain ⟨l1, l2, -⟩ := GlobalTheory.Ker.Ctx.th_laws D S T C x hx φ hφ
  have h3 : GlobalTheory.SW.IsSB ((0 : ℂ) • φ) := by
    rw [zero_smul]
    exact GlobalTheory.SW.isSB_zero
  refine h0 (((l1 _ h3).2 ?_).trans (zero_smul ℂ φ))
  rw [l2, h, smul_zero]

theorem Th_zero {x : Frame C.X.Ψ T.rank} (hx : x ∈ C.X.dom) : C.Th x (0 : TF S.rank C.g) = 0 := by
  have h := (GlobalTheory.Ker.Ctx.th_laws D S T C x hx 0 GlobalTheory.SW.isSB_zero).2.1 0
  rwa [zero_smul, zero_smul] at h

theorem scalar_eq {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : GlobalTheory.Ker.IsWeak C.ψ S T om)
    {u : GA D T} {B B' : C.Bas} (hB : C.IsB B) (hB' : C.IsB B') {φ : TF S.rank C.g} (hφ : GlobalTheory.SW.IsSB φ)
    (h0 : φ ≠ 0) {c c' : ℂ} (hc' : ‖c'‖ = 1)
    (e : om (1, u) (C.Th (C.xB B) φ) = c • C.Th (C.xB (C.mvB u B)) φ)
    (e' : om (1, u) (C.Th (C.xB B') φ) = c' • C.Th (C.xB (C.mvB u B')) φ) : c = c' := by
  obtain ⟨⟨μ, 𝓕, hμ⟩, hip⟩ := GlobalTheory.Ker.ScalarProduct.ip_basic D S T C
  have hmv : ∀ A, C.IsB A → C.IsB (C.mvB u A) := fun A hA =>
    (((GlobalTheory.Ker.onBasis_frame_period D S T C).2 A hA).2.2.2.2.2 u).1
  have hth : ∀ A, C.IsB A → C.IsTh (C.Th (C.xB A) φ) := fun A hA =>
    (GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ (xB_mem_dom C hA) φ hφ).1.1
  have hd : dbl C.X C.bas C.idx φ φ 0 ≠ 0 := by
    intro hc
    have h1 := GlobalTheory.AdTh.Overlap.ipO_Th C hμ (xB_mem_dom C hB) (xB_mem_dom C hB) hφ hφ
    rw [hc, zero_mul] at h1
    exact Th_ne_zero C (xB_mem_dom C hB) hφ h0 ((hip μ 𝓕 hμ _ (hth B hB)).2.1 h1)
  have hk : kZero C.X C.idx (C.xB B) (C.xB B') (0 : Fin S.rank → Fin C.g → ℂ) 0 ≠ 0 := by
    rw [GlobalTheory.AdTh.Overlap.kZero_zero]
    exact Finset.prod_ne_zero_iff.2 fun τ _ => inv_ne_zero (pow_ne_zero _ (mul_ne_zero
      (DblPoint.det_aLin_ne_zero (xB_mem_dom C hB) (xB_mem_dom C hB') τ)
      (DblPoint.det_aAnti_ne_zero (xB_mem_dom C hB) (xB_mem_dom C hB') τ)))
  have h1 := ((hip μ 𝓕 hμ _ (hth B hB)).2.2.2 _ (hth B' hB')).2.2.2.2.2 om hom (1, u)
  have h2 : GlobalTheory.Ker.ipO μ 𝓕 (c • C.Th (C.xB (C.mvB u B)) φ) (c' • C.Th (C.xB (C.mvB u B')) φ) =
      c * conj c' * GlobalTheory.Ker.ipO μ 𝓕 (C.Th (C.xB (C.mvB u B)) φ) (C.Th (C.xB (C.mvB u B')) φ) := by
    rw [GlobalTheory.Ker.ipO, GlobalTheory.Ker.ipO, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  rw [e, e', h2, GlobalTheory.AdTh.Overlap.ipO_Th C hμ (xB_mem_dom C (hmv B hB)) (xB_mem_dom C (hmv B' hB')) hφ hφ,
    GlobalTheory.AdTh.Overlap.ipO_Th C hμ (xB_mem_dom C hB) (xB_mem_dom C hB') hφ hφ,
    GlobalTheory.AdTh.Overlap.kZero_mvB C hB u] at h1
  have h3 : c * conj c' = 1 := mul_right_cancel₀ (mul_ne_zero hd hk) (h1.trans (one_mul _).symm)
  have h4 : c' * conj c' = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc']
    simp
  linear_combination c' * h3 - c * h4

end GlobalTheory.FrameEquiv.RealChar

open GlobalTheory.FrameEquiv.RealChar in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.FrameEquiv.exists_real_character : ∀ (D : D7) (S T : HSp D) (C : GlobalTheory.Ker.Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak C.ψ S T om → ∃ χ : GA D T → ℂ, (∀ u ∈ GinfC T, ‖χ u‖ = 1) ∧ (∀ u ∈ GinfC T, ∀ u' ∈ GinfC T, χ (u * u') = χ u * χ u') ∧ ∀ u ∈ GinfC T, ∀ B, C.IsB B → ∀ φ : TF S.rank C.g, GlobalTheory.SW.IsSB φ → om (1, u) (C.Th (C.xB B) φ) = χ u • C.Th (C.xB (C.mvB u B)) φ := by
  intro D S T C om hom
  by_cases hex : ∃ φ₀ : TF S.rank C.g, GlobalTheory.SW.IsSB φ₀ ∧ φ₀ ≠ 0
  swap
  · refine ⟨fun _ => 1, fun _ _ => norm_one, fun _ _ _ _ => (mul_one _).symm, fun u _ B hB φ hφ => ?_⟩
    have h0 : φ = 0 := by
      by_contra h
      exact hex ⟨φ, hφ, h⟩
    have hmv : C.IsB (C.mvB u B) := (((GlobalTheory.Ker.onBasis_frame_period D S T C).2 B hB).2.2.2.2.2 u).1
    rw [h0, Th_zero C (xB_mem_dom C hB), Th_zero C (xB_mem_dom C hmv), map_zero, smul_zero]
  obtain ⟨φ₀, s₀, n₀⟩ := hex
  obtain ⟨⟨B₀, hB₀⟩, hJ⟩ := GlobalTheory.Ker.onBasis_frame_period D S T C
  have hr := GlobalTheory.Ker.RealScalar.om_real_Th D S T C om hom 1 (one_mem _)
  choose! χ hχ1 hχ using fun u hu => hr u hu B₀ hB₀
  have main : ∀ u ∈ GinfC T, ∀ B, C.IsB B → ∀ φ : TF S.rank C.g, GlobalTheory.SW.IsSB φ →
      om (1, u) (C.Th (C.xB B) φ) = χ u • C.Th (C.xB (C.mvB u B)) φ := fun u hu B hB φ hφ => by
    obtain ⟨c, -, hc⟩ := hr u hu B hB
    rw [← scalar_eq C hom hB hB₀ s₀ n₀ (hχ1 u hu) (hc φ₀ s₀) (hχ u hu φ₀ s₀)]
    exact hc φ hφ
  refine ⟨χ, hχ1, fun u hu u' hu' => ?_, main⟩
  have h1 := main (u * u') (mul_mem hu hu') B₀ hB₀ φ₀ s₀
  obtain ⟨hm, hmul, -⟩ := (hJ B₀ hB₀).2.2.2.2.2 u'
  have e : ((1, u * u') : GA D S × GA D T) = (1, u) * (1, u') := by simp
  rw [e, map_mul, Module.End.mul_apply, main u' hu' B₀ hB₀ φ₀ s₀, map_smul, main u hu _ hm φ₀ s₀, hmul u,
    smul_smul] at h1
  have hne := Th_ne_zero C (xB_mem_dom C ((hJ _ hm).2.2.2.2.2 u).1) s₀ n₀
  rw [mul_comm]
  exact (smul_left_injective ℂ hne h1).symm
