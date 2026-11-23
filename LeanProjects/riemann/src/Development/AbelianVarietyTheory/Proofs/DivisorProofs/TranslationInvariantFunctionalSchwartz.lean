import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenScaledInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaledIntegralFiniteAdelePointsSubsetNhds
import GroundTheory.AutomorphicForms.StrongApproximationSLDense
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledIntegralIndicatorSchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSumNeZeroIndicatorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatInvariantScaledLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicCompactSupportFiniteSumStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section
namespace GlobalTheory.ThetaGlue

theorem coset_mem_SB : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F)
    (r : κ → FiniteAdeleRing (𝓞 F) F), a ≠ 0 →
    Set.indicator {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a} (fun _ => (1 : ℂ)) ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) :=
  GlobalTheory.T.scaled_integral_indicator_schwartz_bruhat

theorem exists_thetaSum_coset_ne_zero (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F) (ha : a ≠ 0) :
    ∃ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      thetaSum F (pureA F f (Set.indicator {y | y - 0 ∈ GlobalTheory.EvAdm.scaledInt F κ a} fun _ => (1 : ℂ))) ≠ 0 :=
  GlobalTheory.T.theta_sum_ne_zero_indicator F κ a ha (coset_mem_SB F κ a 0 ha)

theorem exists_scaledInt_invariant : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) →
    ∃ d : F, d ≠ 0 ∧ ∀ y, ∀ u ∈ GlobalTheory.EvAdm.scaledInt F κ d, g (y + u) = g y :=
  GlobalTheory.T.schwartz_bruhat_invariant_scaled_lattice

theorem eq_sum_coset : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (d : F), d ≠ 0 →
    ∀ g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ, HasCompactSupport g →
    (∀ y, ∀ u ∈ GlobalTheory.EvAdm.scaledInt F κ d, g (y + u) = g y) →
    ∃ R : Finset (κ → FiniteAdeleRing (𝓞 F) F),
      g = ∑ r ∈ R, g r • Set.indicator {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ d} (fun _ => (1 : ℂ)) :=
  GlobalTheory.T.periodic_compact_support_finite_sum

theorem span_eq_mul_thetaSum {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (L : ((κ → AF F) → ℂ) → ℂ) (hadd : ∀ Ψ ∈ schA F κ, ∀ Ψ' ∈ schA F κ, L (Ψ + Ψ') = L Ψ + L Ψ')
    (hsmul : ∀ c : ℂ, ∀ Ψ ∈ schA F κ, L (c • Ψ) = c * L Ψ) (c : ℂ) (S : Set ((κ → AF F) → ℂ))
    (hS : ∀ Ψ ∈ S, Ψ ∈ schA F κ ∧ L Ψ = c * thetaSum F Ψ) :
    ∀ Ψ ∈ Submodule.span ℂ S, Ψ ∈ schA F κ ∧ L Ψ = c * thetaSum F Ψ := by
  intro Ψ hΨ
  induction hΨ using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero =>
    refine ⟨zero_mem _, ?_⟩
    have h0 := hsmul 0 0 (zero_mem _)
    rw [zero_smul, zero_mul] at h0
    rw [h0]
    simp [thetaSum]
  | add x y _ _ hx hy =>
    refine ⟨add_mem hx.1 hy.1, ?_⟩
    rw [hadd x hx.1 y hy.1, thetaSum_add F hx.1 hy.1, hx.2, hy.2]
    ring
  | smul a x _ hx =>
    refine ⟨Submodule.smul_mem _ a hx.1, ?_⟩
    rw [hsmul a x hx.1, thetaSum_smul F a x, hx.2]
    ring

theorem main : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (L : ((κ → AF F) → ℂ) → ℂ), (∀ Ψ ∈ schA F κ, ∀ Ψ' ∈ schA F κ, L (Ψ + Ψ') = L Ψ + L Ψ') →
      (∀ c : ℂ, ∀ Ψ ∈ schA F κ, L (c • Ψ) = c * L Ψ) →
      (∀ ξ : κ → F, ∀ Ψ ∈ schA F κ, L (fun x => Ψ (x + fun i => algebraMap F (AF F) (ξ i))) = L Ψ) →
      (∀ a : F, a ≠ 0 → ∀ r : κ → FiniteAdeleRing (𝓞 F) F, ∃ c : ℂ,
        ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
          L (pureA F f (Set.indicator {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a} fun _ => (1 : ℂ))) =
            c * thetaSum F (pureA F f (Set.indicator {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a} fun _ => (1 : ℂ)))) →
      ∃ c : ℂ, ∀ Ψ ∈ schA F κ, L Ψ = c * thetaSum F Ψ := by
  intro F _ _ κ _ L hadd hsmul htr hloc
  classical
  have hloc0 := fun (a : F) (ha : a ≠ 0) => hloc a ha 0
  choose! cst hcst using hloc0

  have hcoset : ∀ b : F, b ≠ 0 → ∀ r : κ → FiniteAdeleRing (𝓞 F) F,
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        L (pureA F f (Set.indicator {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ b} fun _ => (1 : ℂ))) =
          cst b * thetaSum F (pureA F f (Set.indicator {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ b} fun _ => (1 : ℂ))) := by
    intro b hb r f
    have hd : DenseRange (Pi.map fun (_ : κ) => algebraMap F (FiniteAdeleRing (𝓞 F) F)) :=
      DenseRange.piMap fun _ => GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing F
    have hop : IsOpen {y : κ → FiniteAdeleRing (𝓞 F) F | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ b} :=
      (GlobalTheory.EvAdm.isOpen_scaledInt b).preimage (continuous_id.sub continuous_const)
    obtain ⟨ρ, hρ⟩ := hd.exists_mem_open hop ⟨r, by simp [zero_mem]⟩
    set ρ' : κ → FiniteAdeleRing (𝓞 F) F := fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ρ i) with hρ'
    have hρ'm : ρ' - r ∈ GlobalTheory.EvAdm.scaledInt F κ b := hρ
    have hind : (Set.indicator {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ b} fun _ => (1 : ℂ)) =
        Set.indicator {y | y - ρ' ∈ GlobalTheory.EvAdm.scaledInt F κ b} fun _ => (1 : ℂ) := by
      congr 1
      ext y
      simp only [Set.mem_setOf_eq]
      constructor
      · intro h
        have := sub_mem h hρ'm
        rwa [sub_sub_sub_cancel_right] at this
      · intro h
        have := add_mem h hρ'm
        rwa [sub_add_sub_cancel] at this
    rw [hind]
    set Ψ := pureA F f (Set.indicator {y | y - ρ' ∈ GlobalTheory.EvAdm.scaledInt F κ b} fun _ => (1 : ℂ)) with hΨ
    have hΨm : Ψ ∈ schA F κ := Submodule.subset_span ⟨f, _, coset_mem_SB F κ b ρ' hb, rfl⟩
    have htrans := GlobalTheory.SchwartzTranslate.pureA_translate F (fun i => algebraMap F (AF F) (ρ i)) f
      (Set.indicator {y | y - ρ' ∈ GlobalTheory.EvAdm.scaledInt F κ b} fun _ => (1 : ℂ))
    have hshift : (fun y : κ → FiniteAdeleRing (𝓞 F) F =>
        (Set.indicator {y | y - ρ' ∈ GlobalTheory.EvAdm.scaledInt F κ b} fun _ => (1 : ℂ))
          (y + fun i => (algebraMap F (AF F) (ρ i)).2)) =
        Set.indicator {y | y - 0 ∈ GlobalTheory.EvAdm.scaledInt F κ b} fun _ => (1 : ℂ) := by
      funext y
      have e : (y + fun i => (algebraMap F (AF F) (ρ i)).2) - ρ' = y - 0 := by
        rw [sub_zero]; exact add_sub_cancel_right y ρ'
      simp only [Set.indicator, Set.mem_setOf_eq, e]
    rw [hshift] at htrans
    have hT : (fun x => Ψ (x + fun i => algebraMap F (AF F) (ρ i))) =
        pureA F ⇑((SchwartzMap.compSubConstCLM ℂ (-fun i =>
          (InfiniteAdeleRing.ringEquiv_mixedSpace F) ((algebraMap F (AF F) (ρ i)).1))) f)
          (Set.indicator {y | y - 0 ∈ GlobalTheory.EvAdm.scaledInt F κ b} fun _ => (1 : ℂ)) := htrans
    have hθ : thetaSum F (fun x => Ψ (x + fun i => algebraMap F (AF F) (ρ i))) = thetaSum F Ψ := by
      unfold thetaSum
      have e : ∀ ξ : κ → F, ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) +
          fun i => algebraMap F (AF F) (ρ i)) = fun i => algebraMap F (AdeleRing (𝓞 F) F) ((Equiv.addRight ρ ξ) i) := by
        intro ξ; funext i; simp [map_add]
      simp only [e]
      exact (Equiv.addRight ρ).tsum_eq (fun ξ => Ψ fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))
    rw [← htr ρ Ψ hΨm, ← hθ, hT]
    exact hcst b hb _

  have hinv : ∀ d : F, d ≠ 0 → ∀ g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ, HasCompactSupport g →
      (∀ y, ∀ u ∈ GlobalTheory.EvAdm.scaledInt F κ d, g (y + u) = g y) →
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
        L (pureA F f g) = cst d * thetaSum F (pureA F f g) := by
    intro d hd g hg hgi f
    obtain ⟨R, hR⟩ := eq_sum_coset F κ d hd g hg hgi
    let S : Set ((κ → AF F) → ℂ) := {Ψ | ∃ r, Ψ = pureA F f (Set.indicator {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ d} fun _ => (1 : ℂ))}
    have hS : ∀ Ψ ∈ S, Ψ ∈ schA F κ ∧ L Ψ = cst d * thetaSum F Ψ := by
      rintro _ ⟨r, rfl⟩
      exact ⟨Submodule.subset_span ⟨f, _, coset_mem_SB F κ d r hd, rfl⟩, hcoset d hd r f⟩
    have hsum : pureA F f g = ∑ r ∈ R, g r • pureA F f
        (Set.indicator {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ d} fun _ => (1 : ℂ)) := by
      conv_lhs => rw [hR]
      funext x
      simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => by ring
    have hmem : pureA F f g ∈ Submodule.span ℂ S := by
      rw [hsum]
      exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)
    exact (span_eq_mul_thetaSum L hadd hsmul (cst d) S hS _ hmem).2

  have hcmp : ∀ a : F, a ≠ 0 → ∀ d : F, d ≠ 0 →
      (GlobalTheory.EvAdm.scaledInt F κ d : Set (κ → FiniteAdeleRing (𝓞 F) F)) ⊆ GlobalTheory.EvAdm.scaledInt F κ a → cst a = cst d := by
    intro a ha d hd hsub
    obtain ⟨f, hf⟩ := exists_thetaSum_coset_ne_zero F κ a ha
    have h1 := hcst a ha f
    have h2 := hinv d hd _ (coset_mem_SB F κ a 0 ha).2 (fun y u hu => by
      simp only [Set.indicator, Set.mem_setOf_eq, sub_zero]
      have hu' : u ∈ GlobalTheory.EvAdm.scaledInt F κ a := hsub hu
      by_cases hy : y ∈ GlobalTheory.EvAdm.scaledInt F κ a
      · rw [if_pos (add_mem hy hu'), if_pos hy]
      · rw [if_neg hy, if_neg]
        intro h
        exact hy (by simpa using sub_mem h hu')) f
    exact mul_right_cancel₀ hf (h1.symm.trans h2)
  have hall : ∀ d : F, d ≠ 0 → cst d = cst 1 := by
    intro d hd
    have hn : ((GlobalTheory.EvAdm.scaledInt F κ d : Set _) ∩ GlobalTheory.EvAdm.scaledInt F κ 1) ∈ 𝓝 (0 : κ → FiniteAdeleRing (𝓞 F) F) :=
      Filter.inter_mem ((GlobalTheory.EvAdm.isOpen_scaledInt d).mem_nhds (zero_mem _))
        ((GlobalTheory.EvAdm.isOpen_scaledInt 1).mem_nhds (zero_mem _))
    obtain ⟨e, he, hsub⟩ := GlobalTheory.EvAdm.exists_scaledInt_subset_of_mem_nhds F κ _ hn
    rw [hcmp d hd e he (hsub.trans Set.inter_subset_left), hcmp 1 one_ne_zero e he (hsub.trans Set.inter_subset_right)]
  refine ⟨cst 1, fun Ψ hΨ => ?_⟩
  refine (span_eq_mul_thetaSum L hadd hsmul (cst 1) _ ?_ Ψ hΨ).2
  rintro _ ⟨f, g, hg, rfl⟩
  refine ⟨Submodule.subset_span ⟨f, g, hg, rfl⟩, ?_⟩
  obtain ⟨d, hd, hgi⟩ := exists_scaledInt_invariant F κ g hg
  rw [hinv d hd g hg.2 hgi f, hall d hd]

end GlobalTheory.ThetaGlue
end
