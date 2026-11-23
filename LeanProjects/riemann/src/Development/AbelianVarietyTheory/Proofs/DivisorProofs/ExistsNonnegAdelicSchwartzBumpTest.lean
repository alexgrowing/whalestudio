import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReindexDblIncM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrInt
import GroundTheory.GlobalFields.Adele.Discrete
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdeleVectorAnnihilatorsCompactOpenBasis
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableOfRapidDecay
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

open Topology Filter

namespace GlobalTheory.AdelicBumpTest

theorem exists_nonneg_test : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (U : Set (κ → AF F)), U ∈ nhds 0 →
    ∃ Φ ∈ schA F κ, Continuous Φ ∧ (∀ x, Φ x ≠ 0 → x ∈ U) ∧ (∀ x, (Φ x).im = 0 ∧ 0 ≤ (Φ x).re) ∧ Φ 0 = 1 := by
  intro F _ _ κ _ U hU
  classical
  let e' : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) → (κ → AdeleRing (𝓞 F) F) :=
    fun p i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i)
  have he' : Continuous e' := continuous_pi fun i =>
    ((GlobalTheory.Core.Rk.RapidInt.continuous_ofMixed F).comp ((continuous_apply i).comp continuous_fst)).prodMk
      ((continuous_apply i).comp continuous_snd)
  have he'0 : e' (0, 0) = 0 := by
    funext i
    refine Prod.ext ?_ rfl
    show (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm 0 = 0
    exact map_zero _
  have hpre : e' ⁻¹' U ∈ 𝓝 ((0 : κ → mixedEmbedding.mixedSpace F), (0 : κ → FiniteAdeleRing (𝓞 F) F)) :=
    he'.continuousAt.preimage_mem_nhds (by rw [he'0]; exact hU)
  obtain ⟨V₁, hV₁, V₂, hV₂, hsub⟩ := mem_nhds_prod_iff.mp hpre
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV₁

  let b : ContDiffBump (0 : κ → mixedEmbedding.mixedSpace F) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  let f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ :=
    h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hf : ∀ y, f y = ((b y : ℝ) : ℂ) := fun y => rfl

  obtain ⟨L, hLo, hLc, hL⟩ : ∃ L : AddSubgroup (FiniteAdeleRing (𝓞 F) F), IsOpen (L : Set (FiniteAdeleRing (𝓞 F) F)) ∧
      IsCompact (L : Set (FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ u : κ → FiniteAdeleRing (𝓞 F) F, (∀ i, u i ∈ L) → u ∈ V₂ := by
    let q := Fintype.equivFin κ
    have hc : Continuous fun (u : Fin (Fintype.card κ) → FiniteAdeleRing (𝓞 F) F) (i : κ) => u (q i) :=
      continuous_pi fun i => continuous_apply _
    have hV' : (fun (u : Fin (Fintype.card κ) → FiniteAdeleRing (𝓞 F) F) (i : κ) => u (q i)) ⁻¹' V₂ ∈
        𝓝 (0 : Fin (Fintype.card κ) → FiniteAdeleRing (𝓞 F) F) :=
      hc.continuousAt.preimage_mem_nhds hV₂
    obtain ⟨L, hLo, hLc, hL⟩ := GlobalTheory.SWQ.FinAnnih.basis_nhds (F := F) _ hV'
    refine ⟨L, hLo, hLc, fun u hu => ?_⟩
    have := hL (fun l => u (q.symm l)) fun l => hu _
    simpa using this
  let S : Set (κ → FiniteAdeleRing (𝓞 F) F) := Set.pi Set.univ fun _ => (L : Set (FiniteAdeleRing (𝓞 F) F))
  have hSo : IsOpen S := isOpen_set_pi Set.finite_univ fun _ _ => hLo
  have hSc : IsClosed S := isClosed_set_pi fun _ _ => AddSubgroup.isClosed_of_isOpen L hLo
  let g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := S.indicator 1
  have hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
    refine ⟨?_, ?_⟩
    · refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
      by_cases hx : x ∈ S
      · exact ⟨S, hSo, hx, fun y hy => by simp only [g, Set.indicator_of_mem hy, Set.indicator_of_mem hx, Pi.one_apply]⟩
      · exact ⟨Sᶜ, hSc.isOpen_compl, hx, fun y hy => by simp only [g, Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
    · exact HasCompactSupport.intro (isCompact_univ_pi fun _ => hLc) fun x hx => Set.indicator_of_notMem hx _
  refine ⟨pureA F f g, Submodule.subset_span ⟨f, g, hg, rfl⟩, ?_, ?_, ?_, ?_⟩
  · exact (f.continuous.comp (continuous_pi fun i => (GlobalTheory.Core.Rk.RapidInt.continuous_toMixed F).comp
      (continuous_fst.comp (continuous_apply i)))).mul
      (hg.1.continuous.comp (continuous_pi fun i => continuous_snd.comp (continuous_apply i)))
  · intro x hx
    have hx1 : f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) ≠ 0 := left_ne_zero_of_mul hx
    have hx2 : g (fun i => (x i).2) ≠ 0 := right_ne_zero_of_mul hx
    have hb : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1) ∈ V₁ := by
      refine hball ?_
      rw [← b.support_eq]
      intro h0
      apply hx1
      rw [hf, h0]; simp
    have hS : (fun i => (x i).2) ∈ S := by
      by_contra h
      exact hx2 (Set.indicator_of_notMem h _)
    have hmem := hsub (Set.mk_mem_prod hb (hL _ fun i => hS i (Set.mem_univ i)))
    have hxe : e' ((fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1), fun i => (x i).2) = x := by
      funext i
      refine Prod.ext ?_ rfl
      exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _
    rw [← hxe]
    exact hmem
  · intro x
    show (f _ * g _).im = 0 ∧ 0 ≤ (f _ * g _).re
    rw [hf]
    by_cases h : (fun i => (x i).2) ∈ S
    · simp only [g, Set.indicator_of_mem h, Pi.one_apply, mul_one, Complex.ofReal_im, Complex.ofReal_re, true_and]
      exact b.nonneg
    · simp only [g, Set.indicator_of_notMem h, mul_zero, Complex.zero_im, Complex.zero_re, le_refl, and_self]
  · show f _ * g _ = 1
    have h0 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AdeleRing (𝓞 F) F) i).1) = 0 := by
      funext i
      exact map_zero _
    have hS0 : (fun i => ((0 : κ → AdeleRing (𝓞 F) F) i).2) ∈ S := fun i _ => L.zero_mem
    rw [h0, hf, b.one_of_mem_closedBall (Metric.mem_closedBall_self (half_pos hε).le)]
    simp only [g, Set.indicator_of_mem hS0, Pi.one_apply, Complex.ofReal_one, mul_one]

end GlobalTheory.AdelicBumpTest
