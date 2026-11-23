import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentCocompactInArithmeticStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.CtCont

theorem continuous_setIntegral_of_cocompact {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G]
    [FirstCountableTopology G] (Γ N : Subgroup G) [MeasurableSpace N] [OpensMeasurableSpace N]
    (hc : GlobalTheory.Cusp.Cocompact Γ N) (f : G → ℂ) (hf : Continuous f) (hinv : ∀ γ ∈ Γ, ∀ h, f (γ * h) = f h)
    (μ : Measure N) (𝓕 : Set N) (h𝓕 : μ 𝓕 ≠ ⊤) :
    Continuous (fun g => ∫ u in 𝓕, f (u.1 * g) ∂μ) := by
  obtain ⟨K, hK, hs⟩ := hc
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨C, hC⟩ := (hK.image (f := fun k : N => ‖f (k.1 * x)‖) (by fun_prop)).bddAbove
  have hev : ∀ᶠ y in 𝓝 x, ∀ k ∈ K, ‖f (k.1 * y)‖ < C + 1 := by
    refine hK.eventually_forall_of_forall_eventually fun k hk => ?_
    have hcont : Continuous fun p : G × N => ‖f (p.2.1 * p.1)‖ := by fun_prop
    have h1 : ‖f (k.1 * x)‖ < C + 1 := (hC ⟨k, hk, rfl⟩).trans_lt (lt_add_one C)
    exact hcont.continuousAt.eventually (gt_mem_nhds h1)
  refine continuousAt_of_dominated (bound := fun _ => C + 1) ?_ ?_ ?_ ?_
  · exact .of_forall fun y => (hf.comp (continuous_subtype_val.mul continuous_const)).aestronglyMeasurable
  · filter_upwards [hev] with y hy
    refine .of_forall fun u => ?_
    obtain ⟨γ, hγ, hk⟩ := hs u
    have e : f ((γ * u).1 * y) = f (u.1 * y) := by
      show f ((γ.1 * u.1) * y) = f (u.1 * y)
      rw [mul_assoc]; exact hinv _ (Subgroup.mem_subgroupOf.1 hγ) _
    rw [← e]; exact (hy _ hk).le
  · exact integrableOn_const h𝓕
  · exact .of_forall fun u => (hf.comp (continuous_const.mul continuous_id)).continuousAt

theorem topGroup_secondCountable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    IsTopologicalGroup (UA σ J) ∧ SecondCountableTopology (UA σ J) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin n) (AE F E)) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  exact ⟨inferInstance, inferInstance⟩

theorem continuous_ctf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ f : UA σ G.W.J → ℂ, Continuous f → (∀ γ ∈ ratU σ G.W.J, ∀ h, f (γ * h) = f h) → ∀ (μ : Measure (unip σ G.W H')) (𝓕 : Set (unip σ G.W H')), μ.IsHaarMeasure → IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕 μ → μ 𝓕 = 1 → Continuous (GlobalTheory.CtTyp.ctf H' μ 𝓕 f) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hA f hf hinv μ 𝓕 _ _ h1
  obtain ⟨i1, i2⟩ := topGroup_secondCountable σ G.W.J
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  haveI : FirstCountableTopology (UA σ G.W.J) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i2
  haveI : ContinuousMul (UA σ G.W.J) := i1.toContinuousMul
  exact continuous_setIntegral_of_cocompact (ratU σ G.W.J) (unip σ G.W H')
    (GlobalTheory.T.unipotent_cocompact_in_arithmetic F E σ B a a' G X om om' hT d₁ W₁ H' i₀ i₁ hA) f hf hinv μ 𝓕 (by rw [h1]; exact ENNReal.one_ne_top)

end GlobalTheory.CtCont
