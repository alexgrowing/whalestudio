import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.UnifVSpec

noncomputable section

namespace PI.VolStabW

namespace LatFactsW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))

theorem smul_mem_latSub {a M : ℕ} {s : Fv F v} (hs : s ∈ v.adicCompletionIntegers F)
    {x : Fin a → Fin M → Fv F v ⊗[F] E} (hx : x ∈ latSub b v a M) : s • x ∈ latSub b v a M := by
  have hx' : ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (x i j) k ∈
      v.adicCompletionIntegers F := hx
  show ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) b).repr ((s • x) i j) k ∈
      v.adicCompletionIntegers F
  intro i j k
  simp only [Pi.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact mul_mem hs (hx' i j k)

theorem isOpen_hermO (σ : E →ₐ[F] E) (a : ℕ) : IsOpen (hermO b v σ a : Set (HermR (Fv F v) σ a)) :=
  continuous_subtype_val.isOpen_preimage _ (PositiveNearLattice.isClopen_latV b v a a).isOpen

theorem isCompact_hermO (σ : E →ₐ[F] E) (a : ℕ) :
    IsCompact (hermO b v σ a : Set (HermR (Fv F v) σ a)) := by
  have := locallyCompact_Fv F v
  exact (isClosed_HermR (Fv F v) σ a).isClosedEmbedding_subtypeVal.isCompact_preimage
    (PositiveNearLattice.isCompact_latV b v a a)

instance contSMul_herm (σ : E →ₐ[F] E) (a : ℕ) : ContinuousSMul (Fv F v) (HermR (Fv F v) σ a) := by
  refine ⟨continuous_induced_rng.2 ?_⟩
  show Continuous fun p : Fv F v × HermR (Fv F v) σ a =>
    p.1 • (p.2 : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))
  exact continuous_fst.smul (continuous_subtype_val.comp continuous_snd)

end LatFactsW

open scoped TensorProduct
open NumberField IsDedekindDomain Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW LatFactsW

theorem latFacts_holds : LatFacts := by
  intro F E _ _ _ _ _ σ d b a M v
  obtain ⟨h0, hπ, hint⟩ := unifV_spec v
  refine ⟨fun n => ?_, fun n => ?_, ?_, ?_, fun n => ?_, fun n => ?_, ?_⟩
  · exact isOpen_smulSub _ (pow_ne_zero _ h0) _ (PositiveNearLattice.isClopen_latV b v a M).isOpen
  · exact isCompact_smulSub _ _ (PositiveNearLattice.isCompact_latV b v a M)
  · intro m n hmn x hx
    simp only [lamF, mem_smulSub] at hx ⊢
    obtain ⟨p, hp, rfl⟩ := hx
    refine ⟨unifV v ^ (n - m) • p, smul_mem_latSub b v (pow_mem hint _) hp, ?_⟩
    rw [smul_smul, ← pow_add]
    congr 2
    omega
  · intro x hx
    simp only [lamF, mem_smulSub] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact smul_mem_latSub b v (pow_mem hint _) hp
  · exact isOpen_smulSub _ (pow_ne_zero _ h0) _ (isOpen_hermO b v σ a)
  · exact isCompact_smulSub _ _ (isCompact_hermO b v σ a)
  · intro N hN
    obtain ⟨k, hk⟩ := eventually_smul_sub (hermO b v σ a : Set (HermR (Fv F v) σ a))
      (isCompact_hermO b v σ a) (fun k => unifV v ^ (k + 1)) (hπ.comp (tendsto_add_atTop_nat 1)) N hN
    refine ⟨k, ?_⟩
    simp only [hF, coe_smulSub]
    rintro _ ⟨p, hp, rfl⟩
    exact hk p hp

end PI.VolStabW
