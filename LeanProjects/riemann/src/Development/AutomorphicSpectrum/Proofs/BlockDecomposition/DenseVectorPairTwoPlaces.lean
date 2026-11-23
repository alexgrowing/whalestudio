import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem exists_tensCoord (K : Type) [NontriviallyNormedField K] [Algebra F K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (b : Module.Basis ι F E) :
    ∃ ψ : (ι → K) → K ⊗[F] E, Continuous ψ ∧ Function.Surjective ψ ∧
      ∀ c : ι → F, ψ (fun i => algebraMap F K (c i)) = inclR K (∑ i, c i • b i) := by
  haveI : IsModuleTopology K (K ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (K ⊗[F] E) := IsModuleTopology.toContinuousAdd K (K ⊗[F] E)
  haveI : ContinuousSMul K (K ⊗[F] E) := IsModuleTopology.toContinuousSMul K (K ⊗[F] E)
  let e := (Algebra.TensorProduct.basis K b).equivFun
  refine ⟨e.symm, IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap, e.symm.surjective, fun c => ?_⟩
  change (Algebra.TensorProduct.basis K b).equivFun.symm _ = (1 : K) ⊗ₜ[F] (∑ i, c i • b i)
  rw [Module.Basis.equivFun_symm_apply, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
    TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one]

theorem denseRange_inclR_pair [FiniteDimensional F E] {K₁ K₂ : Type} [NontriviallyNormedField K₁] [Algebra F K₁]
    [NontriviallyNormedField K₂] [Algebra F K₂]
    (h : DenseRange (fun f : F => (algebraMap F K₁ f, algebraMap F K₂ f))) :
    DenseRange (fun x : E => ((inclR K₁ x, inclR K₂ x) : (K₁ ⊗[F] E) × (K₂ ⊗[F] E))) := by
  classical
  let b := Module.finBasis F E
  obtain ⟨ψ₁, c₁, s₁, h₁⟩ := exists_tensCoord K₁ b
  obtain ⟨ψ₂, c₂, s₂, h₂⟩ := exists_tensCoord K₂ b
  let G : (Fin (Module.finrank F E) → K₁ × K₂) → (K₁ ⊗[F] E) × (K₂ ⊗[F] E) :=
    fun w => (ψ₁ (fun i => (w i).1), ψ₂ (fun i => (w i).2))
  have hGc : Continuous G := (c₁.comp (by fun_prop)).prodMk (c₂.comp (by fun_prop))
  have hGs : Function.Surjective G := by
    rintro ⟨x, y⟩
    obtain ⟨u, rfl⟩ := s₁ x
    obtain ⟨v, rfl⟩ := s₂ y
    exact ⟨fun i => (u i, v i), rfl⟩
  have hD : DenseRange (Pi.map fun (_ : Fin (Module.finrank F E)) (f : F) =>
      (algebraMap F K₁ f, algebraMap F K₂ f)) := DenseRange.piMap fun _ => h
  refine Dense.mono ?_ (hGs.denseRange.comp hD hGc)
  rintro _ ⟨c, rfl⟩
  refine ⟨∑ i, c i • b i, ?_⟩
  exact (Prod.ext (h₁ c) (h₂ c)).symm

end Coord

theorem denseRange_ratPairs : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {K₁ K₂ : Type} [NontriviallyNormedField K₁] [Algebra F K₁] [NontriviallyNormedField K₂] [Algebra F K₂], DenseRange (fun f : F => (algebraMap F K₁ f, algebraMap F K₂ f)) → ∀ M : ℕ, DenseRange (fun p : (Fin M → E) × (Fin M → E) => (((incV K₁ p.1, incV K₁ p.2), (incV K₂ p.1, incV K₂ p.2)) : ((Fin M → K₁ ⊗[F] E) × (Fin M → K₁ ⊗[F] E)) × ((Fin M → K₂ ⊗[F] E) × (Fin M → K₂ ⊗[F] E)))) := by
  intro F E _ _ _ _ _ σ _ K₁ K₂ _ _ _ _ h M
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hP : DenseRange (Pi.map fun (_ : Fin M) (x : E) =>
      ((inclR K₁ x, inclR K₂ x) : (K₁ ⊗[F] E) × (K₂ ⊗[F] E))) :=
    DenseRange.piMap fun _ => denseRange_inclR_pair h
  let g : ((Fin M → (K₁ ⊗[F] E) × (K₂ ⊗[F] E)) × (Fin M → (K₁ ⊗[F] E) × (K₂ ⊗[F] E))) →
      ((Fin M → K₁ ⊗[F] E) × (Fin M → K₁ ⊗[F] E)) × ((Fin M → K₂ ⊗[F] E) × (Fin M → K₂ ⊗[F] E)) :=
    fun q => ((fun i => (q.1 i).1, fun i => (q.2 i).1), (fun i => (q.1 i).2, fun i => (q.2 i).2))
  have hgc : Continuous g := by fun_prop
  have hgs : Function.Surjective g := by
    rintro ⟨⟨a, b⟩, ⟨c, d⟩⟩
    exact ⟨(fun i => (a i, c i), fun i => (b i, d i)), rfl⟩
  exact hgs.denseRange.comp (hP.prodMap hP) hgc

end GlobalTheory.CompanionTheory.SaGen
