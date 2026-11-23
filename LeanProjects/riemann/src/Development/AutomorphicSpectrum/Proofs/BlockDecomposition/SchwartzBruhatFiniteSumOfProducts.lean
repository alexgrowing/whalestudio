import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatFactorizableDecomposition
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

theorem schwartzBruhat_eq_sum_pureTuples : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), IsSchwartzBruhat Φ → ∃ (N : ℕ) (φ : Fin N → (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (A : Fin N → (∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))) (S : Finset (HeightOneSpectrum (𝓞 F))), (∀ i, IsSchwartzArch (φ i)) ∧ (∀ i v, IsCompact (A i v) ∧ IsOpen (A i v)) ∧ (∀ i v, v ∉ S → A i v = latV b v) ∧ ∀ X, Φ X = ∑ i, pureN (φ i) (A i) X := by
  intro F E _ _ _ _ _ σ _ M J _ n _ d b Φ hΦ
  classical
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨k, Φinf, Φf, hinf, hf, hsum⟩ := hΦ
  choose s A S hA hAS hdec using fun i => GlobalTheory.CompanionTheory.WhitFree.DecN.exists_box_combN b (Φf i) (hf i)
  let e := Fintype.equivFin (Σ i : Fin k, (s i))
  refine ⟨Fintype.card (Σ i : Fin k, (s i)),
    fun j Z => Φinf (e.symm j).1 Z * Φf (e.symm j).1 (e.symm j).2,
    fun j => A (e.symm j).1 (e.symm j).2, Finset.univ.biUnion S, ?_, ?_, ?_, ?_⟩
  · intro j
    exact GlobalTheory.CompanionTheory.WhitFree.DecN.isSchwartzArch_const_mulN (hinf _) _
  · intro j v
    exact hA _ _ v
  · intro j v hv
    exact hAS _ _ (e.symm j).2.2 v
      (fun h => hv (Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, h⟩))
  · intro X
    rw [hsum X]
    symm
    refine (Equiv.sum_comp e.symm (fun p : (Σ i : Fin k, (s i)) =>
      pureN (fun Z => Φinf p.1 Z * Φf p.1 p.2) (A p.1 p.2) X)).trans ?_
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hdec i (projFin X), Finset.mul_sum, ← Finset.sum_coe_sort (s i)]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    unfold GlobalTheory.CompanionTheory.SiegelND.Coef.pureN
    exact mul_assoc _ _ _

end GlobalTheory.CompanionTheory.SiegelND.Coef
