import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LApproxIdS
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LIdemEx
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HCoContinuousAddEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPairingInCoordinatesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinateFormSymmetricNondegenerateStatement

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

theorem transfer {H K ι : Type} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H] [MeasurableSpace H]
    [BorelSpace H] [AddCommGroup K] [TopologicalSpace K] [IsTopologicalAddGroup K] [LocallyCompactSpace K]
    [SecondCountableTopology K] [T2Space K] [MeasurableSpace K] [BorelSpace K] [Fintype ι]
    (Θ : H ≃ₜ+ (ι → K)) (lam : Measure H) [lam.IsAddHaarMeasure] (ν : Measure K) [ν.IsAddHaarMeasure] :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ f : ι → K → ℂ, (∫ x, ∏ i, f i (Θ x i) ∂lam = (c : ℂ) * ∏ i, ∫ y, f i y ∂ν) ∧
      ((∀ i, Integrable (f i) ν) → Integrable (fun x => ∏ i, f i (Θ x i)) lam) := by
  have : (Measure.pi fun _ : ι => ν).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  obtain ⟨c, hc, hmap⟩ := haar_map_eq Θ lam (Measure.pi fun _ : ι => ν)
  have hemb : MeasurableEmbedding Θ := Θ.toHomeomorph.measurableEmbedding
  refine ⟨c, hc, fun f => ⟨?_, fun hf => ?_⟩⟩
  · have h1 := hemb.integral_map (μ := lam) (fun v : ι → K => ∏ i, f i (v i))
    rw [← h1, hmap, integral_smul_nnreal_measure, integral_fintype_prod_eq_prod, NNReal.smul_def, Complex.real_smul]
  · have h2 : Integrable (fun v : ι → K => ∏ i, f i (v i)) (lam.map Θ) := by
      rw [hmap]
      exact (Integrable.fintype_prod (μ := fun _ => ν) hf).smul_measure ENNReal.coe_ne_top
    exact hemb.integrable_map_iff.mp h2

open GlobalTheory.CompanionTheory.SiegelND.Coef.TestN in

theorem hCo_smul {F E R : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    {d n : ℕ} (b : Module.Basis (Fin d) F E) (r : R) (X X' : HermR R σ n)
    (h : X'.1 = algebraMap R (R ⊗[F] E) r • X.1) (i : Idx n d) : hCo R σ b X' i = r * hCo R σ b X i := by
  rcases i with i | q
  · simp only [hCo, Sum.elim_inl, h, Matrix.smul_apply, smul_eq_mul, ← Algebra.smul_def, map_smul]
    exact (mul_smul_comm _ _ _).symm
  · simp only [hCo, Sum.elim_inr, h, Matrix.smul_apply, smul_eq_mul, ← Algebra.smul_def, map_smul,
      Finsupp.smul_apply]

theorem char_sum {A ι : Type} [AddCommMonoid A] (ψ : AddChar A ℂ) (s : Finset ι) (a : ι → A) :
    ψ (∑ i ∈ s, a i) = ∏ i ∈ s, ψ (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, AddChar.map_add_eq_mul, ih]

end PositivityTheory.Rg.Rsw.L.LApproxId

end
