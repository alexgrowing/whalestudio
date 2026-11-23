import Mathlib
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.HermitianLatticeDegreeEqBundleDegree
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.GramMat
open NumberField TensorProduct GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.Lines Matrix
open scoped ComplexOrder nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_lattice_degree_eq_bundle_degree : ∀ (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L) (F : Submodule (𝓞 L) B.carrier) (i : ℕ) (f : Fin i → F) (c : F →ₗ[𝓞 L] (Fin i → L)) (Fl : HermLattice L i), LinearIndependent (𝓞 L) f → i = B.rank F → Function.Injective c → (∀ j, c (f j) = Pi.single j 1) → Fl.lattice = LinearMap.range c → (∀ σ, Fl.metric σ = gramMat B σ (fun j => (f j : B.carrier))) → Fl.degree = B.degreeWith F f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Lines.degree_eq_degreeWith | exact GlobalTheory.CompanionTheory.Ar.Lines.degree_eq_degreeWith | (intros; apply GlobalTheory.CompanionTheory.Ar.Lines.degree_eq_degreeWith <;> assumption)
