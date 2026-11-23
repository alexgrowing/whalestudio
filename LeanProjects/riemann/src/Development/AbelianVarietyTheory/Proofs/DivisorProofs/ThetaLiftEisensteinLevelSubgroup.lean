import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinResidue
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.EisensteinMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSchwartzVectorField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstMemAndComm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatAdelicMatrixContinuousLeMajorant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableMajorantCoordinateCosetMeasure

noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.CentreWeilComm

variable {D : D7} {θ : InfFam D} {V : HSp D} {n : ℕ} {τ : D.what₂.Tau}

theorem continuous_of_mem (hθ : IsInfFam θ) {m : ℕ} (Φ : schwartzA θ m n) : Continuous Φ.1 :=
  (GlobalTheory.SchwartzMaj.continuous_and_le_maj D θ hθ m n Φ.1
    (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ m n Φ.1 Φ.2)).1

theorem integrable_of_mem (hθ : IsInfFam θ) {m : ℕ} (μ : Measure (Mx D m n)) [μ.IsAddHaarMeasure] (Φ : schwartzA θ m n) :
    Integrable Φ.1 μ := by
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  obtain ⟨hc, K, hK, hC⟩ := GlobalTheory.SchwartzMaj.continuous_and_le_maj D θ hθ m n Φ.1
    (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ m n Φ.1 Φ.2)
  obtain ⟨N, hN⟩ := GlobalTheory.Unf.MajInt.maj_integrable D θ hθ m n (fun _ _ => True) 0 μ inferInstance
    (.of_forall fun _ _ _ h => (h trivial).elim) (fun t _ => map_add_right_eq_self μ t)
  obtain ⟨C, hC⟩ := hC N
  exact ((hN K hK).const_mul C).mono' hc.aestronglyMeasurable (.of_forall hC)

variable (τ) in

def IsDer (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (Φ Ψ : schwartzA θ V.rank n) : Prop :=
  ∀ y : Mx D V.rank n, HasDerivAt (fun t : ℝ => Φ.1 (mt V (oneP θ V τ X t)⁻¹ ⬝ y)) (Ψ.1 y) 0

variable {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle}
  {μ : Measure (Mx D V.rank n)} {𝓕 : Set (Mx D V.rank n)} {ω : StdUnn.G D n →* Module.End ℂ (schwartzA θ V.rank n)}

theorem IsDer.at (hθ : IsInfFam θ) (hX : X ∈ lieAt V τ) {Φ Ψ : schwartzA θ V.rank n} (h : IsDer τ X Φ Ψ)
    (y : Mx D V.rank n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Φ.1 (mt V (oneP θ V τ X s)⁻¹ ⬝ y)) (Ψ.1 (mt V (oneP θ V τ X t)⁻¹ ⬝ y)) t := by
  have := GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (φ := fun g => Φ.1 (mt V g⁻¹ ⬝ y)) (φ' := fun g => Ψ.1 (mt V g⁻¹ ⬝ y))
    (fun g => by
      simp only [mul_inv_rev, mt_mul, Matrix.mul_assoc]
      exact h _) 1 t
  simpa only [one_mul] using this

variable (ω) in

def Induced (T : (GA D V → ℂ) → GA D V → ℂ) : Prop :=
  ∀ Φ : schwartzA θ V.rank n, ∃ Ψ : schwartzA θ V.rank n, ∀ (g : StdUnn.G D n) (x : Mx D V.rank n),
    T (fun h => (ω g Φ).1 (mt V h⁻¹ ⬝ x)) = fun h => (ω g Ψ).1 (mt V h⁻¹ ⬝ x)

theorem Induced.sum {ι : Type} (s : Finset ι) (c : ι → ℂ) (A : ι → (GA D V → ℂ) → GA D V → ℂ)
    (h : ∀ i, Induced ω (A i)) : Induced ω fun f => ∑ i ∈ s, c i • A i f := by
  intro Φ
  choose Ψ e using fun i => h i Φ
  refine ⟨∑ i ∈ s, c i • Ψ i, fun g x => ?_⟩
  funext k
  simp only [e, map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply]

section

variable (hψ : IsCharAF D.host.F ψ) (hθ : IsInfFam θ) (hμ : IsCovolOne (ratMx D V.rank n) μ 𝓕)
  (hω : StdUnn.IsWeilSch ψ χ θ V μ ω)
include hψ hθ hμ hω

end

end GlobalTheory.RegSch.CentreWeilComm

end
