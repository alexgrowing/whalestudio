import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddHsConjLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CasselmanWallachExtensionBanachTarget
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsKFinDRep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.AutSpace GlobalTheory.TypeSum GlobalTheory.TypeSum.GrowthAtPlace Formalism.REAL

namespace GlobalTheory.TypeSum.GKCoef

theorem mem_kFin_iff {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
    {σ : Mx n → (H →L[ℂ] H)} {v : H} : v ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ ↔ IsKFin ε σ v := by
  constructor
  · intro hv
    have : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ ≤ kfin ε σ := sSup_le fun W hW w hw => ⟨W, hW.1, hw, hW.2⟩
    exact this hv
  · rintro ⟨S, h1, h2, h3⟩
    exact (le_sSup (show S ∈ {W : Submodule ℂ H | FiniteDimensional ℂ W ∧ IsKStableOn ε σ W} from ⟨h1, h3⟩)) h2

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {τ : D.what₂.Tau}
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin V.rank → Bool}
  {σ : Mx V.rank → (H →L[ℂ] H)} {P : Mx V.rank} {T : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ →ₗ[ℂ] (GA D V → ℂ)}

theorem map_K (hθ : IsInfFam (D := D) θ) (hP : IsUnit P) (h : Pᴴ * Jm ε * P = gramAt D V τ)
    (hT : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ ε σ P T) {k : Mx V.rank} (hk : k ∈ Kset ε)
    (v w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ) (hw : (w : H) = σ k v) (x : GA D V) {y : Mx V.rank} (hy : y ∈ UJset ε) :
    T w (x * atTau θ V τ (P⁻¹ * y * P)) = T v (x * atTau θ V τ (P⁻¹ * (y * k) * P)) := by
  have hd := (isUnit_iff_isUnit_det _).1 hP
  have hkU := K_le_UJ hk
  have e : P * (P⁻¹ * k * P) * P⁻¹ = k := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  have := hT.mapK (P⁻¹ * k * P) (conj_inv_mem hP h hkU) (by rw [e]; exact hk) v w (by rw [e]; exact hw)
  rw [this, rTr, conj_mul hP, atTau_mul hθ V τ (conj_inv_mem hP h hy) (conj_inv_mem hP h hkU), mul_assoc]

theorem hasDerivAt_map (hθ : IsInfFam (D := D) θ) (hP : IsUnit P) (h : Pᴴ * Jm ε * P = gramAt D V τ)
    (hT : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ ε σ P T) (v w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ) {X : Mx V.rank}
    (hX : X ∈ lieSet ε) (hv : Sm ε σ (v : H)) (hw : (w : H) = dRep σ X v) (x : GA D V) {y : Mx V.rank}
    (hy : y ∈ UJset ε) :
    HasDerivAt (fun t : ℝ => T v (x * atTau θ V τ (P⁻¹ * (y * NormedSpace.exp (t • X)) * P)))
      (T w (x * atTau θ V τ (P⁻¹ * y * P))) 0 := by
  have hd := (isUnit_iff_isUnit_det _).1 hP
  have hX' : P⁻¹ * X * P ∈ lieAt V τ := conj_lie hP h hX
  have e1 : ∀ t : ℝ, P * NormedSpace.exp (t • (P⁻¹ * X * P)) * P⁻¹ = NormedSpace.exp (t • X) := fun t => by
    rw [← conj_exp hP, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  have hder : HasDerivAt (fun t : ℝ => σ (P * NormedSpace.exp (t • (P⁻¹ * X * P)) * P⁻¹) v) w 0 := by
    simp only [e1]; rw [hw]; exact hasDerivAt_dRep (G := Jm ε) hv hX
  have hTw := hT.mapLie _ hX' v w hder
  rw [hTw, Rder]
  have hdiff := differentiable_oneP (hT.aut v).smooth hX' (x * atTau θ V τ (P⁻¹ * y * P)) 0
  refine hdiff.hasDerivAt.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  show T v (x * atTau θ V τ (P⁻¹ * (y * NormedSpace.exp (t • X)) * P)) =
    T v (x * atTau θ V τ (P⁻¹ * y * P) * oneP θ V τ (P⁻¹ * X * P) t)
  rw [conj_mul hP, atTau_mul hθ V τ (conj_inv_mem hP h hy) (conj_inv_mem hP h (exp_mem_UJ hX t)), conj_exp hP,
    ← mul_assoc]
  rfl

end GlobalTheory.TypeSum.GKCoef
