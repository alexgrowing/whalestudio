import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LocInstSt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGaussIndicator
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.LocLawH

variable {D : D7} {n : ℕ}

open Classical in

def atT {m : ℕ} (σ : (D.what₂.Tau → ℂ) →+ AE D) (τ : D.what₂.Tau) (M : Matrix (Fin m) (Fin n) ℂ) : Mx D m n :=
  fun i j => σ (Pi.single τ (M i j))

theorem compAt_atT {m : ℕ} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) (τ : D.what₂.Tau)
    (M : Matrix (Fin m) (Fin n) ℂ) : compAt θ τ (atT σ τ M) = M := by
  classical
  ext i j
  simp only [compAt, atT, Matrix.map_apply, h.comp, Pi.single_eq_same]

theorem compAt_atT_ne {m : ℕ} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) {τ τ' : D.what₂.Tau}
    (hne : τ' ≠ τ) (M : Matrix (Fin m) (Fin n) ℂ) : compAt θ τ' (atT σ τ M) = 0 := by
  classical
  ext i j
  simp only [compAt, atT, Matrix.map_apply, h.comp, Matrix.zero_apply]
  exact Pi.single_eq_of_ne hne _

theorem finPart_atT {m : ℕ} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) (τ : D.what₂.Tau)
    (M : Matrix (Fin m) (Fin n) ℂ) (i : Fin m) (j : Fin n) : finPart D (atT σ τ M i j) = 0 := h.fin _

theorem compAt_zero {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) : compAt θ τ (0 : Mx D m n) = 0 := by
  ext i j; simp [compAt]

def intW (D : D7) (m n : ℕ) : AddSubgroup (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E)) where
  carrier := {a | ∀ i j, a i j ∈ intAE D}
  add_mem' := fun ha hb i j => (intAE D).add_mem (ha i j) (hb i j)
  zero_mem' := fun _ _ => (intAE D).zero_mem
  neg_mem' := fun ha i j => (intAE D).neg_mem (ha i j)

open Classical in

def g0 (D : D7) (m n : ℕ) : (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) → ℂ := fun a =>
  if (QuotientAddGroup.mk (show Matrix (Fin m) (Fin n) _ from a) : _ ⧸ intW D m n) = 0 then (1 : ℂ) else 0

theorem gaussian_mem_schwartz_bruhat (D : D7) (m n : ℕ) : g0 D m n ∈ GlobalTheory.WeilM.SB (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) := by
  classical
  have hWe : (intW D m n : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) =
      ⋂ i, ⋂ j, (fun a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => a i j) ⁻¹'
        (intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) := by
    ext a
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    rfl
  have hWo : IsOpen (intW D m n : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) := by
    rw [hWe]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage ((continuous_apply j).comp (continuous_apply i))
  have hWc : IsCompact (intW D m n : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => GlobalTheory.SchwartzBruhatTensor.isCompact_intAE D
  exact GlobalTheory.SchwartzBruhatTensor.coset_mem_SB (intW D m n) hWo hWc 0

theorem gaussian_at_zero_eq_one (D : D7) (m n : ℕ) : g0 D m n 0 = 1 := by
  classical
  simp only [g0]
  rw [if_pos]
  exact (QuotientAddGroup.eq_zero_iff (N := intW D m n) (0 : Matrix (Fin m) (Fin n) _)).2 (intW D m n).zero_mem

def psi0 (θ : InfFam D) (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) : Mx D V.rank n → ℂ := fun x =>
  evalPoly (1 : MvPolynomial (D.what₂.Tau × Fin V.rank × Fin n × Bool) ℂ) (fun τ => compAt θ τ x) *
    gAway V l s τ (fun τ => compAt θ τ x) * g0 D V.rank n (fun i j => finPart D (x i j))

theorem unitaryFinitePointsToGLFiniteAdeles_isUnitary (θ : InfFam D) (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) : psi0 θ V n l s τ ∈ awayA θ V n l s τ :=
  Submodule.subset_span ⟨1, g0 D V.rank n, gaussian_mem_schwartz_bruhat D V.rank n, fun v hv => by simp at hv, rfl⟩

theorem gAway_of {V : HSp D} (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (τ : D.what₂.Tau)
    (z : D.what₂.Tau → Matrix (Fin V.rank) (Fin n) ℂ) (hz : ∀ τ', τ' ≠ τ → z τ' = 0) : gAway V l s τ z = 1 := by
  classical
  simp only [gAway]
  rw [Finset.sum_eq_zero]
  · simp
  · intro τ' h'
    rw [hz τ' (Finset.mem_filter.1 h').2]
    simp

theorem gaussian_vacuum_archimedean_point {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) (V : HSp D)
    (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (τ : D.what₂.Tau)
    (M : Matrix (Fin V.rank) (Fin n) ℂ) : psi0 θ V n l s τ (atT σ τ M) = 1 := by
  have e1 : (fun i j => finPart D (atT σ τ M i j)) = (0 : Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) := by
    funext i j; exact finPart_atT h τ M i j
  simp only [psi0, evalPoly, map_one, one_mul, e1, gaussian_at_zero_eq_one, mul_one]
  exact gAway_of l s τ _ fun τ' h' => compAt_atT_ne h h' M

theorem cmTraceAdditiveCharacter_zero (θ : InfFam D) (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) : psi0 θ V n l s τ 0 = 1 := by
  have e1 : (fun i j => finPart D ((0 : Mx D V.rank n) i j)) = (0 : Fin V.rank → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) := by
    funext i j; simp
  simp only [psi0, evalPoly, map_one, one_mul, e1, gaussian_at_zero_eq_one, mul_one]
  exact gAway_of l s τ _ fun τ' _ => compAt_zero θ τ'

theorem tens_cancel {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : GlobalTheory.FockCompare.Chart θ σ) (V : HSp D)
    (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (τ : D.what₂.Tau)
    {fr : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hfr : IsUnit fr.det) {f f' : (Fin V.rank → Fin n → ℂ) → ℂ}
    (e : tens θ τ fr f (psi0 θ V n l s τ) = tens θ τ fr f' (psi0 θ V n l s τ)) : f = f' := by
  funext u
  let U : Matrix (Fin V.rank) (Fin n) ℂ := u
  have := congrFun e (atT σ τ (fr * U))
  simp only [tens, compAt_atT h, gaussian_vacuum_archimedean_point h, mul_one] at this
  have e2 : fr⁻¹ * (fr * U) = U := by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hfr, Matrix.one_mul]
  rw [e2] at this
  exact this

theorem tens_zero {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (fr : Matrix (Fin m) (Fin m) ℂ) (f : (Fin m → Fin n → ℂ) → ℂ)
    (Ψ : Mx D m n → ℂ) : tens θ τ fr f Ψ 0 = f 0 * Ψ 0 := by
  simp only [tens, compAt_zero, Matrix.mul_zero]
  rfl

theorem phiS_val {m : ℕ} {θ : InfFam D} {τ : D.what₂.Tau} {fr : Matrix (Fin m) (Fin m) ℂ} {c : ℝ} {Ψ : Mx D m n → ℂ}
    {P : PX m n} (hm : tens θ τ fr (fP c P) Ψ ∈ schwartzA θ m n) : (phiS θ τ fr c Ψ P).1 = tens θ τ fr (fP c P) Ψ := by
  simp only [phiS, dif_pos hm]

end PositivityTheory.Rg.Sw.Glob.LocLawH
