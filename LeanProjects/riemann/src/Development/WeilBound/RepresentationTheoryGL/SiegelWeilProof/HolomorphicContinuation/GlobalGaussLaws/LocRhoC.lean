import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.FourierZeroN
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockPolynomialSchwartzKilledByLongAnnihilation
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGaussIndicator

noncomputable section

open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AdelicU GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.RhoH

variable {D : D7} {n : ℕ}

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

theorem eval_aeval_subst {σ τ' : Type} (x : τ' → ℂ) (f : σ → MvPolynomial τ' ℂ) (p : MvPolynomial σ ℂ) :
    MvPolynomial.eval x (MvPolynomial.aeval f p) = MvPolynomial.eval (fun v => MvPolynomial.eval x (f v)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.eval_C, MvPolynomial.eval_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p v hp => rw [map_mul, map_mul, hp, MvPolynomial.aeval_X, map_mul, MvPolynomial.eval_X]

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
  have hWe : ((intW D m n) : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) =
      ⋂ i, ⋂ j, (fun a : Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E) => a i j) ⁻¹'
        (intAE D : Set (Af D.host.F ⊗[D.host.F] D.host.E)) := by
    ext a
    simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
    rfl
  have hWo : IsOpen ((intW D m n) : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) := by
    rw [hWe]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (GlobalTheory.SchwartzBruhatTensor.isOpen_intAE D).preimage ((continuous_apply j).comp (continuous_apply i))
  have hWc : IsCompact ((intW D m n) : Set (Matrix (Fin m) (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))) :=
    isCompact_pi_infinite fun _ => isCompact_pi_infinite fun _ => GlobalTheory.SchwartzBruhatTensor.isCompact_intAE D
  convert GlobalTheory.SchwartzBruhatTensor.coset_mem_SB (intW D m n) hWo hWc 0 using 1
  funext a
  unfold g0
  exact if_congr Iff.rfl rfl rfl

theorem gaussian_at_zero_eq_one (D : D7) (m n : ℕ) : g0 D m n 0 = 1 := by
  unfold g0
  split_ifs with h
  · rfl
  · exact (h ((QuotientAddGroup.eq_zero_iff (N := intW D m n) (0 : Matrix (Fin m) (Fin n) _)).2 (intW D m n).zero_mem)).elim

def psi0 (θ : InfFam D) (V : HSp D) (n : ℕ) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) : Mx D V.rank n → ℂ :=
  fun x => gAway V l s τ (fun τ => compAt θ τ x) * g0 D V.rank n (fun i j => finPart D (x i j))

theorem unitaryFinitePointsToGLFiniteAdeles_isUnitary (θ : InfFam D) (V : HSp D) (l : D.what₂.Tau → ℝ) (s : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (τ : D.what₂.Tau) : psi0 θ V n l s τ ∈ awayA θ V n l s τ := by
  refine Submodule.subset_span ⟨1, g0 D V.rank n, gaussian_mem_schwartz_bruhat D V.rank n, ?_, ?_⟩
  · intro v hv
    simp at hv
  · funext x
    simp [psi0, evalPoly]

def xL (θ : InfFam D) (τ : D.what₂.Tau) {m : ℕ} (Z : Matrix (Fin m) (Fin n) ℂ) : Mx D m n := lineAt θ τ Z 1

theorem compAt_xL {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m : ℕ} (Z : Matrix (Fin m) (Fin n) ℂ) :
    (fun τ' => compAt θ τ' (xL θ τ Z)) = GlobalTheory.FockAnnKill.dirAt τ Z := by
  have h := GlobalTheory.FockAnnKill.compAt_add_lineAt hθ (0 : Mx D m n) τ Z 1
  simp only [zero_add] at h
  rw [xL, h]
  funext τ'
  have h0 : compAt θ τ' (0 : Mx D m n) = 0 := by
    ext i j
    simp [compAt]
  simp [h0]

theorem finPart_xL {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {m : ℕ} (Z : Matrix (Fin m) (Fin n) ℂ) :
    (fun i j => finPart D ((xL θ τ Z) i j)) = 0 := by
  have h := GlobalTheory.FockAnnKill.finPart_add_lineAt hθ (0 : Mx D m n) τ Z 1
  simp only [zero_add] at h
  rw [xL, h]
  funext i j
  simp

end PositivityTheory.Rg.Sw.Glob.RhoH
