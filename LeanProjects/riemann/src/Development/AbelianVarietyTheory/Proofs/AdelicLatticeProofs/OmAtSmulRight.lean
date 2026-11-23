import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacUnique

open GlobalTheory.FockCompare

variable {D : D7}

def hAt (S T : HSp D) (τ : D.what₂.Tau) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) : ℂ :=
  ((gramAt D S τ)⁻¹ * yᴴ * gramAt D T τ * x).trace

def omAt (S T : HSp D) (τ : D.what₂.Tau) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) : ℝ :=
  2 * (tauE D τ D.host.xi0 * hAt S T τ x y).re

theorem omAt_add_left (S T : HSp D) (τ : D.what₂.Tau) (x x' y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    omAt S T τ (x + x') y = omAt S T τ x y + omAt S T τ x' y := by
  simp only [omAt, hAt, Matrix.mul_add, Matrix.trace_add, mul_add, Complex.add_re]

theorem omAt_add_right (S T : HSp D) (τ : D.what₂.Tau) (x y y' : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    omAt S T τ x (y + y') = omAt S T τ x y + omAt S T τ x y' := by
  simp only [omAt, hAt, Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, mul_add,
    Complex.add_re]

theorem omAt_smul_left (S T : HSp D) (τ : D.what₂.Tau) (c : ℝ) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    omAt S T τ (c • x) y = c * omAt S T τ x y := by
  simp only [omAt, hAt, Matrix.mul_smul, Matrix.trace_smul, mul_smul_comm, Complex.smul_re, smul_eq_mul]
  ring

theorem omAt_smul_right (S T : HSp D) (τ : D.what₂.Tau) (c : ℝ) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    omAt S T τ x (c • y) = c * omAt S T τ x y := by
  simp only [omAt, hAt, Matrix.conjTranspose_smul, star_trivial, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul,
    mul_smul_comm, Complex.smul_re, smul_eq_mul]
  ring

def omO (S T : HSp D) : RW T S →ₗ[ℝ] RW T S →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => ∑ τ, omAt S T τ (x τ) (y τ))
    (fun x x' y => by rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun τ _ => omAt_add_left S T τ _ _ _)
    (fun c x y => by rw [smul_eq_mul, Finset.mul_sum]; exact Finset.sum_congr rfl fun τ _ => omAt_smul_left S T τ c _ _)
    (fun x y y' => by rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun τ _ => omAt_add_right S T τ _ _ _)
    (fun c x y => by rw [smul_eq_mul, Finset.mul_sum]; exact Finset.sum_congr rfl fun τ _ => omAt_smul_right S T τ c _ _)

theorem omO_apply (S T : HSp D) (x y : RW T S) : omO S T x y = ∑ τ, omAt S T τ (x τ) (y τ) := rfl

theorem cplxO_add {m n : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (t : Matrix (Fin m) (Fin m) ℂ)
    (x y : Matrix (Fin m) (Fin n) ℂ) : cplxO s t (x + y) = cplxO s t x + cplxO s t y := by
  simp only [cplxO, Matrix.mul_add, Matrix.add_mul, smul_add]

theorem cplxO_smul {m n : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (t : Matrix (Fin m) (Fin m) ℂ) (c : ℝ)
    (x : Matrix (Fin m) (Fin n) ℂ) : cplxO s t (c • x) = c • cplxO s t x := by
  simp only [cplxO, Matrix.mul_smul, Matrix.smul_mul]
  exact smul_comm _ _ _

def jO (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) : RW T S →ₗ[ℝ] RW T S where
  toFun x := fun τ => cplxO (sS τ) (sT τ) (x τ)
  map_add' x y := by funext τ; exact cplxO_add _ _ _ _
  map_smul' c x := by funext τ; exact cplxO_smul _ _ c _

theorem jO_apply (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (x : RW T S) (τ : D.what₂.Tau) :
    jO S T sS sT x τ = cplxO (sS τ) (sT τ) (x τ) := rfl

def infRat (S T : HSp D) : Matrix (Fin T.rank) (Fin S.rank) D.host.E →+ RW T S where
  toFun γ := fun τ i j => tauE D τ (γ i j)
  map_zero' := by funext τ i j; exact (tauE D τ).map_zero
  map_add' x y := by funext τ i j; exact (tauE D τ).map_add _ _

def finRat (S T : HSp D) : Matrix (Fin T.rank) (Fin S.rank) D.host.E →+ WO S T where
  toFun γ := Matrix.of fun i j => (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (γ i j)
  map_zero' := by funext i j; exact TensorProduct.tmul_zero _ _
  map_add' x y := by funext i j; exact TensorProduct.tmul_add _ _ _

theorem finRat_inf (S T : HSp D) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    (finRat S T γ).map (infPart D) = 0 := by
  funext i j
  show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (γ i j) = 0
  exact TensorProduct.zero_tmul _ _

theorem finRat_fin (S T : HSp D) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    (finRat S T γ).map (finPart D) = (ratW T S γ).map (finPart D) := rfl

theorem piW_of_inf (θ : InfFam D) {S T : HSp D} {u : WO S T} (hu : u.map (infPart D) = 0) :
    piW θ T S u = 0 := by
  funext τ i j
  have : infPart D (u i j) = 0 := congrFun (congrFun hu i) j
  show θ τ (infPart D (u i j)) = 0
  rw [this, RingHom.map_zero]

theorem piW_ratW {θ : InfFam D} (hθ : IsInfFam θ) (S T : HSp D)
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : piW θ T S (ratW T S γ) = infRat S T γ := by
  funext τ i j
  exact comp_incA hθ τ _

theorem ratW_eq {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (h : Chart θ σ) (S T : HSp D)
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    ratW T S γ = iotaW σ T S (infRat S T γ) + finRat S T γ := by
  have e : (ratW T S γ - finRat S T γ : WA T S) = iotaW σ T S (infRat S T γ) := by
    refine h.real_ext ?_ (h.real_iota T S _) ?_
    · funext i j
      have e1 : finPart D (finRat S T γ i j) = finPart D (ratW T S γ i j) := rfl
      show finPart D (ratW T S γ i j - finRat S T γ i j) = 0
      rw [RingHom.map_sub, e1, sub_self]
    · rw [AddMonoidHom.map_sub, piW_of_inf θ (finRat_inf S T γ), piW_ratW h.inf, h.pi_iota, sub_zero]
  exact sub_eq_iff_eq_add.1 e

theorem latO_inf (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) {u : WO S T} (hu : u ∈ latO S T LS LT P) :
    u.map (infPart D) = 0 := by
  have : latO S T LS LT P ≤ ((infPart D).toAddMonoidHom.mapMatrix (m := Fin T.rank) (n := Fin S.rank)).ker := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨α, -, -, a, -, s, -, t, -, rfl⟩
    funext i j
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] _ = 0
    exact TensorProduct.zero_tmul _ _
  exact this hu

end GlobalTheory.VacUnique

end
