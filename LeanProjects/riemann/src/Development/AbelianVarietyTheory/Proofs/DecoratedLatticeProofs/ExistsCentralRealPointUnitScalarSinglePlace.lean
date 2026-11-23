import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectorsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.CentralUnit

variable {D : D7}

theorem exists_unit {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ∃ a : AE D, finPart D a = 1 ∧ (∀ ρ, θ ρ (infPart D a) = if ρ = τ then ζ else 1) ∧ cA D a * a = 1 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.exists_chart hθ
  let v : D.what₂.Tau → ℂ := fun ρ => if ρ = τ then ζ - 1 else 0
  let a : AE D := 1 + σ v
  have a1 : finPart D a = 1 := by
    simp only [a]; rw [RingHom.map_add, hσ.fin, RingHom.map_one, add_zero]
  have a2 : ∀ ρ, θ ρ (infPart D a) = if ρ = τ then ζ else 1 := by
    intro ρ
    simp only [a]; rw [RingHom.map_add, RingHom.map_add, hσ.comp, RingHom.map_one, RingHom.map_one]
    simp only [v]
    split_ifs <;> ring
  refine ⟨a, a1, a2, sub_eq_zero.1 (hσ.ext _ ?_ fun ρ => ?_)⟩
  · have e : finPart D (cA D a) = sigR (Af D.host.F) D.sp.cm.sig (finPart D a) :=
      GlobalTheory.FockCompare.LiftUnitary.snd_sigR D.sp.cm.sig a
    rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_one, e, a1, RingHom.map_one, one_mul, sub_self]
  · rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, RingHom.map_one, RingHom.map_one,
      GlobalTheory.FockCompare.comp_cA hθ, a2]
    split_ifs
    · rw [Complex.conj_mul', hζ, Complex.ofReal_one, one_pow, sub_self]
    · rw [RingHom.map_one, one_mul, sub_self]

theorem scalar_mem (S : HSp D) {a : AE D} (ha : cA D a * a = 1) :
    Formalism.UG.cT (cA D) (Matrix.diagonal fun _ : Fin S.rank => a) * JR (AF D.host.F) S.gram *
      (Matrix.diagonal fun _ : Fin S.rank => a) = JR (AF D.host.F) S.gram := by
  rw [Formalism.UG.cT, Matrix.diagonal_map (RingHom.map_zero _), Matrix.diagonal_transpose]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  linear_combination (JR (AF D.host.F) S.gram i j) * ha

noncomputable def scalarElt (S : HSp D) {a : AE D} (ha : cA D a * a = 1) : GA D S :=
  ⟨⟨Matrix.diagonal fun _ => a, Matrix.diagonal fun _ => cA D a,
    by rw [Matrix.diagonal_mul_diagonal, mul_comm, ha, Matrix.diagonal_one],
    by rw [Matrix.diagonal_mul_diagonal, ha, Matrix.diagonal_one]⟩, scalar_mem S ha⟩

theorem mt_scalarElt (S : HSp D) {a : AE D} (ha : cA D a * a = 1) :
    Formalism.L2.Theta.mt S (scalarElt S ha) = Matrix.diagonal fun _ => a := rfl

theorem scalarElt_mem_GinfC (S : HSp D) {a : AE D} (ha : cA D a * a = 1) (h1 : finPart D a = 1) :
    scalarElt S ha ∈ GinfC S := by
  rw [GinfC, MonoidHom.mem_ker]
  refine Units.ext ?_
  ext i j
  change ((Matrix.diagonal fun _ : Fin S.rank => a).map (finPart D)) i j =
    (1 : Matrix (Fin S.rank) (Fin S.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) i j
  rw [Matrix.map_apply, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs
  · exact h1
  · exact RingHom.map_zero _

theorem scalarElt_mem_center (S : HSp D) {a : AE D} (ha : cA D a * a = 1) :
    scalarElt S ha ∈ Subgroup.center (GA D S) := by
  refine Subgroup.mem_center_iff.2 fun k => Subtype.ext (Units.ext ?_)
  ext i j
  change (k.1.val * Matrix.diagonal fun _ : Fin S.rank => a) i j = ((Matrix.diagonal fun _ : Fin S.rank => a) * k.1.val) i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

theorem compAt_scalarElt (θ : InfFam D) (τ : D.what₂.Tau) (S : HSp D) {a : AE D} (ha : cA D a * a = 1) :
    compAt θ τ (Formalism.L2.Theta.mt S (scalarElt S ha)) = θ τ (infPart D a) • (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) := by
  rw [mt_scalarElt]
  ext i j
  rw [compAt, Matrix.map_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

theorem exists_central_of_norm_one : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (S : HSp D) (τ : D.what₂.Tau) (ζ : ℂ), ‖ζ‖ = 1 → ∃ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) ∧ compAt θ τ (Formalism.L2.Theta.mt S z) = ζ • (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) ∧ ∀ ρ : D.what₂.Tau, ρ ≠ τ → compAt θ ρ (Formalism.L2.Theta.mt S z) = 1 := by
  intro D θ hθ S τ ζ hζ
  obtain ⟨a, a1, a2, ac⟩ := exists_unit hθ τ hζ
  refine ⟨scalarElt S ac, scalarElt_mem_GinfC S ac a1, scalarElt_mem_center S ac, ?_, fun ρ hρ => ?_⟩
  · rw [compAt_scalarElt, a2, if_pos rfl]
  · rw [compAt_scalarElt, a2, if_neg hρ, one_smul]

end GlobalTheory.CentralUnit

end
