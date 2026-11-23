import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemOffP
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryActionAtRealPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FibreAtTau

theorem conj_mem_UJ {n : ℕ} (ε : Fin n → Bool) (G fr g : Matrix (Fin n) (Fin n) ℂ) (hfr : IsUnit fr)
    (hJ : frᴴ * Formalism.REAL.Jm ε * fr = G) (hg : g ∈ Formalism.QuantumDeterminants.UH G) : Formalism.REAL.inUJ ε (fr * g * fr⁻¹) := by
  change gᴴ * G * g = G at hg
  unfold Formalism.REAL.inUJ
  have hd : IsUnit fr.det := (Matrix.isUnit_iff_isUnit_det fr).mp hfr
  have h1 : fr * fr⁻¹ = 1 := Matrix.mul_nonsing_inv fr hd
  have h2 : (fr⁻¹)ᴴ * frᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  calc (fr * g * fr⁻¹)ᴴ * Formalism.REAL.Jm ε * (fr * g * fr⁻¹)
      = (fr⁻¹)ᴴ * (gᴴ * (frᴴ * Formalism.REAL.Jm ε * fr) * g) * fr⁻¹ := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (fr⁻¹)ᴴ * (frᴴ * Formalism.REAL.Jm ε * fr) * fr⁻¹ := by rw [hJ, hg]
    _ = ((fr⁻¹)ᴴ * frᴴ) * Formalism.REAL.Jm ε * (fr * fr⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem cmp_frame_hom : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau), ∃ E : GA D V →* Formalism.REAL.UJ (M.ε τ), ∀ g, Formalism.MainNotions.S.umat (E g) = M.fr τ * cmp θ τ g * (M.fr τ)⁻¹ := by
  intro D θ hθ V S M τ
  have hd : IsUnit (M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit τ)
  have hfi : (M.fr τ)⁻¹ * M.fr τ = 1 := Matrix.nonsing_inv_mul _ hd
  have hif : M.fr τ * (M.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have cmul : ∀ g h : GA D V, M.fr τ * cmp θ τ (g * h) * (M.fr τ)⁻¹ =
      (M.fr τ * cmp θ τ g * (M.fr τ)⁻¹) * (M.fr τ * cmp θ τ h * (M.fr τ)⁻¹) := by
    intro g h
    have e : cmp θ τ (g * h) = cmp θ τ g * cmp θ τ h := map_mul (GlobalTheory.RowReal.infMatHom V (θ τ)) g h
    rw [e]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (M.fr τ)⁻¹ (M.fr τ), hfi, Matrix.one_mul]
  have cone : M.fr τ * cmp θ τ (1 : GA D V) * (M.fr τ)⁻¹ = 1 := by
    have e : cmp θ τ (1 : GA D V) = 1 := map_one (GlobalTheory.RowReal.infMatHom V (θ τ))
    rw [e, Matrix.mul_one, hif]
  let u : GA D V → (Matrix (Fin V.rank) (Fin V.rank) ℂ)ˣ := fun g =>
    ⟨M.fr τ * cmp θ τ g * (M.fr τ)⁻¹, M.fr τ * cmp θ τ g⁻¹ * (M.fr τ)⁻¹,
      by rw [← cmul, mul_inv_cancel, cone], by rw [← cmul, inv_mul_cancel, cone]⟩
  have mem : ∀ g, u g ∈ Formalism.REAL.UJ (M.ε τ) := fun g =>
    conj_mem_UJ (M.ε τ) _ _ _ (M.fr_unit τ) (M.fr_gram τ)
      (GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ)
  refine ⟨{ toFun := fun g => ⟨u g, mem g⟩, map_one' := ?_, map_mul' := ?_ }, fun g => rfl⟩
  · apply Subtype.ext; apply Units.ext; exact cone
  · intro g h; apply Subtype.ext; apply Units.ext; exact cmul g h

end GlobalTheory.FibreAtTau
