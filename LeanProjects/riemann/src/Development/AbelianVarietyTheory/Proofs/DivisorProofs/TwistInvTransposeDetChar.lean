import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsDataDualGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlace
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.JHMult

namespace GlobalTheory.InvTransposeTwist

open Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_invTranspose (n : ℕ) (g : GL (Fin n) k) :
    Matrix.GeneralLinearGroup.det (GlobalTheory.TypeTame.invTranspose n g) = (Matrix.GeneralLinearGroup.det g)⁻¹ := by
  ext
  simp [GlobalTheory.TypeTame.invTranspose, Matrix.GeneralLinearGroup.det, Matrix.det_transpose]

theorem nabs_inv (x : kˣ) : GlobalTheory.SplitWeil.nabs k x⁻¹ = (GlobalTheory.SplitWeil.nabs k x)⁻¹ := by
  simp [GlobalTheory.SplitWeil.nabs]

theorem absPow_det_invTranspose (n : ℕ) (s : ℂ) (g : GL (Fin n) k) :
    detChar (Fin n) (absPow k s) (GlobalTheory.TypeTame.invTranspose n g) =
      detChar (Fin n) (absPow k (-s)) g := by
  ext
  have hp := GlobalTheory.SplitWeil.nabs_pos k (Matrix.GeneralLinearGroup.det g)
  simp only [detChar, absPow, MonoidHom.comp_apply, det_invTranspose]
  simp [nabs_inv, Complex.cpow_neg]

theorem twist_comp_invTranspose (n : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (s : ℂ) :
    (twist π (detChar (Fin n) (absPow k s))).comp (GlobalTheory.TypeTame.invTranspose n) =
      twist (π.comp (GlobalTheory.TypeTame.invTranspose n)) (detChar (Fin n) (absPow k (-s))) := by
  ext g v
  simp only [MonoidHom.comp_apply, twist, MonoidHom.coe_mk, OneHom.coe_mk, absPow_det_invTranspose]

end GlobalTheory.InvTransposeTwist

theorem GlobalTheory.InvTransposeTwist.main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (s : ℂ), Nonempty (Representation.Equiv ((twist π (detChar (Fin n) (absPow k s))).comp (GlobalTheory.TypeTame.invTranspose n)) (twist (π.comp (GlobalTheory.TypeTame.invTranspose n)) (detChar (Fin n) (absPow k (-s))))) := by
  intro k _ _ _ _ n V _ _ π s
  rw [GlobalTheory.InvTransposeTwist.twist_comp_invTranspose]
  exact ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ V) (fun g => rfl)⟩
