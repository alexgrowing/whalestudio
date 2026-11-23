import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalWhittakerDiagonalShiftRamifiedCharacter
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CondExpEqZeroOfNotMem
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalWhittaker_diagonalShift_ramifiedCharacter : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (π : CuspSub E (m + 1)) (w : HeightOneSpectrum (𝓞 E)) (α : Fin (m + 1) → ℂˣ), HasSatGL w (π.locRep w) (Finset.univ.val.map α) → ∀ φ ∈ π.V, (∀ k ∈ KGL w (m + 1), act (.fin (locGL E (m + 1) w k)) φ = φ) → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ e : ℤ, GlobalTheory.RamShift.CondOne w ((ϖ ^ e : (w.adicCompletion E)ˣ) : w.adicCompletion E) → ∀ g : GA E (m + 1), GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g = 1 → ∀ ν : Fin (m + 1) → ℤ, 0 ≤ ν (Fin.last m) → GlobalTheory.JSW.whit φ.1 (g * finGL E (m + 1) (locGL E (m + 1) w (GlobalTheory.IwaCell.tD ϖ (fun i => e * ((m : ℤ) - ((i : ℕ) : ℤ)) + ν i)))) = GlobalTheory.RSCell.sphZ (qV E w) (fun i => (α i : ℂ)) ν * GlobalTheory.JSW.whit φ.1 (g * finGL E (m + 1) (locGL E (m + 1) w (GlobalTheory.IwaCell.tD ϖ (fun i => e * ((m : ℤ) - ((i : ℕ) : ℤ)))))) := by
  first | exact @GlobalTheory.JSW.whit_mul_locGL_tD_shift | exact GlobalTheory.JSW.whit_mul_locGL_tD_shift | (intros; apply GlobalTheory.JSW.whit_mul_locGL_tD_shift <;> assumption)
