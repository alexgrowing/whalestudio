import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LocPoly
import GroundTheory.AutomorphicForms.GL2.GJMatrixSchwartz
open NumberField IsDedekindDomain Matrix GroundTheory.Global GroundTheory.Automorphic.GJMatrix GlobalTheory.HenQ
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc)
open scoped nonZeroDivisors

noncomputable section
namespace GlobalTheory.HenQ
variable {K : Type} [Field K] [NumberField K]

theorem valued_det_of_KGL {w : HeightOneSpectrum (𝓞 K)} {n : ℕ} {g : GL (Fin n) (w.adicCompletion K)}
    (hg : g ∈ GlobalTheory.LFun.KGL w n) : Valued.v g.val.det = 1 := by
  obtain ⟨g0, rfl⟩ := hg
  set O := (w.adicCompletionIntegers K).toSubring
  have hd : ∀ h : GL (Fin n) O, ((Formalism.UG.bc O.subtype h).val.det) = ((h.val.det : O) : w.adicCompletion K) := by
    intro h
    exact (RingHom.map_det O.subtype h.val).symm
  have h1 : Valued.v ((g0.val.det : O) : w.adicCompletion K) ≤ 1 := (g0.val.det).2
  have h2 : Valued.v (((g0⁻¹).val.det : O) : w.adicCompletion K) ≤ 1 := ((g0⁻¹).val.det).2
  have h3 : ((g0.val.det : O) : w.adicCompletion K) * (((g0⁻¹).val.det : O) : w.adicCompletion K) = 1 := by
    rw [← Subring.coe_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
    rfl
  have h4 := congrArg Valued.v h3
  rw [map_mul, map_one] at h4
  rw [hd]
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ := h4.symm
    _ ≤ Valued.v ((g0.val.det : O) : w.adicCompletion K) * 1 := mul_le_mul' le_rfl h2
    _ = _ := mul_one _

end GlobalTheory.HenQ
