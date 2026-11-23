import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableAutomorphicSpace
import Development.AbelianVarietyTheory.Definitions.Divisors.OfIsBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.SquareIntegrableSegment
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ResW

theorem dchi_absC_one_finrank (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (s : ℂ) :
    dchi (GlobalTheory.CuspRep.Model.absC E s) 1 = s * (Module.finrank ℚ E : ℂ) := by
  let A : Cinf E →L[ℝ] ℂ :=
    s • ∑ w, (2 : ℝ) • (Complex.ofRealCLM.comp (Complex.reCLM.comp (ContinuousLinearMap.proj w)))
  have h : dchi (GlobalTheory.CuspRep.Model.absC E s) = A := fderiv_extZero (continuous_chiInf _) fun z => by
    change Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm E (infId E (expU z))) = _
    rw [GlobalTheory.CuspRep.Model.logNorm_infId]
    congr 1
    simp [A, expU, Complex.norm_exp]
  have h2 : Module.finrank ℚ E = 2 * Fintype.card (InfinitePlace E) := by
    rw [IsTotallyComplex.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
      IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  rw [h, h2]
  simp [A, mul_comm]

theorem exists_abs_cpow : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (z : ℂ), ∃ χ : HChar E, (∀ (a : ℕ) (φ : Sm E a), zc E a (mulChi a χ φ) = mulChi a χ (zc E a φ + (a * (Module.finrank ℚ E : ℂ) * z) • φ)) ∧ (∀ v, χ.UnrAt v ∧ ((χ.val v : ℂˣ) : ℂ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-z)) ∧ (∀ x, ‖((χ.1 x : ℂˣ) : ℂ)‖ = ‖(((nu E z.re).1 x : ℂˣ) : ℂ)‖) ∧ (z.im = 0 → χ = nu E z.re) := by
  intro E _ _ _ z
  refine ⟨GlobalTheory.CuspRep.Model.absC E z, fun a φ => ?_, fun v => ⟨fun x hx => Units.ext ?_, ?_⟩, fun x => ?_, fun hz => ?_⟩
  · unfold zc
    rw [lie_mulChi]
    have e : (Matrix.of (fun i j : Fin a => if i = j then (1 : Cinf E) else 0)).trace = (a : ℝ) • (1 : Cinf E) := by
      simp [Matrix.trace, Nat.cast_smul_eq_nsmul]
    rw [e, map_smul, dchi_absC_one_finrank]
    congr 3
    simp only [Complex.real_smul, Complex.ofReal_natCast]; ring
  · change Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm E (GlobalTheory.Mem.Chr.localIdele E v x)) = 1
    rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local v x 0 (by simpa [IsUnitAt] using hx)]; simp
  · change Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm E (GlobalTheory.Mem.Chr.localIdele E v (atFin v (unif v)))) = _
    have h0 : (Ideal.absNorm v.asIdeal : ℕ) ≠ 0 := by simpa [Ideal.absNorm_eq_zero_iff] using v.ne_bot
    rw [GlobalTheory.Mem.Chr.CharModel.logNorm_local v _ 1 (unif_spec v), Complex.cpow_def_of_ne_zero (by exact_mod_cast h0),
      ← Complex.natCast_log]
    congr 1; push_cast; ring
  · change ‖Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm E x)‖ =
      ‖Complex.exp ((z.re : ℂ) * GlobalTheory.Mem.Chr.CharModel.logNorm E x)‖
    rw [Complex.norm_exp, Complex.norm_exp]; simp
  · have e : z = (z.re : ℂ) := Complex.ext rfl (by simpa using hz)
    conv_lhs => rw [e]
    rfl

end GlobalTheory.ResW

end
