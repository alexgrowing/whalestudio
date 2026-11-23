import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CohomologicalCsdTemperedUnrOfFull
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU

noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CuspRep ValuativeRel
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CohomologicalConjSelfDualTempered.UnrModel

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem mem_integer_iff (x : w.adicCompletion E) : x ∈ 𝒪[w.adicCompletion E] ↔ x ∈ Formalism.UG.Ov (F := E) w := by
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [Valuation.mem_integer_iff, ← map_one (valuation _), ← Valuation.vle_iff_le, Valuation.vle_iff_le Valued.v, map_one]
  rfl

theorem range_eq {K : Type} [Field K] {A B : Subring K} (h : A = B) (n : ℕ) :
    (Formalism.UG.bc (n := Fin n) B.subtype).range = (Matrix.GeneralLinearGroup.map (n := Fin n) (algebraMap A K)).range := by
  subst h; rfl

theorem kgl_eq_ko (n : ℕ) : GlobalTheory.LFun.KGL w n = GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n) :=
  range_eq (SetLike.ext fun x => mem_integer_iff w x) n

theorem isSpherical_of_hasSatGL (n : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V} {B : Multiset ℂˣ} (h : GlobalTheory.LFun.HasSatGL w ρ B) :
    GlobalTheory.SmGL.IsSpherical ρ := by
  have h1 := h.1
  unfold GlobalTheory.LGrp.IsSpherical at h1
  unfold GlobalTheory.SmGL.IsSpherical GlobalTheory.SmGL.IsSphericalFor
  rwa [← kgl_eq_ko]

theorem isTemperedGL_of_hasSatGL (hT : GlobalTheory.CohomologicalConjSelfDualTempered.CohomologicalCsdTemperedUnr) (L : Type) [Field L] [NumberField L]
    [IsCMField L] (n : ℕ) (hn : 2 ≤ n) (π : CuspSub L n) (hc : π.IsCsd) (hcoh : GlobalTheory.GKCoh.IsCohomological π)
    (y : HeightOneSpectrum (𝓞 L)) (σ : SmIrr (GL (Fin n) (y.adicCompletion L))) (hσ : π.IsLocComp y σ)
    {B : Multiset ℂˣ} (hB : GlobalTheory.LFun.HasSatGL y σ.ρ B) : GlobalTheory.LocGL.IsTemperedGL σ.ρ :=
  hT L n hn π hc hcoh y σ hσ (isSpherical_of_hasSatGL y n hB)

theorem isSpherical_trivial (n : ℕ) :
    GlobalTheory.SmGL.IsSpherical (1 : Representation ℂ (GL (Fin n) (w.adicCompletion E)) ℂ) := by
  unfold GlobalTheory.SmGL.IsSpherical GlobalTheory.SmGL.IsSphericalFor
  rw [Submodule.ne_bot_iff]
  refine ⟨1, ?_, one_ne_zero⟩
  intro h
  simp

end GlobalTheory.CohomologicalConjSelfDualTempered.UnrModel
