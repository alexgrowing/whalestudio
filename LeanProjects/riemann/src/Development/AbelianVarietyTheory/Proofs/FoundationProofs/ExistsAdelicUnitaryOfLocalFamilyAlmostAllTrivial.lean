import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReLatSelf
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.AdelicUnitaryGroups
import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalUnitaryGlue

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups GlobalTheory.AutFunCompare

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

theorem exists_on_finset (γ : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J)
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∃ k : HA (Af F) σ J, (∀ v ∈ S, mapH σ J (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) k = γ v) ∧
      ∀ v ∉ S, mapH σ J (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) k = 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, fun v hv => absurd hv (Finset.notMem_empty v), fun v _ => map_one _⟩
  | insert a S ha ih =>
    obtain ⟨k, h1, h2⟩ := ih
    have s1 : mapH σ J (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F a) (extH σ J (sgV a) (sgV_mul a) (γ a)) = γ a :=
      mapH_extH_self σ J _ _ _ (fun y => Pi.single_eq_same a y) _
    have s2 : ∀ w, w ≠ a →
        mapH σ J (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w) (extH σ J (sgV a) (sgV_mul a) (γ a)) = 1 :=
      fun w hw => mapH_extH_zero σ J _ _ _ (fun y => Pi.single_eq_of_ne hw y) _
    refine ⟨extH σ J (sgV a) (sgV_mul a) (γ a) * k, fun v hv => ?_, fun v hv => ?_⟩
    · rw [map_mul]
      rcases Finset.mem_insert.1 hv with rfl | hv
      · rw [s1, h2 _ ha, mul_one]
      · rw [s2 v (fun e => ha (e ▸ hv)), h1 v hv, one_mul]
    · rw [Finset.mem_insert, not_or] at hv
      rw [map_mul, s2 v hv.1, h2 v hv.2, one_mul]

theorem exists_of_finite (γ : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ J)
    (h : {v | γ v ≠ 1}.Finite) :
    ∃ k : HA (Af F) σ J, ∀ v, mapH σ J (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) k = γ v := by
  obtain ⟨k, h1, h2⟩ := exists_on_finset σ J γ h.toFinset
  refine ⟨k, fun v => ?_⟩
  by_cases hv : v ∈ h.toFinset
  · exact h1 v hv
  · rw [h2 v hv]
    simpa [eq_comm] using hv

end Gen

theorem exists_finite_adelic : ∀ (D : D7) (V : HSp D) (γ : ∀ v : HeightOneSpectrum (𝓞 D.host.F), HA (Fv D.host.F v) D.sp.cm.sig V.gram), {v | γ v ≠ 1}.Finite → ∃ k ∈ GfC V, ∀ v : HeightOneSpectrum (𝓞 D.host.F), (finMat D.sp.cm.sig V.gram k).map (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV D.host.F v) (AlgHom.id D.host.F D.host.E)) = (HA.mat (Fv D.host.F v) D.sp.cm.sig V.gram (γ v)).1 := by
  intro D V γ h
  obtain ⟨k, hk⟩ := exists_of_finite D.sp.cm.sig V.gram γ h
  refine ⟨ofFin D.sp.cm V k, ?_, fun v => ?_⟩
  · exact congrArg (HA.mat _ _ _) (projInf_ofFin D.sp.cm V k)
  · have e : finMat D.sp.cm.sig V.gram (ofFin D.sp.cm V k) = (HA.mat _ _ _ k).1 :=
      congrArg (fun x => (HA.mat _ _ _ x).1) (projFin_ofFin D.sp.cm V k)
    rw [e, ← hk v]
    rfl

end GlobalTheory.LocalUnitaryGlue
