import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalStabilizerLocallyCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajorantStabilizerIwasawaLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerCommutesMajorant
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot
open Formalism.L2.Host (aboveF)
open Formalism.UG (IsUnifV qV)

noncomputable section

namespace GlobalTheory.SplitChart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

theorem proj_eq_one_of_ne {Y : Spc F E n} {v w : Pl F} (g : UAtSub σ Y (evFin F v)) (hw : w ≠ v) :
    proj σ Y.Jᵀ w (GlobalTheory.LocUnitaryUnimod.toHAe σ Y.J g.1) = 1 := by
  refine GlobalTheory.AutFunCompare.HA_ext σ Y.Jᵀ fun r s => ?_
  have hat : At (evFin F v) ((mat g.1 - 1) r s) := fun u hu => by
    have := congrFun (congrFun (g.2 u hu) r) s
    simpa [smul_sub] using this
  have h0 := (at_evFin_iff.1 hat).2 w hw
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h0
  change (HA.mat (Fv F w) σ Y.Jᵀ (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapH σ Y.Jᵀ (evFin F w) (GlobalTheory.LocUnitaryUnimod.toHAe σ Y.J g.1)) :
    Matrix (Fin n) (Fin n) (Fv F w ⊗[F] E)) r s = _
  rw [GlobalTheory.AutFunCompare.mat_mapH]
  change compFin F E w (mat g.1 r s) = _
  rw [h0, show HA.mat _ σ Y.Jᵀ 1 = 1 from map_one (matHom _ σ Y.Jᵀ)]
  by_cases h : r = s
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

theorem projArch_eq_one {Y : Spc F E n} {v : Pl F} (g : UAtSub σ Y (evFin F v)) (w : InfinitePlace F) :
    projArch σ Y.Jᵀ w (GlobalTheory.LocUnitaryUnimod.toHAe σ Y.J g.1) = 1 := by
  refine GlobalTheory.AutFunCompare.HA_ext σ Y.Jᵀ fun r s => ?_
  have hat : At (evFin F v) ((mat g.1 - 1) r s) := fun u hu => by
    have := congrFun (congrFun (g.2 u hu) r) s
    simpa [smul_sub] using this
  have h0 := (at_evFin_iff.1 hat).1 w
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at h0
  change (HA.mat w.Completion σ Y.Jᵀ (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapH σ Y.Jᵀ (evInf F w) (GlobalTheory.LocUnitaryUnimod.toHAe σ Y.J g.1)) :
    Matrix (Fin n) (Fin n) (w.Completion ⊗[F] E)) r s = _
  rw [GlobalTheory.AutFunCompare.mat_mapH]
  change compInf F E w (mat g.1 r s) = _
  rw [h0, show HA.mat _ σ Y.Jᵀ 1 = 1 from map_one (matHom _ σ Y.Jᵀ)]
  by_cases h : r = s
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

theorem chart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n : ℕ) (Y : Spc F E n), IsCMExt F E σ → IsHermND σ Y.J → Y.L.IsLattice E →
    ∀ v : Pl F, IsSelfDualAt σ Y.Jᵀ Y.L v → ∀ K : Subgroup (UA σ Y.J), IsStab B K →
    ∀ (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)), IsSplitBasis t Y.L b →
    ∃ e : UAtSub σ Y (evFin F v) ≃ₜ* GL (Fin n) (Fv F v), (∀ g, e g = GlobalTheory.KSplit.locMat t b g.1) ∧
      ∀ g, g.1 ∈ K ↔ e g ∈ KGL v n := by
  intro F E _ _ _ _ _ σ B n Y hcm hY hL v hSD K hK t b hb
  have hJt : IsHermND σ Y.Jᵀ := ⟨fun i j => hY.1 j i, by rw [Matrix.det_transpose]; exact hY.2⟩
  refine ⟨(GlobalTheory.LocUnitaryUnimod.locEquiv σ v Y).trans (splitEquivIn hcm hJt t b), fun g => ?_, fun g => ?_⟩
  · refine Units.ext ?_
    change (b⁻¹).1 * ((matHom _ σ Y.Jᵀ (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.mapH σ Y.Jᵀ (evFin F v)
      (GlobalTheory.LocUnitaryUnimod.toHAe σ Y.J g.1))).1.map (splitProj t)) * b.1 =
        (b⁻¹).1 * (mat g.1).map (piW t) * b.1
    congr 2
  · set h := GlobalTheory.LocUnitaryUnimod.toHAe σ Y.J g.1 with hh
    have hg : GlobalTheory.IwLine.ofGAd σ Y.J h = g.1 := Subtype.ext rfl
    have hloc : (GlobalTheory.LocUnitaryUnimod.locEquiv σ v Y) g = proj σ Y.Jᵀ v h := rfl
    rw [(hK _).trans (GlobalTheory.StabHaar.isStab_stabK B Y _).symm, ← hg]
    change _ ↔ splitEquivIn hcm hJt t b ((GlobalTheory.LocUnitaryUnimod.locEquiv σ v Y) g) ∈
      Formalism.UG.GLint (Fin n) (v.adicCompletionIntegers F).toSubring
    rw [hloc, ← mem_stabLoc_iff_GLint hcm hJt hSD hb]
    constructor
    · intro H
      exact (GlobalTheory.KBridgeConv.local_of_ofGAd_mem_stabK F E σ B n Y hL h H).2 v
    · intro H
      refine GlobalTheory.KBridge.ofGAd_mem_stabK F E σ B n Y hL h (fun w => ?_) (fun w => ?_)
      · rw [hh, projArch_eq_one g w]
        simp
      · by_cases hw : w = v
        · subst hw; exact H
        · rw [hh, proj_eq_one_of_ne g hw]; exact one_mem _

end GlobalTheory.SplitChart

end
