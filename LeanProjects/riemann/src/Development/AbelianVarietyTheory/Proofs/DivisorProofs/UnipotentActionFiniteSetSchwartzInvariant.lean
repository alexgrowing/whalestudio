import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncMatTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactOpenPlacesStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.ConeEuler
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

noncomputable section

namespace GlobalTheory.TruncFixOm

open scoped Classical

theorem om_archtriv : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (χX χW : Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ), GlobalTheory.ThK.ActsEx → GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ k : UA σ X.J, (∀ u : AF F, At (evI F) u → u • (mat k - 1) = 0) → ∀ (S : Finset (Pl F)) (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ), (∀ v, φ v ∈ SB (Fin n × Fin d → Fv F v)) → (∀ v ∉ S, φ v = M.vac v) → (∀ v ∉ S, Acts (evFin F v) (om (GlobalTheory.TruncFix.truncU {v} k, 1)) (M.vac v) (M.vac v)) → om (k, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (fun v => locOp v (om (GlobalTheory.TruncFix.truncU {v} k, 1)) (φ v)) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hA hP k hinf S f φ hSB hvac hloc
  classical
  set ψ' : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v => locOp v (om (GlobalTheory.TruncFix.truncU {v} k, 1)) (φ v) with hψ'
  have hone : ∀ v : Pl F, (1 : UA σ W.J) ∈ UAt σ W (evFin F v) := by
    intro v u _
    show u • (mat (1 : UA σ W.J) - 1) = 0
    rw [show mat (1 : UA σ W.J) = 1 from rfl, sub_self, smul_zero]
  have hoff : ∀ v ∉ S, ψ' v = φ v := by
    intro v hv
    show locOp v (om (GlobalTheory.TruncFix.truncU {v} k, 1)) (φ v) = φ v
    rw [hvac v hv]
    exact locOp_eq (hP.good.vac v).1 (hP.good.vac v).1 (hloc v hv)
  let fam : Finset (Pl F) → ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun T v => if v ∈ T then ψ' v else φ v
  have famSB : ∀ T v, fam T v ∈ SB (Fin n × Fin d → Fv F v) := by
    intro T v
    by_cases h : v ∈ T
    · simp only [fam, if_pos h]; exact locOp_mem _ _ _
    · simp only [fam, if_neg h]; exact hSB v
  have famcof : ∀ T, ∀ᶠ w in cofinite, fam T w = M.vac w := by
    intro T
    refine Filter.eventually_cofinite.2 ((T ∪ S).finite_toSet.subset fun w hw => by_contra fun h => hw ?_)
    have h1 : w ∉ T := fun h' => h (Finset.mem_coe.2 (Finset.mem_union_left _ h'))
    have h2 : w ∉ S := fun h' => h (Finset.mem_coe.2 (Finset.mem_union_right _ h'))
    simp only [fam, if_neg h1]; exact hvac w h2
  have famstd : ∀ T, ∀ᶠ w in cofinite, fam T w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
    fun T => ((famcof T).and hP.good.std).mono fun w hw => hw.1.trans hw.2
  have hstep : ∀ T : Finset (Pl F), om (GlobalTheory.TruncFix.truncU T k, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (fam T) := by
    intro T
    refine Finset.induction_on T ?_ ?_
    · have e : fam ∅ = φ := by funext v; simp [fam]
      rw [e, GlobalTheory.TruncFix.truncU_empty, show ((1 : UA σ X.J), (1 : UA σ W.J)) = 1 from rfl, map_one, Module.End.one_apply]
    · intro v T hv ih
      rw [GlobalTheory.TruncFix.truncU_insert hv, show (GlobalTheory.TruncFix.truncU {v} k * GlobalTheory.TruncFix.truncU T k, (1 : UA σ W.J)) =
        (GlobalTheory.TruncFix.truncU {v} k, (1 : UA σ W.J)) * (GlobalTheory.TruncFix.truncU T k, (1 : UA σ W.J)) by simp, map_mul,
        Module.End.mul_apply, ih]
      have hv' : fam T v = φ v := by simp only [fam, if_neg hv]
      have hAct : Acts (evFin F v) (om (GlobalTheory.TruncFix.truncU {v} k, 1)) (fam T v) (ψ' v) := by
        rw [hv']
        exact acts_locOp_om hA hP (GlobalTheory.TruncFix.truncU_mem_UAt v k) (hone v) (hSB v)
      rw [GlobalTheory.ThK.LocalOps.acts_pure v (om (GlobalTheory.TruncFix.truncU {v} k, 1)) f (fam T) (ψ' v)
        (GlobalTheory.ConeMeasV.pure_mem_schA hP.good f _ (famSB T) (famcof T))
        (fun x => GlobalTheory.PureFactor.mulSupport_finite _ (famstd T) x) hAct]
      congr 1
      funext w
      by_cases hw : w = v
      · subst hw; simp [fam]
      · rw [Function.update_of_ne hw]
        simp only [fam, Finset.mem_insert, hw, false_or]
  have hfinal : ∀ T : Finset (Pl F), S ⊆ T → fam T = ψ' := by
    intro T hST
    funext v
    by_cases h : v ∈ T
    · simp only [fam, if_pos h]
    · simp only [fam, if_neg h]; exact (hoff v fun h' => h (hST h')).symm
  have hpure : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ schA F _ :=
    GlobalTheory.ConeMeasV.pure_mem_schA hP.good f φ hSB (by simpa [fam] using famcof ∅)
  funext x
  have hc : Continuous fun g : UA σ X.J × UA σ W.J => om g (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x :=
    hP.weil.2.2 _ (GlobalTheory.TruncFix.eval_mem_adm _ x) _ hpure
  have h1 : Tendsto (fun T : Finset (Pl F) => om (GlobalTheory.TruncFix.truncU T k, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x) atTop
      (𝓝 (om (k, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x)) :=
    ((hc.comp (continuous_id.prodMk continuous_const)).tendsto k).comp (GlobalTheory.TruncFix.tendsto_truncU k hinf)
  have h2 : (fun T : Finset (Pl F) => om (GlobalTheory.TruncFix.truncU T k, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x) =ᶠ[atTop]
      fun _ => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f ψ' x :=
    (Filter.eventually_ge_atTop S).mono fun T hT => by
      show om (GlobalTheory.TruncFix.truncU T k, 1) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) x = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f ψ' x
      rw [hstep T, hfinal T hT]
  exact tendsto_nhds_unique (h1.congr' h2) tendsto_const_nhds

end GlobalTheory.TruncFixOm
