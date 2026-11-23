import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

open scoped Classical

theorem GlobalTheory.TripleAssembly.vac_fixed_of_pure_fixed : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Y Wd) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Wd.J)
    (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)), M.vac v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v) →
    (∀ w ∉ S, M.vac w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1) →
    (∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F w) → ℂ),
      (∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F w)) → (∀ w ∉ S, φ w = M.vac w) →
      om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) →
    ∀ ψ : (Fin n × Fin d → Fv F v) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, k)) (M.vac v) ψ → ψ = M.vac v := by
  intro F E _ _ _ _ _ σ n d Y Wd M om v k S hvac hstd hfix ψ hψ
  let ind : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F w) → ℂ :=
    fun w => Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1

  let φ := Function.update ind v (M.vac v)
  have hφv : φ v = M.vac v := by simp [φ]
  have hφw : ∀ w, w ≠ v → φ w = ind w := fun w h => by simp [φ, h]
  have hφev : ∀ᶠ w in Filter.cofinite,
      φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 := by
    rw [Filter.eventually_cofinite]
    refine (Set.finite_singleton v).subset fun w hw => ?_
    by_contra hne
    exact hw (hφw w hne)
  have hSB : ∀ w, φ w ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F w) := by
    intro w
    by_cases h : w = v
    · subst h; rw [hφv]; exact hvac
    · rw [hφw w h]; exact GlobalTheory.StdVacuum.indicator_mem_SB w
  obtain ⟨f, hf⟩ := GlobalTheory.TensUniq.exists_sInf_ne_zero F (Fin n × Fin d)
  obtain ⟨r, hrinv, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hφev
  have hupd : ∀ ψ₀, Function.update φ v ψ₀ = Function.update ind v ψ₀ :=
    fun ψ₀ => Function.update_idem _ _ _

  have hfixφ : om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
    refine hfix f φ hSB fun w hw => ?_
    by_cases h : w = v
    · subst h; exact hφv
    · rw [hφw w h, hstd w hw]
  have hpv : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) (M.vac v) r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
    rw [hrt, hupd]
  have hRest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.AdelicU.evFin F v) (M.vac v) r := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest
    refine ⟨hrinv, ?_⟩
    rw [hpv]
    exact GlobalTheory.TensUniq.pure_mem_schA f φ hSB hφev
  have key : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) ψ r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) (M.vac v) r := by
    rw [← hψ r hRest, hpv, hfixφ]

  have hr0 : r 0 ≠ 0 := by
    have h1 := congrFun (hrt (fun _ => 1)) 0
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, one_mul] at h1
    rw [h1, hupd]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
    have e1 : (fun i : Fin n × Fin d => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((0 : Fin n × Fin d → AF F) i)) = 0 := by
      funext i
      show InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : Fin n × Fin d → AF F) i).1 = 0
      exact map_zero _
    have e2 : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, Function.update ind v (fun _ => 1) w
        (fun i => GlobalTheory.AdelicU.evFin F w ((0 : Fin n × Fin d → AF F) i)) = 1 := by
      intro w
      by_cases h : w = v
      · subst h; simp
      · rw [Function.update_of_ne h]
        show Set.indicator {x : Fin n × Fin d → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F} 1
          (fun i => GlobalTheory.AdelicU.evFin F w ((0 : Fin n × Fin d → AF F) i)) = 1
        rw [Set.indicator_of_mem]
        · rfl
        · simp only [Set.mem_setOf_eq, Pi.zero_apply, map_zero]
          exact fun _ => zero_mem _
    rw [e1, finprod_congr e2, finprod_one, mul_one]
    exact hf
  funext y
  have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (fun i => GlobalTheory.EmbChart.atPlace v (y i)) := by
    intro u hu
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [mul_comm, GlobalTheory.EmbChart.atPlace_mul_right, hu, mul_zero, map_zero]
  have hrz : r (fun i => GlobalTheory.EmbChart.atPlace v (y i)) = r 0 := by
    simpa using hrinv 0 _ hz
  have h2 := congrFun key (fun i => GlobalTheory.EmbChart.atPlace v (y i))
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, GlobalTheory.EmbChart.evFin_atPlace, hrz] at h2
  exact mul_right_cancel₀ hr0 h2
