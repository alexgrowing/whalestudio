import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvFinMkPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepPureTensorLocalStatement

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine

noncomputable section

open scoped Classical

namespace GlobalTheory.VacEig

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem exists_schwartz_one (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∃ Φ : SchwartzMap V ℂ, Φ 0 = 1 := by
  let b : ContDiffBump (0 : V) := ⟨1, 2, one_pos, one_lt_two⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  refine ⟨h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff), ?_⟩
  change ((b 0 : ℝ) : ℂ) = 1
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)]
  simp

theorem eventually_int' (x : κ → AF F) :
    ∀ᶠ u in cofinite, ∀ i, evFin F u (x i) ∈ u.adicCompletionIntegers F :=
  Filter.eventually_all.mpr fun i => (x i).2.2

theorem finite_mulSupport' (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (hφ : ∀ᶠ u in cofinite, φ u = indO u)
    (x : κ → AF F) : (Function.mulSupport fun u => φ u (fun i => evFin F u (x i))).Finite := by
  have h : ∀ᶠ u in cofinite, φ u (fun i => evFin F u (x i)) = 1 := by
    filter_upwards [hφ, eventually_int' x] with u hu hx
    rw [hu]
    simp [indO, Set.indicator, hx]
  exact (Filter.eventually_cofinite.mp h).subset fun u hu hp => hu hp

theorem pure_split (f : SInf F κ) (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (hφ : ∀ᶠ u in cofinite, φ u = indO u)
    (v : Pl F) (x : κ → AF F) :
    pure f φ x = φ v (fun i => evFin F v (x i)) *
      (f (fun i => evI F (x i)) * ∏ᶠ (u) (_ : u ≠ v), φ u (fun i => evFin F u (x i))) := by
  have hfin := finite_mulSupport' _ hφ x
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
  rw [← mul_finprod_cond_ne v hfin]
  ring

theorem pure_update_split (f : SInf F κ) (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (hφ : ∀ᶠ u in cofinite, φ u = indO u)
    (v : Pl F) (g : (κ → Fv F v) → ℂ) (x : κ → AF F) :
    pure f (Function.update φ v g) x = g (fun i => evFin F v (x i)) *
      (f (fun i => evI F (x i)) * ∏ᶠ (u) (_ : u ≠ v), φ u (fun i => evFin F u (x i))) := by
  have hφ' : ∀ᶠ u in cofinite, Function.update φ v g u = indO u := by
    filter_upwards [hφ, (Set.finite_singleton v).compl_mem_cofinite] with u hu hv
    rw [Function.update_of_ne hv, hu]
  rw [pure_split f _ hφ' v x, Function.update_self]
  congr 2
  exact finprod_congr fun u => finprod_congr fun hu => by rw [Function.update_of_ne hu]

theorem vac_eig : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), M.IsGood ψ →
    ∀ c : Pl F → Matrix (Fin n) (Fin d) (AE F E) → ℂ,
    (∀ v, ∀ γ ∈ latAtV X W v, ∀ f : SInf F (Fin n × Fin d),
      M.co.rho ψ γ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) = c v γ • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) →
    ∀ v, ∀ γ ∈ latAtV X W v, locOp ψ v (locPt v (M.co.e γ)) (M.vac v) = c v γ • M.vac v := by
  intro F E _ _ _ _ _ σ n d X W M ψ hM c hc v γ hγ
  have hvacO : ∀ᶠ u in cofinite, M.vac u = indO u := by
    filter_upwards [hM.std] with u hu
    rw [hu]
    rfl
  obtain ⟨f, hf⟩ := exists_schwartz_one (Fin n × Fin d → mixedEmbedding.mixedSpace F)
  have e2 := hc v γ hγ f
  rw [GlobalTheory.T.weil_rep_pure_tensor_local M ψ v γ (at_latAtV hγ) f M.vac hvacO] at e2
  choose w hw using fun u => Function.ne_iff.mp (hM.vac u).2.1
  have hT : {u | M.vac u ≠ indO u ∧ u ≠ v}.Finite :=
    (Filter.eventually_cofinite.mp hvacO).subset fun u hu => hu.1
  set T := hT.toFinset with hTdef
  funext z
  set y : Fin n × Fin d → Af F := fun i => singleFin v (z i) + ∑ u ∈ T, singleFin u (w u i) with hy
  set x := mkPt (fun _ => (0 : mixedEmbedding.mixedSpace F)) y with hx
  have hxv : (fun i => evFin F v (x i)) = z := by
    funext i
    rw [hx, evFin_mkPt, hy]
    simp only [map_add, map_sum, evalV_singleFin_self]
    rw [Finset.sum_eq_zero, add_zero]
    intro u hu
    have : u ≠ v := (hT.mem_toFinset.mp hu).2
    exact evalV_singleFin_ne (Ne.symm this) _
  have hxu : ∀ u, u ≠ v → M.vac u (fun i => evFin F u (x i)) ≠ 0 := by
    intro u huv
    have hcomp : ∀ i, evFin F u (x i) = ∑ u' ∈ T, evalV F u (singleFin u' (w u' i)) := by
      intro i
      rw [hx, evFin_mkPt, hy]
      simp only [map_add, map_sum, evalV_singleFin_ne huv, zero_add]
    by_cases huT : u ∈ T
    · have : (fun i => evFin F u (x i)) = w u := by
        funext i
        rw [hcomp, Finset.sum_eq_single_of_mem u huT, evalV_singleFin_self]
        intro u' _ hne
        exact evalV_singleFin_ne (Ne.symm hne) _
      rw [this]
      exact hw u
    · have hstd : M.vac u = indO u := by
        by_contra h
        exact huT (hT.mem_toFinset.mpr ⟨h, huv⟩)
      have : (fun i => evFin F u (x i)) = 0 := by
        funext i
        rw [hcomp, Finset.sum_eq_zero]
        · rfl
        intro u' hu'
        have hne : u ≠ u' := fun h => huT (h ▸ hu')
        exact evalV_singleFin_ne hne _
      rw [this, hstd]
      simp [indO, Set.indicator, zero_mem]
  have hR : (f fun i => evI F (x i)) * ∏ᶠ (u) (_ : u ≠ v), M.vac u (fun i => evFin F u (x i)) ≠ 0 := by
    refine mul_ne_zero ?_ (finprod_ne_zero fun u => ?_)
    · have : (fun i => evI F (x i)) = 0 := by
        funext i
        rw [hx, evI_mkPt]
        rfl
      rw [this, hf]
      exact one_ne_zero
    · rw [finprod_eq_if]
      split_ifs with huv
      · exact hxu u huv
      · exact one_ne_zero
  have h := congrFun e2 x
  rw [Pi.smul_apply, smul_eq_mul, pure_update_split f M.vac hvacO v _ x, pure_split f M.vac hvacO v x, hxv] at h
  rw [Pi.smul_apply, smul_eq_mul]
  exact mul_right_cancel₀ hR (by linear_combination h)

end GlobalTheory.VacEig
