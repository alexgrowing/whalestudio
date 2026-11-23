import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NodeFunctionLeviDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV.NodeFlat

theorem flatFn_nodeFn : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ} (e₁ : GA E r → ℂ) (e₂ : GA E s → ℂ), FlatFn e₁ → FlatFn e₂ → FlatFn (nodeFn e₁ e₂) := by
  intro E _ _ _ r s e₁ e₂ h₁ h₂
  have ap : ∀ (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s))
      (c : GL (Fin (r + s)) (Af E)), c ∈ KO E (r + s) →
      nodeFn e₁ e₂ (unip u * lev (Ad E) r s m * cf (r + s) k c) = e₁ m.1 * e₂ m.2 :=
    fun u m k c hc => GlobalTheory.T.node_function_levi_decomposition e₁ e₂ h₁ h₂ u m k c hc
  have hleft : ∀ (v : BlockIx (r + s) r → Ad E) (x : GA E (r + s)),
      nodeFn e₁ e₂ (unip v * x) = nodeFn e₁ e₂ x := by
    intro v x
    obtain ⟨u, m, k, c, hc, rfl⟩ := exists_iw x
    rw [← mul_assoc, ← mul_assoc, ← PositivityTheory.Rg.Rs.InducedTensorMap.D.unip_add', ap _ _ _ _ hc, ap _ _ _ _ hc]
  have hright : ∀ (x : GA E (r + s)) (k' : Kinf E (r + s)), ∀ c' ∈ KO E (r + s),
      nodeFn e₁ e₂ (x * cf (r + s) k' c') = nodeFn e₁ e₂ x := by
    intro x k' c' hc'
    obtain ⟨u, m, k, c, hc, rfl⟩ := exists_iw x
    rw [mul_assoc _ (cf (r + s) k c), PositivityTheory.Rg.Rs.InducedTensorMap.cf_mul,
      ap _ _ _ _ ((KO E (r + s)).mul_mem hc hc'), ap _ _ _ _ hc]
  have key : ∀ m : GA E r × GA E s,
      ContDiffAt ℝ ∞ (chart (nodeFn e₁ e₂) (lev (Ad E) r s m)) (oneL E (r + s)) := by
    intro m
    obtain ⟨b₁, b₂, κ, u, hb₁, hb₂, hκ, hb₁1, hb₂1, hκ1, hloc⟩ := exists_local E r s
    have c₁ : ContDiffAt ℝ ∞ (fun y => e₁ (m.1 * infGL E r (b₁ y))) (oneL E (r + s)) := by
      have := (contDiffAt_chart h₁.sm m.1 (val_mem_invSet (b₁ (oneL E (r + s))))).comp (oneL E (r + s)) hb₁
      simpa only [Function.comp_def, chart_val] using this
    have c₂ : ContDiffAt ℝ ∞ (fun y => e₂ (m.2 * infGL E s (b₂ y))) (oneL E (r + s)) := by
      have := (contDiffAt_chart h₂.sm m.2 (val_mem_invSet (b₂ (oneL E (r + s))))).comp (oneL E (r + s)) hb₂
      simpa only [Function.comp_def, chart_val] using this
    refine ContDiffAt.congr_of_eventuallyEq (c₁.mul c₂) ?_
    filter_upwards [hloc] with y hy
    have hyw : y = toL (unip (u y) * lev (Cinf E) r s (b₁ y, b₂ y) * Unitary.toUnits (κ y)).val := by
      show y = toL ((unip (u y) * lev (Cinf E) r s (b₁ y, b₂ y)).val * (κ y).1)
      rw [← hy]
      rfl
    conv_lhs => rw [hyw, chart_val]
    obtain ⟨v, hv⟩ := lev_mul_infGL m (u y) (b₁ y) (b₂ y) (κ y)
    rw [hv, ap _ _ _ _ ((KO E (r + s)).one_mem)]
  refine ⟨fun x => ?_, hright, ?_⟩
  · obtain ⟨u, m, k, c, hc, rfl⟩ := exists_iw x
    rw [ap _ _ _ _ hc]
    exact mul_ne_zero (h₁.ne _) (h₂.ne _)
  refine GlobalTheory.DiscSMO.mem_Sm_of_one fun x => ?_
  obtain ⟨u, m, k, g, hg, rfl⟩ := exists_iw x
  have e1 : chart (nodeFn e₁ e₂) (unip u * lev (Ad E) r s m * cf (r + s) k g) =
      chart (nodeFn e₁ e₂) (lev (Ad E) r s m * cf (r + s) k g) := by
    funext z
    unfold chart
    split_ifs
    · simp only [mul_assoc]
      exact hleft u _
    · rfl
  rw [e1, cf, infGL_comm, ← mul_assoc]
  refine GlobalTheory.DiscSMO.contDiffAt_chart_mul ?_
  rw [← chart_rt_fin]
  have e2 : (fun x => (fun x => nodeFn e₁ e₂ (x * infGL E (r + s) (Unitary.toUnits k))) (x * finGL E (r + s) g)) =
      nodeFn e₁ e₂ := by
    funext z
    show nodeFn e₁ e₂ (z * finGL E (r + s) g * infGL E (r + s) (Unitary.toUnits k)) = nodeFn e₁ e₂ z
    rw [mul_assoc, ← infGL_comm]
    exact hright z k g hg
  rw [e2]
  exact key m

end GlobalTheory.CompanionTheory.LimV.NodeFlat
