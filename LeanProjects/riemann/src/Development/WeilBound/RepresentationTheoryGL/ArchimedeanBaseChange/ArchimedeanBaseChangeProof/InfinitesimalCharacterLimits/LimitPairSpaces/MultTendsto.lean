import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LimitPairSpaces.TensorSpanEqPairSpace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatNodeFunctionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NodeFunctionLeviDecompositionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TendstoAbsoluteCharacterOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatAbsoluteCharacterStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.LV

open PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.E

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mul_mem_Sm' {N : ℕ} {f g : GA E N → ℂ} (hf : f ∈ Sm E N) (hg : g ∈ Sm E N) :
    (fun x => f x * g x) ∈ Sm E N := by
  refine GlobalTheory.DiscSMO.mem_Sm_of_one fun x => ?_
  have h0 : oneL E N ∈ invSet E N := by
    have := val_mem_invSet (E := E) (1 : GL (Fin N) (Cinf E))
    rwa [Units.val_one] at this
  refine ((contDiffAt_chart hf x h0).mul (contDiffAt_chart hg x h0)).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_invSet.mem_nhds h0] with y hy
  obtain ⟨u, hu⟩ := hy
  have hy' : y = toL (u : GL (Fin N) (Cinf E)).val := by rw [hu]; rfl
  rw [hy', chart_val, chart_val, chart_val]

theorem mult_flat {N : ℕ} (b : Tr E N) (γ : ℕ → ℂ) : GlobalTheory.CompanionTheory.LimV.FlatFn (mult b γ) := by
  induction b generalizing γ with
  | leaf V z => exact GlobalTheory.T.flat_absolute_character _ _
  | node t₁ t₂ ih₁ ih₂ => exact GlobalTheory.T.flat_node_function _ _ (ih₁ _) (ih₂ _)

theorem mult_rinv {N : ℕ} (b : Tr E N) (γ : ℕ → ℂ) (x : GA E N) (k : Kinf E N) {c : GL (Fin N) (Af E)}
    (hc : c ∈ Cint E N) : mult b γ (x * InducedTensorMap.cf N k c) = mult b γ x :=
  (mult_flat b γ).rinv x k c hc

theorem mult_node {r s : ℕ} (t₁ : Tr E r) (t₂ : Tr E s) (γ : ℕ → ℂ) (u : BlockIx (r + s) r → Ad E)
    (m : GA E r × GA E s) (k : Kinf E (r + s)) {c : GL (Fin (r + s)) (Af E)} (hc : c ∈ Cint E (r + s)) :
    mult (Tr.node t₁ t₂) γ (unip u * lev (Ad E) r s m * InducedTensorMap.cf (r + s) k c) =
      mult t₁ γ m.1 * mult t₂ (fun i => γ (i + t₁.twists.length)) m.2 :=
  GlobalTheory.T.node_function_levi_decomposition _ _ (mult_flat _ _) (mult_flat _ _) u m k c hc

theorem mult_ne {N : ℕ} (b : Tr E N) (γ : ℕ → ℂ) (x : GA E N) : mult b γ x ≠ 0 :=
  (mult_flat b γ).ne x

theorem mult_tendsto {N : ℕ} (b : Tr E N) (γ : ℕ → ℕ → ℂ) (hγ : ∀ i, Tendsto (fun k => γ k i) atTop (𝓝 0))
    (x : GA E N) : Tendsto (fun k => mult b (γ k) x) atTop (𝓝 1) := by
  induction b generalizing γ with
  | leaf V z => exact GlobalTheory.T.tendsto_absolute_character_one _ x (fun k => γ k 0) (hγ 0)
  | node t₁ t₂ ih₁ ih₂ =>
    have h := (ih₁ γ hγ (GlobalTheory.CompanionTheory.LimV.leviOf x).1).mul
      (ih₂ (fun k i => γ k (i + t₁.twists.length)) (fun i => hγ _) (GlobalTheory.CompanionTheory.LimV.leviOf x).2)
    rw [one_mul] at h
    exact h

theorem mult_mem_Sm {N : ℕ} (b : Tr E N) (γ : ℕ → ℂ) : mult b γ ∈ Sm E N :=
  (mult_flat b γ).sm

end PositivityTheory.Rg.BcB.SpectralAccumulation.LV

end
