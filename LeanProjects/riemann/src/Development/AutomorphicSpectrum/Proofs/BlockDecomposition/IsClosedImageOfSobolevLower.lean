import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CasselmanWallachAdm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurLemmaEquivariantPairBoundedFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CasselmanWallachOfHyp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVecCompleteOfUnitary

noncomputable section

open Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta Matrix MeasureTheory GlobalTheory.SmoothGlob

namespace GlobalTheory.CompanionTheory.SmoothClosed

theorem smoothVec_sub {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Lie : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {u v : H}
    (hu : SmoothVec Lie σ u) (hv : SmoothVec Lie σ v) : SmoothVec Lie σ (u - v) := by
  intro k Xs hX
  simpa only [map_sub] using (hu k Xs hX).sub (hv k Xs hX)

theorem tendsto_seminorm_sub {E : Type} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    {q : Seminorm ℂ E} (hq : Continuous q) {u : ℕ → E} {y : E} (hu : Filter.Tendsto u Filter.atTop (nhds y)) :
    Filter.Tendsto (fun k => q (u k - y)) Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun k => u k - y) Filter.atTop (nhds (y - y)) := hu.sub_const y
  rw [sub_self] at h
  simpa [Function.comp_def, map_zero] using (hq.tendsto 0).comp h

theorem isClosed_image_of_sobolev_lower : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ (E : Type) [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [T2Space E] (p : ℕ → Seminorm ℂ E) (π dπ : Matrix (Fin n) (Fin n) ℂ → (E →L[ℂ] E)), IsSmoothModRep ε p π dπ → ∀ T : H →ₗ[ℂ] E, IsSmoothGMap ε σ p π T → (∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) → ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ w, SmoothVec (lieSet ε) σ w → sobNorm σ S w ≤ q (T w)) → IsClosed (T '' {w | SmoothVec (lieSet ε) σ w}) := by
  intro n ε H _ _ _ σ hU hI E _ _ _ _ _ _ p π dπ hmod T hT hlow
  haveI : FirstCountableTopology E := hmod.withSeminorms.firstCountableTopology
  refine IsSeqClosed.isClosed ?_
  intro x y hx hxy
  choose w hw hTw using hx
  have hcauchy : ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) →
      ∀ δ > 0, ∃ K, ∀ k ≥ K, ∀ m ≥ K, sobNorm σ S (w k - w m) < δ := by
    intro S hS δ hδ
    obtain ⟨q, hq, hqb⟩ := hlow S hS
    have ht := tendsto_seminorm_sub hq hxy
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.1 (ht.eventually (gt_mem_nhds (half_pos hδ)))
    refine ⟨K, fun k hk m hm => ?_⟩
    calc sobNorm σ S (w k - w m) ≤ q (T (w k - w m)) := hqb _ (smoothVec_sub (hw k) (hw m))
      _ = q ((x k - y) - (x m - y)) := by rw [T.map_sub, hTw, hTw, sub_sub_sub_cancel_right]
      _ ≤ q (x k - y) + q (x m - y) := map_sub_le_add q _ _
      _ < δ / 2 + δ / 2 := add_lt_add (hK k hk) (hK m hm)
      _ = δ := add_halves δ
  obtain ⟨w0, hw0, hconv⟩ := GlobalTheory.CompanionTheory.SobComplete.smoothVec_complete n ε H σ hU hI w hw hcauchy
  refine ⟨w0, hw0, ?_⟩
  obtain ⟨-, hT2⟩ := hT
  have hT' : Filter.Tendsto (fun k => T (w k)) Filter.atTop (nhds (T w0)) := by
    refine (hmod.withSeminorms.tendsto_nhds _ _).2 ?_
    intro i δ hδ
    obtain ⟨S, C, hS, hb⟩ := hT2 i
    have hC : Filter.Tendsto (fun k => C * sobNorm σ S (w k - w0)) Filter.atTop (nhds 0) := by
      simpa using (hconv S hS).const_mul C
    filter_upwards [hC.eventually (gt_mem_nhds hδ)] with k hk
    calc p i (T (w k) - T w0) = p i (T (w k - w0)) := by rw [T.map_sub]
      _ ≤ C * sobNorm σ S (w k - w0) := hb _ (smoothVec_sub (hw k) hw0)
      _ < δ := hk
  have hx' : Filter.Tendsto (fun k => T (w k)) Filter.atTop (nhds y) := by
    simp only [hTw]
    exact hxy
  exact tendsto_nhds_unique hT' hx'

end GlobalTheory.CompanionTheory.SmoothClosed

end
