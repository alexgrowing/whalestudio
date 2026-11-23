import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.CasselmanWallachAdm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SchurLemmaEquivariantPairBoundedFunctionsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CasselmanWallachOfHyp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormMapValuesCompactSobolevBound

noncomputable section

open Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta Matrix MeasureTheory GlobalTheory.SmoothGlob Filter
open GlobalTheory.TypeSum GlobalTheory.LowTypeDetermined
open scoped Topology

namespace GlobalTheory.CompanionTheory.SobComplete

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem Dw_sub_of_sm {σ : Mx n → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ) {l : List (Mx n)}
    (hl : ∀ X ∈ l, X ∈ lieSet ε) {x y : H} (hx : Sm ε σ x) (hy : Sm ε σ y) :
    Dw σ l (x - y) = Dw σ l x - Dw σ l y := by
  have hxy : Sm ε σ (x - y) := sm_iff.2 (Submodule.sub_mem _ (sm_iff.1 hx) (sm_iff.1 hy))
  have h := Dw_add hσ hl hxy hy
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

theorem tendsto_sobNorm_zero {σ : Mx n → (H →L[ℂ] H)} {u : ℕ → H} (S : List (List (Mx n)))
    (h : ∀ l ∈ S, Tendsto (fun k => ‖l.foldr (dRep σ) (u k)‖) atTop (𝓝 0)) :
    Tendsto (fun k => sobNorm σ S (u k)) atTop (𝓝 0) := by
  induction S with
  | nil => simpa [sobNorm] using tendsto_const_nhds
  | cons l S ih =>
    have h1 := h l List.mem_cons_self
    have h2 := ih fun l' hl' => h l' (List.mem_cons_of_mem _ hl')
    have h3 := h1.add h2
    rw [add_zero] at h3
    refine h3.congr fun k => ?_
    simp [sobNorm]

theorem smoothVec_complete_of_unitary (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (hσ : IsURepOn (UJset ε) σ) (w : ℕ → H) (hw : ∀ k, SmoothVec (lieSet ε) σ (w k))
    (hC : ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) → ∀ δ > 0,
      ∃ K, ∀ k ≥ K, ∀ m ≥ K, sobNorm σ S (w k - w m) < δ) :
    ∃ w₀, SmoothVec (lieSet ε) σ w₀ ∧ ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)),
      (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) → Tendsto (fun k => sobNorm σ S (w k - w₀)) atTop (𝓝 0) := by
  have hρ : ModRep ε σ := GlobalTheory.FamSmooth.modRep_of_isURepOn hσ
  have hmem : ∀ l : List (lie (Jm ε)), ∀ X ∈ l.map Subtype.val, X ∈ lieSet ε := fun l X hX => by
    obtain ⟨Y, -, rfl⟩ := List.mem_map.1 hX
    exact Y.2
  let U : ℕ → List (lie (Jm ε)) → H := fun k l => Dw σ (l.map Subtype.val) (w k)
  have hU : ∀ k, U k ∈ Fam ε σ := fun k => GlobalTheory.SobUnif.smooth_fam hσ (hw k)
  have hcau : ∀ l, CauchySeq fun k => U k l := fun l => by
    refine Metric.cauchySeq_iff.2 fun δ hδ => ?_
    obtain ⟨K, hK⟩ := hC [l.map Subtype.val] (by simpa using hmem l) δ hδ
    refine ⟨K, fun k hk m hm => ?_⟩
    rw [dist_eq_norm]
    show ‖Dw σ (l.map Subtype.val) (w k) - Dw σ (l.map Subtype.val) (w m)‖ < δ
    rw [← Dw_sub_of_sm hσ (hmem l) (hw k) (hw m)]
    exact (norm_Dw_le_sobNorm σ List.mem_cons_self _).trans_lt (hK k hk m hm)
  choose v hv using fun l => cauchySeq_tendsto_of_complete (hcau l)
  have hvF : v ∈ Fam ε σ :=
    (GlobalTheory.T.isClosed_derivativeFamilies_moderateGrowth n ε H σ hρ).mem_of_tendsto (tendsto_pi_nhds.2 hv) (Eventually.of_forall hU)
  obtain ⟨hs, hd⟩ := GlobalTheory.SobUnif.fam_smooth hσ hvF
  refine ⟨v [], hs, fun S hS => tendsto_sobNorm_zero S fun l hl => ?_⟩
  obtain ⟨l', rfl⟩ := GlobalTheory.SobUnif.exists_lift l (hS l hl)
  have h1 : Tendsto (fun k => U k l' - v l') atTop (𝓝 0) := by
    simpa using (hv l').sub_const (v l')
  have h2 := h1.norm
  rw [norm_zero] at h2
  refine h2.congr fun k => ?_
  show ‖Dw σ (l'.map Subtype.val) (w k) - v l'‖ = ‖Dw σ (l'.map Subtype.val) (w k - v [])‖
  rw [Dw_sub_of_sm hσ (hmem l') (hw k) hs, hd l']

theorem smoothVec_complete : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ w : ℕ → H, (∀ k, SmoothVec (lieSet ε) σ (w k)) → (∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) → ∀ δ > 0, ∃ K, ∀ k ≥ K, ∀ m ≥ K, sobNorm σ S (w k - w m) < δ) → ∃ w₀, SmoothVec (lieSet ε) σ w₀ ∧ ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), (∀ l ∈ S, ∀ X ∈ l, X ∈ lieSet ε) → Filter.Tendsto (fun k => sobNorm σ S (w k - w₀)) Filter.atTop (nhds 0) :=
  fun n ε H _ _ _ σ hσ _ w hw hC => smoothVec_complete_of_unitary n ε H σ hσ w hw hC

end GlobalTheory.CompanionTheory.SobComplete

end
