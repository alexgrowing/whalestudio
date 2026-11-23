import Mathlib
import Formalism.SharpRestriction.Divisibility.HookProducts.AdmPerTw
import Formalism.SharpRestriction.Divisibility.HookProducts.AdmPtTw
import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField

namespace GlobalTheory.PerRedU

theorem perTwAt_of_perDecTw {D : D7} {Dx : DivX D} {T : TwForms D} (hD : DGamDef D) {u : D.what₂.Word} {μ : D.what₂.Tup}
    (h : Formalism.MainNotions.RT.PeriodPointConditions.PerDecTw D Dx T u μ) :
    ∀ x ∈ (T.fm u μ).ptLat.L, ∀ F ∈ (D.what₂.Mtilde μ).carrier, F ∈ D.what₂.V0 μ →
      ∃ y : D.what₂.LL, D.what₂.embLL y = (D.PTw u μ).period ((T.fm u μ).ptEmb x) ((D.eMtTw u μ).symm F) ∧
        ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w ∉ Dx.Qp μ →
          y = 0 ∨ -ur D w (Formalism.MainNotions.WeilJacquetShalikaLaw.vDG D u w) ≤ (vAdd (D.plEq w) y : ℝ) := by
  intro x hx F hF _
  obtain ⟨pc, hs, hi⟩ := h
  choose y hy hv using hi x hx F hF
  refine ⟨∑ c, ((Nat.card ((T.fm u μ).stabilizer₂ c) : ℕ) : D.what₂.LL)⁻¹ * y c, ?_, fun w hw => ?_⟩
  · rw [hs, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul, map_inv₀, map_natCast, hy c]
  · refine Finset.sum_induction _ (fun t => t = 0 ∨ -ur D w (Formalism.MainNotions.WeilJacquetShalikaLaw.vDG D u w) ≤ (vAdd (D.plEq w) t : ℝ))
      (fun a b ha hb => Formalism.MainNotions.WeightDegreeSizes.pair_add_ge D w ha hb) (Or.inl rfl) fun c _ => ?_
    rcases hv c w hw with h0 | h0
    · left; rw [h0, mul_zero]
    by_cases hy0 : y c = 0
    · left; rw [hy0, mul_zero]
    right
    have hn0 : ((Nat.card ((T.fm u μ).stabilizer₂ c) : ℕ) : D.what₂.LL) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    rw [Formalism.MainNotions.OrbitPlaces.vAdd_mul w (inv_ne_zero hn0) hy0, Formalism.MainNotions.OrbitPlaces.vAdd_inv w hn0]
    have hb := Formalism.MainNotions.DIV.HookProducts.AdmPerTw.vAdd_dvd_le (D := D) w (D.mem u).C.DGam_pos.ne'
      (Formalism.MainNotions.DIV.HookProducts.AdmPerTw.card_stabilizer_dvd₂ hD T u μ c)
    have h0' : (0 : ℝ) ≤ (vAdd (D.plEq w) (y c) : ℝ) := by exact_mod_cast h0
    unfold Formalism.MainNotions.WeilJacquetShalikaLaw.vDG
    push_cast
    linarith

theorem exists_muAt_of_usedT {D : D7} {μ : D.what₂.Tup} (hU : Formalism.MainNotions.LocalQuadraticParts.UsedT D μ) (hμ : μ ≠ D.what₂.mu0) :
    ∃ w, μ = D.what₂.muAt w :=
  hU.resolve_left hμ

theorem admissiblePeriodTwists_of_periodDecompositions {D : D7} {Dx : DivX D} {T : TwForms D}
    (h : ∀ u μ, μ ≠ D.what₂.mu0 → (∃ w, μ = D.what₂.muAt w) → Formalism.MainNotions.RT.PeriodPointConditions.PerDecTw D Dx T u μ) :
    Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible D Dx T :=
  fun hD u μ hU hμ => perTwAt_of_perDecTw hD (h u μ hμ (exists_muAt_of_usedT hU hμ))

theorem main : ∀ (D : D7) (Dx : DivX D) (T : TwForms D), (∀ u μ, μ ≠ D.what₂.mu0 → (∃ w, μ = D.what₂.muAt w) → Formalism.MainNotions.RT.PeriodPointConditions.PerDecTw D Dx T u μ) → Formalism.L2.G.Adm2InU.TwistedPeriodAdmissible D Dx T :=
  fun _ _ _ h => admissiblePeriodTwists_of_periodDecompositions h

end GlobalTheory.PerRedU

end
