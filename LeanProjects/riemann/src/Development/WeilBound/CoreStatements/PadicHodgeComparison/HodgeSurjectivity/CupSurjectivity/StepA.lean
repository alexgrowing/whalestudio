import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.ProperGenMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem stepA (hC : CupLaws) (P : HTPre l K) {M : Model l K} {d : ℕ} (S : Sq M (d + 1)) (hEt : Etale S.D.f)
    (r : E.Roots l) (v : S.Y.T 2) (hv : IsEtaleFirstChernUntwisted r S.D v) (e : Hdg S.Y.q 1 2) (he : IsDlogFirstChernClass S.Y.q (genD S.D) e)
    (c : S.P.T (2 + 2 * d)) (w : S.Y.T (2 * d)) (z : S.Y.T (2 + 2 * d)) (hz : S.Y.CupT v w z)
    (hcz : S.Y.toV _ (Model.pullT S.π S.hπ _ c) = S.Y.toV _ z) (A : ℕ) (Θ : Module.Dual K (Hdg S.P.q A (2 + 2 * d)))
    (hΘ : ∀ C, (pullH (Model.genMap S.π S.hπ) (Model.genMap_q S.π S.hπ) A _ C = 0 ∨ ∃ (a₀ n₀ : ℕ) (ha : 1 + a₀ = A)
      (hn : 2 + n₀ = 2 + 2 * d) (w : Hdg S.Y.q a₀ n₀),
        pullH (Model.genMap S.π S.hπ) (Model.genMap_q S.π S.hπ) A _ C = cupH S.Y.q ha hn e w) → Θ C = 0) :
    P.h S.P A (2 + 2 * d) (S.P.toV _ c) Θ = 0 := by
  obtain ⟨φ, hφf, hφg⟩ : ∃ φ : Module.Dual K (Hdg S.Y.q A (2 + 2 * d)),
      φ ∘ₗ pullH (Model.genMap S.π S.hπ) (Model.genMap_q S.π S.hπ) A (2 + 2 * d) = Θ ∧
      ∀ (a₀ : ℕ) (ha : 1 + a₀ = A) (u : Hdg S.Y.q a₀ (2 * d)), φ (cupH S.Y.q ha rfl e u) = 0 := by
    rcases Nat.eq_zero_or_pos A with hA | hA
    · subst hA
      obtain ⟨φ, h1, -⟩ := la_kill (pullH (Model.genMap S.π S.hπ) (Model.genMap_q S.π S.hπ) 0 (2 + 2 * d))
        (0 : Hdg S.Y.q 0 (2 + 2 * d) →ₗ[K] Hdg S.Y.q 0 (2 + 2 * d)) Θ
        (fun C u h => hΘ C (Or.inl (by simpa using h)))
      exact ⟨φ, h1, fun a₀ ha => absurd ha (by omega)⟩
    · obtain ⟨a, rfl⟩ : ∃ a, A = 1 + a := ⟨A - 1, by omega⟩
      obtain ⟨φ, h1, h2⟩ := la_kill (pullH (Model.genMap S.π S.hπ) (Model.genMap_q S.π S.hπ) (1 + a) (2 + 2 * d))
        (cupL hC S.Y.q (a := 1) (a' := a) (c := 1 + a) (i := 2) (j := 2 * d) (n := 2 + 2 * d) rfl rfl e) Θ
        (fun C u h => hΘ C (Or.inr ⟨a, 2 * d, rfl, rfl, u, by rw [h, cupL_apply]⟩))
      refine ⟨φ, h1, fun a₀ ha u => ?_⟩
      obtain rfl : a₀ = a := by omega
      have := LinearMap.congr_fun h2 u
      simpa [cupL_apply] using this
  have hc1 := P.c1 S.Y S.smY S.D hEt S.loc r v e hv he
  let b : ∀ a, Module.Basis (Fin (Module.finrank K (Hdg S.Y.q a 2))) K (Hdg S.Y.q a 2) := fun a =>
    haveI := (P.fin S.Y S.smY a 2).1
    Module.finBasis K _
  let b' : ∀ a, Module.Basis (Fin (Module.finrank K (Hdg S.Y.q a (2 * d)))) K (Hdg S.Y.q a (2 * d)) := fun a =>
    haveI := (P.fin S.Y S.smY a (2 * d)).1
    Module.finBasis K _
  have key : ∀ (a a' : ℕ) (ha : a + a' = A), ∑ s, ∑ s', P.h S.Y a 2 (S.Y.toV _ v) ((b a).coord s) *
      P.h S.Y a' (2 * d) (S.Y.toV _ w) ((b' a').coord s') *
        kC K (φ (cupH S.Y.q ha rfl (b a s) (b' a' s'))) = 0 := by
    intro a a' ha
    by_cases h1 : a = 1
    · subst h1
      simp_rw [hc1.1]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun s' _ => ?_
      have hs := esum (kC K) (b 1) (φ ∘ₗ (cupL hC S.Y.q (i := 2) (j := 2 * d) ha rfl).flip (b' a' s')) e
      simp only [LinearMap.comp_apply, LinearMap.flip_apply, cupL_apply] at hs
      rw [hφg a' ha, map_zero] at hs
      calc ∑ s, kC K ((b 1).coord s e) * P.h S.Y a' (2 * d) (S.Y.toV _ w) ((b' a').coord s') *
            kC K (φ (cupH S.Y.q ha rfl (b 1 s) (b' a' s')))
          = P.h S.Y a' (2 * d) (S.Y.toV _ w) ((b' a').coord s') *
            ∑ s, kC K ((b 1).coord s e) * kC K (φ (cupH S.Y.q ha rfl (b 1 s) (b' a' s'))) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun s _ => ?_
            ring
        _ = 0 := by rw [hs, mul_zero]
    · refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun s' _ => ?_
      rw [hc1.2 a h1, zero_mul, zero_mul]
  rw [← hφf, ← P.nat S.Y S.P S.π S.hπ S.smY S.smP A (2 + 2 * d) (S.P.toV _ c) φ, pullV_toV, hcz,
    P.cup S.Y S.smY v w z hz b b' A φ]
  exact Finset.sum_eq_zero fun p _ => key _ _ _

end CrystallineSemistableComparison.Onto

end
