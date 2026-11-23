import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContractionLieDerivativeDivPowerCompatFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamAlgebraQuotientRingSurjectiveAndKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivPowerCompatRelFiltrationTwoSidedRelEqBotOfBasStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

set_option autoImplicit false

namespace GlobalTheory.PDForm

theorem quot_fil_rel : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (J : Ideal B) (δ : DividedPowers J) (G : Type) [CommRing G] [Algebra R G] (J' : Ideal G) (δ' : DividedPowers J') (q : B →+* G) (h : SemiHom (RingHom.id R) q) (n : ℕ), IsDPMorphism δ δ' q → Function.Surjective q → J' = J.map q → (∀ b, q b = 0 ↔ b ∈ fil δ (n + 1)) → (∀ x, h.mDR x ∈ rel R δ' → x ∈ filDR R δ n) ∧ ∀ x ∈ filDR R δ (n + 1), h.mDR x ∈ rel R δ' := by
  intro R B _ _ _ J δ G _ _ J' δ' q h n hd hq hJ hk
  obtain ⟨-, -, hsurj, hker⟩ := GlobalTheory.T.deRhamAlgebra_quotientRing_surjective_and_kernel R B G q h hq
  obtain ⟨-, -, hmul, -, -, hanti, -⟩ := (GlobalTheory.T.divPowerCompatRel_filtration_twoSided_rel_eq_bot_of_base).1 R B J δ
  have hv : ∀ m, ∀ a ∈ J, (0 : Derivation R B B) (δ.dpow (m + 1) a) = δ.dpow m a * (0 : Derivation R B B) a := by
    intro m a _; simp
  have hd0 := ((GlobalTheory.T.contraction_lieDerivative_divPowerCompat_filtration_rules).2 R B J δ 0 hv n).2.1
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  ·
    have hle : rel R δ' ≤ (rel R δ).map h.mDR := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨m, a', ha', rfl⟩
      rw [hJ, Ideal.mem_map_iff_of_surjective _ hq] at ha'
      obtain ⟨a, ha, rfl⟩ := ha'
      have e : ι1 (D R G (δ'.dpow (m + 1) (q a)) - δ'.dpow m (q a) • D R G (q a)) =
          h.mDR (ι1 (D R B (δ.dpow (m + 1) a) - δ.dpow m a • D R B a)) := by
        rw [h.mDR_ι, map_sub h.m1, h.m1_D, h.oneFormMap_smul_semilinear, h.m1_D, hd.2 a ha, hd.2 a ha]
      rw [e]
      exact Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨m, a, ha, rfl⟩)
    obtain ⟨y, hy, hxy⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).1 (hle hx)
    have hK : x - y ∈ filDR R δ n := by
      refine hker (filDR R δ n) (hmul n) (fun b hb ↦ ?_) (x - y) (by rw [map_sub, hxy, sub_self])
      have hb1 : algebraMap B (DR R B) b ∈ filDR R δ (n + 1) :=
        Ideal.mem_sup_left (Ideal.subset_span ⟨b, (hk b).1 hb, rfl⟩)
      refine ⟨hanti n (n + 1) (Nat.le_succ n) hb1, ?_⟩
      rw [← dDR_algebraMap]
      exact hd0 _ hb1
    have hyn : y ∈ filDR R δ n := Ideal.mem_sup_right hy
    simpa using add_mem hK hyn
  · have hle : filDR R δ (n + 1) ≤ (rel R δ').comap h.mDR := by
      refine sup_le (Ideal.span_le.2 ?_) (fun z hz ↦ mDR_mem_rel h hd hz)
      rintro _ ⟨b, hb, rfl⟩
      change h.mDR (algebraMap B _ b) ∈ rel R δ'
      rw [h.mDR_algebraMap, (hk b).2 hb, map_zero]
      exact zero_mem _
    exact hle hx

end GlobalTheory.PDForm
