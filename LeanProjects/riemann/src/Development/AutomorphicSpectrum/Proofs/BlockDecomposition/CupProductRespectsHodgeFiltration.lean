import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.TotPairing
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.CupdR

theorem dividedPowerFiltration_mul {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (r s : ℕ) :
    pdP δ r * pdP δ s ≤ pdP δ (r + s) := by
  unfold pdP
  rw [Ideal.span_mul_span']
  refine Ideal.span_le.2 ?_
  rintro _ ⟨_, ⟨l, hl, hr, rfl⟩, _, ⟨l', hl', hr', rfl⟩, rfl⟩
  refine Ideal.subset_span ⟨l ++ l', ?_, ?_, ?_⟩
  · intro q hq
    rcases List.mem_append.1 hq with h | h
    exacts [hl q h, hl' q h]
  · simp only [List.map_append, List.sum_append]
    omega
  · simp [List.map_append, List.prod_append]

theorem term_mem {b : Base} {L : b.Fun} {p n r : ℕ} (t : ComposableArrows (Thick L) n)
    (f : CH.Cn (CH.modF (thA L)) p) (hf : ∀ s, (show (s.obj (Fin.last p)).B from f s) ∈ (s.obj (Fin.last p)).pdPow r)
    (g : Fin (p + 1) → Fin (n + 1)) (hg : Monotone g) :
    (show (t.obj (Fin.last n)).B from CH.term (CH.modF (thA L)) t f g hg) ∈ (t.obj (Fin.last n)).pdPow r :=
  dividedPowerFiltration_map (t.map (homOfLE (Fin.le_last (g (Fin.last p))))).dp r (hf (hg.functor ⋙ t))

theorem cup_bilinear_filtered {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (i j : ℕ) :
    (∃ b : HdR q i →ₗ[K] HdR q j →ₗ[K] HdR q (i + j), ∀ x y, b x y = cupK q rfl x y) ∧
    ∀ r s, ∀ x ∈ FilR q i r, ∀ y ∈ FilR q j s, cupK q rfl x y ∈ FilR q (i + j) (r + s) := by
  refine ⟨CrystallineSemistableComparison.P.cup_bilin (CH.mulP (thA (smFun X q))) (rfl : i + j = i + j), ?_⟩
  rintro r s x ⟨z, rfl, hz⟩ y ⟨w, rfl, hw⟩
  obtain ⟨hc, e⟩ := CrystallineSemistableComparison.P.cup_cls (CH.mulP (thA (smFun X q))) (rfl : i + j = i + j) z.1 w.1 z.2 w.2
  refine ⟨⟨_, hc⟩, e.symm, fun t => ?_⟩
  exact dividedPowerFiltration_mul _ r s (Ideal.mul_mem_mul
    (term_mem t z.1 hz (CH.front rfl) (CH.front_mono rfl)) (term_mem t w.1 hw (CH.back rfl) (CH.back_mono rfl)))

end GlobalTheory.CompanionTheory.CupdR
