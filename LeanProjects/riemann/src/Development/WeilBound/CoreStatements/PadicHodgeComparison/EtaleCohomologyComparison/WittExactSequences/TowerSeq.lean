import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.TensCompl
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.SpanMap
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ColimLift

set_option autoImplicit false

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace CrystallineSemistableComparison.D

structure St (p : ℕ) {A : Type} [CommRing A] (r : ℕ → A) : Type 1 where
  G : Type
  [ring : CommRing G]
  [alg : Algebra A G]
  pf : Pf p G
  cov : Cov p r G

attribute [instance] St.ring St.alg

theorem St.next (p : ℕ) [Fact p.Prime] {A : Type} [CommRing A] {r : ℕ → A} (hA : Pf p A) (hr : IsRt p r) (s : St p r) :
    ∃ (s' : St p r) (f : s.G →ₐ[A] s'.G), AICm (f : s.G →+* s'.G) ∧ VALm (algebraMap A s.G (r 0)) (f : s.G →+* s'.G) ∧
      Splits p (algebraMap A s.G (r 0)) (f : s.G →+* s'.G) := by
  obtain ⟨B, _, _, hB, hc, h1, h2, h3⟩ := cov_step p s.G (fun k => algebraMap A s.G (r k)) s.pf
    (fun k => by rw [← map_pow, hr k])
  letI : Algebra A B := ((algebraMap s.G B).comp (algebraMap A s.G)).toAlgebra
  haveI : IsScalarTower A s.G B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ⟨⟨B, hB, Leaf.cov_comp p A s.G B r hA s.pf hr s.cov hc⟩, IsScalarTower.toAlgHom A s.G B, h1, h2, h3⟩

theorem tower_seq : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (r : ℕ → A), Pf p A → IsRt p r → ∃ (G : ℕ → Type) (_ : ∀ n, CommRing (G n)) (_ : ∀ n, Algebra A (G n)) (f : ∀ n, G n →ₐ[A] G (n + 1)), (∀ n, Pf p (G n) ∧ Cov p r (G n) ∧ AICm (f n : G n →+* G (n + 1)) ∧ VALm (algebraMap A (G n) (r 0)) (f n : G n →+* G (n + 1)) ∧ Splits p (algebraMap A (G n) (r 0)) (f n : G n →+* G (n + 1))) ∧ Function.Bijective (algebraMap A (G 0)) := by
  intro p _ A _ r hA hr
  choose nx f h using St.next p hA hr
  let s : ℕ → St p r := fun n => Nat.rec ⟨A, hA, (Leaf.cov_mono p A r).1⟩ (fun _ t => nx t) n
  exact ⟨fun n => (s n).G, fun n => (s n).ring, fun n => (s n).alg, fun n => f (s n),
    fun n => ⟨(s n).pf, (s n).cov, h (s n)⟩, Function.bijective_id⟩

theorem cov_tower : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (r : ℕ → A), Pf p A → IsRt p r → ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧ AIC B ∧ VAL (algebraMap A B (r 0)) ∧ Splits p (r 0) (algebraMap A B) := by
  intro p _ A _ r hA hr
  obtain ⟨G, _, _, f, h, h0⟩ := tower_seq p A r hA hr
  obtain ⟨L, _, _, ι, hι⟩ := Leaf.colim_ex A G f
  have hp := Leaf.colim_pf p A G f L ι hι
  have ht := Leaf.colim_test A (r 0) G f L ι hι (fun n => (h n).2.2.1) (fun n => (h n).2.2.2.1)
  refine ⟨L, inferInstance, inferInstance, hp.1 fun n => (h n).1, Leaf.cov_cmp p A L r fun m n a c hs => ?_, ht.1, ht.2, ?_⟩
  · obtain ⟨N, hN⟩ := hp.2 m n a c hs
    exact ⟨G N, inferInstance, inferInstance, (h N).2.1, hN⟩
  · intro T _ x hT h1 h2
    have step : ∀ n (y : {y : G n →+* T // y.comp (algebraMap A (G n)) = x}),
        ∃ y' : {y : G (n + 1) →+* T // y.comp (algebraMap A (G (n + 1))) = x}, ∀ z, y'.1 (f n z) = y.1 z := by
      intro n y
      obtain ⟨y', hy'⟩ := (h n).2.2.2.2 T y.1 hT h1 (by rw [← RingHom.comp_apply, y.2]; exact h2)
      have e : ∀ z, y' (f n z) = y.1 z := fun z => RingHom.congr_fun hy' z
      refine ⟨⟨y', RingHom.ext fun a => ?_⟩, e⟩
      rw [RingHom.comp_apply, ← (f n).commutes, e, ← RingHom.comp_apply, y.2]
    choose nx hnx using step
    let e0 := RingEquiv.ofBijective (algebraMap A (G 0)) h0
    let y : ∀ n, {y : G n →+* T // y.comp (algebraMap A (G n)) = x} := fun n =>
      Nat.rec ⟨x.comp e0.symm.toRingHom, RingHom.ext fun a => congrArg x (e0.symm_apply_apply a)⟩ (fun n t => nx n t) n
    obtain ⟨z, hz⟩ := colim_lift A G f L ι hι T (fun n => (y n).1) (fun n => hnx n (y n))
    refine ⟨z, RingHom.ext fun a => ?_⟩
    rw [RingHom.comp_apply, ← (ι 0).commutes, hz, ← RingHom.comp_apply, (y 0).2]

end CrystallineSemistableComparison.D
