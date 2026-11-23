import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantCochainOneConstOnDegree
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.FstTszeSec
open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_cochainOne_const_on_degree : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → ∀ (h : C1 K.Oc) (l : Λ), (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = l → ψ.deg = 0 → h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ)) → (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = l → h T T'' (φ ≫ ψ) = h T' T'' ψ) → ∃ p : Hol F.V, ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = l → h T T' φ = algebraMap (Hol F.V) T'.C p := by
  first | exact @GlobalTheory.AnPer.Charts.invCochain_const | exact GlobalTheory.AnPer.Charts.invCochain_const | (intros; apply GlobalTheory.AnPer.Charts.invCochain_const <;> assumption)
