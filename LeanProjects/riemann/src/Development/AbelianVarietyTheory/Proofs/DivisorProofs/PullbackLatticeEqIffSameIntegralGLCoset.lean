import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusOfSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSummandGoodPlaceIndicator
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

noncomputable section

namespace GlobalTheory.KapOrb.PullInj

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem mem_KGL_of_int {n : ℕ} (w : Pl E) (g : GLw n w)
    (h1 : ∀ a b, g.val a b ∈ w.adicCompletionIntegers E)
    (h2 : ∀ a b, (g⁻¹).val a b ∈ w.adicCompletionIntegers E) : g ∈ GlobalTheory.LFun.KGL w n := by
  let O : Subring (w.adicCompletion E) := Ov E w
  have inj : Function.Injective (O.subtype.mapMatrix (m := Fin n)) :=
    fun A B h => funext fun i => funext fun j => Subtype.ext (congrFun (congrFun h i) j)
  let A : Matrix (Fin n) (Fin n) O := fun i j => ⟨g.val i j, h1 i j⟩
  let B : Matrix (Fin n) (Fin n) O := fun i j => ⟨(g⁻¹).val i j, h2 i j⟩
  have hA : O.subtype.mapMatrix A = g.val := rfl
  have hB : O.subtype.mapMatrix B = (g⁻¹).val := rfl
  refine ⟨⟨A, B, inj ?_, inj ?_⟩, Units.ext rfl⟩
  · rw [map_mul, hA, hB, map_one, Units.mul_inv]
  · rw [map_mul, hA, hB, map_one, Units.inv_mul]

theorem mem_pullLat_iff (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} {e : K.E ≃+* w.adicCompletion E} (hB : Bridge w K e)
    (B : GlobalTheory.UnitLemma.InvAlg K) {n : ℕ} (ψ : B.A ≃+ (Fin n → w.adicCompletion E))
    (hψ : ∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) (g : GLw n w) (y : B.A) :
    y ∈ pullLat w B ψ g ↔ ∀ i, ((g⁻¹ : GLw n w).val *ᵥ ψ y) i ∈ w.adicCompletionIntegers E := by
  constructor
  · intro h i
    simpa using h 1 i
  · intro h c i
    have hc : Valued.v (e (algebraMap K.O K.E c)) ≤ 1 := (hB.2.1 _).1 ⟨c, rfl⟩
    have hc' : e (algebraMap K.O K.E c) ∈ w.adicCompletionIntegers E := hc
    change ((g⁻¹ : GLw n w).val *ᵥ ψ (c • y)) i ∈ w.adicCompletionIntegers E
    rw [← algebraMap_smul K.E c y, hψ, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    exact mul_mem hc' (h i)

theorem entries_int_of_le (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} {e : K.E ≃+* w.adicCompletion E} (hB : Bridge w K e)
    (B : GlobalTheory.UnitLemma.InvAlg K) {n : ℕ} (ψ : B.A ≃+ (Fin n → w.adicCompletion E))
    (hψ : ∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) (g g' : GLw n w)
    (h : pullLat w B ψ g' ≤ pullLat w B ψ g) (i j : Fin n) :
    (g⁻¹ * g').val i j ∈ w.adicCompletionIntegers E := by
  set y := ψ.symm (g'.val *ᵥ Pi.single j 1) with hy
  have hψy : ψ y = g'.val *ᵥ Pi.single j 1 := by simp [hy]
  have hy' : y ∈ pullLat w B ψ g' := by
    rw [mem_pullLat_iff w hB B ψ hψ, hψy]
    intro k
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    by_cases hk : k = j
    · subst hk; simp
    · simp [Pi.single_apply, hk]
  have := (mem_pullLat_iff w hB B ψ hψ g y).1 (h hy') i
  rw [hψy, Matrix.mulVec_mulVec, ← Units.val_mul, Matrix.mulVec_single_one] at this
  simpa using this

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ)
    (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ)
    (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), (∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) →
    ∀ g g' : GLw n w, pullLat w B ψ g = pullLat w B ψ g' → g⁻¹ * g' ∈ GlobalTheory.LFun.KGL w n := by
  intro E _ _ _ w K e hB B n ψ hψ g g' h
  refine mem_KGL_of_int w _ (entries_int_of_le w hB B ψ hψ g g' h.ge) ?_
  intro a b
  have e1 : (g⁻¹ * g')⁻¹ = g'⁻¹ * g := by group
  rw [e1]
  exact entries_int_of_le w hB B ψ hψ g' g h.le a b

end GlobalTheory.KapOrb.PullInj
