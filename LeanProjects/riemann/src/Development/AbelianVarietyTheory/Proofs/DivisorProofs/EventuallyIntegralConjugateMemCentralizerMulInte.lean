import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjSetLocalUnitaryEqDoubleCosetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalConjugationInvolutiveValuationPreservingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralLiftCoprimeDerivativeStatement

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.GoodConj

theorem eventually_mem_integers {E : Type} [Field E] [NumberField E] (a : E) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite,
      algebraMap E (w.adicCompletion E) a ∈ w.adicCompletionIntegers E :=
  (algebraMap E (FiniteAdeleRing (𝓞 E) E) a).2

theorem mem_KGL_of_entries {E : Type} [Field E] [NumberField E] {n : ℕ} (w : Pl E) (g : GLw n w)
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

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ γ : UE E n,
    γ.1.val.charpoly.Separable → ∀ᶠ w in cofinite, ∀ g : UL n w, g⁻¹ * locPt w γ * g ∈ KL n w →
      ∃ t ∈ twCent (MonoidHom.id (UL n w)) (locPt w γ), t⁻¹ * g ∈ KL n w := by
  intro E _ _ _ _ n _ γ hsep
  have hint : ∀ᶠ w : Pl E in cofinite, ∀ i j,
      algebraMap E (w.adicCompletion E) ((γ.1 : GL (Fin n) E).val i j) ∈ w.adicCompletionIntegers E ∧
      algebraMap E (w.adicCompletion E) (((γ.1 : GL (Fin n) E)⁻¹).val i j) ∈ w.adicCompletionIntegers E :=
    eventually_all.2 fun i => eventually_all.2 fun j =>
      (eventually_mem_integers _).and (eventually_mem_integers _)
  filter_upwards [hint, GlobalTheory.T.eventually_integral_lift_coprime_derivative E _ hsep] with w hw hP
  obtain ⟨P₀, hP₀, hcop⟩ := hP
  intro g hg
  set y : GLw n w := Matrix.GeneralLinearGroup.map (algebraMap E (w.adicCompletion E)) (γ.1 : GL (Fin n) E) with hy
  by_cases hmem : y ∈ UL n w
  · have hloc : ((locPt w γ : UL n w) : GLw n w) = y := by
      simp only [locPt, toSub]
      rw [dif_pos hmem]
    have hyK : y ∈ GlobalTheory.LFun.KGL w n := by
      apply mem_KGL_of_entries
      · intro a b; exact (hw a b).1
      · intro a b
        rw [hy, ← map_inv]
        exact (hw a b).2
    have hK : locPt w γ ∈ KL n w := by
      rw [KL, Subgroup.mem_subgroupOf, hloc]; exact hyK
    obtain ⟨h1, h2⟩ := GlobalTheory.T.localConjugation_involutive_valuation_preserving E w
    have hcp : (locPt w γ).1.val.charpoly =
        P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) := by
      rw [hloc, hP₀, hy]
      exact Matrix.charpoly_map _ _
    obtain ⟨t, ht, k, hk, he⟩ := GlobalTheory.T.integral_conj_set_localUnitary_eq_doubleCoset E n w h1 h2 P₀ hcop (locPt w γ) hcp 1 g
      (by simpa using hK) hg
    refine ⟨t, ht, ?_⟩
    rw [he, mul_one, inv_mul_cancel_left]
    exact hk
  · have hloc : locPt w γ = 1 := by
      simp only [locPt, toSub]
      rw [dif_neg hmem]
    refine ⟨g, ?_, by rw [inv_mul_cancel]; exact one_mem _⟩
    rw [hloc]
    show g * 1 = 1 * (MonoidHom.id _) g
    simp

end GlobalTheory.BCT.GoodConj
