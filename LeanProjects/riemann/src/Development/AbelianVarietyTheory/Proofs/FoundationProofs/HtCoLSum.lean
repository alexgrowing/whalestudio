import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HtCoLOfEq
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ

namespace GlobalTheory.LambdaValuationPowers

theorem htCoL_sum : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (c : Coef l) (j : Ω →+* Qbar l)
    (ι : Type) [Fintype ι] (a : ι → Qbar l) (Z : ι → ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) (m c₀ : ℕ)
    (y : (ZMod (l ^ m))ˣ) (h : ι → Qbar l),
    (∀ i, ‖a i‖ ≤ 1 ∧ GlobalTheory.LambdaValuationPowers.FixIc c (a i)) → (∀ i, GlobalTheory.LambdaValuationPowers.HTCoL A c j (Z i) m c₀ y (h i)) →
    GlobalTheory.LambdaValuationPowers.HTCoL A c j (fun r s y' => ∑ i, a i * Z i r s y') m c₀ y (∑ i, a i * h i) := by
  intro l _ Ω _ _ A c j ι _ a Z m c₀ y h ha hZ
  choose q o w hint hcg using hZ
  let e : Fin (Fintype.card (Σ i, Fin (q i))) ≃ (Σ i, Fin (q i)) := (Fintype.equivFin _).symm
  refine ⟨Fintype.card (Σ i, Fin (q i)), fun k => a (e k).1 * o (e k).1 (e k).2, fun k => w (e k).1 (e k).2, ?_, ?_⟩
  · intro k
    obtain ⟨h1, h2, h3⟩ := hint (e k).1 (e k).2
    refine ⟨?_, ?_, h3⟩
    · rw [norm_mul]; exact mul_le_one₀ (ha _).1 (norm_nonneg _) h1
    · intro σ hσ hσ'
      rw [map_mul, (ha _).2 σ hσ hσ', h2 σ hσ hσ']
  · intro s hs hcyc
    have hre : (∑ k : Fin (Fintype.card (Σ i, Fin (q i))), a (e k).1 * o (e k).1 (e k).2 * (j (s (w (e k).1 (e k).2)) - j (w (e k).1 (e k).2)))
        = ∑ i, a i * ∑ r, o i r * (j (s (w i r)) - j (w i r)) := by
      rw [Equiv.sum_comp e (fun x => a x.1 * o x.1 x.2 * (j (s (w x.1 x.2)) - j (w x.1 x.2)))]
      rw [Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
    unfold Cg
    rw [hre]
    have key : (l : Qbar l) ^ c₀ * (∑ i, a i * Z i m s y) -
        ((l : Qbar l) ^ c₀ * (∑ i, a i * h i) * lamv l m s + ∑ i, a i * ∑ r, o i r * (j (s (w i r)) - j (w i r)))
        = ∑ i, a i * ((l : Qbar l) ^ c₀ * Z i m s y - ((l : Qbar l) ^ c₀ * h i * lamv l m s + ∑ r, o i r * (j (s (w i r)) - j (w i r)))) := by
      simp only [Finset.mul_sum, Finset.sum_mul, mul_sub, mul_add, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [key]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_
    rw [norm_mul]
    have := hcg i s hs hcyc
    unfold Cg at this
    calc ‖a i‖ * _ ≤ 1 * _ := mul_le_mul_of_nonneg_right (ha i).1 (norm_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact this

end GlobalTheory.LambdaValuationPowers
