import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPlueckerNeZero
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem PlueckerNeZero.proof : PlueckerNeZero.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl τ i
  classical

  choose cX hcX using D.arith.2.1.2.2
  have hy : ∀ k, D.y ⟨k, cX k⟩ ≠ 0 := by
    intro k h0
    apply hcX k
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, map_zero, zero_mul]
  have hseg : segreCoord D.y cX ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hy k

  obtain ⟨M, f, cc, -, -, hsum, hPr⟩ := Pl.generates τ i cX hseg
  have hM : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h
      simp at hsum
    · exact h
  obtain ⟨b, -, -, hA⟩ := hPr ⟨0, hM⟩
  have hmono : StrictMono (Fin.castLE (step_le i)) := Fin.strictMono_castLE (step_le i)
  obtain ⟨a, -, ha⟩ := hA _ hmono
  have h1 := ha _ hmono
  rw [if_pos rfl] at h1
  obtain ⟨m0, -, hm0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h1.symm ▸ one_ne_zero)
  have hb : Pl.gen τ i m0 (exteriorPower.ιMulti Ω _ (b ∘ Fin.castLE (step_le i))) ≠ 0 :=
    fun h => hm0 (by rw [h, zero_mul, mul_zero])

  have hc0 : ∃ c0 : Fin ((i : ℕ) + 1) → Fin D.N,
      Pl.gen τ i m0 (exteriorPower.ιMulti Ω _ (Pl.e τ ∘ c0)) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    let B : Module.Basis (Fin D.N) Ω (E τ) := Module.Basis.mk (Pl.e_indep τ) (Pl.e_span τ).ge
    have hzero : (Pl.gen τ i m0).compAlternatingMap (exteriorPower.ιMulti Ω ((i : ℕ) + 1)) = 0 := by
      refine Module.Basis.ext_alternating B fun v _ => ?_
      simp only [LinearMap.compAlternatingMap_apply, AlternatingMap.zero_apply, B, Module.Basis.coe_mk]
      exact hcon v
    apply hb
    have := congrArg (fun φ => φ (b ∘ Fin.castLE (step_le i))) hzero
    simpa using this
  obtain ⟨c0, hc0⟩ := hc0

  refine ⟨m0, ?_⟩
  let v : (Fin ((i : ℕ) + 1) → Fin D.N) → Fin ((i : ℕ) + 1) → Ψ × Fin D.N × Fin D.N :=
    fun c a => (τ, headIdx (step_le i) a, c a)
  let μ : (Fin ((i : ℕ) + 1) → Fin D.N) → (Ψ × Fin D.N × Fin D.N) →₀ ℕ :=
    fun c => ∑ a, Finsupp.single (v c a) 1
  let g : (Fin ((i : ℕ) + 1) → Fin D.N) → Ω :=
    fun c => Pl.gen τ i m0 (exteriorPower.ιMulti Ω _ (Pl.e τ ∘ c))
  let P : MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω := ∑ c, monomial (μ c) (g c)
  have hP : Pl.pluecker τ i m0 = algebraMap _ Pl.ΩY P := by
    simp only [PlueckerData.pluecker, PlueckerData.gvar, PlueckerData.ofΩ, P, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← map_prod, ← map_mul]
    congr 1
    rw [show monomial (μ c) (g c) = C (g c) * monomial (μ c) 1 by rw [C_mul_monomial, mul_one],
      monomial_sum_one, mul_comm]
    rfl
  have hμ : ∀ c, μ c = μ c0 → c = c0 := by
    intro c h
    funext a
    have h2 := congrArg (fun φ : (Ψ × Fin D.N × Fin D.N) →₀ ℕ => φ (τ, headIdx (step_le i) a, c0 a)) h
    simp only [μ, v, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply, Prod.mk.injEq,
      true_and, headIdx, Fin.castLE_inj] at h2
    rw [Finset.sum_eq_single a (fun a' _ h' => if_neg fun h'' => h' h''.1) (by simp),
      Finset.sum_eq_single a (fun a' _ h' => if_neg fun h'' => h' h''.1) (by simp)] at h2
    by_contra hne
    simp [hne] at h2
  have hcoeff : coeff (μ c0) P = g c0 := by
    simp only [P, coeff_sum, coeff_monomial]
    rw [Finset.sum_eq_single c0 (fun c _ hc => if_neg fun h => hc (hμ c h)) (by simp), if_pos rfl]
  have hPne : P ≠ 0 := fun h => hc0 (by rw [h, coeff_zero] at hcoeff; exact hcoeff.symm)
  rw [hP]
  exact fun h => hPne (IsFractionRing.injective (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY
    (by rw [h, map_zero]))

end GroundTheory.Heights₂.Heights.LowerBoundFree
