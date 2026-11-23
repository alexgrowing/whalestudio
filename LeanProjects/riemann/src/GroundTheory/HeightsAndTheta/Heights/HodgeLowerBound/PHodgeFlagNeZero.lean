import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlagNeZero
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem HodgeFlagNeZero.proof : HodgeFlagNeZero.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl H B τ i
  classical

  let BE : Module.Basis (Fin D.N) Ω (E τ) := Module.Basis.mk (B.e_indep τ) (B.e_span τ).ge
  let w : ⋀[Ω]^((i : ℕ) + 1) (E τ) := exteriorPower.ιMulti Ω _ (B.e τ ∘ Fin.castLE (step_le i))
  have hw : w ≠ 0 := by
    have h := (BE.exteriorPower ((i : ℕ) + 1)).ne_zero
      (Set.powersetCard.ofFinEmbEquiv (Fin.castLEOrderEmb (step_le i)))
    rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family, Equiv.symm_apply_apply] at h
    convert h using 2
    funext x
    simp [BE, Fin.castLEOrderEmb]

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
  obtain ⟨b, -, hbspan, hA⟩ := hPr ⟨0, hM⟩
  have : Module.Finite Ω (E τ) := Module.Finite.of_basis BE
  have hbi : LinearIndependent Ω b :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hbspan.ge
      (by rw [Module.finrank_eq_card_basis BE])
  let Bw := (Module.Basis.mk hbi hbspan.ge).exteriorPower ((i : ℕ) + 1)

  have hm : ∃ m, Pl.gen τ i m w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hw
    refine Bw.forall_coord_eq_zero_iff.1 fun t => ?_
    obtain ⟨a, -, ha⟩ := hA _ (Set.powersetCard.ofFinEmbEquiv.symm t).strictMono
    let ψ : Module.Dual Ω (⋀[Ω]^((i : ℕ) + 1) (E τ)) :=
      ∑ m, (a m * chartMono D.y cX (-Pl.bdeg τ i)) • Pl.gen τ i m
    have hψ : ψ = Bw.coord t := by
      refine Bw.ext fun u => ?_
      have h1 := ha _ (Set.powersetCard.ofFinEmbEquiv.symm u).strictMono
      rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      simp only [Bw, exteriorPower.basis_apply, exteriorPower.ιMulti_family, ψ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Module.Basis.coe_mk]
      calc ∑ m, a m * chartMono D.y cX (-Pl.bdeg τ i) * Pl.gen τ i m (exteriorPower.ιMulti Ω _
              (b ∘ Set.powersetCard.ofFinEmbEquiv.symm u))
          = ∑ m, a m * (Pl.gen τ i m (exteriorPower.ιMulti Ω _
              (b ∘ Set.powersetCard.ofFinEmbEquiv.symm u)) * chartMono D.y cX (-Pl.bdeg τ i)) :=
            Finset.sum_congr rfl fun m _ => by ring
        _ = _ := h1
        _ = _ := by
          by_cases htu : t = u
          · subst htu
            simp
          · rw [if_neg fun h' =>
              htu (Set.powersetCard.ofFinEmbEquiv.symm.injective (DFunLike.coe_injective h')).symm]
            simp [Ne.symm htu]
    rw [← hψ]
    simp [ψ, hcon]
  obtain ⟨m0, hm0⟩ := hm

  refine ⟨m0, ?_⟩
  let c0 : Fin ((i : ℕ) + 1) → Fin D.N := Fin.castLE (step_le i)
  let v : (Fin ((i : ℕ) + 1) → Fin D.N) → Fin ((i : ℕ) + 1) → Ψ × Fin D.N × Fin D.N :=
    fun c a => (τ, headIdx (step_le i) a, c a)
  let μ : (Fin ((i : ℕ) + 1) → Fin D.N) → (Ψ × Fin D.N × Fin D.N) →₀ ℕ :=
    fun c => ∑ a, Finsupp.single (v c a) 1
  let g : (Fin ((i : ℕ) + 1) → Fin D.N) → Ω :=
    fun c => Pl.gen τ i m0 (exteriorPower.ιMulti Ω _ (B.e τ ∘ c))
  let z : (Fin ((i : ℕ) + 1) → Fin D.N) → Ω := fun c =>
    ∏ a, if ((headIdx (step_le i) a : ℕ) < D.j ∧ D.j ≤ (c a : ℕ)) then 0 else 1
  let P : MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω := ∑ c, monomial (μ c) (z c * g c)
  have hP : Pl.pluecker0 B τ i m0 = algebraMap _ Pl.ΩY P := by
    simp only [PlueckerData.pluecker0, PlueckerData.gvar0, PlueckerData.gvar, PlueckerData.ofΩ, P, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hfac : ∀ a, (if ((headIdx (step_le i) a : ℕ) < D.j ∧ D.j ≤ (c a : ℕ)) then (0 : Pl.ΩY)
        else algebraMap (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY (X (τ, headIdx (step_le i) a, c a))) =
        algebraMap (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY
          (C (if ((headIdx (step_le i) a : ℕ) < D.j ∧ D.j ≤ (c a : ℕ)) then 0 else 1) *
            X (τ, headIdx (step_le i) a, c a)) := by
      intro a
      split_ifs <;> simp
    rw [Finset.prod_congr rfl fun a _ => hfac a, ← map_prod, ← map_mul]
    congr 1
    rw [show monomial (μ c) (z c * g c) = C (z c * g c) * monomial (μ c) 1 by rw [C_mul_monomial, mul_one],
      monomial_sum_one, Finset.prod_mul_distrib]
    simp only [z, g, map_mul, map_prod, v, MvPolynomial.X]
    ring
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
  have hz : z c0 = 1 :=
    Finset.prod_eq_one fun a _ => if_neg fun h => lt_irrefl _ (h.1.trans_le h.2)
  have hcoeff : coeff (μ c0) P = g c0 := by
    simp only [P, coeff_sum, coeff_monomial]
    rw [Finset.sum_eq_single c0 (fun c _ hc => if_neg fun h => hc (hμ c h)) (by simp), if_pos rfl, hz, one_mul]
  have hPne : P ≠ 0 := fun h => hm0 (by rw [h, coeff_zero] at hcoeff; exact hcoeff.symm)
  rw [hP]
  exact fun h => hPne (IsFractionRing.injective (MvPolynomial (Ψ × Fin D.N × Fin D.N) Ω) Pl.ΩY
    (by rw [h, map_zero]))

end GroundTheory.Heights₂.Heights.LowerBoundFree
