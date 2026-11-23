import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFlagSpan
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PPlueckerSpan
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

theorem HodgeFlagSpan.full : HodgeFlagSpan.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl H B τ i
  classical
  let Be : Module.Basis (Fin D.N) Ω (E τ) := Module.Basis.mk (B.e_indep τ) (B.e_span τ).ge
  have hcoe : ⇑Be = B.e τ := Module.Basis.coe_mk _ _

  have hgen : Submodule.span Ω (Set.range (Pl.gen τ i)) = ⊤ := by
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
    obtain ⟨b, -, hspan, hA⟩ := hPr ⟨0, hM⟩
    have hli : LinearIndependent Ω b :=
      linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge
        (by rw [Module.finrank_eq_card_basis Be])
    let Bb : Module.Basis (Fin D.N) Ω (E τ) := Module.Basis.mk hli hspan.ge
    have hBb : ⇑Bb = b := Module.Basis.coe_mk _ _
    refine PlueckerSpan.span_eq_top_of_dual Bb (Pl.gen τ i) fun A hA0 => ?_
    obtain ⟨a, -, ha⟩ := hA A hA0
    refine ⟨fun m => a m * chartMono D.y cX (-Pl.bdeg τ i), fun A' hA' => ?_⟩
    rw [← ha A' hA', hBb]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring

  let P : Module.Dual Ω (⋀[Ω]^((i : ℕ) + 1) (E τ)) →ₗ[Ω] Pl.ΩY :=
    { toFun := fun φ => ∑ c : Fin ((i : ℕ) + 1) → Fin D.N,
        (∏ a, Pl.gvar0 τ (headIdx (step_le i) a) (c a)) *
          algebraMap Ω Pl.ΩY (φ (exteriorPower.ιMulti Ω _ (B.e τ ∘ c)))
      map_add' := fun φ ψ => by
        simp only [LinearMap.add_apply, map_add, mul_add, Finset.sum_add_distrib]
      map_smul' := fun x φ => by
        simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, Algebra.smul_def,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        ring }
  have hPpl : ∀ m, P (Pl.gen τ i m) = Pl.pluecker0 B τ i m := by
    intro m
    simp only [P, LinearMap.coe_mk, AddHom.coe_mk, PlueckerData.pluecker0, PlueckerData.ofΩ_eq]

  have hPexp : ∀ φ, P φ = ∑ T : Set.powersetCard (Fin D.N) ((i : ℕ) + 1),
      algebraMap Ω Pl.ΩY (φ (Be.exteriorPower _ T)) *
        flagMinor (genMat0Fr Ω Ψ D.N D.j τ) i ⟨(T : Finset (Fin D.N)), Set.powersetCard.card_eq T⟩ := by
    intro φ
    have h := PlueckerSpan.sum_prod_mul_apply_eq (R := Pl.ΩY) Be
      (Matrix.of fun a b => Pl.gvar0 τ (headIdx (step_le i) a) b) φ
    rw [hcoe] at h
    exact h.trans (Finset.sum_congr rfl fun T _ => rfl)

  have hrange : LinearMap.range P =
      Submodule.span Ω (Set.range (flagMinor (genMat0Fr Ω Ψ D.N D.j τ) i)) := by
    apply le_antisymm
    · rintro _ ⟨φ, rfl⟩
      rw [hPexp]
      refine Submodule.sum_mem _ fun T _ => ?_
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨S, rfl⟩
      let T : Set.powersetCard (Fin D.N) ((i : ℕ) + 1) := ⟨S.1, Set.powersetCard.mem_iff.2 S.2⟩
      refine ⟨(Be.exteriorPower _).coord T, ?_⟩
      rw [hPexp, Finset.sum_eq_single T]
      · rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same, map_one, one_mul]
      · intro T' _ hT'
        rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne (Ne.symm hT'),
          map_zero, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ T) h

  have hpl : Set.range (Pl.pluecker0 B τ i) = P '' Set.range (Pl.gen τ i) := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun m => (hPpl m).symm)
  rw [hpl, ← Submodule.map_span, hgen, Submodule.map_top, hrange]

end GroundTheory.Heights₂.Heights.LowerBoundFree
