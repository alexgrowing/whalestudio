import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPlueckerSpan
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

namespace PlueckerSpan

theorem sum_prod_mul_det_indicator {R : Type} [CommRing R] {s N : ℕ} (M : Matrix (Fin s) (Fin N) R)
    (t : Fin s → Fin N) :
    ∑ c : Fin s → Fin N, (∏ a, M a (c a)) *
        (Matrix.of fun a j => if c a = t j then (1 : R) else 0).det =
      (Matrix.of fun a j => M a (t j)).det := by
  classical
  have hrow : (Matrix.of fun a j => M a (t j)) =
      fun a => ∑ b, M a b • fun j => if b = t j then (1 : R) else 0 := by
    ext a j
    simp [Finset.sum_apply]
  rw [hrow]
  change _ = Matrix.detRowAlternating _
  have h1 := (Matrix.detRowAlternating (R := R) (n := Fin s)).toMultilinearMap.map_sum
    (fun a b => M a b • fun j => if b = t j then (1 : R) else 0)
  simp only [AlternatingMap.coe_multilinearMap] at h1
  rw [h1]
  refine Finset.sum_congr rfl fun c _ => ?_
  have h2 := (Matrix.detRowAlternating (R := R) (n := Fin s)).toMultilinearMap.map_smul_univ
    (fun a => M a (c a)) (fun a j => if c a = t j then (1 : R) else 0)
  simp only [AlternatingMap.coe_multilinearMap, smul_eq_mul] at h2
  rw [h2]
  rfl

theorem sum_prod_mul_apply_eq {Ω R E : Type} [Field Ω] [CommRing R] [Algebra Ω R] [AddCommGroup E] [Module Ω E]
    {s N : ℕ} (e : Module.Basis (Fin N) Ω E) (M : Matrix (Fin s) (Fin N) R)
    (φ : Module.Dual Ω (⋀[Ω]^s E)) :
    ∑ c : Fin s → Fin N, (∏ a, M a (c a)) * algebraMap Ω R (φ (exteriorPower.ιMulti Ω s (e ∘ c))) =
      ∑ T : Set.powersetCard (Fin N) s, algebraMap Ω R (φ (e.exteriorPower s T)) *
        (Matrix.of fun a j => M a (Set.powersetCard.ofFinEmbEquiv.symm T j)).det := by
  classical
  have hc : ∀ c : Fin s → Fin N, algebraMap Ω R (φ (exteriorPower.ιMulti Ω s (e ∘ c))) =
      ∑ T : Set.powersetCard (Fin N) s, algebraMap Ω R (φ (e.exteriorPower s T)) *
        (Matrix.of fun a j => if c a = Set.powersetCard.ofFinEmbEquiv.symm T j then (1 : R) else 0).det := by
    intro c
    conv_lhs => rw [← (e.exteriorPower s).sum_repr (exteriorPower.ιMulti Ω s (e ∘ c))]
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [map_smul, smul_eq_mul, map_mul, mul_comm, exteriorPower.basis_repr_apply,
      exteriorPower.ιMultiDual_apply_ιMulti, RingHom.map_det]
    congr 2
    ext a j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Function.comp_apply,
      Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  simp_rw [hc, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [← sum_prod_mul_det_indicator M, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

theorem span_eq_top_of_dual {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {s N M : ℕ}
    (b : Module.Basis (Fin N) Ω E) (φ : Fin M → Module.Dual Ω (⋀[Ω]^s E))
    (h : ∀ A : Fin s → Fin N, StrictMono A → ∃ a : Fin M → Ω, ∀ A' : Fin s → Fin N, StrictMono A' →
      ∑ m, a m * φ m (exteriorPower.ιMulti Ω s (b ∘ A')) = if A' = A then 1 else 0) :
    Submodule.span Ω (Set.range φ) = ⊤ := by
  classical
  refine Submodule.eq_top_iff'.2 fun ψ => ?_
  rw [← (b.exteriorPower s).sum_dual_apply_smul_coord ψ]
  refine Submodule.sum_mem _ fun T _ => Submodule.smul_mem _ _ ?_
  obtain ⟨a, ha⟩ := h _ (Set.powersetCard.ofFinEmbEquiv.symm T).strictMono
  have hT : (b.exteriorPower s).coord T = ∑ m, a m • φ m := by
    refine (b.exteriorPower s).ext fun T' => ?_
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, smul_eq_mul, exteriorPower.basis_apply, exteriorPower.ιMulti_family]
    rw [ha _ (Set.powersetCard.ofFinEmbEquiv.symm T').strictMono, Finsupp.single_apply]
    have hiff : ((Set.powersetCard.ofFinEmbEquiv.symm T' : Fin s → Fin N) =
        Set.powersetCard.ofFinEmbEquiv.symm T) ↔ T' = T := by
      constructor
      · intro h'
        exact Set.powersetCard.ofFinEmbEquiv.symm.injective (DFunLike.coe_injective h')
      · rintro rfl
        rfl
    by_cases hTT : T' = T
    · rw [if_pos hTT, if_pos (hiff.2 hTT)]
    · rw [if_neg hTT, if_neg (fun h' => hTT (hiff.1 h'))]
  rw [hT]
  exact Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)

theorem proof : PlueckerSpan.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D Pl τ i
  classical
  let Be : Module.Basis (Fin D.N) Ω (E τ) := Module.Basis.mk (Pl.e_indep τ) (Pl.e_span τ).ge
  have hcoe : ⇑Be = Pl.e τ := Module.Basis.coe_mk _ _

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
    refine span_eq_top_of_dual Bb (Pl.gen τ i) fun A hA0 => ?_
    obtain ⟨a, -, ha⟩ := hA A hA0
    refine ⟨fun m => a m * chartMono D.y cX (-Pl.bdeg τ i), fun A' hA' => ?_⟩
    rw [← ha A' hA', hBb]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring

  let P : Module.Dual Ω (⋀[Ω]^((i : ℕ) + 1) (E τ)) →ₗ[Ω] Pl.ΩY :=
    { toFun := fun φ => ∑ c : Fin ((i : ℕ) + 1) → Fin D.N,
        (∏ a, Pl.gvar τ (headIdx (step_le i) a) (c a)) *
          algebraMap Ω Pl.ΩY (φ (exteriorPower.ιMulti Ω _ (Pl.e τ ∘ c)))
      map_add' := fun φ ψ => by
        simp only [LinearMap.add_apply, map_add, mul_add, Finset.sum_add_distrib]
      map_smul' := fun x φ => by
        simp only [LinearMap.smul_apply, smul_eq_mul, map_mul, RingHom.id_apply, Algebra.smul_def,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        ring }
  have hPpl : ∀ m, P (Pl.gen τ i m) = Pl.pluecker τ i m := by
    intro m
    simp only [P, LinearMap.coe_mk, AddHom.coe_mk, PlueckerData.pluecker, PlueckerData.ofΩ_eq]

  have hPexp : ∀ φ, P φ = ∑ T : Set.powersetCard (Fin D.N) ((i : ℕ) + 1),
      algebraMap Ω Pl.ΩY (φ (Be.exteriorPower _ T)) *
        flagMinor (genMatFr Ω Ψ D.N τ) i ⟨(T : Finset (Fin D.N)), Set.powersetCard.card_eq T⟩ := by
    intro φ
    have h := sum_prod_mul_apply_eq (R := Pl.ΩY) Be
      (Matrix.of fun a b => Pl.gvar τ (headIdx (step_le i) a) b) φ
    rw [hcoe] at h
    exact h.trans (Finset.sum_congr rfl fun T _ => rfl)

  have hrange : LinearMap.range P =
      Submodule.span Ω (Set.range (flagMinor (genMatFr Ω Ψ D.N τ) i)) := by
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

  have hpl : Set.range (Pl.pluecker τ i) = P '' Set.range (Pl.gen τ i) := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun m => (hPpl m).symm)
  rw [hpl, ← Submodule.map_span, hgen, Submodule.map_top, hrange]

end PlueckerSpan

end GroundTheory.Heights₂.Heights.LowerBoundFree
