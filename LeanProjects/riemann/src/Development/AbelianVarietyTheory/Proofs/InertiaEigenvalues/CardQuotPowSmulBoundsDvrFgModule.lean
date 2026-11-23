import Mathlib
open Module

noncomputable section

namespace GlobalTheory.DVRQuotCount

open scoped TensorProduct DirectSum

theorem card_quot_smul_top_of_flat' {R N : Type} [CommRing R] [IsDomain R] [AddCommGroup N] [Module R N]
    [Module.Finite R N] [Module.Flat R N] (I : Ideal R) [Finite (R ⧸ I)] :
    Nat.card (N ⧸ (I • ⊤ : Submodule R N)) = Nat.card (R ⧸ I) ^ Module.finrank R N := by
  have : IsArtinianRing (R ⧸ I) := isArtinian_of_finite
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq (R ⧸ I) ((R ⧸ I) ⊗[R] N) (Module.finrank R N)
    (fun P => by
      have := P.isMaximal
      let : Field ((R ⧸ I) ⧸ P.asIdeal) := Ideal.Quotient.field _
      rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange R (R ⧸ I) ((R ⧸ I) ⧸ P.asIdeal)
        ((R ⧸ I) ⧸ P.asIdeal) N).finrank_eq]
      have h1 := Module.rankAtStalk_baseChange (R := R) (M := N) (S := (R ⧸ I) ⧸ P.asIdeal) ⊥
      rw [Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq, Ideal.finrank_fiber_eq_finrank] at h1
      exact h1)
  rw [← Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul N I).toEquiv,
    Nat.card_congr b.equivFun.toEquiv, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]

theorem rank_prod_of_rank_zero {R A B : Type} [CommRing R] [IsDomain R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (hB : ∀ x : B, ∃ a : R, a ≠ 0 ∧ a • x = 0) :
    Module.rank R (A × B) = Module.rank R A := by
  have h := LinearMap.rank_range_add_rank_ker (LinearMap.fst R A B)
  have hk : Module.rank R (LinearMap.ker (LinearMap.fst R A B)) = 0 := by
    rw [rank_eq_zero_iff]
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, hax⟩ := hB x.2
    refine ⟨a, ha, ?_⟩
    ext
    · simpa using congrArg (a • ·) (show x.1 = 0 from hx)
    · simpa using hax
  rw [LinearMap.range_eq_top.2 (fun a => ⟨(a, 0), rfl⟩), rank_top, hk, add_zero] at h
  exact h.symm

theorem irreducible_dvd {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p t : O}
    (hp : Irreducible p) (ht : t ≠ 0) (htu : ¬ IsUnit t) : p ∣ t := by
  obtain ⟨q, hq, hqt⟩ := WfDvdMonoid.exists_irreducible_factor htu ht
  exact (IsDiscreteValuationRing.associated_of_irreducible O hp hq).dvd.trans hqt

theorem card_quot_pow_smul_bounds : ∀ (O M : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup M] [Module O M] [Module.Finite O M] (t : O), t ≠ 0 → ¬ IsUnit t →
    (∀ r : ℕ, Finite (O ⧸ Ideal.span {t ^ r})) → ∃ C : ℕ, 0 < C ∧ ∀ r : ℕ,
      Nat.card (O ⧸ Ideal.span {t ^ r}) ^ finrank O M ≤
        Nat.card (M ⧸ (Ideal.span {t ^ r} • ⊤ : Submodule O M)) ∧
      Nat.card (M ⧸ (Ideal.span {t ^ r} • ⊤ : Submodule O M)) ≤
        C * Nat.card (O ⧸ Ideal.span {t ^ r}) ^ finrank O M := by
  intro O M _ _ _ _ _ _ t ht htu hfin
  obtain ⟨n, ι, _, p, hp, e, ⟨eqv⟩⟩ := Module.equiv_free_prod_directSum O M
  set T := ⨁ i : ι, O ⧸ O ∙ p i ^ e i
  set F := Fin n →₀ O

  have hTi : ∀ i, Finite (O ⧸ O ∙ p i ^ e i) := by
    intro i
    have hle : Ideal.span {t ^ e i} ≤ Ideal.span {p i ^ e i} := by
      rw [Ideal.span_singleton_le_span_singleton]
      exact pow_dvd_pow_of_dvd (irreducible_dvd (hp i) ht htu) _
    haveI := hfin (e i)
    exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle)
  haveI : Finite T := Finite.of_equiv _ (DirectSum.linearEquivFunOnFintype O ι _).toEquiv.symm

  have hkill : ∀ x : T, ∃ a : O, a ≠ 0 ∧ a • x = 0 := by
    intro x
    refine ⟨∏ i, p i ^ e i, Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hp i).ne_zero, ?_⟩
    ext i
    rw [DirectSum.smul_apply, DirectSum.zero_apply]
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (x i)
    rw [← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul,
      Submodule.mem_span_singleton]
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun j => p j ^ e j) (Finset.mem_univ i)
    exact ⟨c * y, by rw [hc, smul_eq_mul]; ring⟩
  have hrank : finrank O M = n := by
    rw [eqv.finrank_eq]
    unfold Module.finrank
    rw [rank_prod_of_rank_zero hkill]
    change finrank O F = n
    simp [F]
  refine ⟨Nat.card T, Nat.card_pos, fun r => ?_⟩
  set I : Ideal O := Ideal.span {t ^ r}
  haveI := hfin r
  have hcard : Nat.card (M ⧸ (I • ⊤ : Submodule O M)) =
      Nat.card (O ⧸ I) ^ n * Nat.card (T ⧸ (I • ⊤ : Submodule O T)) := by
    rw [← Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul M I).toEquiv,
      Nat.card_congr (TensorProduct.congr (LinearEquiv.refl O (O ⧸ I)) eqv).toEquiv,
      Nat.card_congr (TensorProduct.prodRight O O (O ⧸ I) F T).toEquiv, Nat.card_prod,
      Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul F I).toEquiv,
      Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul T I).toEquiv,
      card_quot_smul_top_of_flat']
    simp [F]
  haveI : Finite (T ⧸ (I • ⊤ : Submodule O T)) := Finite.of_surjective _ (Submodule.mkQ_surjective _)
  have h1 : 1 ≤ Nat.card (T ⧸ (I • ⊤ : Submodule O T)) := Nat.card_pos
  have h2 : Nat.card (T ⧸ (I • ⊤ : Submodule O T)) ≤ Nat.card T :=
    Nat.card_le_card_of_surjective _ (Submodule.mkQ_surjective _)
  rw [hcard, hrank]
  constructor
  · exact Nat.le_mul_of_pos_right _ h1
  · rw [mul_comm]; exact Nat.mul_le_mul_right _ h2

end GlobalTheory.DVRQuotCount
