import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.TwistedFourierKernels.IsTwistTwD
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoFinite

open IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Ws.H5

private theorem comap_max {B Q : Type} [CommRing B] [IsLocalRing B] [CommGroup Q] [Finite Q]
    (M : Ideal (MonoidAlgebra B Q)) [M.IsMaximal] :
    M.comap (algebraMap B (MonoidAlgebra B Q)) = maximalIdeal B :=
  eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M)

private theorem single_sub_mem {l : ℕ} (hl : l.Prime) {B Q : Type} [CommRing B] [IsLocalRing B]
    [CommGroup Q] [Finite Q] (hB : ((l : ℕ) : B) ∈ maximalIdeal B) (hQ : IsPGroup l Q)
    (M : Ideal (MonoidAlgebra B Q)) [hM : M.IsMaximal] (z : Q) :
    (MonoidAlgebra.single z 1 - 1 : MonoidAlgebra B Q) ∈ M := by
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨k, hk⟩ := hQ z
  have hlM : ((l : ℕ) : MonoidAlgebra B Q) ∈ M := by
    have h1 : ((l : ℕ) : B) ∈ M.comap (algebraMap B (MonoidAlgebra B Q)) := by
      rw [comap_max M]
      exact hB
    rw [Ideal.mem_comap, map_natCast] at h1
    exact h1
  letI : Field (MonoidAlgebra B Q ⧸ M) := Ideal.Quotient.field M
  have hlK : ((l : ℕ) : MonoidAlgebra B Q ⧸ M) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk M), Ideal.Quotient.eq_zero_iff_mem]
    exact hlM
  haveI : CharP (MonoidAlgebra B Q ⧸ M) l := by
    rcases hl.eq_one_or_self_of_dvd _ (ringChar.dvd hlK) with h1 | h1
    · exact absurd h1 (CharP.ringChar_ne_one)
    · rw [← h1]
      exact ringChar.charP _
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h0 : (Ideal.Quotient.mk M (MonoidAlgebra.single z 1 - 1)) ^ l ^ k = 0 := by
    rw [map_sub, map_one, sub_pow_char_pow, one_pow, ← map_pow, MonoidAlgebra.single_pow, one_pow, hk,
      ← MonoidAlgebra.one_def, map_one, sub_self]
  exact (pow_eq_zero_iff (pow_ne_zero k hl.ne_zero)).mp h0

private theorem sub_aug_mem {B Q : Type} [CommRing B] [CommGroup Q]
    (M : Ideal (MonoidAlgebra B Q))
    (h : ∀ z : Q, (MonoidAlgebra.single z 1 - 1 : MonoidAlgebra B Q) ∈ M) (x : MonoidAlgebra B Q) :
    x - algebraMap B (MonoidAlgebra B Q) (MonoidAlgebra.lift B B Q 1 x) ∈ M := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, map_add, add_sub_add_comm]
    exact M.add_mem hx hy
  | single g b =>
    have e : MonoidAlgebra.single g b - algebraMap B (MonoidAlgebra B Q) (MonoidAlgebra.lift B B Q 1 (MonoidAlgebra.single g b)) =
        algebraMap B (MonoidAlgebra B Q) b * (MonoidAlgebra.single g 1 - 1) := by
      rw [MonoidAlgebra.lift_single]
      simp [mul_sub, MonoidAlgebra.single_mul_single, MonoidAlgebra.one_def]
    rw [e]
    exact M.mul_mem_left _ (h g)

theorem UpperTheory.V.Ws.H5.grpCO :
    ∀ (l : ℕ) [Fact l.Prime] (O B : Type) [CommRing O] [IsLocalRing O] [CommRing B] [Algebra O B] [IsCO O B], ((l : ℕ) : B) ∈ maximalIdeal B → ∀ (Q : Type) [CommGroup Q] [Finite Q], IsPGroup l Q → ∃ _ : IsCO O (MonoidAlgebra B Q), ∀ z : Q, (MonoidAlgebra.single z 1 - 1 : MonoidAlgebra B Q) ∈ maximalIdeal (MonoidAlgebra B Q) := by
  intro l _ O B _ _ _ _ _ hB Q _ _ hQ
  have hl : l.Prime := Fact.out
  let aug : MonoidAlgebra B Q →+* B := (MonoidAlgebra.lift B B Q 1).toRingHom
  let φ : MonoidAlgebra B Q →+* ResidueField B := (residue B).comp aug
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨b, rfl⟩ := residue_surjective y
    refine ⟨algebraMap B _ b, ?_⟩
    simp [φ, aug]
  have hM0 := RingHom.ker_isMaximal_of_surjective φ hφ
  have hle : ∀ (M : Ideal (MonoidAlgebra B Q)), M.IsMaximal → RingHom.ker φ ≤ M := by
    intro M hM x hx
    have h1 : aug x ∈ maximalIdeal B := by
      rw [RingHom.mem_ker] at hx
      exact (residue_eq_zero_iff _).mp hx
    have h2 : algebraMap B _ (aug x) ∈ M := by
      have : aug x ∈ M.comap (algebraMap B _) := by
        rw [comap_max M]
        exact h1
      exact this
    have h3 : x - algebraMap B _ (aug x) ∈ M := sub_aug_mem M (single_sub_mem hl hB hQ M) x
    have := M.add_mem h3 h2
    rwa [sub_add_cancel] at this
  haveI : IsLocalRing (MonoidAlgebra B Q) := by
    apply IsLocalRing.of_unique_max_ideal
    refine ⟨RingHom.ker φ, hM0, fun M hM => ?_⟩
    exact (hM0.eq_of_le hM.ne_top (hle M hM)).symm
  have hres : ∀ x : MonoidAlgebra B Q, ∃ a : O, x - algebraMap O _ a ∈ maximalIdeal (MonoidAlgebra B Q) := by
    intro x
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) (aug x)
    refine ⟨a, ?_⟩
    have h3 : x - algebraMap B _ (aug x) ∈ maximalIdeal (MonoidAlgebra B Q) :=
      sub_aug_mem _ (single_sub_mem hl hB hQ _) x
    have h4 : algebraMap B (MonoidAlgebra B Q) (aug x - algebraMap O B a) ∈ maximalIdeal (MonoidAlgebra B Q) := by
      have : aug x - algebraMap O B a ∈ (maximalIdeal (MonoidAlgebra B Q)).comap (algebraMap B _) := by
        rw [comap_max]
        exact ha
      exact this
    have := (maximalIdeal _).add_mem h3 h4
    rw [IsScalarTower.algebraMap_apply O B (MonoidAlgebra B Q)]
    rwa [map_sub, sub_add_sub_cancel] at this
  exact ⟨co_finite O B (MonoidAlgebra B Q) hres, fun z => single_sub_mem hl hB hQ _ z⟩
