import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramSub
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnramifiedExtTorsionPointsGoodReduction
open IsLocalRing Polynomial

namespace GlobalTheory.KummerUnram

theorem etale_adjoinRoot_pow_sub {R : Type} [CommRing R] [Nontrivial R] {k : ℕ} (hk : IsUnit (k : R)) (u : Rˣ) :
    Algebra.Etale R (AdjoinRoot (X ^ k - C (u : R))) := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact not_isUnit_zero (M₀ := R) (by simpa using hk)
  have hm : (X ^ k - C (u : R)).Monic := monic_X_pow_sub_C _ hk0
  have h1 : AdjoinRoot.root (X ^ k - C (u : R)) ^ k = algebraMap R _ (u : R) := by
    have := AdjoinRoot.eval₂_root (X ^ k - C (u : R))
    simpa [sub_eq_zero] using this
  have hr : IsUnit (AdjoinRoot.root (X ^ k - C (u : R))) :=
    (isUnit_pow_iff hk0).1 (h1 ▸ (u.isUnit.map _))
  let P : StandardEtalePair R := ⟨X ^ k - C (u : R), hm, derivative (X ^ k - C (u : R)), 1, 0, 1, by simp⟩
  have h : IsUnit (AdjoinRoot.mk (X ^ k - C (u : R)) (derivative (X ^ k - C (u : R)))) := by
    have e : AdjoinRoot.mk (X ^ k - C (u : R)) (derivative (X ^ k - C (u : R))) =
        algebraMap R _ (k : R) * AdjoinRoot.root _ ^ (k - 1) := by
      simp [derivative_X_pow, AdjoinRoot.algebraMap_eq]
    rw [e]
    exact (hk.map _).mul (hr.pow _)
  exact .of_equiv (P.equivAwayAdjoinRoot.trans
    ((IsLocalization.atUnit _ (Localization.Away (AdjoinRoot.mk _ (derivative (X ^ k - C (u : R))))) _
      h).symm.restrictScalars R))

end GlobalTheory.KummerUnram

namespace GlobalTheory.KummerUnram

theorem exists_root_step {F : Type} [Field F] [IsAlgClosed F] (T : Subring F)
    [IsDiscreteValuationRing T] {k : ℕ} (hk : IsUnit (k : T)) (u : Tˣ)
    (ub : AlgebraicClosure (ResidueField T)) (hub : ub ^ k = algebraMap _ _ (residue T u)) :
    ∃ T' : Subring F, UnramSub T.subtype T' ∧ ∃ y ∈ T', y ^ k = ((u : T) : F) ∧
      ∀ n : ℕ, ub ^ n ≠ 1 → y ^ n ≠ 1 := by
  have := etale_adjoinRoot_pow_sub hk u
  let ρ : T →+* AlgebraicClosure (ResidueField T) :=
    (algebraMap (ResidueField T) _).comp (residue T)
  let ε : AdjoinRoot (X ^ k - C (u : T)) →+* AlgebraicClosure (ResidueField T) :=
    AdjoinRoot.lift ρ ub (by simp [ρ, hub])
  have hερ : ε.comp (algebraMap T _) = ρ := by
    ext t
    simp [ε, AdjoinRoot.algebraMap_eq]
  have hε : IsLocalHom (ε.comp (algebraMap T (AdjoinRoot (X ^ k - C (u : T))))) := by
    rw [hερ]; infer_instance
  obtain ⟨B, _, _, _, ψ, ρ', j', -, h2, h3, h4, h5⟩ :=
    TorsionUnram.exists_local_of_etale ε hε T.subtype Subtype.val_injective
  obtain ⟨hD, f, hf, hirr⟩ := UnramSub.range (i := j') h3
  refine ⟨j'.range, ⟨hD, f.comp (ψ.comp (algebraMap T _)), fun v => ?_,
    fun π hπ => hirr _ (h5 π hπ)⟩, j' (ψ (AdjoinRoot.root _)), ⟨_, rfl⟩, ?_, fun n hn hy => hn ?_⟩
  · rw [RingHom.comp_apply, hf]
    exact congr($h4 v)
  · have h1 : AdjoinRoot.root (X ^ k - C (u : T)) ^ k = algebraMap T _ (u : T) := by
      have := AdjoinRoot.eval₂_root (X ^ k - C (u : T))
      simpa [sub_eq_zero] using this
    rw [← map_pow, ← map_pow, h1]
    exact congr($h4 (u : T))
  · have e1 : ψ (AdjoinRoot.root (X ^ k - C (u : T))) ^ n = 1 :=
      h3 (by rw [map_pow, hy, map_one])
    have e2 : ρ' (ψ (AdjoinRoot.root (X ^ k - C (u : T)))) = ub := by
      rw [← RingHom.comp_apply, h2]
      simp [ε]
    rw [← e2, ← map_pow, e1, map_one]

end GlobalTheory.KummerUnram

namespace GlobalTheory.KummerUnram

theorem exists_rootsOfUnity {F : Type} [Field F] [IsAlgClosed F] (T : Subring F)
    [IsDiscreteValuationRing T] {k : ℕ} (hk : IsUnit (k : T)) :
    ∃ T' : Subring F, UnramSub T.subtype T' ∧ ∀ z : F, z ^ k = 1 → z ∈ T' := by
  let ρ : T →+* AlgebraicClosure (ResidueField T) :=
    (algebraMap (ResidueField T) _).comp (residue T)
  have hkΩ : ((k : ℕ) : AlgebraicClosure (ResidueField T)) ≠ 0 := by
    simpa [ρ] using (hk.map ρ).ne_zero
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hkΩ)
  haveI : NeZero ((k : ℕ) : AlgebraicClosure (ResidueField T)) := ⟨hkΩ⟩
  obtain ⟨ub, hub⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure (ResidueField T)) k
  obtain ⟨T', hT', y, hyT, hy, hyn⟩ := exists_root_step T hk 1 ub (by simp [hub.pow_eq_one])
  have hy1 : y ^ k = 1 := by simpa using hy
  have hprim : IsPrimitiveRoot y k := IsPrimitiveRoot.mk_of_lt y hk0 hy1
    fun l hl hlk => hyn l (hub.pow_ne_one_of_pos_of_lt hl.ne' hlk)
  refine ⟨T', hT', fun z hz => ?_⟩
  haveI : NeZero k := ⟨hk0.ne'⟩
  obtain ⟨i, -, rfl⟩ := hprim.eq_pow_of_pow_eq_one hz
  exact pow_mem hyT i

end GlobalTheory.KummerUnram

namespace GlobalTheory

open KummerUnram in

theorem exists_unramSub_of_pow_eq_units : ∀ (F : Type) [Field F] [IsAlgClosed F] (T : Subring F) [IsDiscreteValuationRing T] (k : ℕ), IsUnit (k : T) → ∀ U : Set Tˣ, U.Finite → ∃ T' : Subring F, GlobalTheory.UnramSub T.subtype T' ∧ ∀ x : F, (∃ u ∈ U, x ^ k = ((u : T) : F)) → x ∈ T' := by
  intro F _ _ T _ k hk U hU
  obtain ⟨T₁, h₁, hroots⟩ := exists_rootsOfUnity T hk
  suffices key : ∃ T' : Subring F, UnramSub T.subtype T' ∧ T₁ ≤ T' ∧
      ∀ x : F, (∃ u ∈ U, x ^ k = ((u : T) : F)) → x ∈ T' by
    obtain ⟨T', h, -, h'⟩ := key
    exact ⟨T', h, h'⟩
  induction U, hU using Set.Finite.induction_on with
  | empty => exact ⟨T₁, h₁, le_rfl, by simp⟩
  | @insert a s _ _ ih =>
    obtain ⟨T', hT', hle, hmem⟩ := ih
    haveI := hT'.isDVR
    have hTT' : T ≤ T' := fun z hz => hT'.mem ⟨z, hz⟩
    let ι : T →+* T' := Subring.inclusion hTT'
    have hk' : IsUnit (k : T') := by simpa [ι] using hk.map ι
    let a' : T'ˣ := Units.map ι.toMonoidHom a
    have hk0 : k ≠ 0 := by rintro rfl; exact not_isUnit_zero (M₀ := T) (by simpa using hk)
    obtain ⟨ub, hub⟩ := IsAlgClosed.exists_pow_nat_eq
      (algebraMap (ResidueField T') (AlgebraicClosure (ResidueField T')) (residue T' a'))
      (Nat.pos_of_ne_zero hk0)
    obtain ⟨T'', hT'', y, hyT, hy, -⟩ := exists_root_step T' hk' a' ub hub
    have hy' : y ^ k = ((a : T) : F) := by simpa [a', ι] using hy
    have ha0 : ((a : T) : F) ≠ 0 := fun h => a.ne_zero (Subtype.ext h)
    have hy0 : y ≠ 0 := by rintro rfl; exact ha0 (by rw [← hy', zero_pow hk0])
    have hle' : T' ≤ T'' := UnramSub.le hT''
    refine ⟨T'', hT'.trans hT'', hle.trans hle', fun x ⟨u, hu, hx⟩ => ?_⟩
    rcases Set.mem_insert_iff.1 hu with rfl | hu
    · have hz : (x / y) ^ k = 1 := by rw [div_pow, hx, hy', div_self ha0]
      have : x = (x / y) * y := by field_simp
      rw [this]
      exact mul_mem (hle' (hle (hroots _ hz))) hyT
    · exact hle' (hmem x ⟨u, hu, hx⟩)

end GlobalTheory
