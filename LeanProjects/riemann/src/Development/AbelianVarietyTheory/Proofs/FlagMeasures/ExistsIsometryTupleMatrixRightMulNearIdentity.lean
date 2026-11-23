import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NcardImageOfLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryNearIdentityCloseTuplesStatement

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.RStab

theorem gramT_scale {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) {n m : ℕ}
    (Hm : Matrix (Fin n) (Fin n) E) (x : Fin m → Fin n → E) (t : F) :
    gramT L Hm (fun a => algebraMap F E t • x a)
      = (algebraMap F E t * algebraMap F E t) • gramT L Hm x := by
  ext a b
  simp only [gramT, hf, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul,
    AlgEquiv.commutes, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem rmul_sub {E : Type} [CommRing E] {n m : ℕ} (x : Fin m → Fin n → E)
    (A : Matrix (Fin m) (Fin m) E) (a : Fin m) :
    rmul x A a - x a = ∑ i, (A i a - (1 : Matrix (Fin m) (Fin m) E) i a) • x i := by
  simp only [rmul, sub_smul, Finset.sum_sub_distrib]
  congr 1
  simp [Matrix.one_apply, ite_smul]

theorem exists_isometry_rmul : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (ϖ : 𝒪[F]), Irreducible ϖ → ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ Λ, IsSD L Hm Λ → ∀ (m : ℕ) (Γ : Matrix (Fin m) (Fin m) E), IsUnit Γ.det → ∀ N e : ℕ, ∃ i0 : ℕ, ∀ i ≥ i0, ∀ x : Fin m → Fin n → E, (∀ a, algebraMap F E ((ϖ : F) ^ e) • x a ∈ Λ) → gramT L Hm x = Γ → ∀ A ∈ congK L ϖ m i, cT L A * Γ * A = Γ → ∃ g ∈ isomG L Hm, CongId L ϖ Λ N g ∧ ∀ a, g (x a) = rmul x A a := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ n Hm hH Λ hΛ m Γ hΓ N e
  have h0 : ((ϖ : F) ^ e) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hϖ.ne_zero)
  have ht : IsUnit (algebraMap F E ((ϖ : F) ^ e)) := (IsUnit.mk0 _ h0).map _
  set t := algebraMap F E ((ϖ : F) ^ e) with htdef
  have hΓ' : IsUnit ((t * t) • Γ).det := by
    rw [Matrix.det_smul]; exact ((ht.mul ht).pow _).mul hΓ
  obtain ⟨N', hN'⟩ := GlobalTheory.T.exists_isometry_near_identity_close_tuples L ϖ hϖ Hm hH Λ hΛ m _ hΓ' N
  refine ⟨N', fun i hi x hx hG A hA hAΓ => ?_⟩
  have hϖO : algebraMap F E ((ϖ : F) ^ (i - N')) ∈ L.O := by
    rw [L.O_def]
    have h1 : IsIntegral 𝒪[F] ((ϖ : F) ^ (i - N')) :=
      (isIntegral_algebraMap (R := 𝒪[F]) (A := F) (x := ϖ)).pow _
    exact h1.map (IsScalarTower.toAlgHom 𝒪[F] F E)
  obtain ⟨g, hg, hc, hgx⟩ := hN' (fun a => t • x a) (fun a => t • rmul x A a) hx
    (by rw [gramT_scale, hG]) (by rw [gramT_scale, ContModel.gramT_rmul, hG, hAΓ]) (by
      intro a
      choose c hc hc' using hA
      refine ⟨∑ j, (algebraMap F E ((ϖ : F) ^ (i - N')) * c j a) • t • x j, ?_, ?_⟩
      · refine Λ.sum_mem fun j _ => ?_
        exact Λ.smul_mem (⟨_, L.O.mul_mem hϖO (hc j a)⟩ : L.O) (hx j)
      · rw [← smul_sub, rmul_sub, Finset.smul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hc', smul_smul, smul_smul, smul_smul]
        congr 1
        have : (ϖ : F) ^ i = (ϖ : F) ^ N' * (ϖ : F) ^ (i - N') := by
          rw [← pow_add]; congr 1; omega
        rw [this, map_mul]; ring)
  refine ⟨g, hg, hc, fun a => ?_⟩
  have h := hgx a
  simp only [map_smul] at h
  exact ht.smul_left_cancel.1 h

end GlobalTheory.HL.RStab
