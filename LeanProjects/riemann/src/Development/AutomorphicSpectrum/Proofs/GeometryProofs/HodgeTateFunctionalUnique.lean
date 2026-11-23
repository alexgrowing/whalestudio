import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HasValues
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SectionEqZeroOfValuesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueTangentDualNumberStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT.HT

private lemma valAt_sub' {B : Type} [CommRing B] {X : Scheme.{0}} (y : Spec (CommRingCat.of B) ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U) (a b : Γ(X, U)) :
    valAt y U h (a - b) = valAt y U h a - valAt y U h b := by
  simp [valAt, map_sub]

private lemma exists_dual_of_dvd {R : Type} [CommRing R] [IsDomain R] {L : Type} [AddCommGroup L]
    [Module R L] (c : R) (hc : c ≠ 0) (d : Module.Dual R L) (h : ∀ e, c ∣ d e) :
    ∃ u : Module.Dual R L, d = c • u := by
  choose f hf using h
  refine ⟨{ toFun := f, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y
    apply mul_left_cancel₀ hc
    rw [mul_add, ← hf, ← hf, ← hf, map_add]
  · intro r x
    apply mul_left_cancel₀ hc
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [← hf, map_smul, smul_eq_mul, hf x]
    ring
  · ext e
    show d e = c • f e
    rw [hf e, smul_eq_mul]

theorem isHT_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → (N : R) ≠ 0 → ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (χ : T →* Rˣ) (w w' : Module.Dual R L), Γ.IsHT i M N χ w → (Γ.IsHT i M N χ w' ↔ ∃ u : Module.Dual R L, w' = w + N • u) := by
  intro R _ _ T _ _ Γ S G _ _ x N i hT hsm hN L _ _ M χ w w' hw
  obtain ⟨s, hs, hsv⟩ := hw
  constructor
  · rintro ⟨s', hs', hsv'⟩
    have hss : s' = s := by
      have h0 := GlobalTheory.T.section_eq_zero_of_values R T Γ ⊤ (s' - s) (fun t h => by
        rw [valAt_sub', hs' t, hs t, sub_self])
      exact sub_eq_zero.mp h0
    subst hss
    have hdvd : ∀ e, (N : R) ∣ w' e - w e := by
      intro e
      obtain ⟨v, hv1, hv2, hv3⟩ := hsv e
      obtain ⟨v', hv1', hv2', hv3'⟩ := hsv' e
      have hvv : v' = v := (GlobalTheory.T.existsUnique_tangent_dual_number R T Γ S G x N i hT L M e).unique ⟨hv1', hv2'⟩ ⟨hv1, hv2⟩
      subst hvv
      rw [hv3] at hv3'
      have h1 : Ideal.Quotient.mk (Ideal.span {(N : R)}) (w e) = Ideal.Quotient.mk (Ideal.span {(N : R)}) (w' e) := by
        simpa using congrArg TrivSqZeroExt.snd hv3'
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
      exact h1.symm
    obtain ⟨u, hu⟩ := exists_dual_of_dvd (N : R) hN (w' - w) (fun e => by simpa using hdvd e)
    refine ⟨u, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul R, ← hu]
    abel
  · rintro ⟨u, rfl⟩
    refine ⟨s, hs, fun e => ?_⟩
    obtain ⟨v, hv1, hv2, hv3⟩ := hsv e
    refine ⟨v, hv1, hv2, ?_⟩
    have h0 : Ideal.Quotient.mk (Ideal.span {(N : R)}) ((N • u) e) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, ← Nat.cast_smul_eq_nsmul R,
        LinearMap.smul_apply, smul_eq_mul]
      exact dvd_mul_right _ _
    rw [hv3, LinearMap.add_apply, map_add, h0, add_zero]

end GlobalTheory.CompanionTheory.Ar.BT.HT
