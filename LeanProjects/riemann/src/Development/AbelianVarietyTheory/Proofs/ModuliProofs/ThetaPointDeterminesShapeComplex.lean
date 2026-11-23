import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFamilyFromVeryDensePointsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem isThetaPt_unit_mul {S : Scheme.{0}} (P : Out.PolAV S) (k : ℕ) {T : Over S} {I : Type}
    (x : I → (T ⟶ P.A)) (v : I → Γ(T.left, ⊤)) (c : Γ(T.left, ⊤)) (hc : IsUnit c)
    (H : Out.IsThetaPt P k x v) : Out.IsThetaPt P k x (fun i => c * v i) := by
  obtain ⟨h1, h2, h3⟩ := H
  refine ⟨h1, h2, fun p => ?_⟩
  obtain ⟨V, hV, th, s1, α, τ, U, s2, w, u, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h3 p
  obtain ⟨c', hc'⟩ := hc.map V.ι.appTop.hom
  refine ⟨V, hV, th, s1, α, τ, U, s2, w, (c' * (show Γ(V.toScheme, ⊤)ˣ from u) : Γ(V.toScheme, ⊤)ˣ), a1, a2, a3, a4, a5, a6, a7, fun i => ?_⟩
  have aux : ∀ (a : Γ(T.left, ⊤)) (u₀ : Γ(V.toScheme, ⊤)ˣ) (w₀ : Γ(V.toScheme, ⊤)),
      V.ι.appTop.hom a = u₀.val * w₀ → V.ι.appTop.hom (c * a) = (c' * u₀).val * w₀ := by
    intro a u₀ w₀ h
    rw [map_mul, h, Units.val_mul, hc', _root_.mul_assoc]
  exact aux (v i) u (w i) (a8 i)

theorem TObj.HasTh.unit_smul {o : Type} [CommRing o] {S : Scheme.{0}} {g N' : ℕ} {J : Type}
    {b : TBase o (N' ^ 2)} {s : S ⟶ Sp o} {t : TObj g (N' ^ 2) J b s} {R : Type} [CommRing R]
    {x : Sp R ⟶ S} {v : Ix g (N' ^ 2) → R} (H : t.HasTh x v) {c : R} (hc : IsUnit c) :
    t.HasTh x (c • v) := by
  have h := isThetaPt_unit_mul t.pol N' (T := Over.mk x) _ _ _
    (hc.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) H
  unfold TObj.HasTh
  convert h using 2 with a
  exact map_mul (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c (v a)

theorem tmap_of_hasTh_complex : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (em : o →+* ℂ) (t t' : TObj g ((n ^ j) ^ 2) J b (spMap em)) (v : Ix g ((n ^ j) ^ 2) → ℂ) (c : ℂ), c ≠ 0 → t.Shape Mat κ → t'.Shape Mat κ → t.HasTh (𝟙 _) v → t'.HasTh (𝟙 _) (c • v) → TMap t' t (𝟙 _) := by
  intro hL hL2 g J _ Mat κ n hn hodd
  obtain ⟨j₀, H⟩ := GlobalTheory.T.exists_theta_family_from_very_dense_points hL hL2 g J Mat κ n hn hodd
  refine ⟨j₀, fun j hj o _ b em t t' v c hc hs hs' hv hv' => ?_⟩
  have hid : spMap (RingHom.id ℂ) = 𝟙 (Sp ℂ) := Spec.map_id (CommRingCat.of ℂ)
  have hv'' : t'.HasTh (𝟙 _) v := by
    have h := hv'.unit_smul (IsUnit.mk0 c⁻¹ (inv_ne_zero hc))
    rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h
  have key : ∀ s : Sp ℂ ⟶ Sp o, s = spMap (RingHom.id ℂ) ≫ spMap em →
      ∀ t t' : TObj g ((n ^ j) ^ 2) J b s, t.Shape Mat κ → t'.Shape Mat κ →
        t.HasTh (𝟙 _) v → t'.HasTh (𝟙 _) v → TMap t' t (𝟙 _) := by
    intro s hs t t' h1 h1' h2 h2'
    subst hs
    have hvd : VeryDense (objPrimes b Mat κ em v) := by
      intro q f hq hf
      have hq0 : q = ⊥ := (Ideal.eq_bot_or_top q).resolve_right hq.ne_top
      subst hq0
      refine ⟨⊥, ⟨ℂ, inferInstance, inferInstance, RingHom.id ℂ, t, ?_, h1, h2⟩, hq, le_rfl, hf⟩
      exact (RingHom.injective_iff_ker_eq_bot _).1 (RingHom.id ℂ).injective
    obtain ⟨t₀, -, h₀⟩ := H j hj o b ℂ em v hvd
    have m := h₀ ℂ (RingHom.id ℂ) t h1 h2
    have m' := h₀ ℂ (RingHom.id ℂ) t' h1' h2'
    refine ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g _ J b _ _ _ _ _ _ t₀ t t').2 _ (𝟙 _) m).2 ?_
    rwa [Category.id_comp]
  exact key _ (by rw [hid, Category.id_comp]) t t' hs hs' hv hv''

end GlobalTheory.ZM
