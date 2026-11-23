import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral

noncomputable section

open GlobalTheory.Prism

namespace GlobalTheory.BSP

def fracMap {A : Type} [CommRing A] {N P : Type} [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]
    (S : Submonoid A) (L : P →ₗ[A] N) (s : ↥S) : P →ₗ[A] LocalizedModule S N where
  toFun y := LocalizedModule.mk (L y) s
  map_add' x y := by
    rw [LocalizedModule.mk_add_mk, LocalizedModule.mk_eq]
    exact ⟨1, by simp [mul_smul]⟩
  map_smul' c x := by
    rw [map_smul, RingHom.id_apply, LocalizedModule.smul'_mk]

theorem isLocalizedModule_fracMap {A : Type} [CommRing A] (t : A) {N P : Type} [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A P] (L : P →ₗ[A] N) (n : ℕ) (hk : ∀ y, L y = 0 → t ^ n • y = 0)
    (hc : ∀ x, ∃ y, L y = t ^ n • x) (s : ↥(Submonoid.powers t)) :
    IsLocalizedModule (Submonoid.powers t) (fracMap (Submonoid.powers t) L s) where
  map_units := IsLocalizedModule.map_units (LocalizedModule.mkLinearMap (Submonoid.powers t) N)
  surj z := by
    induction z using LocalizedModule.induction_on with
    | _ m r =>
      obtain ⟨y, hy⟩ := hc m
      refine ⟨⟨(s : A) • y, r * ⟨t ^ n, n, rfl⟩⟩, ?_⟩
      change ((r : A) * t ^ n) • LocalizedModule.mk m r = LocalizedModule.mk (L ((s : A) • y)) s
      rw [LocalizedModule.smul'_mk, LocalizedModule.mk_eq, map_smul, hy]
      refine ⟨1, ?_⟩
      simp only [Submonoid.smul_def, smul_smul]
      congr 1
      ring
  exists_of_eq {x y} h := by
    change LocalizedModule.mk (L x) s = LocalizedModule.mk (L y) s at h
    rw [LocalizedModule.mk_eq] at h
    obtain ⟨c, h⟩ := h
    refine ⟨⟨t ^ n, n, rfl⟩ * (c * s), ?_⟩
    have h1 := hk (((c : A) * s) • (x - y)) (by
      rw [map_smul, map_sub, smul_sub, sub_eq_zero, mul_smul, mul_smul]
      exact h)
    rw [smul_smul, smul_sub, sub_eq_zero] at h1
    exact h1

theorem semiBC_localized (A : Type) [CommRing A] (φ : A →+* A) (t : A) (N : Type) [AddCommGroup N] [Module A N]
    (P : Type) [AddCommGroup P] [Module A P] (u : N →ₛₗ[φ] P) (hu : SemiBC u) (L : P →ₗ[A] N) (n a : ℕ)
    (hk : ∀ y, L y = 0 → t ^ n • y = 0) (hc : ∀ x, ∃ y, L y = t ^ n • x)
    (Φ : N →ₛₗ[(algebraMap A (Localization.Away t)).comp φ] LocalizedModule (Submonoid.powers t) N)
    (hΦ : ∀ x, IsFrac t (Φ x) (L (u x)) a) : SemiBC Φ := by
  intro Q _ _ v
  letI : Module A Q := Module.compHom Q (algebraMap A (Localization.Away t))
  haveI : IsScalarTower A (Localization.Away t) Q := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let s : ↥(Submonoid.powers t) := ⟨t ^ a, a, rfl⟩
  haveI := isLocalizedModule_fracMap t L n hk hc s
  have hb := IsLocalizedModule.isBaseChange (Submonoid.powers t) (Localization.Away t)
    (fracMap (Submonoid.powers t) L s)
  have hΦ' : ∀ x, Φ x = fracMap (Submonoid.powers t) L s (u x) := hΦ
  let v' : N →ₛₗ[φ] Q :=
    { toFun := v
      map_add' := v.map_add
      map_smul' := fun c x => v.map_smulₛₗ c x }
  obtain ⟨w₀, hw₀, hun⟩ := hu Q v'
  refine ⟨hb.lift w₀, fun x => ?_, fun w hw => ?_⟩
  · rw [hΦ', hb.lift_eq]
    exact hw₀ x
  · refine hb.algHom_ext _ _ fun y => ?_
    rw [hb.lift_eq, ← hun ((w.restrictScalars A).comp (fracMap (Submonoid.powers t) L s))
      fun x => (congrArg w (hΦ' x).symm).trans (hw x)]
    rfl

end GlobalTheory.BSP
