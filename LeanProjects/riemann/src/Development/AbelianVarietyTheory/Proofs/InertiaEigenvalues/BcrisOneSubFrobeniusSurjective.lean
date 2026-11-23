import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BcrisEqAcrisLocalizationPeriodTStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusAcrisDecompositionMuPower
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisFrobeniusFontaineTEqMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLogTeichmullerAcrisEqMuMulUnit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisLogTeichmullerUniqueGaloisFrobeniusBdR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineTIsUnitBcrisAndUniformizerBdRPlus
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobSubMulSurjective
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMaps
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.OneSubPhi

theorem one_sub_mul_onto (p : ℕ) {A : Type} [CommRing A] (φ : A →+* A)
    (hA : IsAdicComplete (Ideal.span {(p : A)}) A) (x : A) : ∃ y : A, y - (p : A) * φ y = x := by
  have hc : IsAdicComplete (Ideal.span {(p : ℤ)}) A := by
    rw [← IsAdicComplete.map_algebraMap_iff (S := A), Ideal.map_span, Set.image_singleton, map_natCast]
    exact hA
  let f : A →ₗ[ℤ] A :=
    LinearMap.id - ((AddMonoidHom.mulLeft (p : A)).comp φ.toAddMonoidHom).toIntLinearMap
  have hf : ∀ y, f y = y - (p : A) * φ y := fun _ => rfl
  have hs : Function.Surjective f := by
    refine surjective_of_mkQ_comp_surjective (I := Ideal.span {(p : ℤ)}) fun G => ?_
    obtain ⟨g, rfl⟩ := Submodule.mkQ_surjective _ G
    refine ⟨g, ?_⟩
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hf]
    have : g - (p : A) * φ g - g = (p : ℤ) • (-φ g) := by simp
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  obtain ⟨y, hy⟩ := hs x
  exact ⟨y, (hf y).symm.trans hy⟩

theorem onto_of_denom (p : ℕ) {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (φ : A →+* A)
    (ψ : B →+* B) (hψ : ∀ x, ψ (f x) = f (φ x)) (t : A) (ht : φ t = (p : A) * t)
    (hT : IsUnit (f t)) (hp : IsUnit (p : B))
    (h0 : ∀ x : A, ∃ y : A, y - (p : A) * φ y = x)
    (h1 : ∀ (r : ℕ) (x : A), ∃ β z : A, (p : A) * φ x = (p : A) * (φ β - (p : A) ^ r * β) + t * z)
    (r : ℕ) : ∀ (x : A) (b : B), b * f t ^ r = f x * f t → ∃ y : B, y - ψ y = b := by
  have hψT : ψ (f t) = (p : B) * f t := by rw [hψ, ht, map_mul, map_natCast]
  induction r with
  | zero =>
    intro x b hb
    obtain ⟨y, hy⟩ := h0 x
    refine ⟨f y * f t, ?_⟩
    have e := congrArg f hy
    rw [map_sub, map_mul, map_natCast] at e
    rw [map_mul, hψT, hψ]
    linear_combination f t * e - hb
  | succ r ih =>
    intro x b hb
    have hb' : b * f t ^ r = f x := hT.mul_right_cancel (by rw [← hb]; ring)
    obtain ⟨β, z, hz⟩ := h1 r x
    obtain ⟨s, hs⟩ := (hT.pow r).exists_left_inv
    obtain ⟨q, hq⟩ := (hp.pow (r + 1)).exists_left_inv
    have hψq : ψ q * (p : B) ^ (r + 1) = 1 := by
      have := congrArg ψ hq
      rwa [map_mul, map_pow, map_natCast, map_one] at this
    have eq : ψ q = q := by linear_combination q * hψq - ψ q * hq
    have hψs : ψ s * ((p : B) ^ r * f t ^ r) = 1 := by
      have := congrArg ψ hs
      rwa [map_mul, map_pow, hψT, map_one, mul_pow] at this
    obtain ⟨y, hy⟩ := ih z (f z * f t * s) (by rw [mul_assoc, hs, mul_one])
    have e1 := congrArg ψ hb'
    rw [map_mul, map_pow, hψT, hψ, mul_pow] at e1
    have e2 := congrArg f hz
    simp only [map_mul, map_add, map_sub, map_pow, map_natCast] at e2
    refine ⟨b - f β * s + q * y, ?_⟩
    rw [map_add, map_sub, map_mul, map_mul, eq, hψ]
    apply ((hp.pow (r + 1)).mul (hT.pow r)).mul_left_cancel
    linear_combination -(p : B) * e1 - e2 - (p : B) ^ (r + 1) * f β * hs + (p : B) * f (φ β) * hψs
      + f t ^ r * (y - ψ y) * hq + f t ^ r * hy + f z * f t * hs

variable {l : ℕ} [Fact l.Prime]

theorem ainf_onto (r : ℕ) (a : Per.Ainf l) : ∃ β : Per.Ainf l, Per.φA l β - (l : Per.Ainf l) ^ r * β = a := by
  obtain ⟨β, hβ⟩ := (ArtinSchreierWitt.main l).2.2 ((l : Per.Ainf l) ^ r) a
  exact ⟨β, by rw [GlobalTheory.RingBasics.φA_apply]; exact hβ⟩

theorem phiA_alg (a : Per.Ainf l) : phiA l (algebraMap (Per.Ainf l) (Per.Acris l) a) =
    algebraMap (Per.Ainf l) (Per.Acris l) (Per.φA l a) := (GlobalTheory.CrisMaps.phiA_extends l).alg a

theorem exists_w (e : Per.Fl l) (he : e.untilt = 1) : ∃ w : Per.Acris l,
    (l : Per.Acris l) * w = algebraMap (Per.Ainf l) (Per.Acris l) (mu e) ^ (l - 1) := by
  obtain ⟨w, hw, -⟩ := exists_mu_pow_div l e he
  have hw0 : (l : Per.Acris0 l) * w = algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e) ^ (l - 1) :=
    Subtype.ext (by simpa using hw)
  have hw1 := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) hw0
  rw [map_mul, map_natCast, map_pow, ← TFil.alg_factor] at hw1
  exact ⟨_, hw1⟩

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem mul_phi_mem (C : Core l) (x : Per.Acris l) : ∃ (a : Per.Ainf l) (z : Per.Acris l),
    (l : Per.Acris l) * phiA l x = (l : Per.Acris l) * algebraMap (Per.Ainf l) (Per.Acris l) a + C.t * z := by
  have he := core_isEps l C
  obtain ⟨t, u, ht, hu, htu⟩ := exists_isLogA l C.ε he.1
  have e1 : t = C.t := (LogFun.log_fun l C.ε C.t he.1 C.t_log).1 t ht
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  obtain ⟨w, hw⟩ := exists_w C.ε he.1
  obtain ⟨a, z, hz⟩ := phiA_mem_ainf_add l C.ε he w hw x
  have h2 : l - 1 = l - 2 + 1 := by
    have := (Fact.out : l.Prime).two_le
    omega
  rw [h2, pow_succ] at hw
  generalize algebraMap (Per.Ainf l) (Per.Acris l) (mu C.ε) = m at hw htu
  refine ⟨a, v * m ^ (l - 2) * z, ?_⟩
  rw [hz, ← e1, htu]
  linear_combination z * hw - m * m ^ (l - 2) * z * hv

end GlobalTheory.MemLoc.OneSubPhi

namespace GlobalTheory.MemLoc

theorem one_sub_phi_onto (l : ℕ) [Fact l.Prime] (C : Core l) : C.OneSubPhiOnto := by
  intro b
  obtain ⟨r, x, hx⟩ := GlobalTheory.T.bcris_eq_acris_localization_periodT l C b
  obtain ⟨hT, -, -, hl⟩ := core_t_unit_fil l C
  refine OneSubPhi.onto_of_denom l (algebraMap (Per.Acris l) (Per.Bcris l)) (phiA l) (Per.φB l)
    (ActLaws.act_laws l).2.2.2.2.2.2.2.2.2.2.2.2 C.t (TPhi.t_phi l C) hT hl
    (OneSubPhi.one_sub_mul_onto l (phiA l) (acris_basic l).1) (fun s y => ?_) (r + 1) x b
    (by rw [pow_succ, ← mul_assoc, hx])
  obtain ⟨a, z, hz⟩ := OneSubPhi.mul_phi_mem C y
  obtain ⟨β, hβ⟩ := OneSubPhi.ainf_onto s a
  refine ⟨algebraMap (Per.Ainf l) (Per.Acris l) β, z, ?_⟩
  rw [hz, ← hβ, OneSubPhi.phiA_alg, map_sub, map_mul, map_pow, map_natCast]

end GlobalTheory.MemLoc
