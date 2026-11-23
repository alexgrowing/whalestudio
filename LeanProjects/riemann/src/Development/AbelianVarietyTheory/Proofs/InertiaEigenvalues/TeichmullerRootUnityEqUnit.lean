import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

open Polynomial in

theorem exists_zmod_of_pow_eq_self {F : Type} [CommRing F] [IsDomain F] (l : ℕ) [Fact l.Prime] [CharP F l]
    (ζ : F) (h : ζ ^ l = ζ) : ∃ a : ZMod l, ZMod.castHom (dvd_refl l) F a = ζ := by
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  set P : (ZMod l)[X] := X ^ l - X with hP
  have hmon : P.Monic := by
    apply Polynomial.monic_X_pow_sub
    simp [hl]
  have hroots : P.roots = Finset.univ.val := by
    have := FiniteField.roots_X_pow_card_sub_X (ZMod l)
    rwa [ZMod.card] at this
  have hdeg : P.natDegree = l := FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod l) hl
  have hprod : (Multiset.map (fun a => X - C a) P.roots).prod = P :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon
      (by rw [hroots, hdeg]; simp [ZMod.card])
  have hev := congrArg (fun Q : (ZMod l)[X] => Q.eval₂ (ZMod.castHom (dvd_refl l) F) ζ) hprod
  simp only [hP, eval₂_sub, eval₂_X_pow, eval₂_X, h, sub_self] at hev
  rw [Polynomial.eval₂_multiset_prod, Multiset.map_map] at hev
  obtain ⟨q, hq, hq0⟩ : ∃ q ∈ _, q = (0:F) := ⟨0, Multiset.prod_eq_zero_iff.1 hev, rfl⟩
  rw [Multiset.mem_map] at hq
  obtain ⟨a, -, rfl⟩ := hq
  refine ⟨a, ?_⟩
  simp only [Function.comp, eval₂_sub, eval₂_X, eval₂_C] at hq0
  exact (sub_eq_zero.1 hq0).symm

theorem padicInt_ringHom_witt_ext_pt {l : ℕ} [Fact l.Prime] {F : Type} [CommRing F] [CharP F l]
    (f g : ℤ_[l] →+* WittVector l F) : f = g := by
  ext x n
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec (n + 1) x)
  have hx : x = (x.appr (n + 1) : ℤ_[l]) + y * (l : ℤ_[l]) ^ (n + 1) := by rw [hy]; ring
  have hd : f x = g x + (f y - g y) * (l : WittVector l F) ^ (n + 1) := by
    conv_lhs => rw [hx]
    conv_rhs => rw [hx]
    simp only [map_add, map_mul, map_pow, map_natCast]
    ring
  have ht : WittVector.truncate (n + 1) ((f y - g y) * (l : WittVector l F) ^ (n + 1)) = 0 := by
    rw [← RingHom.mem_ker, WittVector.mem_ker_truncate]
    intro i hi
    exact WittVector.mul_pow_charP_coeff_zero _ hi
  have he : WittVector.truncate (n + 1) (f x) = WittVector.truncate (n + 1) (g x) := by
    rw [hd, map_add, ht, add_zero]
  have := congrArg (fun z => TruncatedWittVector.coeff (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) z) he
  simpa only [WittVector.coeff_truncate] using this

theorem teichmuller_root_unity_eq_unit : ∀ (l : ℕ) [Fact l.Prime] (ζ : Formalism.Per.Fl l), ζ ^ l = ζ → ζ ≠ 0 →
    ∃ c : ℤ_[l], IsUnit c ∧ zc l c = tc l ζ := by
  intro l _ ζ h hne
  obtain ⟨a, rfl⟩ := exists_zmod_of_pow_eq_self l ζ h
  have ha : a ≠ 0 := by rintro rfl; exact hne (map_zero _)
  refine ⟨WittVector.toPadicInt l (WittVector.teichmuller l a), ?_, ?_⟩
  · exact ((Ne.isUnit ha).map (WittVector.teichmuller l)).map (WittVector.toPadicInt l)
  · have hz : Formalism.Per.zA l = (WittVector.map (ZMod.castHom (dvd_refl l) (Formalism.Per.Fl l))).comp
        (WittVector.fromPadicInt l) := padicInt_ringHom_witt_ext_pt _ _
    simp only [zc, tc, RingHom.comp_apply, hz, Formalism.Per.tm]
    have hft : WittVector.fromPadicInt l (WittVector.toPadicInt l (WittVector.teichmuller l a)) =
        WittVector.teichmuller l a :=
      RingHom.congr_fun (WittVector.fromPadicInt_comp_toPadicInt (p := l)) _
    rw [hft, WittVector.map_teichmuller]

end GlobalTheory.PMon.Gauss
