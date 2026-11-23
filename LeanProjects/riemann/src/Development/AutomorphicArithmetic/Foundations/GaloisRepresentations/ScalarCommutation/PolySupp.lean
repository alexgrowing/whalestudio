import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.TypeSlice
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.CommensuratedOfIsOpenIsCompact

set_option autoImplicit false

open Formalism.UG (Hecke conv IsCommensurated)
open UpperTheory.Gal.LocalSmoothExtension (wordFn polyFn)

namespace UpperTheory.Gal.Spc

section Abstract

variable {H J : Type} [Group H] {K : Subgroup H}

private theorem word_mem (hK : IsCommensurated K) {ψ : J → H → ℂ} (hψ : ∀ j, ψ j ∈ Hecke ℂ K) {f : H → ℂ}
    (hf : f ∈ Hecke ℂ K) (w : List J) : wordFn K ψ w f ∈ Hecke ℂ K := by
  induction w with
  | nil => exact hf
  | cons j w ih => exact Formalism.UG.Final.HeckeConvMem H K ℂ hK _ (hψ j) _ ih

private theorem poly_mem (hK : IsCommensurated K) {ψ : J → H → ℂ} (hψ : ∀ j, ψ j ∈ Hecke ℂ K) {f : H → ℂ}
    (hf : f ∈ Hecke ℂ K) (s : List J →₀ ℂ) : polyFn K ψ s f ∈ Hecke ℂ K := by
  unfold UpperTheory.Gal.LocalSmoothExtension.polyFn
  exact Submodule.sum_mem _ fun w _ => Submodule.smul_mem _ _ (word_mem hK hψ hf w)

private theorem pow_mem (hK : IsCommensurated K) {u e : H → ℂ} (hu : u ∈ Hecke ℂ K) (he : e ∈ Hecke ℂ K) (n : ℕ) :
    powFn K u e n ∈ Hecke ℂ K := by
  induction n with
  | zero => exact he
  | succ n ih =>
    rw [powFn, Function.iterate_succ_apply']
    exact Formalism.UG.Final.HeckeConvMem H K ℂ hK _ hu _ ih

private theorem fix_step (hK : IsCommensurated K) {e t x : H → ℂ} (he : e ∈ Hecke ℂ K) (ht : t ∈ Hecke ℂ K)
    (hx : x ∈ Hecke ℂ K) (hte : conv K e (conv K t e) = conv K t e) (hex : conv K e x = x) :
    conv K e (conv K t x) = conv K t x := by
  have A := Formalism.UG.Final.HeckeAssoc H K ℂ hK
  have M := Formalism.UG.Final.HeckeConvMem H K ℂ hK
  calc conv K e (conv K t x) = conv K e (conv K t (conv K e x)) := by rw [hex]
    _ = conv K e (conv K (conv K t e) x) := by rw [A t ht e he x hx]
    _ = conv K (conv K e (conv K t e)) x := by rw [A e he (conv K t e) (M t ht e he) x hx]
    _ = conv K (conv K t e) x := by rw [hte]
    _ = conv K t (conv K e x) := by rw [A t ht e he x hx]
    _ = conv K t x := by rw [hex]

private theorem pow_fix (hK : IsCommensurated K) {u e : H → ℂ} (hu : u ∈ Hecke ℂ K) (he : e ∈ Hecke ℂ K)
    (hidem : conv K e e = e) (heu : conv K e (conv K u e) = conv K u e) (n : ℕ) :
    conv K e (powFn K u e n) = powFn K u e n := by
  induction n with
  | zero => exact hidem
  | succ n ih =>
    rw [powFn, Function.iterate_succ_apply']
    exact fix_step hK he hu (pow_mem hK hu he n) heu ih

private theorem word_fix (hK : IsCommensurated K) {ψ : J → H → ℂ} (hψ : ∀ j, ψ j ∈ Hecke ℂ K) {e f : H → ℂ}
    (he : e ∈ Hecke ℂ K) (hf : f ∈ Hecke ℂ K) (heT : ∀ j, conv K e (conv K (ψ j) e) = conv K (ψ j) e)
    (hef : conv K e f = f) (w : List J) : conv K e (wordFn K ψ w f) = wordFn K ψ w f := by
  induction w with
  | nil => exact hef
  | cons j w ih => exact fix_step hK he (hψ j) (word_mem hK hψ hf w) (heT j) ih

private theorem comm_fix (hK : IsCommensurated K) {e a b x : H → ℂ} (he : e ∈ Hecke ℂ K) (ha : a ∈ Hecke ℂ K)
    (hb : b ∈ Hecke ℂ K) (hx : x ∈ Hecke ℂ K) (hab : conv K a (conv K b e) = conv K b (conv K a e))
    (hex : conv K e x = x) : conv K a (conv K b x) = conv K b (conv K a x) := by
  have A := Formalism.UG.Final.HeckeAssoc H K ℂ hK
  have M := Formalism.UG.Final.HeckeConvMem H K ℂ hK
  calc conv K a (conv K b x) = conv K a (conv K b (conv K e x)) := by rw [hex]
    _ = conv K a (conv K (conv K b e) x) := by rw [A b hb e he x hx]
    _ = conv K (conv K a (conv K b e)) x := by rw [A a ha (conv K b e) (M b hb e he) x hx]
    _ = conv K (conv K b (conv K a e)) x := by rw [hab]
    _ = conv K b (conv K (conv K a e) x) := by rw [A b hb (conv K a e) (M a ha e he) x hx]
    _ = conv K b (conv K a (conv K e x)) := by rw [A a ha e he x hx]
    _ = conv K b (conv K a x) := by rw [hex]

private theorem conv_supp {a f : H → ℂ} {g : H} (h : conv K a f g ≠ 0) : ∃ x : H, a x ≠ 0 ∧ f (x⁻¹ * g) ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  unfold Formalism.UG.conv
  apply finsum_eq_zero_of_forall_eq_zero
  intro q
  by_cases ha : a (Quotient.out q) = 0
  · rw [ha, zero_mul]
  · rw [hc _ ha, mul_zero]

private theorem word_supp {ψ : J → H → ℂ} {f : H → ℂ} {R : Set H} (hR : ∀ j a, ψ j a ≠ 0 → ∀ g ∈ R, a * g ∈ R)
    (hf : ∀ g, f g ≠ 0 → g ∈ R) (w : List J) : ∀ g, wordFn K ψ w f g ≠ 0 → g ∈ R := by
  induction w with
  | nil => exact hf
  | cons j w ih =>
    intro g hg
    obtain ⟨x, hx1, hx2⟩ := conv_supp (K := K) (a := ψ j) (f := wordFn K ψ w f) hg
    have hx := hR j x hx1 _ (ih _ hx2)
    simpa using hx

private theorem poly_supp {ψ : J → H → ℂ} {f : H → ℂ} {R : Set H} (hR : ∀ j a, ψ j a ≠ 0 → ∀ g ∈ R, a * g ∈ R)
    (hf : ∀ g, f g ≠ 0 → g ∈ R) (s : List J →₀ ℂ) (g : H) (hg : polyFn K ψ s f g ≠ 0) : g ∈ R := by
  by_contra hgR
  apply hg
  unfold UpperTheory.Gal.LocalSmoothExtension.polyFn
  rw [Finsupp.sum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro w _
  rw [Pi.smul_apply, smul_eq_mul]
  have hw : wordFn K ψ w f g = 0 := by
    by_contra hne
    exact hgR (word_supp (K := K) hR hf w g hne)
  rw [hw, mul_zero]

end Abstract

theorem words : Words := by
  intro p _ G Lv J ψ e u u' hψ he hu hrel n
  have hK : IsCommensurated (Lv.K : Subgroup G.GAf) :=
    PI.UnitaryGroupMassFormula.AdIndexEq.commensurated_of_isOpen_isCompact _ Lv.K.isOpen Lv.compact
  have hP := pow_mem hK hu he n
  have hfix := pow_fix hK hu he hrel.idem hrel.eu n
  refine ⟨hP, fun s => poly_mem hK hψ hP s, fun j j' w => ?_, fun R hR hf s g hg => poly_supp hR hf s g hg⟩
  exact comm_fix hK he (hψ j) (hψ j') (word_mem hK hψ hP w) (hrel.TT j j') (word_fix hK hψ he hP hrel.eT hfix w)

end UpperTheory.Gal.Spc
