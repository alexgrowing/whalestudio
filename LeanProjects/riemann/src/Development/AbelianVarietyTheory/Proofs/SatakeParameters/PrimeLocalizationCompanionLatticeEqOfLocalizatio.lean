import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open Formalism.UG (bc prV)
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.CompanLocP

section General

variable {R : Type*} [CommRing R] {W : Type*} [AddCommGroup W] [Module R W]

theorem mem_locP (p : Ideal R) [p.IsPrime] (M : Submodule R W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ p M ↔ ∃ s ∈ p.primeCompl, s • x ∈ M := Iff.rfl

theorem le_locP (p : Ideal R) [p.IsPrime] (M : Submodule R W) : M ≤ Formalism.HermitianLatticesTheory.localization₂ p M :=
  fun x hx => (mem_locP p M x).2 ⟨1, p.primeCompl.one_mem, by simpa using hx⟩

theorem localization_mono (p : Ideal R) [p.IsPrime] {M M₁ : Submodule R W} (h : M ≤ M₁) :
    Formalism.HermitianLatticesTheory.localization₂ p M ≤ Formalism.HermitianLatticesTheory.localization₂ p M₁ := by
  intro x hx
  obtain ⟨s, hs, hx⟩ := (mem_locP p M x).1 hx
  exact (mem_locP p M₁ x).2 ⟨s, hs, h hx⟩

theorem localization_le_localization_of_le_localization (p : Ideal R) [p.IsPrime] {M M₁ : Submodule R W}
    (h : M ≤ Formalism.HermitianLatticesTheory.localization₂ p M₁) : Formalism.HermitianLatticesTheory.localization₂ p M ≤ Formalism.HermitianLatticesTheory.localization₂ p M₁ := by
  intro x hx
  obtain ⟨s, hs, hx⟩ := (mem_locP p M x).1 hx
  obtain ⟨t, ht, hx'⟩ := (mem_locP p M₁ _).1 (h hx)
  refine (mem_locP p M₁ x).2 ⟨t * s, p.primeCompl.mul_mem ht hs, ?_⟩
  rw [mul_smul]
  exact hx'

end General

section Form

variable {E : Type} [Field E] [NumberField E] {N : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E)

theorem hform_smul_right (x y : Fin N → E) (c : E) :
    Formalism.UG.hform σ J x (c • y) = c * Formalism.UG.hform σ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_smul_left (x y : Fin N → E) (c : E) :
    Formalism.UG.hform σ J (c • x) y = σ c * Formalism.UG.hform σ J x y := by
  simp only [Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_add_left (x x' y : Fin N → E) :
    Formalism.UG.hform σ J (x + x') y = Formalism.UG.hform σ J x y + Formalism.UG.hform σ J x' y := by
  simp only [Formalism.UG.hform, Pi.add_apply, map_add, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hform_zero_left (y : Fin N → E) : Formalism.UG.hform σ J 0 y = 0 := by
  simp [Formalism.UG.hform]

theorem ointSmul (s : 𝓞 E) (y : Fin N → E) : s • y = (s : E) • y :=
  (algebraMap_smul E s y).symm

theorem span_dualSet_le (q : Ideal (𝓞 E)) [q.IsPrime] (Λ Λ' : Submodule (𝓞 E) (Fin N → E)) (hΛ' : Λ'.FG)
    (h' : Λ' ≤ Formalism.HermitianLatticesTheory.localization₂ (q.comap (RingOfIntegers.mapRingHom σ)) Λ) :
    Submodule.span (𝓞 E) (dualSet σ J Λ) ≤
      Formalism.HermitianLatticesTheory.localization₂ q (Submodule.span (𝓞 E) (dualSet σ J Λ')) := by
  classical
  rw [Submodule.span_le]
  intro y hy
  obtain ⟨S, hS⟩ := hΛ'
  have hgen : ∀ g ∈ S, ∃ s ∈ q.primeCompl,
      ((s : 𝓞 E) : E) * Formalism.UG.hform σ J g y ∈ (algebraMap (𝓞 E) E).range := by
    intro g hg
    obtain ⟨t, ht, htg⟩ := (mem_locP _ _ _).1 (h' (hS ▸ Submodule.subset_span hg))
    refine ⟨RingOfIntegers.mapRingHom σ t, ht, ?_⟩
    have e : Formalism.UG.hform σ J (t • g) y = ((RingOfIntegers.mapRingHom σ t : 𝓞 E) : E) * Formalism.UG.hform σ J g y := by
      rw [ointSmul, hform_smul_left]
      rfl
    rw [← e]
    exact hy _ htg
  choose! f hf hf' using hgen
  refine (mem_locP _ _ _).2 ⟨∏ g ∈ S, f g, q.primeCompl.prod_mem (fun g hg => hf g hg), Submodule.subset_span ?_⟩
  intro x hx
  rw [← hS] at hx
  rw [ointSmul, hform_smul_right]
  induction hx using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem f hg
    rw [hc, mul_comm (f g) c, show ((c * f g : 𝓞 E) : E) = (c : E) * (f g : E) from map_mul (algebraMap (𝓞 E) E) c (f g), mul_assoc]
    exact Subring.mul_mem _ ⟨c, rfl⟩ (hf' g hg)
  | zero =>
    rw [hform_zero_left, mul_zero]
    exact Subring.zero_mem _
  | add x x' _ _ hx hx' =>
    rw [hform_add_left, mul_add]
    exact Subring.add_mem _ hx hx'
  | smul c x _ hx =>
    rw [ointSmul, hform_smul_left, mul_left_comm]
    exact Subring.mul_mem _ ⟨RingOfIntegers.mapRingHom σ c, rfl⟩ hx

end Form

theorem locP_companion_le {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (q : Ideal (𝓞 E)) [q.IsPrime]
    (Λ Λ' : Submodule (𝓞 E) (Fin N → E)) (hΛ' : Λ'.FG)
    (h : Formalism.HermitianLatticesTheory.localization₂ q Λ = Formalism.HermitianLatticesTheory.localization₂ q Λ')
    (h' : Formalism.HermitianLatticesTheory.localization₂ (q.comap (RingOfIntegers.mapRingHom (sp.cm.sig : E →+* E))) Λ =
      Formalism.HermitianLatticesTheory.localization₂ (q.comap (RingOfIntegers.mapRingHom (sp.cm.sig : E →+* E))) Λ') :
    Formalism.HermitianLatticesTheory.localization₂ q (compan (sp := sp) J a Λ) ≤ Formalism.HermitianLatticesTheory.localization₂ q (compan (sp := sp) J a Λ') := by
  apply localization_le_localization_of_le_localization
  unfold compan
  refine sup_le ((le_locP q Λ).trans (h.le.trans (localization_mono q le_sup_left))) ?_
  refine Submodule.smul_le.2 fun r hr m hm => ?_
  have hd := span_dualSet_le (sp.cm.sig : E →+* E) J q Λ Λ' hΛ' ((le_locP _ Λ').trans h'.symm.le) hm
  obtain ⟨s, hs, hsm⟩ := (mem_locP _ _ _).1 hd
  refine (mem_locP _ _ _).2 ⟨s, hs, ?_⟩
  rw [smul_comm]
  exact Submodule.mem_sup_right (Submodule.smul_mem_smul hr hsm)

theorem locP_companion_eq : ∀ {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (a : 𝓞 E) (q : Ideal (𝓞 E)) [q.IsPrime]
    (Λ Λ' : Submodule (𝓞 E) (Fin N → E)), Λ.FG → Λ'.FG →
    Formalism.HermitianLatticesTheory.localization₂ q Λ = Formalism.HermitianLatticesTheory.localization₂ q Λ' →
    Formalism.HermitianLatticesTheory.localization₂ (q.comap (RingOfIntegers.mapRingHom (sp.cm.sig : E →+* E))) Λ =
      Formalism.HermitianLatticesTheory.localization₂ (q.comap (RingOfIntegers.mapRingHom (sp.cm.sig : E →+* E))) Λ' →
    Formalism.HermitianLatticesTheory.localization₂ q (compan (sp := sp) J a Λ) = Formalism.HermitianLatticesTheory.localization₂ q (compan (sp := sp) J a Λ') := by
  intro R F E _ _ _ _ _ _ sp N J a q _ Λ Λ' hΛ hΛ' h h'
  exact le_antisymm (locP_companion_le sp J a q Λ Λ' hΛ' h h') (locP_companion_le sp J a q Λ' Λ hΛ h.symm h'.symm)

end GlobalTheory.CompanLocP

end
