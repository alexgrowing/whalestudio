import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsBasisEmbedding

open NumberField
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Published

instance galSMulCommClassIntegers {K L : Type*} [Field K] [Field L] [Algebra K L] :
    SMulCommClass (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) where
  smul_comm s a x := by
    apply RingOfIntegers.ext
    rw [Algebra.smul_def, Algebra.smul_def]
    change s (algebraMap K L a * x) = algebraMap K L a * s x
    rw [map_mul, AlgEquiv.commutes]

section Defs

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]

def IsUnramifiedAbelian (M : IntermediateField K ℂ) : Prop :=
  FiniteDimensional K M ∧ IsAbelianGalois K M ∧
    ∀ (P : Ideal (𝓞 M)) [P.IsPrime], P ≠ ⊥ → Algebra.IsUnramifiedAt (𝓞 K) P

def IsHilbertClassField (H : IntermediateField K ℂ) : Prop :=
  IsUnramifiedAbelian H ∧ ∀ M : IntermediateField K ℂ, IsUnramifiedAbelian M → M ≤ H

def IsArtinMap {H : IntermediateField K ℂ} (art : ClassGroup (𝓞 K) →* (H ≃ₐ[K] H)) : Prop :=
  ∀ (𝔭 : (Ideal (𝓞 K))⁰) (𝔓 : Ideal (𝓞 H)), 𝔓.IsPrime → 𝔓.LiesOver (𝔭 : Ideal (𝓞 K)) →
    IsArithFrobAt (𝓞 K) (art (ClassGroup.mk0 𝔭)) 𝔓

def IsIdealLattice (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L : PeriodPair) : Prop :=
  (L.lattice : Set ℂ) = algebraMap K ℂ '' 𝔞.1

end Defs

def ComplexMultiplicationJSt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Algebra K ℂ],
    Module.finrank ℚ K = 2 →
    ∃ (H : IntermediateField K ℂ) (art : ClassGroup (𝓞 K) ≃* (H ≃ₐ[K] H)),
      IsHilbertClassField H ∧ IsArtinMap art.toMonoidHom ∧
      (∀ (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L : PeriodPair), IsIdealLattice 𝔞 L →
        K⟮(latticeCurve L).j⟯ = H) ∧
      ∀ (𝔞 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L L' : PeriodPair),
        IsIdealLattice 𝔞 L → IsIdealLattice (𝔟⁻¹ * 𝔞) L' →
        ∀ x : H, (x : ℂ) = (latticeCurve L).j →
          (art (ClassGroup.mk K 𝔟) x : ℂ) = (latticeCurve L').j

section Lemmas

variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]

open NumberField in
open scoped nonZeroDivisors IntermediateField in
variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ] in

theorem _root_.GlobalTheory.Published.latticeCurve_j_eq (L : PeriodPair) :
    (_root_.GlobalTheory.latticeCurve L).j = 1728 * L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ',
    _root_.GlobalTheory.latticeCurve_c₄, _root_.GlobalTheory.latticeCurve_Δ]
  ring

open NumberField in
open scoped nonZeroDivisors IntermediateField in
variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ] in

theorem _root_.GlobalTheory.Published.exists_isIdealLattice [IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2)
    (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ∃ L, _root_.GlobalTheory.Published.IsIdealLattice 𝔞 L := by
  have hc : InfinitePlace.nrComplexPlaces K = 1 := by
    have := IsTotallyComplex.finrank (K := K)
    omega
  have hs := sign_discr K
  rw [hc, pow_one, Int.sign_eq_neg_one_iff_neg] at hs
  have hd : discr K = -((-discr K).toNat : ℤ) := by omega
  obtain ⟨L, hL⟩ := _root_.GlobalTheory.QuadraticZeta.exists_periodPair h2 hd (algebraMap K ℂ) 𝔞
  exact ⟨L, hL⟩

omit [NumberField K] in

theorem IsHilbertClassField.unique {H H' : IntermediateField K ℂ} (h : IsHilbertClassField H)
    (h' : IsHilbertClassField H') : H = H' :=
  le_antisymm (h'.2 H h.1) (h.2 H' h'.1)

theorem IsArtinMap.unique {H : IntermediateField K ℂ} (hH : IsUnramifiedAbelian H)
    {f g : ClassGroup (𝓞 K) →* (H ≃ₐ[K] H)} (hf : IsArtinMap f) (hg : IsArtinMap g) : f = g := by
  have := hH.1
  have : NumberField H := NumberField.of_module_finite K H
  ext1 c
  obtain ⟨⟨I, hI⟩, rfl⟩ := ClassGroup.mk0_surjective c
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => simp at hI
  | h₂ x hx =>
    obtain rfl : x = 1 := isUnit_iff_eq_one.mp hx
    change f (ClassGroup.mk0 1) = g (ClassGroup.mk0 1)
    simp
  | h₃ a p ha hp ih =>
    have ha' : a ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero ha
    have hp' : p ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero hp.ne_zero
    change f (ClassGroup.mk0 (⟨p, hp'⟩ * ⟨a, ha'⟩)) = g (ClassGroup.mk0 (⟨p, hp'⟩ * ⟨a, ha'⟩))
    rw [map_mul, map_mul, map_mul, ih ha']
    congr 1
    have : p.IsPrime := Ideal.isPrime_of_prime hp
    obtain ⟨⟨P, hP, hPp⟩⟩ := (inferInstance : Nonempty (p.primesOver (𝓞 H)))
    have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp.ne_zero P
    have := hH.2.2 P hP0
    have e := AlgHom.IsArithFrobAt.eq_of_isUnramifiedAt (hf ⟨p, hp'⟩ P hP hPp)
      (hg ⟨p, hp'⟩ P hP hPp) (Ideal.primeCompl_le_nonZeroDivisors P)
    apply AlgEquiv.coe_ringEquiv_injective
    apply RingEquiv.toRingHom_injective
    refine IsFractionRing.ringHom_ext (A := 𝓞 H) fun x => ?_
    exact congrArg (fun y : 𝓞 H => (y : H)) (DFunLike.congr_fun e x)

theorem ComplexMultiplicationJSt.map_j (h : ComplexMultiplicationJSt) [IsTotallyComplex K]
    (h2 : Module.finrank ℚ K = 2) {H : IntermediateField K ℂ} (hH : IsHilbertClassField H)
    {art : ClassGroup (𝓞 K) →* (H ≃ₐ[K] H)} (hart : IsArtinMap art)
    {𝔞 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {L L' : PeriodPair}
    (hL : IsIdealLattice 𝔞 L) (hL' : IsIdealLattice (𝔟⁻¹ * 𝔞) L') (ρ : ℂ →+* ℂ)
    (hρ : ∀ x : H, ρ x = art (ClassGroup.mk K 𝔟) x) :
    ρ (latticeCurve L).j = (latticeCurve L').j := by
  obtain ⟨H', art', hH', hart', hgen, hj⟩ := h K h2
  obtain rfl := hH.unique hH'
  obtain rfl := hart.unique hH.1 hart'
  have hm : (latticeCurve L).j ∈ H := hgen 𝔞 L hL ▸ IntermediateField.mem_adjoin_simple_self K _
  exact (hρ ⟨_, hm⟩).trans (hj 𝔞 𝔟 L L' hL hL' ⟨_, hm⟩ rfl)

open NumberField in
open scoped nonZeroDivisors IntermediateField in
variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ] in

theorem _root_.GlobalTheory.Published.ComplexMultiplicationJSt.finrank_eq
    (h : _root_.GlobalTheory.Published.ComplexMultiplicationJSt) [IsTotallyComplex K]
    (h2 : Module.finrank ℚ K = 2) {H : IntermediateField K ℂ} (hH : _root_.GlobalTheory.Published.IsHilbertClassField H) :
    Module.finrank K H = classNumber K := by
  obtain ⟨H₀, art, hH₀, -, -, -⟩ := h K h2
  obtain rfl : H = H₀ := le_antisymm (hH₀.2 H hH.1) (hH.2 H₀ hH₀.1)
  haveI := hH.1.1
  haveI := hH.1.2.1
  rw [← IsGalois.card_aut_eq_finrank, ← Nat.card_congr art.toEquiv, classNumber,
    Nat.card_eq_fintype_card]

open NumberField in
open scoped nonZeroDivisors IntermediateField in
variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ] in

theorem _root_.GlobalTheory.Published.ComplexMultiplicationJSt.exists_ideal
    (h : _root_.GlobalTheory.Published.ComplexMultiplicationJSt) [IsTotallyComplex K]
    (h2 : Module.finrank ℚ K = 2) (ρ : ℂ →ₐ[K] ℂ) :
    ∃ 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ, ∀ (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L L' : PeriodPair),
      _root_.GlobalTheory.Published.IsIdealLattice 𝔞 L → _root_.GlobalTheory.Published.IsIdealLattice (𝔟⁻¹ * 𝔞) L' →
        ρ (_root_.GlobalTheory.latticeCurve L).j = (_root_.GlobalTheory.latticeCurve L').j := by
  obtain ⟨H, art, hH, -, hgen, hact⟩ := h K h2
  haveI := hH.1.1
  haveI := hH.1.2.1
  obtain ⟨𝔟, h𝔟⟩ : ∃ 𝔟, ClassGroup.mk K 𝔟 = art.symm (ρ.restrictNormal' H) :=
    ClassGroup.induction K (P := fun c => ∃ 𝔟, ClassGroup.mk K 𝔟 = c) (fun 𝔟 => ⟨𝔟, rfl⟩) _
  refine ⟨𝔟, fun 𝔞 L L' hL hL' => ?_⟩
  have hj : (_root_.GlobalTheory.latticeCurve L).j ∈ H := by
    rw [← hgen 𝔞 L hL]
    exact IntermediateField.mem_adjoin_simple_self K _
  have key := hact 𝔞 𝔟 L L' hL hL' ⟨_, hj⟩ rfl
  rw [h𝔟, MulEquiv.apply_symm_apply] at key
  rw [← key]
  exact (AlgHom.restrictNormal_commutes ρ H ⟨_, hj⟩).symm

end Lemmas

end GlobalTheory.Published
