import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.StepTStA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.LemSec

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

theorem ringKrullDim_le_of_isIntegral' {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] : ringKrullDim S ≤ ringKrullDim R := by
  unfold ringKrullDim
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) ?_
  intro P Q hPQ
  exact Ideal.IsIntegral.comap_lt_comap (I := P.asIdeal) (J := Q.asIdeal) hPQ

section Arith

variable {Ω : Type*} [Field Ω] [CharZero Ω]

theorem X_mem_coordIdeal_iff {J : Type} (v : J → Ω) (i : J) :
    (X i : MvPolynomial J ℤ) ∈ coordIdeal ℤ v ↔ v i = 0 := by
  rw [coordIdeal, RingHom.mem_ker, coneMap, aeval_X, mul_eq_zero, Polynomial.C_eq_zero]
  simp [Polynomial.X_ne_zero]

theorem isHorizontal_coordIdeal {κ : Type} (v : Ix κ → Ω) :
    IsHorizontal (ι := GlobalTheory κ) (coordIdeal ℤ v) := by
  rw [IsHorizontal, eq_bot_iff]
  intro n hn
  rw [Ideal.mem_comap, coordIdeal, RingHom.mem_ker, coneMap, aeval_C] at hn
  rw [Submodule.mem_bot]
  simpa using hn

theorem isMultiHomogIdeal_coordIdeal {κ : Type} [Fintype κ] (v : Ix κ → Ω) :
    IsMultiHomogIdeal (ι := GlobalTheory κ) (coordIdeal ℤ v) := by
  refine ⟨{f | f ∈ coordIdeal ℤ v ∧ ∃ n, f.IsHomogeneous n}, ?_, ?_⟩
  · rintro f ⟨_, n, hn⟩
    refine ⟨fun _ => n, fun m hm k => ?_⟩
    have h1 : Finsupp.degree m = n := by
      rw [Finsupp.degree_eq_weight_one]
      exact hn (mem_support_iff.mp hm)
    rw [Finsupp.degree_eq_sum, Fintype.sum_sigma] at h1
    cases k
    simpa using h1
  · apply le_antisymm
    · intro f hf
      rw [← sum_homogeneousComponent f]
      exact Ideal.sum_mem _ fun d _ => Ideal.subset_span
        ⟨coordIdeal_isHomogIdeal ℤ v f hf d, d, homogeneousComponent_isHomogeneous d f⟩
    · exact Ideal.span_le.mpr fun f hf => hf.1

theorem coneMap_rename {J J' : Type} (v : J → Ω) (e : J' → J) (p : MvPolynomial J' ℤ) :
    coneMap ℤ v (rename e p) = coneMap ℤ (v ∘ e) p := by
  rw [coneMap, coneMap, aeval_rename]
  rfl

end Arith

section Dim

variable {Ω : Type*} [Field Ω] [CharZero Ω] {J : Type} [Fintype J] {D : ℕ}

theorem isIntegralElem_of_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (val : S →+* T) (hval : Function.Injective val) {s : S}
    (h : (val.comp f).IsIntegralElem (val s)) : f.IsIntegralElem s := by
  obtain ⟨p, hp, he⟩ := h
  refine ⟨p, hp, hval ?_⟩
  rw [map_zero, ← he, Polynomial.hom_eval₂]

theorem isIntegralElem_coneMap (v : J → Ω) (e : Fin (D + 1) → J) (hf : IsProjFrame v e)
    (q : MvPolynomial J ℤ) :
    (coneMap ℤ (v ∘ e) : MvPolynomial (Fin (D + 1)) ℤ →+* Polynomial Ω).IsIntegralElem
      (coneMap ℤ v q) := by
  have hinj : Function.Injective (coneMap ℤ (v ∘ e)) := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    have : p ∈ coordIdeal ℤ (v ∘ e) := by simpa [coordIdeal, RingHom.mem_ker] using hp
    rw [hf.free] at this
    exact (Ideal.mem_bot).mp this
  set φ := AlgEquiv.ofInjective (coneMap ℤ (v ∘ e)) hinj
  have hgen : ∀ i, (coneMap ℤ (v ∘ e) : MvPolynomial (Fin (D + 1)) ℤ →+* Polynomial Ω).IsIntegralElem
      (Polynomial.C (v i) * Polynomial.X) := by
    intro i
    have hi : IsIntegral (coneMap ℤ (v ∘ e)).range (Polynomial.C (v i) * Polynomial.X : Polynomial Ω) :=
      hf.integral i
    obtain ⟨p, hp, hps⟩ := hi
    refine ⟨p.map φ.symm.toRingEquiv.toRingHom,
      hp.map _, ?_⟩
    have hcomp : ((coneMap ℤ (v ∘ e) : MvPolynomial (Fin (D + 1)) ℤ →+* Polynomial Ω).comp
        φ.symm.toRingEquiv.toRingHom) = algebraMap (coneMap ℤ (v ∘ e)).range (Polynomial Ω) := by
      refine RingHom.ext fun r => ?_
      have h1 : ((φ (φ.symm r) : (coneMap ℤ (v ∘ e)).range) : Polynomial Ω) =
          coneMap ℤ (v ∘ e) (φ.symm r) := rfl
      rw [AlgEquiv.apply_symm_apply] at h1
      exact h1.symm
    rw [Polynomial.eval₂_map, hcomp]
    exact hps
  induction q using MvPolynomial.induction_on with
  | C a =>
    have : coneMap ℤ v (C a) = coneMap ℤ (v ∘ e) (C a) := by simp
    rw [this]
    exact RingHom.isIntegralElem_map _
  | add p q hp hq =>
    rw [map_add]
    exact RingHom.IsIntegralElem.add _ hp hq
  | mul_X p i hp =>
    rw [map_mul]
    refine RingHom.IsIntegralElem.mul _ hp ?_
    simpa [coneMap] using hgen i

theorem coneMap_injective_of_frame (v : J → Ω) (e : Fin (D + 1) → J) (hf : IsProjFrame v e) :
    Function.Injective (coneMap ℤ (v ∘ e)) := by
  exact (injective_iff_map_eq_zero _).2 fun p hp => by
    have h : p ∈ coordIdeal ℤ (v ∘ e) := (RingHom.mem_ker).2 hp
    rwa [hf.free, Ideal.mem_bot] at h

theorem ringKrullDim_mvPoly_fin_int :
    ringKrullDim (MvPolynomial (Fin (D + 1)) ℤ) = ((D + 2 : ℕ) : WithBot ℕ∞) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [show ((D + 2 : ℕ) : WithBot ℕ∞) = 1 + ((D + 1 : ℕ) : WithBot ℕ∞) by norm_cast; omega]

theorem ringKrullDim_quot_of_frame (v : J → Ω) (e : Fin (D + 1) → J) (hf : IsProjFrame v e) :
    ringKrullDim (MvPolynomial J ℤ ⧸ coordIdeal ℤ v) = ((D + 2 : ℕ) : WithBot ℕ∞) := by
  have hq : ringKrullDim (MvPolynomial J ℤ ⧸ coordIdeal ℤ v) =
      ringKrullDim (coneMap ℤ v).range :=
    ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerEquivRange (coneMap ℤ v)).toRingEquiv
  let f : MvPolynomial (Fin (D + 1)) ℤ →+* (coneMap ℤ v).range :=
    ((coneMap ℤ v).rangeRestrict.comp (rename e)).toRingHom
  have hvalf : ((coneMap ℤ v).range.val : (coneMap ℤ v).range →+* Polynomial Ω).comp f =
      (coneMap ℤ (v ∘ e) : MvPolynomial (Fin (D + 1)) ℤ →+* Polynomial Ω) := by
    refine RingHom.ext fun p => ?_
    simp [f, coneMap_rename]
  have hinj : Function.Injective f := by
    intro a b hab
    apply coneMap_injective_of_frame v e hf
    have := congrArg ((coneMap ℤ v).range.val : (coneMap ℤ v).range →+* Polynomial Ω) hab
    rw [← RingHom.comp_apply, ← RingHom.comp_apply, hvalf] at this
    exact this
  have hint : f.IsIntegral := fun s => by
    obtain ⟨q, hq⟩ := s.2
    apply isIntegralElem_of_comp f ((coneMap ℤ v).range.val : (coneMap ℤ v).range →+* Polynomial Ω)
      Subtype.val_injective
    rw [hvalf]
    change RingHom.IsIntegralElem _ (s : Polynomial Ω)
    rw [← hq]
    exact isIntegralElem_coneMap v e hf q
  rw [hq]
  apply le_antisymm
  · let _ := f.toAlgebra
    have : Algebra.IsIntegral (MvPolynomial (Fin (D + 1)) ℤ) (coneMap ℤ v).range := ⟨hint⟩
    rw [← ringKrullDim_mvPoly_fin_int]
    exact ringKrullDim_le_of_isIntegral'
  · exact le_ringKrullDim_of_isIntegral f hint hinj _ ringKrullDim_mvPoly_fin_int.ge

end Dim

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
