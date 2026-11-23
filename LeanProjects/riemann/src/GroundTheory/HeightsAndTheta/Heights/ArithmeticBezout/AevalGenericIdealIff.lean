import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ImportsAlt
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormExtend
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PRadicalBaseChange
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk conePts)
open ChowFormExtend (incidenceIdeal coordPoly coeff_coordPoly coordPoly_C_mul_map coordPoly_mem_of_mem_map
  mem_zeroLocus_incidenceIdeal vanishes_incidence_iff incidenceIdeal_map radical_map_eq coordSupport
  sum_coordPoly coordPoly_sum)

namespace ComplexChowFormToChowForm

section Descent

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {Y : Type*}

theorem mem_of_map_mem (T : Ideal (MvPolynomial Y K)) {x : MvPolynomial Y K}
    (hx : map (algebraMap K L) x ∈ T.map (map (algebraMap K L))) : x ∈ T := by
  classical
  let b := Module.Basis.ofVectorSpace K L
  obtain ⟨c, hc⟩ : ∃ c, b.coord c 1 ≠ 0 := by
    by_contra! h
    have h0 : b.repr 1 = 0 := Finsupp.ext fun c => by rw [← Module.Basis.coord_apply]; exact h c
    exact one_ne_zero (b.repr.map_eq_zero_iff.mp h0)
  have hmem := coordPoly_mem_of_mem_map b T hx c
  have e := coordPoly_C_mul_map (b.coord c) (1 : L) x
  rw [C_1, one_mul] at e
  rw [e] at hmem
  have := T.mul_mem_left (C (b.coord c 1)⁻¹) hmem
  rwa [← mul_assoc, ← C_mul, inv_mul_cancel₀ hc, C_1, one_mul] at this

theorem dvd_of_map_dvd {f h : MvPolynomial Y K}
    (hd : map (algebraMap K L) f ∣ map (algebraMap K L) h) : f ∣ h := by
  rw [← Ideal.mem_span_singleton] at hd ⊢
  apply mem_of_map_mem (L := L)
  rwa [Ideal.map_span, Set.image_singleton]

end Descent

variable {n : ℕ}

theorem aeval_genericIdeal_iff (P : Ideal (MRing (PBlk n))) (x : Fin n → ℂ) :
    (∀ q ∈ (genericIdeal P).map (map (algebraMap ℚ ℂ)), aeval x q = 0) ↔
      ∀ h ∈ IndefiniteRowSideFullHecke.ArithBezout.finIdeal P, eval x (map (Int.castRingHom ℂ) h) = 0 := by
  have hc : (map (algebraMap ℚ ℂ)).comp (map (Int.castRingHom ℚ)) =
      (map (Int.castRingHom ℂ) : MvPolynomial (Fin n) ℤ →+* MvPolynomial (Fin n) ℂ) :=
    RingHom.ext fun p => by rw [RingHom.comp_apply, map_map]; congr 1
  rw [genericIdeal, Ideal.map_map, hc]
  constructor
  · intro H h hh
    exact H _ (Ideal.mem_map_of_mem _ hh)
  · intro H q hq
    have hle : (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P).map (map (Int.castRingHom ℂ)) ≤
        RingHom.ker (eval x) := by
      rw [Ideal.map_le_iff_le_comap]
      intro h hh
      rw [Ideal.mem_comap, RingHom.mem_ker]
      exact H h hh
    exact RingHom.mem_ker.mp (hle hq)

theorem vanishes_cone_iff {k : ℕ} (P : Ideal (MRing (PBlk n))) (p : MvPolynomial (Fin k × Fin n) ℂ) :
    (∀ v : Fin k × Fin n → ℂ, (∃ z ∈ conePts (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P),
        ∀ i, ∑ j, v (i, j) * z j = 0) → eval v p = 0) ↔
      ∀ j, X (Sum.inr j) * rename Sum.inl p ∈
        (incidenceIdeal ((genericIdeal P).map (map (algebraMap ℚ ℂ))) k).radical := by
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := ℂ)]
  simp only [mem_vanishingIdeal_iff, mem_zeroLocus_incidenceIdeal, aeval_genericIdeal_iff]
  constructor
  · rintro h j z ⟨hI, hlin⟩
    rw [map_mul, aeval_X, aeval_rename]
    by_cases hx : z ∘ Sum.inr = 0
    · rw [show z (Sum.inr j) = 0 from congrFun hx j, zero_mul]
    · rw [aeval_eq_eval, h (z ∘ Sum.inl) ⟨z ∘ Sum.inr, ⟨hx, hI⟩, hlin⟩, mul_zero]
  · rintro h v ⟨x, ⟨hx, hI⟩, hlin⟩
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := Function.ne_iff.1 hx
    have := h j (Sum.elim v x) ⟨by simpa using hI, by simpa using hlin⟩
    rw [map_mul, aeval_X, aeval_rename, aeval_eq_eval] at this
    simpa [hj] using this

theorem vanishes_zero_iff_dvd {σ : Type*} [Finite σ] {g p : MvPolynomial σ ℂ} (hg : Squarefree g) :
    (∀ v, eval v g = 0 → eval v p = 0) ↔ g ∣ p := by
  have hrad : (Ideal.span {g}).radical = Ideal.span {g} :=
    (isRadical_iff_span_singleton.mp hg.isRadical).radical
  rw [← Ideal.mem_span_singleton, ← hrad, ← vanishingIdeal_zeroLocus_eq_radical (K := ℂ)]
  simp only [mem_vanishingIdeal_iff, mem_zeroLocus_iff, aeval_eq_eval]
  constructor
  · intro h v hv
    exact h v (hv g (Ideal.mem_span_singleton_self g))
  · intro h v hv
    refine h v fun q hq => ?_
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hq
    rw [map_mul, hv, zero_mul]

theorem proof : ComplexChowFormToChowForm.Statement := by
  intro n e δ P g _ hg
  obtain ⟨-, hsq, hzero⟩ := hg
  set R := (incidenceIdeal (genericIdeal P) (e + 1)).radical with hR
  have hradC : (incidenceIdeal ((genericIdeal P).map (map (algebraMap ℚ ℂ))) (e + 1)).radical =
      R.map (map (algebraMap ℚ ℂ)) := by
    rw [incidenceIdeal_map, radical_map_eq RadicalBaseChange.proof]
  have hZ : ∀ v : Fin (e + 1) × Fin n → ℂ, eval v g = 0 ↔
      ∃ z ∈ conePts (Int.castRingHom ℂ) (IndefiniteRowSideFullHecke.ArithBezout.finIdeal P), ∀ i, ∑ j, v (i, j) * z j = 0 :=
    fun v => hzero (fun i j => v (i, j))
  have hC : ∀ p : MvPolynomial (Fin (e + 1) × Fin n) ℂ,
      g ∣ p ↔ ∀ j, X (Sum.inr j) * rename Sum.inl p ∈ R.map (map (algebraMap ℚ ℂ)) := by
    intro p
    rw [← vanishes_zero_iff_dvd hsq, ← hradC, ← vanishes_cone_iff]
    exact forall_congr' fun v => by rw [hZ v]
  have hQ : ∀ h : MvPolynomial (Fin (e + 1) × Fin n) ℚ,
      (∀ u ∈ incidence (genericIdeal P) (e + 1), aeval u h = 0) ↔ g ∣ map (algebraMap ℚ ℂ) h := by
    intro h
    refine (vanishes_incidence_iff _ _ h).trans ?_
    rw [hC]
    refine forall_congr' fun j => ?_
    rw [show X (Sum.inr j) * rename Sum.inl (map (algebraMap ℚ ℂ) h) =
        map (algebraMap ℚ ℂ) (X (Sum.inr j) * rename Sum.inl h) by rw [map_mul, map_X, map_rename]]
    exact ⟨fun hm => Ideal.mem_map_of_mem _ hm, mem_of_map_mem R⟩
  have hg0 : g ≠ 0 := hsq.ne_zero
  obtain ⟨m, hm⟩ := ne_zero_iff.mp hg0
  classical
  let b := Module.Basis.ofVectorSpace ℚ ℂ
  obtain ⟨c, hc⟩ : ∃ c, b.coord c (coeff m g) ≠ 0 := by
    by_contra! h
    have h0 : b.repr (coeff m g) = 0 := Finsupp.ext fun c => by rw [← Module.Basis.coord_apply]; exact h c
    exact hm (b.repr.map_eq_zero_iff.mp h0)
  have hcS : c ∈ coordSupport b g :=
    Finset.mem_biUnion.2 ⟨m, mem_support_iff.2 hm,
      Finsupp.mem_support_iff.2 (by rwa [← Module.Basis.coord_apply])⟩
  set h := coordPoly (b.coord c) g with hh_def
  have hh : g ∣ map (algebraMap ℚ ℂ) h := by
    refine (hQ h).mp ((vanishes_incidence_iff _ _ h).mpr fun j => ?_)
    have e' : X (Sum.inr j) * rename Sum.inl g = ∑ c' ∈ coordSupport b g,
        C (b c') * map (algebraMap ℚ ℂ) (X (Sum.inr j) * rename Sum.inl (coordPoly (b.coord c') g)) := by
      conv_lhs => rw [← sum_coordPoly b g]
      rw [map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c' _ => ?_
      rw [map_mul, rename_C, map_mul, map_X, map_rename]
      ring
    have hmem := coordPoly_mem_of_mem_map b R (e' ▸ (hC g).mp dvd_rfl j) c
    rwa [coordPoly_sum, if_pos hcS] at hmem
  obtain ⟨q, hq⟩ := hh
  have hmh : coeff m (map (algebraMap ℚ ℂ) h) ≠ 0 := by
    rw [coeff_map, hh_def, coeff_coordPoly]
    exact (map_ne_zero _).mpr hc
  have hmh0 : map (algebraMap ℚ ℂ) h ≠ 0 := fun h0 => hmh (by rw [h0, coeff_zero])
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hq
    exact hmh0 hq
  have hsupp : (map (algebraMap ℚ ℂ) h).support ⊆ g.support := by
    intro m' hm'
    rw [mem_support_iff] at hm' ⊢
    intro h0
    rw [coeff_map, hh_def, coeff_coordPoly, h0, map_zero, map_zero] at hm'
    exact hm' rfl
  have hdeg : q.totalDegree = 0 := by
    have h1 := totalDegree_mul_of_isDomain hg0 hq0
    have h2 := totalDegree_le_of_support_subset hsupp
    rw [← hq] at h1
    omega
  rw [totalDegree_eq_zero_iff_eq_C] at hdeg
  set a := q.coeff 0
  have ha : a ≠ 0 := fun h0 => hq0 (by rw [hdeg, h0, C_0])
  have hgm : g = C a⁻¹ * map (algebraMap ℚ ℂ) h := by
    rw [hq, hdeg, mul_comm g, ← mul_assoc, ← C_mul, inv_mul_cancel₀ ha, C_1, one_mul]
  have hu : IsUnit (C a⁻¹ : MvPolynomial (Fin (e + 1) × Fin n) ℂ) :=
    (isUnit_iff_ne_zero.mpr (inv_ne_zero ha)).map C
  refine ⟨a⁻¹, inv_ne_zero ha, h, ?_, ?_⟩
  · rw [show Rat.castHom ℂ = algebraMap ℚ ℂ from Subsingleton.elim _ _]
    exact hgm
  · refine ⟨fun h0 => hmh0 (by rw [h0, map_zero]), fun h' => ?_⟩
    refine (hQ h').trans ?_
    rw [hgm, hu.mul_left_dvd]
    exact ⟨dvd_of_map_dvd, map_dvd _⟩

end ComplexChowFormToChowForm

end ObjectsChow

end GroundTheory.Heights₂.Heights
