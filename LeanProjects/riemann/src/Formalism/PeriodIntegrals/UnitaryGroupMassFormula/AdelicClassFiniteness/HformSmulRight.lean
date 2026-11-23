import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.HformSelfStar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.IdealMulPrincipal

noncomputable section

namespace PIW.AdelClassFin

open Formalism.UG NumberField
open scoped Matrix

section Form

variable {E : Type} [Field E] [StarRing E] {m : ℕ} (J : Matrix (Fin m) (Fin m) E)

theorem hform_add_left' (x x' y : Fin m → E) :
    hform (starRingEnd E) J (x + x') y = hform (starRingEnd E) J x y + hform (starRingEnd E) J x' y := by
  simp [hform, map_add, add_mul, Finset.sum_add_distrib]

theorem hform_add_right' (x y y' : Fin m → E) :
    hform (starRingEnd E) J x (y + y') = hform (starRingEnd E) J x y + hform (starRingEnd E) J x y' := by
  simp [hform, mul_add, Finset.sum_add_distrib]

theorem hform_smul_left' (c : E) (x y : Fin m → E) :
    hform (starRingEnd E) J (c • x) y = star c * hform (starRingEnd E) J x y := by
  unfold hform
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, starRingEnd_apply]
  ring

theorem hform_smul_right' (c : E) (x y : Fin m → E) :
    hform (starRingEnd E) J x (c • y) = c * hform (starRingEnd E) J x y := by
  unfold hform
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem hform_swap' (hJ : IsHerm (starRingEnd E) J) (x y : Fin m → E) :
    hform (starRingEnd E) J y x = star (hform (starRingEnd E) J x y) := by
  have hJ' : ∀ i j, J i j = star (J j i) := by
    intro i j
    have h := congrFun (congrFun hJ i) j
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, starRingEnd_apply] at h
    exact h.symm
  unfold hform
  simp only [starRingEnd_apply, star_sum, star_mul', star_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ' j i]
  ring

theorem hform_exists_ne (hdet : J.det ≠ 0) (S : Set (Fin m → E)) (hS : Submodule.span E S = ⊤)
    {x : Fin m → E} (hx : x ≠ 0) : ∃ z ∈ S, hform (starRingEnd E) J x z ≠ 0 := by
  by_contra h
  push_neg at h
  let f : (Fin m → E) →ₗ[E] E :=
    { toFun := fun y => hform (starRingEnd E) J x y
      map_add' := fun y y' => hform_add_right' J x y y'
      map_smul' := fun c y => by simpa using hform_smul_right' J c x y }
  have hle : Submodule.span E S ≤ LinearMap.ker f := by
    rw [Submodule.span_le]
    intro z hz
    exact LinearMap.mem_ker.mpr (h z hz)
  have hall : ∀ y, hform (starRingEnd E) J x y = 0 := by
    intro y
    have hy : y ∈ Submodule.span E S := by
      rw [hS]
      exact Submodule.mem_top
    exact LinearMap.mem_ker.mp (hle hy)
  have hv : (fun i => starRingEnd E (x i)) ᵥ* J = 0 := by
    funext j
    have hj := hall (Pi.single j 1)
    simpa [hform, Matrix.vecMul, dotProduct, Pi.single_apply] using hj
  have hv0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hv
  apply hx
  funext i
  have hi := congrFun hv0 i
  simpa using hi

end Form

theorem star_int {E : Type} [Field E] [NumberField E] [StarRing E] (q : 𝓞 E) :
    ∃ q' : 𝓞 E, algebraMap (𝓞 E) E q' = star (algebraMap (𝓞 E) E q) := by
  have h : IsIntegral ℤ (algebraMap (𝓞 E) E q) := by
    first
      | exact NumberField.RingOfIntegers.isIntegral_coe q
      | exact q.2
  have h2 : IsIntegral ℤ (star (algebraMap (𝓞 E) E q)) := by
    have h3 := h.map (starRingEnd E).toIntAlgHom
    first
      | exact h3
      | simpa using h3
  exact ⟨⟨_, h2⟩, rfl⟩

private theorem exists_finite_residue_reps_mod_natCast (F : Type) [Field F] [NumberField F] (N : ℕ) (hN : 0 < N) :
    ∃ T : Set (𝓞 F), T.Finite ∧ ∀ f : 𝓞 F, ∃ r ∈ T, ∃ g : 𝓞 F, f = r + (N : 𝓞 F) * g := by
  have hN' : (N : 𝓞 F) ≠ 0 := by
    intro h
    have h2 := congrArg (algebraMap (𝓞 F) F) h
    simp only [map_natCast, map_zero, Nat.cast_eq_zero] at h2
    omega
  have hI : Ideal.span {(N : 𝓞 F)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hN'
  haveI : Finite (𝓞 F ⧸ Ideal.span {(N : 𝓞 F)}) := by
    first
      | exact @Finite.of_fintype _ (Ideal.fintypeQuotientOfFreeOfNeBot _ hI)
      | exact Ideal.finiteQuotientOfFreeOfNeBot _ hI
  refine ⟨Set.range (Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {(N : 𝓞 F)}))),
    Set.finite_range _, ?_⟩
  intro f
  refine ⟨_, Set.mem_range_self (Ideal.Quotient.mk (Ideal.span {(N : 𝓞 F)}) f), ?_⟩
  have h := Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := Ideal.span {(N : 𝓞 F)}))
    (Ideal.Quotient.mk (Ideal.span {(N : 𝓞 F)}) f)
  rw [Ideal.Quotient.eq] at h
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp h
  refine ⟨-g, ?_⟩
  linear_combination hg

theorem partIso_of (hIB : IdealBoundAll) : PartIso := by
  intro F E _ _ _ _ _ _ hCM m d hd
  obtain ⟨B, hB⟩ := hIB E
  have hreps : ∀ k : ℕ, ∃ T : Set (𝓞 F), T.Finite ∧
      ∀ f : 𝓞 F, ∃ r ∈ T, ∃ g : 𝓞 F, f = r + ((2 * d * (k + 1) : ℕ) : 𝓞 F) * g :=
    fun k => exists_finite_residue_reps_mod_natCast F _ (Nat.mul_pos (Nat.mul_pos (by norm_num) hd) k.succ_pos)
  choose T hTf hT using hreps
  refine ⟨⋃ k ∈ Set.Iio B, (fun r : 𝓞 F => !![(0 : E), ((d * (k + 1) : ℕ) : E);
      ((d * (k + 1) : ℕ) : E), algebraMap F E (algebraMap (𝓞 F) F r)]) '' T k, ?_, ?_, ?_⟩
  · exact (Set.finite_Iio B).biUnion fun k _ => (hTf k).image _
  · intro Γ hΓ
    simp only [Set.mem_iUnion, Set.mem_image] at hΓ
    obtain ⟨k, _, r, _, rfl⟩ := hΓ
    have ha : ((d * (k + 1) : ℕ) : E) ≠ 0 := by
      rw [Ne, Nat.cast_eq_zero]
      exact (Nat.mul_pos hd k.succ_pos).ne'
    rw [Matrix.det_fin_two_of]
    intro h
    apply mul_ne_zero ha ha
    linear_combination -h
  · intro p hp x hxM hx0 hxx
    simp only [Lat, Set.mem_setOf_eq] at hp
    obtain ⟨hJ, hdet, -, hspan, hint, hdual⟩ := hp
    have hinj : Function.Injective (algebraMap (𝓞 E) E) := by
      first
        | exact NumberField.RingOfIntegers.coe_injective
        | exact IsFractionRing.injective (𝓞 E) E
        | exact NoZeroSMulDivisors.algebraMap_injective (𝓞 E) E
        | exact FaithfulSMul.algebraMap_injective (𝓞 E) E
    obtain ⟨I, hIdef⟩ : ∃ I : Ideal (𝓞 E), ∀ g, g ∈ I ↔
        ∃ y ∈ p.2, algebraMap (𝓞 E) E g = hform (starRingEnd E) p.1 x y :=
      ⟨{ carrier := {g | ∃ y ∈ p.2, algebraMap (𝓞 E) E g = hform (starRingEnd E) p.1 x y}
         add_mem' := by
           rintro g g' ⟨y, hy, hg⟩ ⟨y', hy', hg'⟩
           exact ⟨y + y', p.2.add_mem hy hy', by rw [map_add, hg, hg', hform_add_right']⟩
         zero_mem' := ⟨0, p.2.zero_mem, by simp [hform]⟩
         smul_mem' := by
           rintro r g ⟨y, hy, hg⟩
           refine ⟨r • y, p.2.smul_mem r hy, ?_⟩
           rw [smul_eq_mul, map_mul, hg, ← algebraMap_smul E r y, hform_smul_right'] },
        fun g => Iff.rfl⟩
    obtain ⟨z, hzM, hz⟩ := hform_exists_ne p.1 hdet (p.2 : Set (Fin m → E)) hspan hx0
    obtain ⟨g0, hg0⟩ := hint x hxM z hzM
    have hI : I ≠ ⊥ := by
      intro hbot
      have hmem : g0 ∈ I := (hIdef g0).mpr ⟨z, hzM, hg0⟩
      rw [hbot, Ideal.mem_bot] at hmem
      apply hz
      rw [← hg0, hmem, map_zero]
    obtain ⟨c, hcI, hc0, e, he1, heB, hdiv⟩ := hB I hI
    obtain ⟨y0, hy0M, hc⟩ := (hIdef c).mp hcI
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    have hc' : algebraMap (𝓞 E) E c ≠ 0 := fun h => hc0 (hinj (by rw [h, map_zero]))
    have hsc : star (algebraMap (𝓞 E) E c) ≠ 0 := star_ne_zero.mpr hc'
    obtain ⟨t, ht⟩ : ∃ t : E, t * star (algebraMap (𝓞 E) E c) = ((k + 1 : ℕ) : E) :=
      ⟨_, div_mul_cancel₀ _ hsc⟩
    have hts : star t * algebraMap (𝓞 E) E c = ((k + 1 : ℕ) : E) := by
      have h := congrArg star ht
      simpa only [star_mul', star_star, star_natCast] using h
    have hw : ∀ z' ∈ p.2, hform (starRingEnd E) p.1 z' (t • x) ∈ (algebraMap (𝓞 E) E).range := by
      intro z' hz'
      obtain ⟨gz, hgz⟩ := hint x hxM z' hz'
      obtain ⟨q, hq⟩ := hdiv gz ((hIdef gz).mpr ⟨z', hz', hgz⟩)
      have hq' : ((k + 1 : ℕ) : E) * hform (starRingEnd E) p.1 x z' =
          algebraMap (𝓞 E) E c * algebraMap (𝓞 E) E q := by
        have h := congrArg (algebraMap (𝓞 E) E) hq
        rw [map_mul, map_mul, map_natCast, hgz] at h
        exact h
      have E1 : ((k + 1 : ℕ) : E) * star (hform (starRingEnd E) p.1 x z') =
          star (algebraMap (𝓞 E) E c) * star (algebraMap (𝓞 E) E q) := by
        have h := congrArg star hq'
        simpa only [star_mul', star_natCast] using h
      obtain ⟨q', hq''⟩ := star_int q
      refine ⟨q', ?_⟩
      rw [hq'', hform_smul_right', hform_swap' p.1 hJ x z']
      apply mul_left_cancel₀ hsc
      linear_combination -E1 - star (hform (starRingEnd E) p.1 x z') * ht
    have hv0M : (d : E) • (t • x) ∈ p.2 := hdual (t • x) hw
    have hv00 : hform (starRingEnd E) p.1 ((d : E) • (t • x)) ((d : E) • (t • x)) = 0 := by
      rw [hform_smul_left', hform_smul_left', hform_smul_right', hform_smul_right', hxx]
      ring
    have hv0y : hform (starRingEnd E) p.1 ((d : E) • (t • x)) y0 = ((d * (k + 1) : ℕ) : E) := by
      rw [hform_smul_left', hform_smul_left', ← hc, hts, star_natCast]
      push_cast
      ring
    generalize (d : E) • (t • x) = v0 at hv0M hv00 hv0y
    obtain ⟨β, hβ⟩ := hint y0 hy0M y0 hy0M
    have hbstar : star (hform (starRingEnd E) p.1 y0 y0) = hform (starRingEnd E) p.1 y0 y0 :=
      (hform_swap' p.1 hJ y0 y0).symm
    obtain ⟨f, hf⟩ := (hCM.fixed _).mp hbstar
    have hβint : IsIntegral ℤ (algebraMap (𝓞 E) E β) := by
      first
        | exact NumberField.RingOfIntegers.isIntegral_coe β
        | exact β.2
    have hfint : IsIntegral ℤ f := by
      rw [hβ, ← hf] at hβint
      exact (isIntegral_algHom_iff (algebraMap F E).toIntAlgHom (algebraMap F E).injective).mp hβint
    obtain ⟨r, hrT, g, hfg⟩ := hT k ⟨f, hfint⟩
    have hgint : IsIntegral ℤ (algebraMap F E (algebraMap (𝓞 F) F g)) := by
      have h1 : IsIntegral ℤ (algebraMap (𝓞 F) F g) := by
        first
          | exact NumberField.RingOfIntegers.isIntegral_coe g
          | exact g.2
      exact h1.map (algebraMap F E).toIntAlgHom
    obtain ⟨sE, hsE⟩ : ∃ sE : 𝓞 E,
        algebraMap (𝓞 E) E sE = -(algebraMap F E (algebraMap (𝓞 F) F g)) := ⟨⟨_, hgint.neg⟩, rfl⟩
    have hsstar : star (algebraMap (𝓞 E) E sE) = algebraMap (𝓞 E) E sE := by
      rw [hsE, star_neg, (hCM.fixed (algebraMap F E (algebraMap (𝓞 F) F g))).mpr ⟨_, rfl⟩]
    have hv1M : y0 + sE • v0 ∈ p.2 := p.2.add_mem hy0M (p.2.smul_mem sE hv0M)
    have hsm : sE • v0 = (algebraMap (𝓞 E) E sE) • v0 := (algebraMap_smul E sE v0).symm
    have hyv0 : hform (starRingEnd E) p.1 y0 v0 = ((d * (k + 1) : ℕ) : E) := by
      rw [hform_swap' p.1 hJ v0 y0, hv0y, star_natCast]
    have h01 : hform (starRingEnd E) p.1 v0 (y0 + sE • v0) = ((d * (k + 1) : ℕ) : E) := by
      rw [hsm, hform_add_right', hform_smul_right', hv0y, hv00]
      ring
    have h10 : hform (starRingEnd E) p.1 (y0 + sE • v0) v0 = ((d * (k + 1) : ℕ) : E) := by
      rw [hsm, hform_add_left', hform_smul_left', hyv0, hv00]
      ring
    have hfg' : f = algebraMap (𝓞 F) F r + ((2 * d * (k + 1) : ℕ) : F) * algebraMap (𝓞 F) F g := by
      have h := congrArg (algebraMap (𝓞 F) F) hfg
      rw [map_add, map_mul, map_natCast] at h
      exact h
    have h11 : hform (starRingEnd E) p.1 (y0 + sE • v0) (y0 + sE • v0) =
        algebraMap F E (algebraMap (𝓞 F) F r) := by
      rw [hsm]
      simp only [hform_add_left', hform_add_right', hform_smul_left', hform_smul_right']
      rw [hyv0, hv0y, hv00, hsstar, ← hf, hfg', hsE, map_add, map_mul, map_natCast]
      push_cast
      ring
    refine ⟨![v0, y0 + sE • v0], ?_, ?_⟩
    · intro i
      fin_cases i
      · simpa using hv0M
      · simpa using hv1M
    · simp only [Set.mem_iUnion, Set.mem_image]
      refine ⟨k, Set.mem_Iio.mpr (by omega), r, hrT, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j <;> simp [gram, h01, h10, h11, hv00]

end PIW.AdelClassFin
