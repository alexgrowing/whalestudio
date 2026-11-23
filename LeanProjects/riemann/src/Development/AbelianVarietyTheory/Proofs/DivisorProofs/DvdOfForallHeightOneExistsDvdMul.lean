import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlatMapColonIdeal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.MemRangeOfForallHeightOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem dvd_of_forall_height_one_exists_dvd_mul {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] {h z : A} (hh : h ≠ 0)
    (H : ∀ P : Ideal A, P.IsPrime → P.height = 1 → ∃ s ∉ P, h ∣ s * z) : h ∣ z := by
  let K := FractionRing A
  have hhK : algebraMap A K h ≠ 0 := fun h0 =>
    hh (IsFractionRing.injective A K (by rw [h0, map_zero]))
  have hmem : algebraMap A K z / algebraMap A K h ∈ (algebraMap A K).range := by
    refine ReciprocityTheory.ChartRestriction.G.Out.KrullAlg.mem_range_of_forall_height_one (A := A) _ ?_
    intro P hP h1
    obtain ⟨s, hs, t, ht⟩ := H P hP h1
    refine ⟨s, hs, t, ?_⟩
    rw [← mul_div_assoc, eq_div_iff hhK, ← map_mul, ← map_mul, ht, mul_comm]
  obtain ⟨c, hc⟩ := hmem
  refine ⟨c, IsFractionRing.injective A K ?_⟩
  rw [map_mul, hc, mul_div_assoc', eq_div_iff hhK, mul_comm]

section SquareIdeal

variable {A : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]

theorem dvd_mul_of_dvd_sq_of_dvd_sq {h x y : A} (hx : h ∣ x ^ 2) (hy : h ∣ y ^ 2) : h ∣ x * y := by
  have : h ^ 2 ∣ (x * y) ^ 2 := by
    rw [mul_pow, sq h]; exact mul_dvd_mul hx hy
  exact (IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1 this

def sqDvdIdeal (h : A) : Ideal A where
  carrier := {x | h ∣ x ^ 2}
  add_mem' := by
    intro x y hx hy
    have hxy := dvd_mul_of_dvd_sq_of_dvd_sq hx hy
    show h ∣ (x + y) ^ 2
    have e : (x + y) ^ 2 = x ^ 2 + 2 * (x * y) + y ^ 2 := by ring
    rw [e]
    exact dvd_add (dvd_add hx (dvd_mul_of_dvd_right hxy _)) hy
  zero_mem' := by show h ∣ (0 : A) ^ 2; simp
  smul_mem' := by
    intro c x hx
    show h ∣ (c * x) ^ 2
    rw [mul_pow]; exact dvd_mul_of_dvd_right hx _

theorem mem_sqDvdIdeal {h x : A} : x ∈ sqDvdIdeal h ↔ h ∣ x ^ 2 := Iff.rfl

end SquareIdeal

theorem isUnit_mul_sq_of_faithfullyFlat : ∀ (C C' : Type) [CommRing C] [IsDomain C] [IsLocalRing C] [IsNoetherianRing C] [IsIntegrallyClosed C] [CommRing C'] [IsDomain C'] [IsNoetherianRing C'] [IsIntegrallyClosed C'] [Algebra C C'] [Module.FaithfullyFlat C C'] (h : C), h ≠ 0 → (∃ (u : C'ˣ) (f : C'), algebraMap C C' h = u * f ^ 2) → (∀ p : Ideal C, p.IsPrime → p.height = 1 → ∃ a b c : C, b ∉ p ∧ c ∉ p ∧ b * h = c * a ^ 2) → ∃ (u : Cˣ) (a : C), h = u * a ^ 2 := by
  intro C C' _ _ _ _ _ _ _ _ _ _ _ h hh hsq Hp
  obtain ⟨u, f, hf⟩ := hsq
  have hflat : (algebraMap C C').Flat := RingHom.flat_algebraMap_iff.2 inferInstance
  let J := sqDvdIdeal h

  have hJf : J.map (algebraMap C C') ≤ Ideal.span {f} := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    obtain ⟨z, hz⟩ := mem_sqDvdIdeal.1 hx
    rw [Ideal.mem_comap, Ideal.mem_span_singleton]
    apply (IsIntegrallyClosed.pow_dvd_pow_iff two_ne_zero).1
    refine ⟨(u : C') * algebraMap C C' z, ?_⟩
    rw [← map_pow, hz, map_mul, hf]; ring

  have hcol : (Ideal.span {h}).colon (J : Set C) ≤ J := by
    intro y hy
    rw [Submodule.mem_colon] at hy
    apply mem_sqDvdIdeal.2
    apply dvd_of_forall_height_one_exists_dvd_mul hh
    intro P hP h1
    obtain ⟨a, b, c, hb, hc, habc⟩ := Hp P hP h1
    have hac : a * c ∈ J := mem_sqDvdIdeal.2 ⟨b * c, by linear_combination (-c) * habc⟩
    have hy' := hy (a * c) hac
    rw [smul_eq_mul, Ideal.mem_span_singleton] at hy'
    obtain ⟨t, ht⟩ := hy'
    refine ⟨b * c, fun hm => (hP.mem_or_mem hm).elim hb hc, t ^ 2, ?_⟩
    have e : h * (b * c * y ^ 2) = h * (h * t ^ 2) := by
      linear_combination (c * y ^ 2) * habc + (y * (a * c) + h * t) * ht
    exact mul_left_cancel₀ hh e

  have hfJ : f ∈ J.map (algebraMap C C') := by
    have hm : f ∈ ((Ideal.span {h}).colon (J : Set C)).map (algebraMap C C') := by
      rw [GlobalTheory.ideal_map_colon_eq_of_flat _ hflat, Ideal.map_span, Set.image_singleton,
        Submodule.mem_colon]
      intro p hp
      obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton.1 (hJf hp)
      rw [smul_eq_mul, Ideal.mem_span_singleton, hf]
      exact ⟨((u⁻¹ : C'ˣ) : C') * w, by linear_combination (-(f ^ 2 * w)) * u.mul_inv⟩
    exact Ideal.map_mono hcol hm
  have hJeq : J.map (algebraMap C C') = Ideal.span {f} :=
    le_antisymm hJf ((Ideal.span_singleton_le_iff_mem _).2 hfJ)

  have hY : ((J * J).colon (Ideal.span {h} : Set C)).map (algebraMap C C') = ⊤ := by
    rw [GlobalTheory.ideal_map_colon_eq_of_flat _ hflat, Ideal.map_mul, hJeq, Ideal.map_span,
      Set.image_singleton, Ideal.span_singleton_mul_span_singleton, Ideal.eq_top_iff_one,
      Submodule.mem_colon]
    intro p hp
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton.1 hp
    rw [smul_eq_mul, _root_.one_mul, Ideal.mem_span_singleton, hf]
    exact ⟨(u : C') * w, by ring⟩
  have hhJJ : h ∈ J * J := by
    have e := Ideal.comap_map_eq_self_of_faithfullyFlat (B := C')
      ((J * J).colon (Ideal.span {h} : Set C))
    rw [hY, Ideal.comap_top] at e
    have h1 : (1 : C) ∈ (J * J).colon (Ideal.span {h} : Set C) := e ▸ Submodule.mem_top
    rw [Submodule.mem_colon] at h1
    simpa using h1 h (Ideal.mem_span_singleton_self h)

  by_contra hne
  have hle : J * J ≤ Ideal.span {h} * maximalIdeal C := by
    refine Ideal.mul_le.2 fun x hx y hy => ?_
    obtain ⟨e, he⟩ := dvd_mul_of_dvd_sq_of_dvd_sq (mem_sqDvdIdeal.1 hx) (mem_sqDvdIdeal.1 hy)
    by_cases hem : e ∈ maximalIdeal C
    · rw [he]; exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self h) hem
    · exfalso
      have heu : IsUnit e := by
        rw [mem_maximalIdeal, mem_nonunits_iff, not_not] at hem; exact hem
      obtain ⟨a, ha⟩ := mem_sqDvdIdeal.1 hx
      obtain ⟨b, hb⟩ := mem_sqDvdIdeal.1 hy
      have hab : a * b = e ^ 2 := by
        have e2 : h ^ 2 * (a * b) = h ^ 2 * e ^ 2 := by
          linear_combination (-(h * b)) * ha - x ^ 2 * hb + (x * y + h * e) * he
        exact mul_left_cancel₀ (pow_ne_zero 2 hh) e2
      have hau : IsUnit a := isUnit_of_mul_isUnit_left (hab ▸ heu.pow 2)
      exact hne ⟨hau.unit⁻¹, x, by rw [ha]; linear_combination (-h) * hau.val_inv_mul⟩
  obtain ⟨z, hz, hz'⟩ := Ideal.mem_span_singleton_mul.1 (hle hhJJ)
  have hz1 : z = 1 := mul_left_cancel₀ hh (by rw [hz', _root_.mul_one])
  exact (maximalIdeal.isMaximal C).ne_top ((Ideal.eq_top_iff_one _).2 (hz1 ▸ hz))

end GlobalTheory.Mum
