import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.IdealSpread

theorem exists_of_map_eq_span {A R : Type} [CommRing A] [CommRing R] [Algebra A R] (M : Submonoid A)
    [IsLocalization M R] {J : Ideal A} (hJ : J.FG) (d : A)
    (h : J.map (algebraMap A R) = Ideal.span {algebraMap A R d}) :
    ∃ s ∈ M, s * d ∈ J ∧ ∀ j ∈ J, ∃ c, s * j = c * d := by

  obtain ⟨s₁, hs₁M, hs₁⟩ : ∃ s₁ ∈ M, s₁ * d ∈ J := by
    have hd : algebraMap A R d ∈ J.map (algebraMap A R) := h ▸ Ideal.subset_span rfl
    obtain ⟨⟨⟨a, ha⟩, m⟩, hm⟩ := (IsLocalization.mem_map_algebraMap_iff M R).1 hd
    simp only at hm
    rw [← map_mul] at hm
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := M) hm
    refine ⟨c * m, M.mul_mem c.2 m.2, ?_⟩
    have : (c : A) * (d * m) = c * a := hc
    rw [show (c : A) * m * d = c * (d * m) by ring, this]
    exact J.mul_mem_left _ ha

  have hone : ∀ g ∈ J, ∃ t ∈ M, ∃ c, t * g = c * d := by
    intro g hg
    have hg' : algebraMap A R g ∈ Ideal.span {algebraMap A R d} := h ▸ Ideal.mem_map_of_mem _ hg
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hg'
    obtain ⟨⟨a, m⟩, ham⟩ := IsLocalization.surj M r
    simp only at ham
    have : algebraMap A R (m * g) = algebraMap A R (a * d) := by
      rw [map_mul, map_mul, ← ham, ← hr]; ring
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := M) this
    exact ⟨c * m, M.mul_mem c.2 m.2, c * a, by linear_combination hc⟩
  have key : ∀ T : Finset A, (∀ g ∈ T, ∃ t ∈ M, ∃ c, t * g = c * d) → ∃ t ∈ M, ∀ g ∈ T, ∃ c, t * g = c * d := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact fun _ => ⟨1, M.one_mem, by simp⟩
    | insert a S haS ih =>
      intro hT
      obtain ⟨t, htM, ht⟩ := ih (fun g hg => hT g (Finset.mem_insert_of_mem hg))
      obtain ⟨t', ht'M, c', hc'⟩ := hT a (Finset.mem_insert_self a S)
      refine ⟨t * t', M.mul_mem htM ht'M, fun g hg => ?_⟩
      rcases Finset.mem_insert.1 hg with rfl | hg
      · exact ⟨t * c', by rw [mul_assoc, hc', mul_assoc]⟩
      · obtain ⟨c, hc⟩ := ht g hg
        exact ⟨t' * c, by rw [mul_comm t t', mul_assoc, hc, mul_assoc]⟩
  obtain ⟨S, rfl⟩ := hJ
  obtain ⟨t, htM, ht⟩ := key S fun g hg => hone g (Ideal.subset_span hg)
  have hall : ∀ j ∈ Ideal.span (S : Set A), ∃ c, t * j = c * d := by
    intro j hj
    induction hj using Submodule.span_induction with
    | mem x hx => exact ht x hx
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [mul_add, ha, hb, add_mul]⟩
    | smul a x _ hx =>
      obtain ⟨b, hb⟩ := hx
      exact ⟨a * b, by rw [smul_eq_mul, mul_left_comm, hb, mul_assoc]⟩
  refine ⟨s₁ * t, M.mul_mem hs₁M htM, ?_, fun j hj => ?_⟩
  · rw [mul_comm s₁ t, mul_assoc]
    exact Ideal.mul_mem_left _ _ hs₁
  · obtain ⟨c, hc⟩ := hall j hj
    exact ⟨s₁ * c, by rw [mul_assoc, hc, mul_assoc]⟩

end GlobalTheory.IdealSpread

namespace GlobalTheory.IdealSpread

theorem ideal_eq_span_of_germ (X : Scheme.{0}) (I : X.IdealSheafData) (U : X.affineOpens) (x₀ : X) (hx : x₀ ∈ U.1)
    (d : Γ(X, U.1)) (hN : IsNoetherianRing Γ(X, U.1))
    (h : (I.ideal U).map (X.presheaf.germ U.1 x₀ hx).hom = Ideal.span {(X.presheaf.germ U.1 x₀ hx).hom d}) :
    ∃ s : Γ(X, U.1), x₀ ∈ X.basicOpen s ∧ ∀ t : Γ(X, U.1), X.basicOpen t ≤ X.basicOpen s →
      I.ideal (X.affineBasicOpen t) = Ideal.span {resG X (X.basicOpen_le t) d} := by
  letI : Algebra Γ(X, U.1) (X.presheaf.stalk x₀) := (X.presheaf.germ U.1 x₀ hx).hom.toAlgebra
  haveI hL : IsLocalization.AtPrime (X.presheaf.stalk x₀) (U.2.primeIdealOf ⟨x₀, hx⟩).asIdeal :=
    U.2.isLocalization_stalk ⟨x₀, hx⟩
  obtain ⟨s, hsM, hsd, hsJ⟩ := exists_of_map_eq_span (R := X.presheaf.stalk x₀)
    (U.2.primeIdealOf ⟨x₀, hx⟩).asIdeal.primeCompl (IsNoetherian.noetherian (I.ideal U)) d h
  refine ⟨s, (X.mem_basicOpen s x₀ hx).2 (IsLocalization.map_units (X.presheaf.stalk x₀) ⟨s, hsM⟩), fun t ht => ?_⟩
  have hu : IsUnit (resG X (X.basicOpen_le t) s) := by
    have h0 : IsUnit (resG X (X.basicOpen_le s) s) := X.toRingedSpace.isUnit_res_basicOpen s
    have h1 := h0.map (resG X ht)
    have e : resG X ht (resG X (X.basicOpen_le s) s) = resG X (X.basicOpen_le t) s := by
      rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
      rfl
    rwa [e] at h1
  rw [← I.map_ideal_basicOpen U t]
  change (I.ideal U).map (resG X (X.basicOpen_le t)) = _
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro j hj
    obtain ⟨c, hc⟩ := hsJ j hj
    rw [Ideal.mem_comap, Ideal.mem_span_singleton']
    refine ⟨↑hu.unit⁻¹ * resG X (X.basicOpen_le t) c, ?_⟩
    have := congrArg (resG X (X.basicOpen_le t)) hc
    rw [map_mul, map_mul] at this
    rw [mul_assoc, ← this, ← mul_assoc, IsUnit.val_inv_mul, one_mul]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    have hm := Ideal.mem_map_of_mem (resG X (X.basicOpen_le t)) hsd
    rw [map_mul] at hm
    have := Ideal.mul_mem_left _ (↑hu.unit⁻¹ : Γ(X, X.basicOpen t)) hm
    rwa [← mul_assoc, IsUnit.val_inv_mul, one_mul] at this

end GlobalTheory.IdealSpread
