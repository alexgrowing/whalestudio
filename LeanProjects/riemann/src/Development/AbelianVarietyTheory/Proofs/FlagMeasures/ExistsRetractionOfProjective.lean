import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor

namespace GlobalTheory.ProjectiveRetraction

open NumberField

theorem exists_retraction_of_projective {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) [Module.Projective R (M ⧸ N)] :
    ∃ p : M →ₗ[R] M, (∀ x, p x ∈ N) ∧ ∀ x ∈ N, p x = x := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ (LinearMap.id : (M ⧸ N) →ₗ[R] (M ⧸ N))
    N.mkQ_surjective
  refine ⟨LinearMap.id - s ∘ₗ N.mkQ, fun x => ?_, fun x hx => ?_⟩
  · have h1 : N.mkQ (s (N.mkQ x)) = N.mkQ x := LinearMap.congr_fun hs (N.mkQ x)
    have h2 : N.mkQ (x - s (N.mkQ x)) = 0 := by rw [map_sub, h1, sub_self]
    exact (Submodule.Quotient.mk_eq_zero N).1 h2
  · have h0 : N.mkQ x = 0 := (Submodule.Quotient.mk_eq_zero N).2 hx
    show x - s (N.mkQ x) = x
    rw [h0, map_zero, sub_zero]

theorem exists_retraction {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (M0 L : Submodule (𝓞 E) V) (hL : L.FG)
    (h : Formalism.MainNotions.S.Lat.IsPrimitiveSub M0 L) :
    ∃ r : L →ₗ[𝓞 E] M0, ∀ x : M0, r ⟨(x : V), h.1 x.2⟩ = x := by
  set N : Submodule (𝓞 E) L := M0.comap L.subtype with hN
  have hsat : ∀ (a : 𝓞 E), a ≠ 0 → ∀ x : L, a • x ∈ N → x ∈ N := by
    intro a ha x hx
    have hx' : a • (x : V) ∈ M0 := hx
    have ha' : (algebraMap (𝓞 E) E a) ≠ 0 := by
      intro h0
      exact ha ((IsFractionRing.injective (𝓞 E) E) (by rw [h0, map_zero]))
    have h1 : (algebraMap (𝓞 E) E a) • (x : V) ∈ Submodule.span E (M0 : Set V) := by
      rw [algebraMap_smul]
      exact Submodule.subset_span hx'
    have h2 : (x : V) ∈ Submodule.span E (M0 : Set V) :=
      (Submodule.smul_mem_iff _ ha').1 h1
    show (x : V) ∈ M0
    rw [h.2]
    exact ⟨x.2, h2⟩
  have htor : Submodule.torsion (𝓞 E) (L ⧸ N) = ⊥ := by
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨x, rfl⟩ := N.mkQ_surjective q
    obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff _).1 hq
    have ha2 : N.mkQ ((a : 𝓞 E) • x) = 0 := by
      rw [map_smul]
      exact ha
    have hx : x ∈ N :=
      hsat a (nonZeroDivisors.ne_zero a.2) x ((Submodule.Quotient.mk_eq_zero N).1 ha2)
    exact (Submodule.Quotient.mk_eq_zero N).2 hx
  haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.2 hL
  haveI : Module.Flat (𝓞 E) (L ⧸ N) := IsDedekindDomain.flat_iff_torsion_eq_bot.2 htor
  haveI : Module.FinitePresentation (𝓞 E) (L ⧸ N) := Module.finitePresentation_of_finite _ _
  haveI : Module.Projective (𝓞 E) (L ⧸ N) := Module.Flat.projective_of_finitePresentation
  obtain ⟨p, hp1, hp2⟩ := exists_retraction_of_projective N
  refine ⟨LinearMap.codRestrict M0 (L.subtype ∘ₗ p) (fun x => hp1 x), fun x => ?_⟩
  apply Subtype.ext
  have hx : (⟨(x : V), h.1 x.2⟩ : L) ∈ N := x.2
  show ((p ⟨(x : V), h.1 x.2⟩ : L) : V) = x
  rw [hp2 _ hx]

end GlobalTheory.ProjectiveRetraction
