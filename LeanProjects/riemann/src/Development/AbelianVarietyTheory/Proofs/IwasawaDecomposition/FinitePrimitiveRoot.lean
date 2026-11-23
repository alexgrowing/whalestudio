import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCyclotomicUnramifiedCompletedIntegersStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal
namespace GlobalTheory.CycLayers

theorem layer_of_clauses {F : Type*} [NormedField F] (A R : Subring F) (h : A ≤ R) (l m : ℕ)
    (hlnorm : ‖(l : F)‖ < 1) (hl0 : (l : F) ≠ 0) (hm : 0 < m)
    (hdiv : ∀ x ∈ R, ∀ y ∈ R, ‖x‖ ≤ ‖y‖ → x / y ∈ R)
    (T : Finset F) (hT : ∀ x, x ∈ R ↔ x ∈ Submodule.span A (T : Set F))
    (ζ : F) (hzmem : ζ ∈ R) (hζ : IsPrimitiveRoot ζ m)
    (hlast : ∀ x ∈ R, ∃ (p : Polynomial A) (d : A), d ≠ 0 ∧ x * (d : F) = Polynomial.aeval ζ p) :
    letI := (Subring.inclusion h).toAlgebra;
    Module.Finite A R ∧ ∃ z : Rˣ, IsPrimitiveRoot (z : R) m ∧ ∀ x : FractionRing R, ∃ p : Polynomial A, ∃ d : A, d ≠ 0 ∧
      x * algebraMap _ (FractionRing R) (algebraMap _ R d) = algebraMap _ (FractionRing R) (Polynomial.aeval (z : R) p) := by
  let _ := (Subring.inclusion h).toAlgebra
  refine ⟨?_, ?_⟩
  · let f : R →ₗ[A] F :=
      { toFun := Subtype.val, map_add' := fun _ _ => rfl,
        map_smul' := fun a y => by rw [RingHom.id_apply, Algebra.smul_def, Subring.smul_def]; rfl }
    let S : Set R := Subtype.val ⁻¹' (T : Set F)
    have hS : S.Finite := T.finite_toSet.preimage Subtype.val_injective.injOn
    have himg : f '' S = (T : Set F) := by
      ext c
      constructor
      · rintro ⟨y, hy, rfl⟩; exact hy
      · intro hc
        have hcR : c ∈ R := (hT c).2 (Submodule.subset_span hc)
        exact ⟨⟨c, hcR⟩, hc, rfl⟩
    have key : ∀ y : R, y ∈ Submodule.span A S := by
      intro y
      have h1 : (y : F) ∈ Submodule.span A (T : Set F) := (hT y).1 y.2
      rw [← himg, ← Submodule.map_span] at h1
      obtain ⟨y', hy', hyy⟩ := h1
      have : y' = y := Subtype.ext hyy
      rw [← this]; exact hy'
    exact ⟨⟨hS.toFinset, by rw [Set.Finite.coe_toFinset]; exact eq_top_iff.2 fun y _ => key y⟩⟩
  · have hprim : IsPrimitiveRoot (⟨ζ, hzmem⟩ : R) m :=
      IsPrimitiveRoot.coe_submonoidClass_iff.1 hζ
    refine ⟨(hprim.isUnit hm.ne').unit, by simpa using hprim, ?_⟩
    intro x
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) x
    set b : R := (s : R) with hbdef
    have hb : b ∈ nonZeroDivisors R := s.2
    have hb0 : (b : F) ≠ 0 := by
      intro h0
      have : b = 0 := Subtype.ext h0
      exact nonZeroDivisors.ne_zero hb this
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 hb0) hlnorm
    have hlR : (l : F) ^ N ∈ R := pow_mem (natCast_mem R l) N
    have hlNA : (l : F) ^ N ∈ A := pow_mem (natCast_mem A l) N
    have hq : (l : F) ^ N / b ∈ R := by
      refine hdiv _ hlR _ b.2 ?_
      rw [norm_pow]; exact hN.le
    obtain ⟨p, d', hd', hpd⟩ := hlast _ (mul_mem a.2 hq)
    refine ⟨p, ⟨(l : F) ^ N, hlNA⟩ * d', ?_, ?_⟩
    · refine mul_ne_zero ?_ hd'
      intro h0
      have h1 : (l : F) ^ N = 0 := congrArg Subtype.val h0
      exact pow_ne_zero N hl0 h1
    · have hev : ((Polynomial.aeval ((hprim.isUnit hm.ne').unit : R) p : R) : F) = Polynomial.aeval ζ p := by
        rw [Polynomial.aeval_def, Polynomial.aeval_def, IsUnit.unit_spec]
        rw [show ((Polynomial.eval₂ (algebraMap A R) (⟨ζ, hzmem⟩ : R) p : R) : F) =
          R.subtype (Polynomial.eval₂ (algebraMap A R) (⟨ζ, hzmem⟩ : R) p) from rfl, Polynomial.hom_eval₂]
        rfl
      have hRd : algebraMap A R (⟨(l : F) ^ N, hlNA⟩ * d') =
          b * ⟨(l : F) ^ N / b, hq⟩ * algebraMap A R d' := by
        rw [map_mul]; congr 1
        apply Subtype.ext
        show (l : F) ^ N = (b : F) * ((l : F) ^ N / b)
        field_simp
      have hfin : a * ⟨(l : F) ^ N / b, hq⟩ * algebraMap A R d' =
          Polynomial.aeval ((hprim.isUnit hm.ne').unit : R) p := by
        apply Subtype.ext
        rw [hev, ← hpd]
        rfl
      rw [hRd, ← hfin, map_mul, map_mul, map_mul, map_mul, ← mul_assoc, ← mul_assoc, IsLocalization.mk'_spec]

theorem finite_primitive_root :
    ∀ (l : ℕ) [Fact l.Prime] (K₀ L : Loc.FinExt l) (k : ℕ) (h : clC l (Kt l K₀ L) ≤ clC l (Kt l K₀ L ⊔ muK l k)), letI := (Subring.inclusion h).toAlgebra; Module.Finite ↥(clC l (Kt l K₀ L)) ↥(clC l (Kt l K₀ L ⊔ muK l k)) ∧ ∃ z : (↥(clC l (Kt l K₀ L ⊔ muK l k)))ˣ, IsPrimitiveRoot (z : ↥(clC l (Kt l K₀ L ⊔ muK l k))) (l ^ k) ∧ ∀ x : FractionRing ↥(clC l (Kt l K₀ L ⊔ muK l k)), ∃ p : Polynomial ↥(clC l (Kt l K₀ L)), ∃ d : ↥(clC l (Kt l K₀ L)), d ≠ 0 ∧ x * algebraMap _ (FractionRing ↥(clC l (Kt l K₀ L ⊔ muK l k))) (algebraMap _ ↥(clC l (Kt l K₀ L ⊔ muK l k)) d) = algebraMap _ (FractionRing ↥(clC l (Kt l K₀ L ⊔ muK l k))) (Polynomial.aeval (z : ↥(clC l (Kt l K₀ L ⊔ muK l k))) p) := by
  intro l _ K₀ L k h
  obtain ⟨-, -, -, -, hdiv, -, ⟨T, hT⟩, ζ, hzmem, hζ, hlast⟩ := GlobalTheory.T.exists_cyclotomic_unramified_completed_integers l K₀ L k
  have hlnorm : ‖(l : ℂ_[l])‖ < 1 := by
    have e : ((l : ℚ_[l]) : ℂ_[l]) = (l : ℂ_[l]) := by simp
    rw [← e, PadicComplex.norm_extends' l (l : ℚ_[l]), Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hl0 : (l : ℂ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  exact layer_of_clauses _ _ h l (l ^ k) hlnorm hl0 (pow_pos (Fact.out : l.Prime).pos k) hdiv T hT ζ hzmem hζ hlast

end GlobalTheory.CycLayers
