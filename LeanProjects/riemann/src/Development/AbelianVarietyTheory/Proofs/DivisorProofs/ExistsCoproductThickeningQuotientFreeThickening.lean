import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeThickeningLevelFinitelyManyElementsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomSpecPointsLevelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientNilCrystallineThickeningOfSubDPIdeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSectionsMonoReductionAffineInfStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientSubDPIdeal

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.CopEx

theorem exists_cop : ∀ (D : Data) (Λ : Lift D) (n : ℕ) (U : AffOp D.X) (T : Thick D.κ D.t), IsLev T.δ (n + 1) →
    ⊤ ≤ (T.x ≫ D.i) ⁻¹ᵁ U.unop.1 → ∃ (F G : Thick D.κ D.t) (u : T ⟶ F) (q : F ⟶ G) (r : Λ.L.obj U ⟶ G),
      (KK D.κ D.t).QAt u ∧ IsLev F.δ (n + 1) ∧ Function.Surjective q.φ ∧ (∀ b, q.φ b ∈ G.J → b ∈ F.J) ∧
        IsCop (n + 1) (u ≫ q) r := by
  intro D Λ n U T hT hU
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.T.hom_spec_points_levels D Λ
  haveI : Algebra.Smooth D.R (Sec D.s U.unop.1) := (GlobalTheory.T.smooth_sections_mono_reduction_affine_inf D).1 U.unop
  obtain ⟨m, pres, hpres⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1
    (inferInstance : Algebra.FiniteType D.R (Sec D.s U.unop.1))
  obtain ⟨g, hgx, hgR⟩ := h2 U T hU
  choose bl hbl using fun i : Fin m ↦ T.surj (g (pres (MvPolynomial.X i)))
  obtain ⟨F, u, τ, hfree, hQ⟩ := GlobalTheory.T.exists_freeThickening_level_finitelyMany_elements D.R D.I D.κ D.X₀ D.t n m T hT
  let ψ : MvPolynomial (Fin m) D.R →ₐ[D.R] F.B := MvPolynomial.aeval fun i ↦ u.φ (bl i) + τ i
  have hψX : ∀ i, ψ (MvPolynomial.X i) = u.φ (bl i) + τ i := fun i ↦ MvPolynomial.aeval_X _ _

  have hψπ : ∀ p, F.π (ψ p) = u.φ₀ (g (pres p)) := by
    have e : F.π.comp (ψ : MvPolynomial (Fin m) D.R →+* F.B) =
        u.φ₀.comp (g.comp (pres : MvPolynomial (Fin m) D.R →+* Sec D.s U.unop.1)) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        show F.π (ψ (MvPolynomial.C r)) = u.φ₀ (g (pres (MvPolynomial.C r)))
        have hC : MvPolynomial.C r = algebraMap D.R (MvPolynomial (Fin m) D.R) r := rfl
        rw [hC, AlgHom.commutes, AlgHom.commutes, hgR, u.comm, u.φ.commutes]
      · intro i
        simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, hψX, map_add]
        rw [(F.ker _).2 (hfree.2.1 i), add_zero, ← hbl i, u.comm]
    exact fun p ↦ RingHom.congr_fun e p
  have hker : ∀ k ∈ RingHom.ker pres, ψ k ∈ F.J := fun k hk ↦
    (F.ker _).1 (by rw [hψπ, (RingHom.mem_ker).1 hk, map_zero, map_zero])
  set 𝔟 : Ideal F.B := Ideal.span {y | ∃ j : ℕ, j ≠ 0 ∧ ∃ x ∈ ψ '' (RingHom.ker pres : Set _), y = F.δ.dpow j x}
    with h𝔟def
  have h𝔟 : F.δ.IsSubDPIdeal 𝔟 := (GlobalTheory.DPQuot.quotient_subDPIdeal F.B F.J F.δ).2 _ (by
    rintro _ ⟨k, hk, rfl⟩; exact hker k hk)
  obtain ⟨G, q, hqs, hq0, hGJ, hGlev, hquniv⟩ := GlobalTheory.T.exists_quotient_nilCrystallineThickening_of_subDPIdeal D.R D.I D.κ D.X₀ D.t F 𝔟 h𝔟
  have hψ𝔟 : ∀ k ∈ RingHom.ker pres, (q.φ.comp ψ) k = 0 := fun k hk ↦ (hq0 _).2
    (Ideal.subset_span ⟨1, one_ne_zero, ψ k, ⟨k, hk, rfl⟩, (F.δ.dpow_one (hker k hk)).symm⟩)

  let y : Sec D.s U.unop.1 →ₐ[D.R] G.B :=
    (Ideal.Quotient.liftₐ (RingHom.ker pres) (q.φ.comp ψ) hψ𝔟).comp
      (Ideal.quotientKerAlgEquivOfSurjective hpres).symm.toAlgHom
  have hy : ∀ p, y (pres p) = q.φ (ψ p) := by
    intro p
    have : (Ideal.quotientKerAlgEquivOfSurjective hpres).symm (pres p) = Ideal.Quotient.mk _ p :=
      (AlgEquiv.symm_apply_eq _).2 rfl
    change Ideal.Quotient.liftₐ (RingHom.ker pres) (q.φ.comp ψ) hψ𝔟
      ((Ideal.quotientKerAlgEquivOfSurjective hpres).symm (pres p)) = _
    rw [this]
    rfl
  have hyπ : G.π.comp (y : Sec D.s U.unop.1 →+* G.B) = (u ≫ q).φ₀.comp g := by
    ext a
    obtain ⟨p, rfl⟩ := hpres a
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.coe_coe, hy]
    rw [← q.comm, hψπ]
    rfl
  obtain ⟨r, hr⟩ := (h1 U G y).1 (by
    rw [hyπ, Cris.spMap_comp, Category.assoc, hgx, ← Category.assoc, (u ≫ q).pt])
  refine ⟨F, G, u, q, r, hQ, hfree.1, hqs, ?_, hGlev _ hfree.1, ?_⟩
  · intro b hb
    rw [hGJ] at hb
    obtain ⟨j, hj, hjb⟩ := (Ideal.mem_map_iff_of_surjective _ hqs).1 hb
    have : b - j ∈ 𝔟 := (hq0 _).1 (by rw [map_sub]; change q.φ b - q.φ j = 0; rw [← hjb]; exact sub_self _)
    have := F.J.add_mem hj (h𝔟.isSubideal this)
    rwa [add_sub_cancel] at this
  intro S hS a b

  have hsame : ∀ x, S.π (b.φ (Λ.e U x)) = a.φ₀ (g x) := by
    have e := h3 U S.B₀ (b.φ₀.comp ((Λ.L.obj U).π.comp (Λ.e U : Sec D.s U.unop.1 →+* (Λ.L.obj U).B)))
      (a.φ₀.comp g) (by
        rw [Cris.spMap_comp, Category.assoc, Λ.pt U, ← Category.assoc, b.pt, Cris.spMap_comp, Category.assoc, hgx, ← Category.assoc, a.pt])
    intro x
    rw [← b.comm]
    exact RingHom.congr_fun e x
  let c : Fin m → S.B := fun i ↦ b.φ (Λ.e U (pres (MvPolynomial.X i))) - a.φ (bl i)
  have hc : ∀ i, c i ∈ S.J := by
    intro i
    refine (S.ker _).1 ?_
    simp only [c, map_sub, hsame, ← a.comm, hbl i, sub_self]
  obtain ⟨g', ⟨hg'u, hg'τ⟩, hg'uniq⟩ := hfree.2.2 S hS a c hc
  have hg'ψ : ∀ p, g'.φ (ψ p) = b.φ (Λ.e U (pres p)) := by
    have e : g'.φ.comp ψ = b.φ.comp ((Λ.e U).toAlgHom.comp pres) := by
      apply MvPolynomial.algHom_ext
      intro i
      simp only [AlgHom.comp_apply, hψX, map_add, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
      rw [hg'τ i, ← Thick.comp_φ, hg'u]
      simp only [c]
      abel
    exact fun p ↦ AlgHom.congr_fun e p
  have hkill : ∀ z ∈ 𝔟, g'.φ z = 0 := by
    intro z hz
    refine (Ideal.span_le (I := RingHom.ker (g'.φ : F.B →+* S.B))).2 ?_ hz
    rintro _ ⟨j, hj, _, ⟨k, hk, rfl⟩, rfl⟩
    change g'.φ (F.δ.dpow j (ψ k)) = 0
    have hdp := g'.dp.dpow_comp (n := j) _ (hker k hk)
    change S.δ.dpow j (g'.φ (ψ k)) = g'.φ (F.δ.dpow j (ψ k)) at hdp
    rw [← hdp, hg'ψ, (RingHom.mem_ker).1 hk, map_zero, map_zero, dpow_eval_zero _ hj]
  obtain ⟨c0, hc0, hc0u⟩ := hquniv S g' hkill
  refine ⟨c0, ⟨by rw [Category.assoc, hc0, hg'u], ?_⟩, ?_⟩
  · ext z
    obtain ⟨x, rfl⟩ := (Λ.e U).surjective z
    obtain ⟨p, rfl⟩ := hpres x
    rw [Thick.comp_φ, hr, hy, ← Thick.comp_φ, hc0, hg'ψ]
  · rintro c1 ⟨hc1a, hc1b⟩
    refine hc0u c1 (hg'uniq (q ≫ c1) ⟨by rw [← Category.assoc, hc1a], fun i ↦ ?_⟩)
    have hτ : τ i = ψ (MvPolynomial.X i) - u.φ (bl i) := by rw [hψX]; abel
    rw [hτ, map_sub, Thick.comp_φ, Thick.comp_φ, ← hy, ← hr, ← Thick.comp_φ, hc1b, ← Thick.comp_φ q c1,
      ← Thick.comp_φ u, ← Category.assoc, hc1a]

end GlobalTheory.CopEx
