import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal

namespace GlobalTheory.PeriodFormEdge

open ReciprocityTheory.ChartRestriction.G.Out Formalism.L2.Pj IsLocalRing

section Local
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem psiIn_mono (D : DegPre R) (χ : D.X) {I J : Ideal R} (hIJ : I ≤ J) (h : D.PsiIn χ I) : D.PsiIn χ J := by
  intro j V hV hle hh
  obtain ⟨r, hr, e⟩ := h j V hV hle hh
  exact ⟨r, Ideal.map_mono hIJ hr, e⟩

theorem ordPsi_of_pole (D : DegPre R) (χ : D.X) (h : ¬ D.PsiIn χ ⊤) : ordPsi D χ = 0 := by
  unfold Formalism.L2.Pj.ordPsi
  exact le_antisymm (iSup₂_le fun n hn => absurd (psiIn_mono D χ le_top hn) h) zero_le

end Local

section At
variable {R : Type} [CommRing R] [IsDomain R] {C : Type} [NormedField C]

end At

section Agree
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PsiCoordLocal
variable {R : Type} [CommRing R] [IsDomain R]

theorem psiIn_iff {D : DegPre R} {χ : D.X} {r : R} (hr : PsiCoord D χ r) (J : Ideal R) : D.PsiIn χ J ↔ r ∈ J := by
  obtain ⟨j0, hc0, h0, e0⟩ := hr
  constructor
  · intro hJ
    obtain ⟨r', hr', e'⟩ := hJ j0 ⊤ (AlgebraicGeometry.isAffineOpen_top _) hc0 h0
    have hrr : r' = DegPre.toOpen ⊤ r := GlobalTheory.PsiCoordLocal.jK_app_inj ⊤ (e'.trans e0.symm)
    subst hrr
    rwa [← Ideal.mem_comap, Ideal.comap_map_of_bijective _ GlobalTheory.PsiCoordLocal.toOpen_top_bijective] at hr'
  · intro hJ j V hV hle h
    have h' := GlobalTheory.PsiCoordLocal.generic_le D χ j0 (le_top.trans hc0 : V ≤ _)
    obtain ⟨u, hu⟩ := GlobalTheory.PsiCoordLocal.exists_trans D χ j j0 hle (le_top.trans hc0) h h'
    refine ⟨(u : _) * DegPre.toOpen V r, Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hJ), ?_⟩
    have hres := congrArg Units.val hu
    simp only [ReciprocityTheory.ChartRestriction.G.Semi.res, ReciprocityTheory.ChartRestriction.G.Semi.pullU, Units.val_mul, Units.coe_map,
      MonoidHom.coe_coe] at hres
    rw [map_mul]
    refine Eq.trans ?_ hres.symm
    congr 1
    have hVt : (TopologicalSpace.Opens.map (jK R).base).obj V ≤ (TopologicalSpace.Opens.map (jK R).base).obj ⊤ :=
      fun x _ => trivial
    have e1 := congrArg (CommRingCat.Hom.hom ((TK R).left.presheaf.map (CategoryTheory.homOfLE hVt).op)) e0
    refine Eq.trans ?_ (e1.trans ?_)
    · have hnat := AlgebraicGeometry.Scheme.Hom.naturality (jK R) (CategoryTheory.homOfLE (le_top : V ≤ ⊤)).op
      have ht : DegPre.toOpen V r = (CommRingCat.Hom.hom ((AlgebraicGeometry.Spec (CommRingCat.of R)).presheaf.map
          (CategoryTheory.homOfLE (le_top : V ≤ ⊤)).op)) (DegPre.toOpen ⊤ r) := by
        simp only [DegPre.toOpen, RingHom.comp_apply, ← CommRingCat.comp_apply, ← Functor.map_comp]
        rfl
      rw [ht, ← CommRingCat.comp_apply, hnat, CommRingCat.comp_apply]
      rfl
    · rw [← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl

variable [IsDiscreteValuationRing R]

theorem iSup_pow_mem {ϖ : R} (hϖ : Irreducible ϖ) (u : Rˣ) (n : ℕ) :
    (⨆ (k : ℕ) (_ : (u : R) * ϖ ^ n ∈ maximalIdeal R ^ k), (k : ℕ∞)) = n := by
  have hm : maximalIdeal R = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  have hmem : ∀ k, (u : R) * ϖ ^ n ∈ maximalIdeal R ^ k ↔ k ≤ n := by
    intro k
    rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton, Units.dvd_mul_left,
      pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit]
  exact le_antisymm (iSup₂_le fun k hk => Nat.cast_le.2 ((hmem k).1 hk))
    (le_iSup₂_of_le (f := fun (k : ℕ) (_ : (u : R) * ϖ ^ n ∈ maximalIdeal R ^ k) => (k : ℕ∞)) n ((hmem n).2 le_rfl) le_rfl)

end Agree

end GlobalTheory.PeriodFormEdge
