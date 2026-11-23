import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.DVR

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem mem_pow_of_thick_zero' (G : Over (Spec (CommRingCat.of V))) [Flat G.hom] (ϖ : V) (hϖ : Irreducible ϖ)
    (U : G.left.Opens) (x : Γ(G.left, U)) (e : ℕ)
    (hx : ((fstG (maximalIdeal V) e G).left.app U).hom x = 0) :
    x ∈ Ideal.span {(G.left.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
      ((G.hom.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ϖ))} ^ (e + 1) := by
  obtain ⟨g, hg⟩ := exists_div G.hom (pow_ne_zero (e + 1) hϖ.ne_zero) U x fun y hy => by
    obtain ⟨W, hW, hyW, le₀⟩ := exists_isAffineOpen_mem_and_subset hy
    have le : W ≤ U := le₀
    let alg : V →+* Γ(G.left, W) :=
      (G.hom.appLE ⊤ W (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom
    have s₀ : hW.fromSpec ≫ G.hom = spMap alg := by
      rw [← IsAffineOpen.SpecMap_appLE_fromSpec G.hom (isAffineOpen_top _) hW (fun _ _ => trivial),
        IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]; rfl
    let J : Ideal Γ(G.left, W) := Ideal.span {alg (ϖ ^ (e + 1))}
    let q : V ⧸ maximalIdeal V ^ (e + 1) →+* Γ(G.left, W) ⧸ J := Ideal.quotientMap J alg (by
      rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_le, Set.singleton_subset_iff]
      exact Ideal.subset_span rfl)
    have sq : (spMap (Ideal.Quotient.mk J) ≫ hW.fromSpec) ≫ G.hom = spMap q ≫ thick V (maximalIdeal V) e := by
      rw [Category.assoc, s₀, ← spMap_comp]
      exact (congrArg spMap (Ideal.quotientMap_comp_mk _).symm).trans (spMap_comp _ _)
    let r : Sp (Γ(G.left, W) ⧸ J) ⟶ (thickObj V (maximalIdeal V) e G).left := pullback.lift _ _ sq
    have r₁ : r ≫ fGl (maximalIdeal V) G e = spMap (Ideal.Quotient.mk J) ≫ hW.fromSpec := pullback.lift_fst _ _ _
    have z₀ : Ideal.Quotient.mk J ((G.left.presheaf.map (homOfLE le).op).hom x) = 0 := cst_ext fun z => by
      have hm : fGl (maximalIdeal V) G e (r z) ∈ U := (congrArg (fun m => m z ∈ U) r₁).mpr
        (le (hW.range_fromSpec.le ⟨spMap (Ideal.Quotient.mk J) z, rfl⟩))
      have e₁ := (gs_fromSpec hW le (spMap (Ideal.Quotient.mk J)) z x).trans (gs_spec _ z _)
      rw [← r₁] at e₁
      rw [← e₁, cst, map_zero, gs_zero _ z ⊤ trivial]
      exact (gs_pull r _ z U hm x).symm.trans ((congrArg (gs r z _) hx).trans (gs_zero r z _ hm))
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 z₀)
    refine ⟨gs (𝟙 _) y W c, (gs_res (𝟙 _) y le hyW _).symm.trans ((congrArg (gs (𝟙 _) y W) hc).trans
      ((gs_mul _ y W hyW _ _).trans (congrArg₂ (· * ·) ?_ rfl)))⟩
    exact (gs_constFn G.hom W (𝟙 _) y hyW _).trans (by rw [Category.id_comp])
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, hg, constFn, map_pow, map_pow]
  exact dvd_mul_right _ _

end ReciprocityTheory.ChartRestriction.G.DVR
