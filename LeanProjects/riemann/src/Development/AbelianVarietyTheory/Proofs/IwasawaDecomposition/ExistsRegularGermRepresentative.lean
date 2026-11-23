import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraitOrdOfTraitOrdPt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolOfFiniteSurjective

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

noncomputable section

namespace GlobalTheory.GermSpread

theorem exists_basicOpen_germ_ne_zero {X : Scheme.{0}} (hX : ∀ x : X, IsDomain (X.presheaf.stalk x))
    {W : X.Opens} (hW : IsAffineOpen W) [IsNoetherianRing Γ(X, W)] {z : X} (hz : z ∈ W)
    (f₀ : Γ(X, W)) (ha : (X.presheaf.germ W z hz).hom f₀ ≠ 0) :
    ∃ s : Γ(X, W), z ∈ X.basicOpen s ∧
      ∀ x (hx : x ∈ X.basicOpen s), (X.presheaf.germ W x (X.basicOpen_le s hx)).hom f₀ ≠ 0 := by
  let I : Ideal Γ(X, W) := LinearMap.ker (LinearMap.mulRight Γ(X, W) f₀)
  obtain ⟨T, hT⟩ := (IsNoetherian.noetherian I : I.FG)
  have key : ∀ t ∈ T, ∃ m : Γ(X, W), IsUnit ((X.presheaf.germ W z hz).hom m) ∧ m * t = 0 := by
    intro t ht
    have htI : t ∈ I := hT ▸ Submodule.subset_span ht
    have h0 : t * f₀ = 0 := htI
    have := hX z
    have hg : (X.presheaf.germ W z hz).hom t = 0 := by
      have e := congrArg (X.presheaf.germ W z hz).hom h0
      rw [map_mul, map_zero] at e
      exact (mul_eq_zero.1 e).resolve_right ha
    letI : Algebra Γ(X, W) (X.presheaf.stalk z) := X.presheaf.algebra_section_stalk ⟨z, hz⟩
    haveI := hW.isLocalization_stalk ⟨z, hz⟩
    obtain ⟨m, hm⟩ := (IsLocalization.map_eq_zero_iff (hW.primeIdealOf ⟨z, hz⟩).asIdeal.primeCompl
      (X.presheaf.stalk z) t).1 hg
    exact ⟨m, IsLocalization.map_units (X.presheaf.stalk z) m, hm⟩
  choose! m hm using key
  have hkill : ∀ u ∈ I, (∏ t ∈ T, m t) * u = 0 := by
    intro u hu
    rw [← hT] at hu
    let K : Ideal Γ(X, W) := LinearMap.ker (LinearMap.mulLeft Γ(X, W) (∏ t ∈ T, m t))
    have hle : Submodule.span Γ(X, W) (T : Set Γ(X, W)) ≤ K := by
      refine Submodule.span_le.2 fun t ht => ?_
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem m ht
      change (∏ t ∈ T, m t) * t = 0
      rw [hc, mul_comm (m t) c, mul_assoc, (hm t ht).2, mul_zero]
    exact hle hu
  refine ⟨∏ t ∈ T, m t, ?_, ?_⟩
  · rw [X.mem_basicOpen _ z hz, map_prod]
    exact Finset.prod_induction _ IsUnit (fun a b ha hb => ha.mul hb) isUnit_one (fun t ht => (hm t ht).1)
  · intro x hx h0
    have hxW := X.basicOpen_le _ hx
    have hu := (X.mem_basicOpen _ x hxW).1 hx
    have := hX x
    letI : Algebra Γ(X, W) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxW⟩
    haveI := hW.isLocalization_stalk ⟨x, hxW⟩
    obtain ⟨u, hu0⟩ := (IsLocalization.map_eq_zero_iff (hW.primeIdealOf ⟨x, hxW⟩).asIdeal.primeCompl
      (X.presheaf.stalk x) f₀).1 h0
    have huI : (u : Γ(X, W)) ∈ I := show (u : Γ(X, W)) * f₀ = 0 from hu0
    have e := congrArg (X.presheaf.germ W x hxW).hom (hkill _ huI)
    rw [map_mul, map_zero] at e
    have h1 : IsUnit ((X.presheaf.germ W x hxW).hom (u : Γ(X, W))) :=
      IsLocalization.map_units (X.presheaf.stalk x) u
    exact not_isUnit_zero (e ▸ hu.mul h1)

theorem exists_isRegularFn_germ_eq : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Level H} {Xo : Moduli D l} {c : Coeff l} (Z : GMod Xo c) (z : Z.X) (a : Z.X.presheaf.stalk z), a ≠ 0 →
    ∃ (U : Z.X.Opens) (hz : z ∈ U) (f : Γ(Z.X, U)), (Z.X.presheaf.germ U z hz).hom f = a ∧ IsRegularFn f := by
  intro E _ _ _ H D l Xo c Z z a ha
  haveI := GlobalTheory.AmpleDown.isNoetherian_gmod Z
  have hN := Z.normal
  obtain ⟨V, hzV, f₀, rfl⟩ := Z.X.presheaf.exists_germ_eq a
  obtain ⟨W, hWa, hzW, hWV⟩ := (Opens.isBasis_iff_nbhd.mp Z.X.isBasis_affineOpens) hzV
  haveI : IsNoetherianRing Γ(Z.X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hWa⟩
  have hW : IsAffineOpen W := hWa
  obtain ⟨s, hzs, hs⟩ := exists_basicOpen_germ_ne_zero (fun x => (hN x).1) hW hzW (resG Z.X hWV f₀)
    (by rwa [germ_resG])
  refine ⟨Z.X.basicOpen s, hzs, resG Z.X ((Z.X.basicOpen_le s).trans hWV) f₀, by rw [germ_resG], ?_⟩
  refine isRegularFn_iff_germ.2 fun x hx => ?_
  have := (hN x).1
  rw [germ_resG]
  refine mem_nonZeroDivisors_of_ne_zero ?_
  have h := hs x hx
  rwa [germ_resG] at h

end GlobalTheory.GermSpread
