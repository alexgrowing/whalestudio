import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageRegSet
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem fnOf_appLE_top (D : Type) [CommRing D] {X' : Scheme.{0}} [IsIntegral X'] (p' : X' ⟶ Sp D) (V : X'.Opens)
    (hV : genericPoint X' ∈ V) (h : V ≤ p' ⁻¹ᵁ ⊤) (z : Γ(Sp D, ⊤)) :
    fnOf V hV ((p'.appLE ⊤ V h) z) = fnOf ⊤ trivial (p'.appTop z) := by
  rw [← Scheme.Hom.appLE_map p' (U := ⊤) (V := ⊤) (by simp) (homOfLE (le_top : V ≤ ⊤)).op]
  rw [CommRingCat.comp_apply]
  refine (X'.presheaf.germ_res_apply (homOfLE (le_top : V ≤ ⊤)) _ hV ((p'.appLE ⊤ ⊤ (by simp)) z)).trans ?_
  have e : p'.appLE ⊤ ⊤ (by simp) = p'.appTop := (Scheme.Hom.app_eq_appLE p').symm
  rw [e]
  rfl

theorem fnOf_preimage_mem_spanBy : ∀ (T D : Type) [CommRing T] [CommRing D] (a : T →+* D) (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] (p : X ⟶ Sp T) (p' : X' ⟶ Sp D) (π : X' ⟶ X) (θ : X.functionField →+* X'.functionField), IsPullback π p' p (spMap a) → PFF (𝟙 _) π θ → ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (hU' : genericPoint X' ∈ π ⁻¹ᵁ U), IsAffineOpen U → ∀ s : Γ(X', π ⁻¹ᵁ U), GlobalTheory.Cartier.fnOf (π ⁻¹ᵁ U) hU' s ∈ spanBy (GlobalTheory.Desc.cst p') (θ '' Set.range (GlobalTheory.Cartier.fnOf U hU)) := by
  intro T D _ _ a X X' _ _ p p' π θ H hθ U hU hU' hAff s
  letI : Algebra D X'.functionField := (GlobalTheory.Desc.cst p').toAlgebra
  set M : Submonoid X'.functionField := ((θ.comp (fnOf U hU)).rangeS).toSubmonoid with hM
  have hMset : (M : Set X'.functionField) = θ '' Set.range (fnOf U hU) := by
    ext v; simp [hM, Set.range_comp]
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := π ⁻¹ᵁ U) le_top le_top
    (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) (isAffineOpen_top _) hAff)
  have hcl := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
  let S : Subring Γ(X', π ⁻¹ᵁ U) := (Algebra.adjoin D (M : Set X'.functionField)).toSubring.comap (fnOf (π ⁻¹ᵁ U) hU')
  have hle : (⊤ : Subring _) ≤ S := by
    rw [← hcl, Subring.closure_le]
    rintro _ (⟨y, rfl⟩ | ⟨z, rfl⟩)
    · show fnOf (π ⁻¹ᵁ U) hU' _ ∈ Algebra.adjoin D (M : Set X'.functionField)
      apply Algebra.subset_adjoin
      rw [hMset]
      refine ⟨fnOf U hU y, ⟨y, rfl⟩, ?_⟩
      rw [GaussPt.theta_fnOf hθ U hU hU', Scheme.Hom.app_eq_appLE]
    · show fnOf (π ⁻¹ᵁ U) hU' _ ∈ Algebra.adjoin D (M : Set X'.functionField)
      have e : fnOf (π ⁻¹ᵁ U) hU' ((p'.appLE ⊤ (π ⁻¹ᵁ U) (by simp)) z) = algebraMap D X'.functionField ((Scheme.ΓSpecIso (CommRingCat.of D)).hom z) := by
        rw [RingHom.algebraMap_toAlgebra]
        simp only [GlobalTheory.Desc.cst, RingHom.comp_apply]
        refine (fnOf_appLE_top D p' _ hU' _ z).trans ?_
        simp
      rw [e]
      exact Subalgebra.algebraMap_mem _ _
  have hs : fnOf (π ⁻¹ᵁ U) hU' s ∈ Algebra.adjoin D (M : Set X'.functionField) := hle (Subring.mem_top s)
  have hsp : fnOf (π ⁻¹ᵁ U) hU' s ∈ Submodule.span D (M : Set X'.functionField) := by
    have := Algebra.adjoin_eq_span D (M : Set X'.functionField)
    rw [Submonoid.closure_eq] at this
    rw [← this]; exact hs
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.1 hsp
  refine ⟨n, f, fun i => g i, fun i => hMset ▸ (g i).2, ?_⟩
  rw [← hfg]
  simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra]

end GlobalTheory.Desc
