import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellOpenLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCellOfLeadingMinorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPermutationLeadingMinorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagComponentEigenframeOnAffineOpenStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam
open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Cell

theorem mem_cellOpen : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F} (C : FlagCpt Z e) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)} (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)), hV.fromSpec ≫ genStr Z = spMap φV → ∀ y : C.Y.X, C.π y ∈ V → ∃ w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ)), y ∈ Cell.cellOpen C hV f₀ w := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C V hV φV f₀ hs₀ y hyV
  obtain ⟨U, hU, hy, φ, fr, t, hUV, hs, htri, -⟩ :=
    Spread.exists_frame_nhds E H Dw l Xo c O β Z F e C y (C.π ⁻¹ᵁ V) hyV
  have hsp : spMap (C.π.appLE V U hUV).hom ≫ hV.fromSpec = hU.fromSpec ≫ C.π :=
    IsAffineOpen.SpecMap_appLE_fromSpec C.π hV hU hUV
  have hx : spMap (C.π.appLE V U hUV).hom ≫ hV.fromSpec ≫ genι Z = (hU.fromSpec ≫ C.π) ≫ genι Z := by
    rw [← Category.assoc, hsp]
  have hφ : (C.π.appLE V U hUV).hom.comp φV = φ := by
    have h1 : spMap ((C.π.appLE V U hUV).hom.comp φV) = spMap φ := by
      rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← hs₀, ← hs, ← Category.assoc, hsp]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  obtain ⟨g, hg⟩ := Spread.exists_bc f₀ (C.π.appLE V U hUV).hom hφ hx
  choose A B hBA hA using Spread.exists_coord g fr
  let gm := (C.Y.X.presheaf.germ U y hy).hom
  have hunit : ∀ τ, IsUnit ((A τ).map gm).det := fun τ => by
    have h := congrArg Matrix.det (hBA τ)
    rw [Matrix.det_mul, Matrix.det_one] at h
    show IsUnit (gm.mapMatrix (A τ)).det
    rw [← RingHom.map_det]
    exact IsUnit.map gm (⟨⟨_, _, (mul_comm _ _).trans h, h⟩, rfl⟩ : IsUnit (A τ).det)
  choose w hw using fun τ => GlobalTheory.T.exists_permutation_leading_minors ((A τ).map gm) (hunit τ)
  let mn : (Σ τ : E →+* ℂ, Fin (Dw.mult τ + 1)) → Γ(C.Y.X, U) := fun p =>
    (((A p.1).submatrix id (w p.1)).submatrix (Fin.castLE (Nat.lt_succ_iff.mp p.2.is_lt))
      (Fin.castLE (Nat.lt_succ_iff.mp p.2.is_lt))).det
  have hmn : ∀ p, IsUnit (gm (mn p)) := fun p => by
    have := hw p.1 p.2 (Nat.lt_succ_iff.mp p.2.is_lt)
    simpa [mn, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.submatrix_map] using this
  let f := ∏ p, mn p
  have hyf : y ∈ C.Y.X.basicOpen f := by
    rw [Scheme.mem_basicOpen _ _ _ hy]
    show IsUnit (gm f)
    rw [map_prod]
    exact IsUnit.prod_univ_iff.mpr hmn
  have hle : C.Y.X.basicOpen f ≤ U := Scheme.basicOpen_le _ f
  let r := (C.Y.X.presheaf.map (homOfLE hle).op).hom
  have hfu : IsUnit (r f) := RingedSpace.isUnit_res_basicOpen C.Y.X.toRingedSpace f
  have hmu : ∀ p, IsUnit (r (mn p)) := fun p =>
    isUnit_of_dvd_unit (map_dvd r (Finset.dvd_prod_of_mem mn (Finset.mem_univ p))) hfu
  have hc : ∀ τ, ∃ a, InCell ((A τ).map r) (w τ) a := fun τ => by
    refine GlobalTheory.T.exists_cell_of_leading_minors _ _ fun k hk => ?_
    have := hmu ⟨τ, ⟨k, Nat.lt_succ_of_le hk⟩⟩
    simpa [mn, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.submatrix_map] using this
  choose a ha using hc
  have hcell := GlobalTheory.T.flag_component_eigenframe_on_affine_open C hV f₀ hU hUV (gen_mem hy) fr t hx A hs htri
    (fun τ i => by rw [hA τ i]; simp only [hg]) (hU.basicOpen f) hle (gen_mem hyf) w a ha
  exact ⟨w, le_sSup (show C.Y.X.basicOpen f ∈ {U | ∃ a, CellAt C hV f₀ w U a} from ⟨a, hcell⟩) hyf⟩

end GlobalTheory.ShFam.Cell
