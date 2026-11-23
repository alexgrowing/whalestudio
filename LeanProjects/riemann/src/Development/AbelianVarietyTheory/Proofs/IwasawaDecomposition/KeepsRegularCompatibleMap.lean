import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.TorRef

open GlobalTheory.Cartier

theorem isRegularFn_of_app_of_denseRange {T Y : Scheme.{0}} (hdom : ∀ y : Y, IsDomain (Y.presheaf.stalk y))
    (φ : T ⟶ Y) (hφ : DenseRange φ) {U : Y.Opens} (g : Γ(Y, U))
    (hg : IsRegularFn ((φ.app U).hom g)) : IsRegularFn g := by
  refine isRegularFn_iff_germ.2 fun x hx => ?_
  haveI := hdom x
  refine mem_nonZeroDivisors_of_ne_zero fun h0 => ?_
  have e : (Y.presheaf.germ U x hx).hom g = (Y.presheaf.germ U x hx).hom 0 := by
    rw [h0, map_zero]
  obtain ⟨W, hxW, i₁, i₂, e'⟩ := Y.presheaf.germ_eq x hx hx _ _ e
  have le : W ≤ U := i₁.le
  have e'' : resG Y le g = resG Y le 0 := e'
  rw [map_zero] at e''
  obtain ⟨u, hu⟩ := hφ.exists_mem_open W.isOpen ⟨x, hxW⟩
  haveI : Nonempty (φ ⁻¹ᵁ W) := ⟨⟨u, hu⟩⟩
  have hr := hg.resG (φ.preimage_mono le)
  rw [← app_resG φ le, e'', map_zero] at hr
  exact hr.ne_zero rfl

theorem keepsRegular_of_comp_j : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (Xo : Moduli D l) (c : Coeff l) (X Z : GMod Xo c) (π : Z.X ⟶ X.X)
    (DX : GlobalTheory.EffCartierData X.X), Z.j ≫ π = X.j → DX.KeepsRegular π := by
  intro E _ _ _ H D l Xo c X Z π DX h i
  have hX := GlobalTheory.genericPart_dense_proOpen (𝓞 c.F) c.F X.X (Xo.XF c) X.s X.jQ X.flat X.proj X.jQ_open X.jQ_dense
  have hZ := GlobalTheory.genericPart_dense_proOpen (𝓞 c.F) c.F Z.X (Xo.XF c) Z.s Z.jQ Z.flat Z.proj Z.jQ_open Z.jQ_dense
  haveI hfl : Flat X.j := hX.2.2.2.2.1
  haveI hd : IsDominant Z.j := hZ.2.2.2.2.2.1
  have hreg := (DX.regular i).app_of_flat X.j
  rw [← h, Scheme.Hom.comp_app] at hreg
  exact isRegularFn_of_app_of_denseRange (fun z => (Z.normal z).1) Z.j Z.j.denseRange _ hreg

end GlobalTheory.TorRef
