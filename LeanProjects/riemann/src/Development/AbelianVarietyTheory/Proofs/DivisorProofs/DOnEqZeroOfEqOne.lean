import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitMkOfFormallyUnramified
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

namespace GlobalTheory

open TopForm

namespace TopForm

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {D : ℕ} {U : Y.Opens}

theorem dOn_eq_zero_of_eq_one (f : Fin D → Γ(Y, U)) (b : Fin D) (hb : f b = 1) : dOn p f = 0 := by
  rw [dOn, dForm_eq]
  refine AlternatingMap.map_coord_zero _ b ?_
  let := (algX p U).toAlgebra
  rw [hb]
  exact (KaehlerDifferential.D k Γ(Y, U)).map_one_eq_zero

theorem jacOn_of_eq_one (f : Fin (D + 1) → Γ(Y, U)) (i : Fin (D + 1)) (hi : f i = 1) :
    jacOn p f = (-1 : Γ(Y, U)) ^ (i : ℕ) • dOn p fun b => f (i.succAbove b) := by
  rw [jacOn_eq, Finset.sum_eq_single i, hi, mul_one]
  · intro a _ ha
    obtain ⟨b, hb⟩ := Fin.exists_succAbove_eq (Ne.symm ha)
    rw [dOn_eq_zero_of_eq_one _ b (by rw [hb, hi]), smul_zero]
  · simp

theorem isUnit_of_affine {f : Γ(Y, U)}
    (h : ∀ W : Y.Opens, IsAffineOpen W → ∀ hW : W ≤ U, IsUnit (resG Y hW f)) : IsUnit f := by
  refine Y.toRingedSpace.isUnit_of_isUnit_germ U f fun x hx => ?_
  obtain ⟨W, hW, hxW, hWU⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hx
  have := (h W hW hWU).map (Y.presheaf.germ W x hxW).hom
  rwa [show (Y.presheaf.germ W x hxW).hom (resG Y hWU f) = (Y.presheaf.germ U x hx).hom f from
    Y.presheaf.germ_res_apply (homOfLE hWU) x hxW f] at this

theorem isFreeGen_dForm_X (k : Type) [CommRing k] (D : ℕ) : IsFreeGen (MvPolynomial (Fin D) k)
    (dForm (algebraMap k (MvPolynomial (Fin D) k)) (X : Fin D → _)) := by
  have key (inst : Algebra k (MvPolynomial (Fin D) k))
      (e : inst = AddMonoidAlgebra.algebra) :
      IsFreeGen (MvPolynomial (Fin D) k) (@dWedge k _ _ _ inst D X) := by
    subst e
    have := isFreeGen_ιMulti (KaehlerDifferential.mvPolynomialBasis k (Fin D))
    rwa [funext (KaehlerDifferential.mvPolynomialBasis_apply k (Fin D))] at this
  exact key _ (Algebra.algebra_ext _ _ fun _ => rfl)

end TopForm

namespace ProjSpace

variable (R : Type) [CommRing R] (N : ℕ)

theorem isFrame_dOn_ratio (i : Fin (N + 1)) :
    IsFrame (dOn (PSpace.str R N) fun b : Fin N => ratio R N i (i.succAbove b)) := by
  refine ⟨isAffineOpen_chart R N i, ?_⟩
  let e : MvPolynomial (Fin N) R ≃ₐ[R] Γ(PSpace R N, chart R N i) :=
    (renameEquiv R (finSuccAboveEquiv i)).trans (chartAlgEquiv R N i)
  have he : (e : MvPolynomial (Fin N) R →+* _).comp (algebraMap R _) =
      algX (PSpace.str R N) (chart R N i) := RingHom.ext fun r => e.commutes r
  have := (isFreeGen_dForm_X R N).formMap (RingHom.Etale.of_bijective e.bijective) he
  rw [formMap_dForm] at this
  convert this using 3 with b
  exact ((congrArg (chartAlgEquiv R N i) (rename_X _ b)).trans
    (chartAlgEquiv_X R N i (finSuccAboveEquiv i b))).symm

theorem isUnit_jacSec_coord [SmoothOfRelativeDimension N (PSpace.str R N)]
    (K : CanonLB (PSpace.str R N) N) (c : (K.adj (O1 R N) (N + 1)).ι) :
    IsUnit ((K.jacSec (coord R N)).f c) := by
  refine isUnit_of_affine fun W hW h => ?_
  have l := h.trans (K.adj_U_le _ c)
  have h₂ : W ≤ chart R N (c.2 PUnit.unit) := l.trans inf_le_right
  rw [K.resG_jacSec_f _ c h (l.trans inf_le_left) h₂]
  change IsUnit (K.coeff _ _ (jacOn _ (ratioOn W (c.2 PUnit.unit) h₂)))
  rw [jacOn_of_eq_one _ (c.2 PUnit.unit) (ratioOn_self (hi := h₂)), map_smul, smul_eq_mul]
  refine (isUnit_one.neg.pow _).mul ((K.isUnit_jacobian_iff _ hW _ _).2 ?_)
  have := (isFrame_dOn_ratio R N (c.2 PUnit.unit)).res hW h₂
  rw [resForm_dOn] at this
  exact this

end ProjSpace

end GlobalTheory
