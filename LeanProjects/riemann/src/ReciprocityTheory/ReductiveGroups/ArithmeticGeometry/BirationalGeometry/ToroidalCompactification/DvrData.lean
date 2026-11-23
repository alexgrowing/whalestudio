import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

structure UnramExt (V : Type) [CommRing V] where
  W : Type
  [ring : CommRing W]
  [dom : IsDomain W]
  [dvr : IsDiscreteValuationRing W]
  [alg : Algebra V W]
  fin : Module.Finite V W
  inj : Function.Injective (algebraMap V W)
  unram : Algebra.FormallyUnramified V W
  complete : IsAdicComplete (maximalIdeal W) W

attribute [instance] UnramExt.ring UnramExt.dom UnramExt.dvr UnramExt.alg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

abbrev ValPt.ξ (P : ValPt Y) (W : UnramExt P.V) : Sp W.W ⟶ Y.X := spMap (algebraMap P.V W.W) ≫ P.yt

def DvrDataOver (P : ValPt Y) (W : UnramExt P.V) (t : SAB H (Sp W.W)) : Prop :=
  ∃ Q : PELUnif (maximalIdeal W.W) t, (∀ y, PsiUnitOn Q.D.toPre y (P.ξ W ⁻¹' abLocus Y.t.G)) ∧ Q.TorsionIso

def SplitOver {V : Type} [CommRing V] (W : UnramExt V) (t : SAB H (Sp W.W)) : Prop :=
  ∃ S : SplitExt (Sp (ResidueField W.W)), S.IsGt ((Over.pullback (spMap (residue W.W))).obj t.G)

def DvrDataAt (P : ValPt Y) : Prop :=
  ∃ (W : UnramExt P.V) (t : SAB H (Sp W.W)) (_ : SABMap t Y.t (P.ξ W)), SplitOver W t ∧ DvrDataOver P W t

def SplitsAt (P : ValPt Y) : Prop :=
  ∃ (W : UnramExt P.V) (t : SAB H (Sp W.W)) (_ : SABMap t Y.t (P.ξ W)), SplitOver W t

private theorem comp_apply_point {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (x : A) :
    (f ≫ g) x = g (f x) := rfl

private theorem spMap_comp_xi_eq_spMap_lift_comp_y_comp_j (P : ValPt Y) (W : UnramExt P.V) (lift : P.K' →+* FractionRing W.W)
    (hlift : lift.comp (algebraMap P.V P.K') =
      (algebraMap W.W (FractionRing W.W)).comp (algebraMap P.V W.W)) :
    spMap (algebraMap W.W (FractionRing W.W)) ≫ P.ξ W = spMap lift ≫ P.y ≫ Y.j := by
  rw [← P.ext]
  simp only [ValPt.ξ, spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hlift]

private theorem sp_nonempty_of_field (R : Type) [Field R] : Nonempty (Sp R) :=
  ⟨(⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum R)⟩

private theorem jQ_mem_preimage_abLocus (p : Xo.XF c) :
    Y.jQ p ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
  rw [Y.ab_gen]
  exact Set.mem_range_self _

private theorem exists_lift_fractionRing_comp_algebraMap (P : ValPt Y) (W : UnramExt P.V) :
    ∃ f : P.K' →+* FractionRing W.W, f.comp (algebraMap P.V P.K') =
      (algebraMap W.W (FractionRing W.W)).comp (algebraMap P.V W.W) := by
  haveI := P.frac
  have hinj : Function.Injective
      ((algebraMap W.W (FractionRing W.W)).comp (algebraMap P.V W.W)) := by
    rw [RingHom.coe_comp]
    exact (IsFractionRing.injective W.W (FractionRing W.W)).comp W.inj
  refine ⟨IsFractionRing.lift hinj, RingHom.ext fun x => ?_⟩
  simp only [RingHom.comp_apply, IsFractionRing.lift_algebraMap]

private theorem xi_spMap_eq_pullback_fst_jQ (P : ValPt Y) (W : UnramExt P.V) (lift : P.K' →+* FractionRing W.W)
    (hlift : lift.comp (algebraMap P.V P.K') =
      (algebraMap W.W (FractionRing W.W)).comp (algebraMap P.V W.W))
    (z : Sp (FractionRing W.W)) :
    (P.ξ W) (spMap (algebraMap W.W (FractionRing W.W)) z) =
      pullback.fst Y.s (spMap β) (Y.jQ (P.y (spMap lift z))) := by
  rw [← comp_apply_point, spMap_comp_xi_eq_spMap_lift_comp_y_comp_j P W lift hlift, comp_apply_point, comp_apply_point, Model.j, comp_apply_point]

theorem ValPt.ξ_ab (P : ValPt Y) (W : UnramExt P.V) : (P.ξ W ⁻¹' abLocus Y.t.G).Nonempty := by
  obtain ⟨lift, hlift⟩ := exists_lift_fractionRing_comp_algebraMap P W
  obtain ⟨z⟩ := sp_nonempty_of_field (FractionRing W.W)
  refine ⟨spMap (algebraMap W.W (FractionRing W.W)) z, ?_⟩
  rw [Set.mem_preimage, xi_spMap_eq_pullback_fst_jQ P W lift hlift z]
  exact Set.mem_preimage.mp (jQ_mem_preimage_abLocus (Y := Y) _)

theorem dvrData_of_splitting (h3 : Y.N3) (P : ValPt Y) (hs : SplitsAt P) : DvrDataAt P := by
  obtain ⟨W, t, m, hsp⟩ := hs
  haveI : CharZero P.K' := P.char0
  haveI : CharZero P.V := (algebraMap P.V P.K').charZero
  haveI : CharZero W.W := ⟨fun a b h => by
    apply Nat.cast_injective (R := P.V)
    apply W.inj
    simpa using h⟩
  exact ⟨W, t, m, hsp, h3 W.W inferInstance inferInstance W.complete (P.ξ W) t m (ValPt.ξ_ab P W) hsp⟩

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
