import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointEigenbasisBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueScaledBaseChangeFibreSectionStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ScaledBaseChangeFibreSectionNonvanishingIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FibreSectionGeneratesOfNowhereZeroStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FibreSectionNowhereZeroOfGeneratesStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames.FramedBaseChange

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem spMap_comp_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'')
    (g : R →+* R') : spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem dualMap_comp_alg {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (dualMap ψ).comp (algebraMap S (DualNumber S)) = (algebraMap T (DualNumber T)).comp ψ := by
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_comp_dualMap {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (TrivSqZeroExt.fstHom T T T).toRingHom.comp (dualMap ψ) = ψ.comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_comp_epsMul {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (a : S) :
    (dualMap ψ).comp (epsMul a) = (epsMul (ψ a)).comp (dualMap ψ) := by
  ext s <;> simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem tan_bc {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) {x : Sp S ⟶ Xo.X}
    {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) :
    IsTanAt (spMap ψ ≫ x) (spMap (dualMap ψ) ≫ v) := by
  obtain ⟨h1, h2⟩ := hv
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h1, ← Category.assoc, spMap_comp_spMap, dualMap_comp_alg, ← spMap_comp_spMap,
      Category.assoc]
  · rw [← Category.assoc, spMap_comp_spMap, fst_comp_dualMap, ← spMap_comp_spMap, Category.assoc, h2]
    have e : (Over.homMk (spMap ψ) rfl : Over.mk (spMap ψ ≫ x) ⟶ Over.mk x) ≫ (1 : Over.mk x ⟶ Xo.univ.t.G) = 1 := by
      simp [Hom.one_def]
    rw [← e, Over.comp_left]
    rfl

theorem eig_bc {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    (τ : E →+* ℂ) {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsEigAt c τ v) :
    IsEigAt c τ (spMap (dualMap ψ.toRingHom) ≫ v) := by
  intro a
  rw [Category.assoc, hv a, ← Category.assoc, spMap_comp_spMap, dualMap_comp_epsMul, ← spMap_comp_spMap,
    Category.assoc]
  congr 3
  exact ψ.commutes _

theorem exists_frMap : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S), ∃ z : FrPt Xo c T, FrMap φ y z := by
  intro hB E _ _ _ H Dw l Xo c S _ _ T _ _ φ y
  obtain ⟨s', hs', -⟩ := GlobalTheory.T.existsUnique_scaledBaseChange_fibreSection E H Dw l Xo S T φ.toRingHom 1 y.x (spMap φ.toRingHom ≫ y.x) rfl y.s
  have hnz : SecNZ y.x y.s := GlobalTheory.T.fibreSectionNowhereZero_of_generates hB E H Dw l Xo S y.x y.s y.gen
  have hnz' : SecNZ (spMap φ.toRingHom ≫ y.x) s' := fun p' =>
    (GlobalTheory.Frames.secBC_nonvanishing_iff E H Dw l Xo S T φ.toRingHom y.x _ rfl y.s s' hs' p').2 (hnz _)
  have hgen : SecGen (spMap φ.toRingHom ≫ y.x) s' := GlobalTheory.T.fibreSectionGenerates_of_nowhereZero hB E H Dw l Xo T _ s' hnz'
  refine ⟨{ x := spMap φ.toRingHom ≫ y.x
            x_over := ?_
            u := fun τ i => spMap (dualMap φ.toRingHom) ≫ y.u τ i
            tan := fun τ i => tan_bc φ.toRingHom (y.tan τ i)
            eig := fun τ i => eig_bc φ τ (y.eig τ i)
            basis := fun τ w hw he => GlobalTheory.T.framedPoint_eigenbasis_baseChange E H Dw l Xo c S T φ y τ w hw he
            s := s'
            gen := hgen }, rfl, fun _ _ => rfl, ?_⟩
  · rw [Category.assoc, y.x_over]
    unfold sOf
    rw [spMap_comp_spMap, ← RingHom.comp_assoc]
    congr 2
    ext r
    simp
  · obtain ⟨pm, h1, h2, h3⟩ := hs'
    refine ⟨pm, h1, h2, fun i h => ?_⟩
    have h4 := h3 i h
    have h5 : scal y.x (1 : S) i = 1 := by
      unfold scal
      rw [map_one]
      simp [Out.liftFun]
    rw [h5, _root_.one_mul] at h4
    exact h4

end GlobalTheory.Frames.FramedBaseChange
