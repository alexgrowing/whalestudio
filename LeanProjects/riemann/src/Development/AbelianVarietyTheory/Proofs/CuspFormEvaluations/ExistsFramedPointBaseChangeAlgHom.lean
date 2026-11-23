import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDVal
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FrameBaseChangeEigenBasisStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointGeneratorRingBaseChangeStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FramedBaseChange

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem spMap_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'')
    (g : R →+* R') : spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem dualMap_comp_algebraMap {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (dualMap ψ).comp (algebraMap S (DualNumber S)) = (algebraMap T (DualNumber T)).comp ψ := by
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem fstHom_comp_dualMap {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    (TrivSqZeroExt.fstHom T T T).toRingHom.comp (dualMap ψ) =
      ψ.comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem dualMap_epsMul {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (a : S) :
    (dualMap ψ).comp (epsMul a) = (epsMul (ψ a)).comp (dualMap ψ) := by
  ext s <;> simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem isTanAt_pull {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) {x : Sp S ⟶ Xo.X}
    {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsTanAt x v) :
    IsTanAt (spMap ψ ≫ x) (spMap (dualMap ψ) ≫ v) := by
  obtain ⟨h1, h2⟩ := hv
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, h1, ← Category.assoc, spMap_spMap, dualMap_comp_algebraMap, ← spMap_spMap,
      Category.assoc]
  · rw [← Category.assoc, spMap_spMap, fstHom_comp_dualMap, ← spMap_spMap, Category.assoc, h2]
    have e : (Over.homMk (spMap ψ) rfl : Over.mk (spMap ψ ≫ x) ⟶ Over.mk x) ≫
        (1 : Over.mk x ⟶ Xo.univ.t.G) = 1 := by
      simp [Hom.one_def]
    rw [← e, Over.comp_left]
    rfl

theorem isEigAt_pull {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (ψ : S →ₐ[c.F] T)
    (τ : E →+* ℂ) {v : Sp (DualNumber S) ⟶ Xo.univ.t.G.left} (hv : IsEigAt c τ v) :
    IsEigAt c τ (spMap (dualMap ψ.toRingHom) ≫ v) := by
  intro a
  rw [Category.assoc, hv a, ← Category.assoc, spMap_spMap, dualMap_epsMul, ← spMap_spMap,
    Category.assoc]
  congr 3
  exact ψ.commutes _

theorem exists_frMap : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S T : Type) [CommRing S] [Algebra c.F S] [CommRing T]
    [Algebra c.F T] (ψ : S →ₐ[c.F] T) (y : FrPt Xo c S), ∃ z : FrPt Xo c T, FrMap ψ y z := by
  intro hLaws E _ _ _ H Dw l Xo c S T _ _ _ _ ψ y
  let h : ptO Xo (spMap ψ.toRingHom ≫ y.x) ⟶ ptO Xo y.x := Over.homMk (spMap ψ.toRingHom) rfl
  obtain ⟨s', hs'⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.exists_pullSec Xo.univ.t.G Xo.univ.t.PP.L 1 (h ▷ Xo.univ.t.G)
    (whiskerRight_snd _ _) y.s
  refine ⟨
    { x := spMap ψ.toRingHom ≫ y.x
      x_over := by
        rw [Category.assoc, y.x_over]
        unfold sOf
        rw [spMap_spMap, ← RingHom.comp_assoc]
        congr 2
        ext r
        simp
      u := fun τ i => spMap (dualMap ψ.toRingHom) ≫ y.u τ i
      tan := fun τ i => isTanAt_pull ψ.toRingHom (y.tan τ i)
      eig := fun τ i => isEigAt_pull ψ τ (y.eig τ i)
      basis := fun τ w hw he => GlobalTheory.T.existsUnique_isCombAt_baseChange_of_isEigAt E H Dw l Xo c S T ψ y τ w hw he
      s := s'
      gen := GlobalTheory.T.framedPoint_generator_ringBaseChange hLaws E H Dw l Xo c S T ψ.toRingHom y h rfl s' hs' },
    rfl, fun _ _ => rfl, (h ▷ Xo.univ.t.G).left, ?_, ?_, fun i hi => ?_⟩
  · rw [← Over.comp_left, whiskerRight_snd]
  · rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
    rfl
  · exact (hs' i).symm

end GlobalTheory.FramedBaseChange
