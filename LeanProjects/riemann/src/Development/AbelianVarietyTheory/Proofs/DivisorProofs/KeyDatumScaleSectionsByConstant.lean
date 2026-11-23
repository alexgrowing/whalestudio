import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyDatumFibreOfComposableBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusOfUnit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyEven

theorem appLE_constFn {K : Type} [CommRing K] {X Y : Scheme.{0}} (p : X ⟶ Sp K) (q : Y ⟶ Sp K) (φ : X ⟶ Y)
    (hw : φ ≫ q = p) (V : Y.Opens) (W : X.Opens) (h : W ≤ φ ⁻¹ᵁ V) (a : K) :
    (φ.appLE V W h).hom (constFn q V a) = constFn p W a := by
  subst hw
  unfold constFn
  rw [← CommRingCat.comp_apply]
  congr 2
  exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _

theorem resG_constFn {K : Type} [CommRing K] {X : Scheme.{0}} (p : X ⟶ Sp K) {U V : X.Opens} (h : V ≤ U) (a : K) :
    resG X h (constFn p U a) = constFn p V a := by
  unfold constFn resG
  rw [← CommRingCat.comp_apply]
  congr 2
  exact Scheme.Hom.appLE_map _ _ _

theorem keyOn_scale (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ σ' : L.L.Sec)
    (x : KeyIn K) (y : Fin x.P.g → (epsR K ⟶ G)) (a : K) (th : x.P.L.Sec)
    (hth : ∀ s : Sp K, ∃ z : x.P.A.left, x.P.A.hom z = s ∧ z ∈ nonzeroLocus th)
    (hth' : ∀ i, th.f i = constFn x.P.A.hom _ a * x.th.f i) (hσ : ∀ i, σ'.f i = constFn G.hom _ a * σ.f i)
    (hK : KeyOn (RingHom.id K) x G L σ y) :
    KeyOn (RingHom.id K) ⟨x.P, x.g_pos, x.rig, x.rig_gen, th, hth, x.v, x.basis⟩ G L σ' y := by
  obtain ⟨φ, he, ψ, F, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := hK
  have hw : φ ≫ G.hom = x.P.A.hom := by
    rw [h₁.1.w, show spMap (RingHom.id K) = 𝟙 (Sp K) from Spec.map_id _, Category.comp_id]
  refine ⟨φ, he, ψ, F, h₁, h₂, h₃, fun j i h => ?_, h₅, h₆, h₇⟩
  show (φ.appLE _ _ h).hom (σ'.f (j PUnit.unit)) = _ * resG _ inf_le_right (th.f i)
  rw [hσ, hth', map_mul, map_mul, h₄ j i h, appLE_constFn x.P.A.hom G.hom φ hw, resG_constFn, mul_left_comm]

end GlobalTheory.KeyEven

end
