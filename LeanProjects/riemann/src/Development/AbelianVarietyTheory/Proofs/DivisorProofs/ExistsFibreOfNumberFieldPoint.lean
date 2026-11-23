import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalPointClosedPointImage
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsExtBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.InteriorFibre

theorem exists_fib_of_polAV {k : Type} [Field k] {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]
    {L : RigLB G} (c : CubicalStr G L) (x : Sp k ⟶ S) (P : Out.PolAV (Sp k)) (θ : P.A.left ⟶ G.left)
    (gp : IsGrpPullback P.A G x θ) (h : LBIso (L.L.pull θ) P.L) :
    ∃ (φ : Fib k) (m : CubeMap φ.G G), IsGrpPullback φ.G G x m.F ∧ m.e = x ∧ m.IsPullCubical φ.cub c := by
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨cB⟩ := (GlobalTheory.firstFiveLaws.1.cube _ P ⟨P.L, rig, P.isLB, hrig⟩ rfl).1
  have hB := TripleModel.isPullCubical_of_lbIso GlobalTheory.globalFns_holds P.isAb gp cB c h.symm
  have hF : (cubeMapOf gp).F = (CubeMap.ofHom (𝟙 P.A)).F ≫ (cubeMapOf gp).F := (Category.id_comp _).symm
  exact ⟨{ G := P.A, smooth := P.isAb.smooth, L := _, cub := cB, P := P, rig := rig
           rig_gen := hrig, cubB := cB, q := 𝟙 _
           q_flat := inferInstanceAs (Flat (𝟙 P.A.left))
           q_surj := inferInstanceAs (Surjective (𝟙 P.A.left))
           q_affine := inferInstanceAs (IsAffineHom (𝟙 P.A.left))
           X := PUnit, i := toUnit _ ≫ η[P.A], i_hom := inferInstance
           isKernel := SelfUnif.isPullback_trivial P.A
           pull := pullCubCancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hF (SpecialFibreExt.comp_eqs _ _ _ hF).1
              (SpecialFibreExt.comp_eqs _ _ _ hF).2 hB hB },
    cubeMapOf gp, gp, rfl, hB⟩

theorem exists_fibAt_of_not_mem_genBd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : Model Xo c (algebraMap (𝓞 c.F) c.F)) (K : Type) [Field K] [NumberField K] (yK : Sp K ⟶ gen Z), yK (IsLocalRing.closedPoint K) ∉ genBd Z → ∃ (φ : Fib K) (m : CubeMap φ.G Z.t.G), FibAt Z.t (yK ≫ genι Z) φ m := by
  intro E _ _ _ H Dw l Xo c Z K _ _ yK hy
  obtain ⟨P, θ, gp, h⟩ := exists_polAV_of_not_mem_genBd Z K yK hy
  exact exists_fib_of_polAV Z.t.cub _ P θ gp h

end GlobalTheory.InteriorFibre
