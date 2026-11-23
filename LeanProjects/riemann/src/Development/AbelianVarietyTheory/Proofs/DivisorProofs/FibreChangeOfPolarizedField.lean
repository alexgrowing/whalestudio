import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsExtBaseChange
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BdFib

open GlobalTheory.SpecialFibreExt

theorem exists_fibAt_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (k k' : Type) [Field k] [Field k'] (f : k →+* k') (x : Sp k ⟶ X) (φ : Fib k) (m : CubeMap φ.G t.G), FibAt t x φ m → ∀ (Q : Out.PolAV (Sp k')) (ψ : Q.A.left ⟶ φ.P.A.left), IsPolFibre f φ.P Q ψ → ∃ (φ' : Fib k') (m' : CubeMap φ'.G t.G) (χ : φ'.G.left ⟶ φ.G.left) (ψ' : φ'.P.A.left ⟶ φ.P.A.left), φ'.P = Q ∧ HEq ψ' ψ ∧ FibAt t (spMap f ≫ x) φ' m' ∧ IsGrpPullback φ'.G φ.G (spMap f) χ ∧ χ ≫ m.F = m'.F ∧ φ'.q.left ≫ ψ' = χ ≫ φ.q.left ∧ Module.finrank ℤ φ'.X = Module.finrank ℤ φ.X := by
  intro E _ _ _ H X t k k' _ _ f x φ m hφ Q ψ hQ
  obtain ⟨h₁, h₂, h₃⟩ := hφ
  obtain ⟨-, gP, hw⟩ := hQ
  have gG := isGrpPullback_pullback φ.G (spMap f)
  obtain ⟨hL, hr, ⟨c', h'⟩, -⟩ := Out.CubePf.cubePull _ _ _ _ (cubeMapOf gG) φ.L φ.cub
  have := φ.i_hom
  obtain ⟨q, i, hq, hi, sq, ker⟩ := exists_ext_baseChange gG gP φ.q φ.i φ.isKernel
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨cB⟩ := (GlobalTheory.firstFiveLaws.1.cube _ Q ⟨Q.L, rig, Q.isLB, hrig⟩ rfl).1
  have hB := TripleModel.isPullCubical_of_lbIso GlobalTheory.globalFns_holds Q.isAb gP cB φ.cubB (LBIso.symm hw)
  have hF : (SpecialFibreExt.comp (cubeMapOf gG) (CubeMap.ofHom φ.q)).F = (CubeMap.ofHom q).F ≫ (cubeMapOf gP).F :=
    sq.w
  have hs : Smooth ((Over.pullback (spMap f)).obj φ.G).hom :=
    MorphismProperty.of_isPullback (P := @Smooth) gG.1 φ.smooth
  refine ⟨{ G := (Over.pullback (spMap f)).obj φ.G, smooth := hs, L := _, cub := c', P := Q, rig := rig
            rig_gen := hrig, cubB := cB, q := q
            q_flat := MorphismProperty.of_isPullback (P := @Flat) sq φ.q_flat
            q_surj := MorphismProperty.of_isPullback (P := @Surjective) sq φ.q_surj
            q_affine := isAffineHom_isStableUnderBaseChange.of_isPullback sq φ.q_affine
            X := φ.X, i := i, i_hom := hi, isKernel := ker
            pull := pullCubCancel _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hF (comp_eqs _ _ _ hF).1 (comp_eqs _ _ _ hF).2 hB
              (pullCubComp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl φ.pull h') },
    SpecialFibreExt.comp (cubeMapOf gG) m, _, ψ, rfl, HEq.rfl,
    ⟨gG.comp h₁, congrArg (spMap f ≫ ·) h₂, pullCubComp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl h₃ h'⟩,
    gG, rfl, sq.w.symm, rfl⟩

end GlobalTheory.BdFib

end
