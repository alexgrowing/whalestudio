import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProperRestrictPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteSeparableCompositum

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

theorem good_pullback : Out.GtBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (_ : SABMap t' t f), Good t → Good t' := by
  intro hB E _ _ _ H X X' t t' f m hg
  obtain ⟨hA, hS, hT⟩ := hg
  obtain ⟨cm, cart, base, act, lin⟩ := m
  have hpb := GlobalTheory.AbLocusPull.abLocus_sections_pull X X' f t.G t'.G cm.F t.semi cart
  refine ⟨hpb.1 hA, GlobalTheory.splitFibres_of_isGrpPullback hB X X' f t.G t'.G cm.F cart hS,
    hpb.2 t.PP.L t'.PP.L t.PP.isLB t'.PP.isLB ?_ hT⟩
  obtain ⟨w, hw, -⟩ := lin
  exact ⟨w, hw⟩

end GlobalTheory.Models
