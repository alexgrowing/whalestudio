import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreeOrthogonalSupportAndSupISpecializes
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSysFFMemFinitePerpProj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.ZHAbLocusNonempty

theorem abLocus_nonempty : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ZH.ArithBase o Ω] (S : ZH.ThetaSys o Ω) (ρ : S.Real) (M : ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (Zh : ZH.ZHOut ρ M U₀ EE), S.Over₀ M U₀ → (abLocus Zh.G).Nonempty := by
  intro o Ω _ _ _ _ S ρ M U₀ EE Zh hO
  obtain ⟨z, hz⟩ := hO.ne
  refine ⟨z, ?_⟩
  rw [Zh.ab]
  show S.TT M z = ⊥
  have hpp := (GlobalTheory.thetaSys_FF_mem_finite_perp_proj o Ω S).2.2.1
  have h1 : S.perp ⊥ = ⊤ := by
    refine top_unique fun a _ h hh => ?_
    rw [AddSubgroup.mem_bot.mp hh]
    simp [ZH.eStd]
  rw [ZH.ThetaSys.TT, ZH.ThetaSys.HH, hO.supI_eq hz, S.supp, ← h1, hpp]

end GlobalTheory.ZHAbLocusNonempty
