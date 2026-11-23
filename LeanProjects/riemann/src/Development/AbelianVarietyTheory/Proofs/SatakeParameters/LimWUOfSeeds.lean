import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CuspFormLimitTwoPlaces
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LatticeDataThicknessBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ApartAllEmpty
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgebraicWeightOfAutomorphicDefiniteUnitar
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AutomorphicLevelAwayNonsplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlowUpFibreSemilocal
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL GlobalTheory.CongL

namespace GlobalTheory.CongL

theorem overPl_unique {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (τ : E →+* ℂ)
    {w u : HeightOneSpectrum (𝓞 E)} (hw : OverPl ι τ w) (hu : OverPl ι τ u) : u = w := by
  by_contra hne
  have hI : u.asIdeal ≠ w.asIdeal := fun h => hne (HeightOneSpectrum.ext h)
  have htop : u.asIdeal ⊔ w.asIdeal = ⊤ := Ideal.IsMaximal.coprime_of_ne u.isMaximal w.isMaximal hI
  have h1 : (1 : 𝓞 E) ∈ u.asIdeal ⊔ w.asIdeal := htop ▸ Submodule.mem_top
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp h1
  have hx' := hu x hx
  have hy' := hw y hy
  have hsum : ι.symm (τ ((x : E))) + ι.symm (τ ((y : E))) = 1 := by
    rw [← map_add, ← map_add]
    have : ((x : E) + (y : E)) = 1 := by exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) hxy
    rw [this, map_one, map_one]
  have hle := IsUltrametricDist.norm_add_le_max (ι.symm (τ ((x : E)))) (ι.symm (τ ((y : E))))
  rw [hsum, norm_one] at hle
  exact absurd hle (not_le.mpr (max_lt hx' hy'))

end GlobalTheory.CongL
