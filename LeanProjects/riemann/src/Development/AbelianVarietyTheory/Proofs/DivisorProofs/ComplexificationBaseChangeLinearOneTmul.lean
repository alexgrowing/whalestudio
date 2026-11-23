import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.DefRead

variable {K : Type} [Field K]

def VC (σ : K →+* ℂ) (W : Type) [AddCommGroup W] [Module K W] : Type :=
  @TensorProduct K _ ℂ W _ _ (σ.toAlgebra.toModule) _

variable (σ : K →+* ℂ) (W : Type) [AddCommGroup W] [Module K W]

instance : AddCommGroup (VC σ W) := @TensorProduct.addCommGroup K _ ℂ W _ _ (σ.toAlgebra.toModule) _

instance : Module ℂ (VC σ W) := by
  letI : Algebra K ℂ := σ.toAlgebra
  exact (TensorProduct.leftModule : Module ℂ (ℂ ⊗[K] W))

instance [FiniteDimensional K W] : FiniteDimensional ℂ (VC σ W) := by
  letI : Algebra K ℂ := σ.toAlgebra
  exact (inferInstance : FiniteDimensional ℂ (ℂ ⊗[K] W))

variable {W}

def bcLin (f : W →ₗ[K] W) : VC σ W →ₗ[ℂ] VC σ W := by
  letI : Algebra K ℂ := σ.toAlgebra
  exact LinearMap.baseChange ℂ f

def tm1 (w : W) : VC σ W := by
  letI : Algebra K ℂ := σ.toAlgebra
  exact (1 : ℂ) ⊗ₜ[K] w

theorem complexificationBaseChangeLinear_one_tmul (f : W →ₗ[K] W) (w : W) : bcLin σ f (tm1 σ w) = tm1 σ (f w) := by
  letI : Algebra K ℂ := σ.toAlgebra
  exact LinearMap.baseChange_tmul (A := ℂ) f 1 w

theorem bcLin_one : bcLin σ (1 : W →ₗ[K] W) = 1 := by
  letI : Algebra K ℂ := σ.toAlgebra
  exact LinearMap.baseChange_id (R := K) (A := ℂ) (M := W)

theorem bcLin_mul (f g : W →ₗ[K] W) : bcLin σ (f * g) = bcLin σ f * bcLin σ g := by
  letI : Algebra K ℂ := σ.toAlgebra
  exact LinearMap.baseChange_comp (A := ℂ) g f

variable {G : Type} [Group G]

def twBC (ρ0 : G →* (W →ₗ[K] W)) (χ : G →* Kˣ) : Representation ℂ G (VC σ W) where
  toFun g := σ (((χ g)⁻¹ : Kˣ) : K) • bcLin σ (ρ0 g)
  map_one' := by simp [bcLin_one]
  map_mul' g h := by
    rw [map_mul, map_mul, bcLin_mul, smul_mul_smul_comm, mul_inv_rev, Units.val_mul, map_mul, mul_comm (σ _)]

theorem twBC_apply (ρ0 : G →* (W →ₗ[K] W)) (χ : G →* Kˣ) (g : G) :
    twBC σ ρ0 χ g = σ (((χ g)⁻¹ : Kˣ) : K) • bcLin σ (ρ0 g) := rfl

end GlobalTheory.DefRead

namespace GlobalTheory.DefRead

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

abbrev VAt (p : PtAt ex Csz) (i : Fin D.R.m) : Type := VC D.what₂.embLL (Fin (p.R.nW i) → D.what₂.LL)

def repAt (p : PtAt ex Csz) (i : Fin D.R.m) : Representation ℂ (G0g D.nd) (VAt p i) :=
  (twBC D.what₂.embLL (p.R.toRealDat.FW i).ρ (p.R.toRealDat.FW i).chi).comp (p.R.eG.trans p.cG).symm.toMonoidHom

theorem repAt_apply (p : PtAt ex Csz) (i : Fin D.R.m) (g : G0g D.nd) :
    repAt p i g = twBC D.what₂.embLL (p.R.toRealDat.FW i).ρ (p.R.toRealDat.FW i).chi ((p.R.eG.trans p.cG).symm g) := rfl

example (p : PtAt ex Csz) (i : Fin D.R.m) : repAt p i 1 = 1 := map_one _

end GlobalTheory.DefRead
