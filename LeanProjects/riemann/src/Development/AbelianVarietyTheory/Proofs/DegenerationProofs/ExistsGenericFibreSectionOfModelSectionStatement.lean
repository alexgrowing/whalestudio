import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenericFibreSectionOfModelSection
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrameUnit
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_genericFibre_section_of_model_section : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (Q : ZHPre ρ M U₀), ∀ (N : M.Z.Opens) (σ : Q.SecFam N) (eta : Sp Ω ⟶ U₀.toScheme), σ ∈ secOn Q.LOne (Q.G.hom ⁻¹ᵁ N) → (N : Set M.Z).Nonempty → eta ≫ U₀.ι = M.pt → ∃ s : LB.Sec (LPow ρ.P.A ρ.P.L 1 (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R))), ∀ (K : Type) [Field K] (β : Ω →+* K) (q : Sp K ⟶ ((Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ⊗ ρ.P.A).left) (g : Sp K ⟶ pullback ρ.P.A.hom Q.u₀) (jP : ρ.P.L.ι) (jL : Q.L.L.ι), q ≫ (fst (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left = spMap β → g ≫ pullback.fst _ _ = q ≫ (snd (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left → g ≫ pullback.snd _ _ = spMap β ≫ eta → Set.range (g ≫ pullback.fst ρ.P.A.hom Q.u₀) ⊆ ρ.P.L.U jP → Set.range (g ≫ Q.φ) ⊆ Q.L.L.U jL → valF q _ (s.f fun _ => jP) = valF g _ (Q.w.s (fun _ => jP, fun _ => jL)).val * valF (g ≫ Q.φ) _ (σ fun _ => jL) := by
  first | exact @GlobalTheory.ZH.GenSec.exists_generic_section | exact GlobalTheory.ZH.GenSec.exists_generic_section | (intros; apply GlobalTheory.ZH.GenSec.exists_generic_section <;> assumption)
