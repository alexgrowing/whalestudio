import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniTrait
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyHomDescendsAlgClosedCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsPrimitiveRootUnitOnIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SymDescentAlgClosed

theorem hypS_of_baseChange : ∀ (K Ω : Type) [Field K] [IsAlgClosed K] [CharZero K] [Field Ω] (j : K →+* Ω) (A : PolAV (Sp K)) (B : PolAV (Sp Ω)) (b : B.A.left ⟶ A.A.left), IsGrpPullback B.A A.A (spMap j) b → LBIso B.L (A.L.pull b) → (letI := B.isAb.comm; GlobalTheory.ZH.HypS B.A B.L) → (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) := by
  intro K Ω _ _ _ _ j A B b h hb hS
  letI := B.isAb.comm
  letI := A.isAb.comm
  obtain ⟨w, wd, hw, hwd, hs, hp, ha⟩ := hS
  obtain ⟨w₀, -, e⟩ := GlobalTheory.T.abelianVariety_hom_descends_algClosed_charZero K Ω j A.A A.A B.A B.A b b A.isAb A.isAb h h w hw
  obtain ⟨wd₀, -, ed⟩ := GlobalTheory.T.abelianVariety_hom_descends_algClosed_charZero K Ω j A.A A.A B.A B.A b b A.isAb A.isAb h h wd hwd
  exact GlobalTheory.SymLevelDescent.hypS_descend j A.isAb h A.isLB B.isLB hb e ed hw hwd hs hp ha

end GlobalTheory.SymDescentAlgClosed
