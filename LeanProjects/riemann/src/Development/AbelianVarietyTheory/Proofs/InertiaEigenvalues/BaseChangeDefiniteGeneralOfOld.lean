import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeDefiniteOfCmDatumRecLaws
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToralOfIsSphericalLocProd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodToralTwistStable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistRecCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BzfinHolds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EpsilonFactorRecCompatible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneCharpolyTwistSpecial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProductStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsSpehProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasSatakeOfUnrT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspidalOfLocalLanglands
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DivisibleGroupTowerCompatibility
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspReadGIffCuspReadT

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.DefiniteBC GlobalTheory.RecT

namespace GlobalTheory.DefiniteBCGood

section Local

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.SmGL GlobalTheory.LocGL

variable {E : Type} [Field E] [NumberField E]

theorem good_of_isSpehQuot {a d N : ℕ} (h : ∑ _ : Fin d, a = N) {w : HeightOneSpectrum (𝓞 E)} (σ : LocIrr w a)
    (σ' : LocIrr w N) (hd : 1 ≤ d) (hq : IsSpehQuot h σ σ') (hG : Good (GlobalTheory.BCSupport.clsOf σ')) :
    Good (GlobalTheory.BCSupport.clsOf σ) := by
  obtain ⟨q, hq⟩ := hq
  let x := IrrGL.of σ.ρ σ.smooth σ.irred
  let T : ∀ i : Fin d, (twist σ.ρ (detChar (Fin a) (absPow (w.adicCompletion E) (((d : ℂ) - 1) / 2 - (i : ℕ))))).Equiv
      (spehFactor x d i).rep := fun i =>
    (twistEquiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred) _).trans (x.twEquiv _ (isSmoothChar_absPow _))
  let M := multiProdEquiv (stdBlocks (fun _ : Fin d => a) h) T
  have hA : IsSubquotient (GlobalTheory.BCSupport.clsOf σ').rep σ'.ρ :=
    IsSubquotient.of_surjective (IrrGL.equivOf σ'.ρ σ'.smooth σ'.irred).toIntertwiningMap
      (IrrGL.equivOf σ'.ρ σ'.smooth σ'.irred).toLinearEquiv.surjective
  have hB : IsSubquotient σ'.ρ (spehInd h σ) := IsSubquotient.of_surjective q hq
  have hC : IsSubquotient (spehInd h σ) (prodIrr (spehFactor x d) h) :=
    IsSubquotient.of_surjective M.symm.toIntertwiningMap M.symm.toLinearEquiv.surjective
  have hs : IsSubquotient (GlobalTheory.BCSupport.clsOf σ').rep (prodIrr (spehFactor x d) h) := hA.trans (hB.trans hC)
  have h0 := (good_toral_of_isSubquotient_prodIrr _ d (spehFactor x d) (GlobalTheory.BCSupport.clsOf σ') h hs).1 hG ⟨0, hd⟩
  exact (good_nu_iff x _).1 h0

end Local

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}

attribute [local instance] host_isCMField

section Statements

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {A : NAut N}

def GoodSplitU {n : ℕ} (U : Submodule ℂ (UA H.E n → ℂ)) : Prop :=
  ∀ w : PlE H, IsSplitPl H w → ∀ σ : LocIrr w n,
    IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ → Good (GlobalTheory.BCSupport.clsOf σ)

def UnitaryReadG (B : NBC A) (rc : RecMap A) (S : ∀ j, B.AU j → Prop) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ R.m → ∀ π : B.AU j, S j π → ∃ U : Submodule ℂ (UA H.E R.nV → ℂ), IsAutRepU U ∧ GoodSplitU U ∧
    (∀ w : PlE H, IsSplitPl H w → ∀ σ : LocIrr w R.nV,
      IsCompAlong U (locU R.nV w) ((cLoc w).comp (locU R.nV w).subtype) σ.ρ → B.locAU j π w = rc w R.nV σ) ∧
    (∀ w : PlE H, ¬ IsSplitPl H w → B.sphAU j π w →
      ∃ α, IsSatAt U w α ∧ B.satAU j π w = Finset.univ.val.map fun i => (α i : ℂ)) ∧
    ∀ τ : H.E →+* ℂ, ∃ lam, HasWeightAt U τ lam ∧ B.infW j (B.wtAU j π) τ = infOfWeight lam

def BaseChangeDefiniteG (B : NBC A) (S : ∀ j, B.AU j → Prop) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ R.m → ∀ π : B.AU j, S j π → GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeDistinctness.SphericalInert B j π →
    ∃ Pa : List (Part A.CG), GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeDistinctness.IsBaseChange B j π Pa

end Statements

section Proof

variable {A : NAut N}

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end Proof

section Frozen

open Formalism.MainNotions

def BaseChangeDefiniteGood (D : D7) (S : ∀ j, D.nbc.AU j → Prop) : Prop :=
  SphericalInertData.HypEFK D → SphericalInertData.HypCM D → ∀ j, 1 ≤ j → j ≤ D.R.m → 1 ≤ D.R.nV →
    (letI := D.host.cmStar; (D.sp.V j).IsDefinite) →
    ∀ π : D.nbc.AU j, S j π → SphericalInertData.SphInert D.nd D.naut D.nbc j π → ∃ Pa, SphericalInertData.IsBC D.nd D.naut D.nbc j π Pa

end Frozen

section LawsCore

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Formalism.ConjugateSelfDual ReciprocityTheory.Gal

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {ar : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h ar} {rc : IrrGL (w.adicCompletion E) → WD h}

end LawsCore

section LawsSpeh

open GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.NuShift

end LawsSpeh

section SatCore

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Formalism.ConjugateSelfDual ReciprocityTheory.Gal

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {ar : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h ar} {rc : IrrGL (w.adicCompletion E) → WD h}

end SatCore

section RecordLaws

open GlobalTheory.LocGL GlobalTheory.WeilDeligne Formalism.ConjugateSelfDual ReciprocityTheory.Gal

variable {A : NAut N} (T : GlobalTheory.RowTie.WDTie N A)
  {rec : ∀ w : PlE H, IrrGL (w.adicCompletion H.E) → WD (E := H.E) (A := N.plOm.1 w) (w := w) (N.plOm.2 w)}

open GlobalTheory.RecLaws GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands Formalism.ConjugateSelfDual ReciprocityTheory.Gal

end RecordLaws

section Top

open GlobalTheory.LocGL GlobalTheory.WeilDeligne Formalism.ConjugateSelfDual ReciprocityTheory.Gal

end Top

section RecordLawsFam

open GlobalTheory.LocGL GlobalTheory.WeilDeligne Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.SmGL GlobalTheory.LocLanglands GlobalTheory.RecLaws

variable {A : NAut N} (T : GlobalTheory.RowTie.WDTie N A) {rc : GlobalTheory.RecT.RecFam}

end RecordLawsFam

end GlobalTheory.DefiniteBCGood

end
