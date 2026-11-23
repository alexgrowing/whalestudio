import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalDegreeUpperC
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Development.AbelianVarietyTheory.Definitions.Divisors.RealisedChainTorusEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPartBaseLinksOfPrimitiveRowsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLiftEigenvalueLowerBoundOtherPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftAdjointEigenvalueLowerBoundBaseEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLiftLowerBoundOffBasePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogLiftEigenvalueLowerBoundBasePlaceStatement

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn
namespace GlobalTheory.LowRow

theorem lamLow_of_weak : ConjRatLift5 → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ) (b C CH : ℝ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → R.toRealDat.ExAt → PrimRows3 R F → (∀ i, R.phs i = 1) → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) i) → (∀ j, Sizes D j b) → (∀ j, (F.Zsc (R.toCx3 F).zs).l6m j ≤ lowB D j b) → (∀ j, (R.num F C CH).l6 j ≤ (F.Zsc (R.toCx3 F).zs).l6m j) → AdelC R.toRealDat F.lv2 → PrimeToHost R.toRealDat A3.A.μ0 → ((R.toCx3 F).data F.cr true).L6 (R.num F C CH) := by
  intro hCR D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O s b C CH hOk hsep hC hEx prim hph hstd fw hbar hio hpins hrow0 htie hsz hlow hnum hAd hPH
  obtain ⟨hcore, hok, hlinks⟩ := GlobalTheory.T.splitPart_baseLinks_of_primitiveRows R F s hOk hsep hC hEx prim hph
  have hgal : ∀ i, GalOut R.toRealDat i 1 := fun i =>
    hCR D G Pl0 T0 A3.A T R.toRealDat F.lv2 κ v₀ O 1 (GlobalTheory.Core5.of_core hcore) hstd fw hbar hio prim.unif hpins i (by
      have h1 := htie i prim.unif (hrow0 i)
      simp only [hph] at h1
      simpa using h1)
  have hext : ∀ i σ, ∃ v : (R.toRealDat.MW i σ).Vec, IsExtVec (R.toRealDat.MW i σ) v := fun i σ => ⟨v₀ i σ, (fw.hv₀ i σ).1⟩
  have htop := GlobalTheory.T.liftAdjoint_eigenvalue_lower_bound_base_embedding R.toRealDat F.lv2 s b hAd hcore hok hPH hsz
  have hform := GlobalTheory.T.rationalLift_lowerBound_off_basePlace R.toRealDat F.lv2 s b hAd hgal hcore hok hext prim.unif hlinks hPH hsz
  have h0 := GlobalTheory.T.log_liftEigenvalue_lowerBound_basePlace R F b hC prim.thmA prim.posScal htop hlow
  have h1 := GlobalTheory.T.log_liftEigenvalue_lowerBound_otherPlaces R F b hC hph prim.posScal prim.scalConj hform hlow
  intro j p v
  have hn := hnum j
  by_cases hv : v = A3.A.v0
  · subst hv
    have := h0 j p
    exact le_trans hn this
  · have := h1 j p v hv
    exact le_trans hn this

end GlobalTheory.LowRow
