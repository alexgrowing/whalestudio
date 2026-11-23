import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.GramSchwartzFunctions.BC

open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions

variable {D : D7}

def hermA (D : D7) (r : ℕ) : AddSubgroup (Mx D r r) where
  carrier := {b | adj b = b}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, GlobalTheory.MixModel.adj] at *
    rw [Matrix.map_add _ (map_add _), Matrix.transpose_add, ha, hb]
  zero_mem' := by
    simp only [Set.mem_setOf_eq, GlobalTheory.MixModel.adj]
    rw [Matrix.map_zero _ (map_zero _), Matrix.transpose_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, GlobalTheory.MixModel.adj] at *
    rw [Matrix.map_neg _ (map_neg _), Matrix.transpose_neg, ha]

def ratHerm (D : D7) (r : ℕ) : AddSubgroup (hermA D r) := (ratMx D r r).comap (hermA D r).subtype

def IsCovolOneH {r : ℕ} (lam : Measure (hermA D r)) (𝓕 : Set (hermA D r)) : Prop :=
  lam.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratHerm D r) 𝓕 lam ∧ lam 𝓕 = 1

def Jt (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {r : ℕ} (μ : Measure (Mx D V.rank r)) (φ : Mx D V.rank r → ℂ)
    (b : hermA D r) : ℂ :=
  ∫ y, φ y * ψ (halfTr (Matrix.trace (HMul.hMul b.1 (inner V y y) : Mx D r r))) ∂μ

def W (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {r : ℕ} (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r))
    (φ : Mx D V.rank r → ℂ) (β : HermE D r) : ℂ :=
  ∫ b, Jt ψ V μ φ b * ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) b.1 : Mx D r r))) ∂lam

def gramQ (V : HSp D) {r : ℕ} (x : Matrix (Fin V.rank) (Fin r) D.host.E) : Matrix (Fin r) (Fin r) D.host.E :=
  (x.map (D.sp.cm.sig : D.host.E → D.host.E)).transpose * (HSpace.gram V * x)

def IfrB (V : HSp D) (ν : Measure (GA D V)) {r : ℕ} (φ : Mx D V.rank r → ℂ) (β : HermE D r) : ℂ :=
  ⨍ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (fun h => ∑' x : {x : Matrix (Fin V.rank) (Fin r) D.host.E // x.rank = r ∧ gramQ V x = β.1},
    φ (HMul.hMul (Formalism.L2.Theta.mt V h⁻¹) (x.1.map (incA D)))) q ∂autMeasure V ν

def Hyp (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (μ : Measure (Mx D V.rank r))
    (lam : Measure (hermA D r)) (ν : Measure (GA D V)) (φ : Mx D V.rank r → ℂ) : Prop :=
  2 * r < V.rank ∧ IsCharAF D.host.F ψ ∧ IsInfFam θ ∧ (∃ 𝓕, IsCovolOne (ratMx D V.rank r) μ 𝓕) ∧
    (∃ 𝓖, IsCovolOneH lam 𝓖) ∧ ν.IsHaarMeasure ∧ φ ∈ schwartzA θ V.rank r ∧
    GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤

def PoissonHerm : Prop :=
  ∀ (D : D7) (r : ℕ) (V : HSp D) ψ θ μ lam ν φ, Hyp D r V ψ θ μ lam ν φ →
    Summable (fun b : HermE D r => J ψ V μ φ b) →
    HasSum (fun β : HermE D r => W ψ V μ lam φ β) (∑' b : HermE D r, J ψ V μ φ b)

def SplitGram : Prop :=
  ∀ (D : D7) (r : ℕ) (V : HSp D) (ν : Measure (GA D V)), ν.IsHaarMeasure → ∀ φ : Mx D V.rank r → ℂ,
    GlobalTheory.SiegelFormula.absThetaInt V ν φ < ⊤ →
    HasSum (fun β : HermE D r => IfrB V ν φ β) (Ifr V ν φ)

def SiegelND : Prop :=
  ∀ (D : D7) (r : ℕ) (V : HSp D) ψ θ μ lam ν φ, Hyp D r V ψ θ μ lam ν φ →
    ∀ β : HermE D r, β.1.det ≠ 0 → IfrB V ν φ β = W ψ V μ lam φ β

def SiegelDeg : Prop :=
  ∀ (D : D7) (r : ℕ) (V : HSp D) ψ θ μ lam ν φ, Hyp D r V ψ θ μ lam ν φ →
    ∀ β : HermE D r, β.1.det = 0 → IfrB V ν φ β = W ψ V μ lam φ β

end PositivityTheory.GramSchwartzFunctions.BC
