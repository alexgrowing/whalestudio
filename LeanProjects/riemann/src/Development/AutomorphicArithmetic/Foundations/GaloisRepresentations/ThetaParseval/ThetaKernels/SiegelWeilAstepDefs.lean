import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.FourierZero
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.AStep
structure Hyps_k : Prop where
  holLead : HolLead
  holT : HolT
  tAll : _root_.PositivityTheory.SiegelWeilFormula.TAll_k
  thetaCoef : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k
  auxEx : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties
  coefEx : _root_.PositivityTheory.SiegelWeilFormula.CoefEx_k
  fockMem : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k
  liftEx : _root_.PositivityTheory.SiegelWeilFormula.LiftEx_k
  locOpEx : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k
  locInst : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k
  gSplit : _root_.PositivityTheory.SiegelWeilFormula.GSplit_k
  polyKFin : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k
  secK : _root_.PositivityTheory.SiegelWeilFormula.SecK_k
  eisWk : _root_.PositivityTheory.SiegelWeilFormula.EisWk_k
  lamBd : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k
  lamSing : _root_.PositivityTheory.SiegelWeilFormula.LamSing_k
  fourierZero : _root_.PositivityTheory.SiegelWeilFormula.FourierZero_k
  unfold : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k
  whitLow : _root_.PositivityTheory.SiegelWeilFormula.WhitLow_k
  vacK : _root_.PositivityTheory.SiegelWeilFormula.VacK_k
  iwaQ : _root_.PositivityTheory.SiegelWeilFormula.IwaQ_k
  cTSplit : _root_.PositivityTheory.SiegelWeilFormula.CTSplit_k
  uEx : _root_.PositivityTheory.SiegelWeilFormula.UEx_k
  fcConj : _root_.PositivityTheory.SiegelWeilFormula.FcConj_k
  orbRes : _root_.PositivityTheory.SiegelWeilFormula.OrbRes_k
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def EData_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (f : d.G → ℂ) (s₁ s₀ : ℂ) (U : Set ℂ) (p : Polynomial ℂ) (Ê : ℂ → d.G → ℂ) (t : ℝ) : Prop :=
  IsOpen U ∧ IsRightDomain U ∧ s₀ ∈ U ∧ p ≠ 0 ∧
    (∀ g, DifferentiableOn ℂ (Ê · g) U) ∧ ContinuousOn (fun y : ℂ × d.G => Ê y.1 y.2) (U ×ˢ Set.univ) ∧
    (∀ z ∈ U, ∀ γ ∈ rat2 σ d.Y, ∀ g, Ê z (γ * g) = Ê z g) ∧
    ∀ z : ℂ, t < z.re → (∀ C : Set d.G, IsCompact C → ∃ u : GlobalTheory.Eis.Cosets (par2 σ d.Y) (rat2 σ d.Y) → ℝ, Summable u ∧
        ∀ g ∈ C, ∀ q, ‖GlobalTheory.Eis.term (par2 σ d.Y) (rat2 σ d.Y) (fun x => ((d.Ht x : ℝ) : ℂ) ^ (z - s₁) * f x) g q‖ ≤ u q) ∧
      ∀ g, Ê z g = p.eval z * d.eis f s₁ z g
def avg_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (uM : (Fin L.n → AE F E) → d.G) (ν : Measure (Fin L.n → AE F E)) (𝓤 : Set (Fin L.n → AE F E))
    (nb : nA σ d.Y d.b → d.G) (lam : Measure (nA σ d.Y d.b)) (𝓖 : Set (nA σ d.Y d.b)) (φ : d.G → ℂ) (T : nF σ d.Y d.b)
    (x : d.G) : ℂ :=
  ∫ u in 𝓤, fc d.B.ψ d.b nb lam 𝓖 φ T (uM u * x) ∂ν
def cOne_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) (f : d.G → ℂ) (s₁ z : ℂ) (nb' : nA σ L.Y L.b → L.sd.G) (lam' : Measure (nA σ L.Y L.b))
    (𝓖' : Set (nA σ L.Y L.b)) (T' : nF σ L.Y L.b) (x : d.G) : ℂ :=
  fc d.B.ψ L.b nb' lam' 𝓖' (GlobalTheory.Eis.cosetSum (par2 σ L.Y) (rat2 σ L.Y) fun g =>
    ((d.Ht (L.j g * x) : ℝ) : ℂ) ^ (z - s₁) * f (L.j g * x)) T' 1
end PositivityTheory.SiegelWeilFormula.AStep
end
end
