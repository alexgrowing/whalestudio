import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen
variable {D : D7}

def realPt (θ : InfFam D) {m n : ℕ} (z : D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ) : Mx D m n :=
  Classical.epsilon fun w : Mx D m n => w.map (finPart D) = 0 ∧ ∀ τ, compAt θ τ w = z τ

variable (θ : InfFam D) (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ)

def xiN (f : WO S T → ℂ) (z : VCx D.what₂.Tau a b) : ℂ :=
  Complex.exp ((Real.pi : ℂ) / 2 * HV sc z z) *
    f (realPt θ fun τ => Matrix.of fun i j => -(δ⁻¹ * z τ (Fin.cast hT i) (Fin.cast hS j)))

def toHom (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : (Fin a → D.host.E) →ₗ[D.host.E] (Fin b → D.host.E) :=
  Matrix.toLin' (γ.reindex (finCongr hT) (finCongr hS))

def jetP (s : ℂ) (G : VCx D.what₂.Tau a b → ℂ) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) : ℂ :=
  ∑ k ∈ P.support, P.coeff k * jetC (fun _ => s) G (k.mapDomain fun v => (v.1, Fin.cast hT v.2.1, Fin.cast hS v.2.2))

def latFr (V : HSp D) {n : ℕ} (hn : V.rank = n) (N : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin V.rank → D.host.E) :=
  {x | (fun i => x (Fin.cast hn.symm i)) ∈ N}

def Moves (V : HSp D) {n : ℕ} (hn : V.rank = n) (g : GA D V) (N : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Prop :=
  ∀ x : Fin n → D.host.E, x ∈ N ↔ ∀ i, (finM V hn g⁻¹ *ᵥ fun j => eToEAf D (x j)) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E

structure StdPair (ψ : AddChar (AF D.host.F) ℂ) : Prop where
  std : IsStdChar D ψ (-1)
  inf : IsInfFam θ
  gS : S.gram = 1
  gT : T.gram = 1
  sigS : S.SigOK
  sigT : T.SigOK
  rk : 0 < S.rank ∧ S.rank < T.rank ∧ Even S.rank ∧ Even T.rank
  cc : D.host.ccK = ⊤
  ne : δ ≠ 0
  xi : ∀ τ, tauE D τ D.host.xi0 = Complex.I * ((Real.sqrt D.host.d)⁻¹ : ℝ)
  scale : sc * ‖δ‖ ^ 2 = 2 * (Real.sqrt D.host.d)⁻¹

def IsHol (ψ : AddChar (AF D.host.F) ℂ) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) f

def splitPart (V : HSp D) : Subgroup (GA D V) := Subgroup.closure {g | ∃ e, IsSplitIdem D e ∧ SuppAt e V g}

def IsRatFin (V : HSp D) (g : GA D V) : Prop := g ∈ GfC V ∧ ∃ γ ∈ GQ V, finHom V γ = finHom V g

end Gen

section World
variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {Ch : ℕ → Type}
  (A : ColDat I l Z u Ch) (θ : InfFam (I.rec7 l Z)) (i : ℕ) (hi : i + 1 ≤ B.R.m)

abbrev ColDat.xiS (f : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ) : VCx (I.rec7 l Z).what₂.Tau (B.R.N i) (B.R.N (i + 1)) → ℂ :=
  xiN θ _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) I.A.δ I.A.sc f

def ColDat.MoveAt (c₀ : ℂ) (g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)) (h : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X (i + 1))) : Prop :=
  ∀ N N', Moves _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) g N → Moves _ (rankN (I.rec7 l Z) (i + 1) hi) h N' →
    ∀ x y, IsDetRoot _ g x → IsDetRoot _ h y →
      ColDat.xiS θ i hi (A.om i (g, h) (A.vac i)) = fun z =>
        c₀ * (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) * I.J.V.thMoved (B.R.N i) (B.R.N (i + 1)) N N' z

def ColDat.VacMove : Prop := ∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∀ g ∈ GfC _, ∀ h ∈ GfC _, A.MoveAt θ i hi c₀ g h

end World

end GlobalTheory.AdForm
