import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiPinnedWithFinIff

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Core.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Dense

variable {V W : HSp D} {S S' : D.what₂.Tau → SPar}

open Classical in

def SepCont (M : DSModel V S) (Λ : SmT M →ₗ[ℂ] ℂ) : Prop :=
  ∀ τ (v : M.Vec), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
    ∀ w : M.sm τ, ℓ w = Λ (PiTensorProduct.tprod ℂ (Function.update v τ w))

def KVecP (M : DSModel V S) (v : M.Vec) : Prop := ∀ τ, IsKFin (M.ε τ) (M.σ τ) (v τ : M.H τ)

def PolStable (θ : InfFam D) (M : DSModel V S) (ω : Om V W) (pt : PolF D W.rank V.rank → (WO V W → ℂ)) : Prop :=
  ∀ τ, (∀ X ∈ lieAt V τ, ∀ P, ∃ P', ∀ z, HasDerivAt (fun t : ℝ => ω (oneP θ V τ X t, 1) (pt P) z) (pt P' z) 0) ∧
    ∃ deg : ℕ → Submodule ℂ (PolF D W.rank V.rank), (∀ n, FiniteDimensional ℂ (deg n)) ∧ (∀ P, ∃ n, P ∈ deg n) ∧
      ∀ k ∈ Formalism.REAL.Kset (M.ε τ), ∀ n, ∀ P ∈ deg n, ∃ P' ∈ deg n,
        pt P' = ω (atTau θ V τ ((M.fr τ)⁻¹ * k * M.fr τ), 1) (pt P)

def ItSpans (M : DSModel V S) (M' : DSModel W S') (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M) : Prop :=
  ∀ v : M.Vec, KVecP M v → PiTensorProduct.tprod ℂ v ∈
    Submodule.span ℂ {x | ∃ (P : PolF D W.rank V.rank) (y : M'.Vec), KVecP M' y ∧ x = It P (PiTensorProduct.tprod ℂ y)}

end Dense

def PropTo {I : Type} (f τ : I → ℂ) : Prop := ∃ a : ℂ, ∀ i, f i = a * τ i

def DenseExt (D : D7) : Prop :=
  ∀ (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (S : D.what₂.Tau → SPar) (M : DSModel B.V S)
    (J : Set (GA D B.V)) (χ : GA D B.V → ℂ) (t : GA D B.V) (I : Type) (τ : I → ℂ) (φ : I → GA D B.A → ℂ)
    (T : I → SmT M →ₗ[ℂ] (GA D B.V → ℂ)), IsInfFam θ → IsStdChar D ψ (-1) → (∀ i, IsContAut B.A (φ i)) →
    (∀ i, T i ∈ MultT θ M J χ) →
    (∀ v : M.Vec, KVecP M v → PropTo (fun i => B.per ψ (φ i) (rTrans t (T i (PiTensorProduct.tprod ℂ v)))) τ) →
    ∀ x : SmT M, PropTo (fun i => B.per ψ (φ i) (rTrans t (T i x))) τ

def TowerSpans (W : Tower D) : Prop :=
  (∀ k, k + 1 < D.R.m → ItSpans (W.MY k) (W.MY (k + 1)) (W.ItY k)) ∧ ItSpans (W.MY (D.R.m - 1)) W.MX W.ItX

section Model

variable (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)

def IdE : Prop := ∀ x : X.B.I.E, HEq (X.ιE x) x

def rowJ : Set (GA D (D.sp.Y 0)) := iotaX X h ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}

def rowChi (k : GA D (D.sp.Y 0)) : ℂ := star (X.chi2 (iotaX X h k).2)

def Matches (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) : Prop :=
  t ∈ GfC (D.sp.Y 0) ∧ ConjLevel t⁻¹ J χ (rowJ X h) (rowChi X h)

def evS (t : GA D (D.sp.Y 0)) (F : GA D (D.sp.Y 0) → ℂ) : X.B.I.GA → ℂ := fun x => F ((iotaX X h).symm x * t)

def ConjVec (θ : InfFam D) {S : D.what₂.Tau → SPar} (M : DSModel (D.sp.Y 0) S) (v₀ : M.Vec) : Prop :=
  ∃ c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ),
    (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) =
      X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) ∧
    ∀ τ, c τ (v₀ τ : M.H τ) = X.B.w (X.pl.symm τ)

def RealSplit (θ : InfFam D) : Prop :=
  (∀ k : GA D (D.sp.Y 0), k ∈ GfC (D.sp.Y 0) ↔ (iotaX X h k).1 = 1) ∧
  (∀ k : GA D (D.sp.Y 0), k ∈ GinfC (D.sp.Y 0) ↔ (iotaX X h k).2 = 1) ∧
  (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), (iotaX X h (atTau θ (D.sp.Y 0) τ g)).2 = 1 ∧
    (∀ v, v ≠ X.pl.symm τ → (iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 v = 1) ∧
    HEq (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ)))
      ((fun Pm : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ => Pm⁻¹ * g * Pm)
        ((Formalism.L2.SG.InstExistsPf.instOf D).P (Formalism.L2.Host.tauPl D τ)))) ∧
  ∀ τ (y : Formalism.REAL.UJ (X.B.I.ε (X.pl.symm τ))), ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ),
    (iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ) = y

def EvalAll (θ : InfFam D) {S : D.what₂.Tau → SPar} (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0)))
    (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (v₀ : M.Vec) : Prop :=
  ∃ j : MultT θ M J χ →ₗ⋆[ℂ] HHX X, Function.Bijective j ∧ ∀ T : MultT θ M J χ,
    (((j T : HHX X) : L2X X) : X.B.I.GA → ℂ) =ᵐ[muX X] fun x => star (evS X h t (T.1 (PiTensorProduct.tprod ℂ v₀)) x)

structure RowFun (f : X.B.I.GA → ℂ) : Prop where
  cont : Continuous f
  bdd : ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C
  left : ∀ γ ∈ X.B.I.GFset, ∀ x, f (γ * x) = f x
  right : ∀ k ∈ X.K2, ∀ x, f (x * (1, k)) = star (X.chi2 k) * f x

structure SBes (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) where
  V₀ : HSp D
  L : HSp D
  d : HypDec (D.sp.Y 0) V₀ D.R.rS
  o : OrthDec V₀ A L
  ζ : Fin L.rank → D.host.E
  line : IsLineVec L ζ
  cpt : CoCpt A
  vA : Vol A
  vN : VolN d
  tieN : ∀ n, n ∈ flagN d ↔ (iotaX X h n).1 ∈ X.NinfU u ∧ (iotaX X h n).2 ∈ X.NfinU u
  tieH : ∀ g, g ∈ (embA d o).range ↔ (iotaX X h g).1 ∈ Hinf X u ∧ (iotaX X h g).2 ∈ Hfin X u
  tieψ : ∀ n ∈ flagN d, star (psiBes ψ d 1 (vecB o ζ) n) = X.psiInfU u (iotaX X h n).1 * X.psiFinU u (iotaX X h n).2

namespace SBes

variable {X h} {u : D.what₂.Word} {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D} (B : SBes X h u ψ A)

abbrev lev : BesLev D D.R.rS := ⟨D.sp.Y 0, B.V₀, A, B.L, B.d, B.o, B.ζ, B.line, B.cpt, B.vA, B.vN⟩

def toH (a : GA D A) : Hinf X u × Hfin X u :=
  (⟨(iotaX X h (embA B.d B.o a)).1, ((B.tieH _).1 ⟨a, rfl⟩).1⟩, ⟨(iotaX X h (embA B.d B.o a)).2, ((B.tieH _).1 ⟨a, rfl⟩).2⟩)

def colForm (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (ξ : X.Vpi u) : GA D A → ℂ := fun a => T ξ (B.toH a)

def PerLaw (Y : Formalism.L2.SG.Full.Full X) : Prop :=
  ∃ c : ℂ, ∀ (T : Cu X u Y.hK) (f : X.B.I.GA → ℂ) (φ : L2X X), RowFun X f → (φ : X.B.I.GA → ℂ) =ᵐ[muX X] f →
    ⟪star φ, PuFun X u Y.hK (Y.Dt u) T⟫_ℂ =
      c * ∫ y, B.lev.per ψ (B.colForm T.1 (X.Wu u y)) (fun g => f (iotaX X h g * (y, X.xu u))) ∂(X.nuQ u)

end SBes

theorem rank_eq (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) : (D.sp.Y 0).rank = X.B.I.n := by
  rw [h]; rfl

def SBes.Adapted {X : HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
    {ψ : AddChar (AF D.host.F) ℂ} (B : SBes X h u ψ (D.sp.X 0)) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) : Prop :=
  ∀ k j, (B.d.i₀ * B.o.iA) k j = X.ιE (X.crd (Formalism.L2.SG.ColDict.qFr wt
    (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) j)) (Fin.cast (rank_eq X h) k))

end Model

section MI

variable {F₀ : ∀ u, Formalism.L2.Forms.Forms0 D u} (S : STrue D F₀) (u : D.what₂.Word) (W : Tower D) (L : Link D u W)

def colOf (x : D.s.Cu u) : Cu S.X u S.Y.hK := (S.hI S.hF).eCu u x

def shift (t : GA D (D.sp.Y 0)) : GA D (D.sp.Y 0) := (iotaX S.X S.inst).symm (1, S.X.xu u) * t

def ThetaIdentityOfMapsAt (t : GA D (D.sp.Y 0)) {A : HSp D} (B : SBes S.X S.inst u W.ψ A) : Prop :=
  ∃ U : (D.mem u).A.Mram →ₗ[ℂ] D.s.Cu u, Function.Injective U ∧
    ∀ (ξ : S.X.Vpi u) (x : SmT (W.MY 0)), ∃ a : ℂ,
      ∀ (φ : (D.mem u).A.Mram) (F : (D.mem u).P.Mt) (T₀ : SmT (W.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ)), W.IsDn (L.eT F) T₀ →
        B.lev.per W.ψ (B.colForm (colOf S u (U φ)).1 ξ) (rTrans (shift S u t) (T₀ x)) =
          a * PhiC (D.mem u).C (D.mem u).A (D.mem u).P φ F

def ThetaVectorCompatibility (v₀ : (W.MY 0).Vec) (t : GA D (D.sp.Y 0)) : Prop :=
  L.RowPinAt S.toSTies S.hF v₀ t ∧
    Matches S.X S.inst (levS (Yc D 0) (W.βY 0) (W.datYt () 0 L.P)) (levChi (Yc D 0) (W.βY 0) (W.datYt () 0 L.P)) t

end MI

open GlobalTheory.Mem GlobalTheory.Mem.Col2 in

def ThetaIdentityOfMapsAll {Bs : Base} {Xp : PreX Bs.toPre} {I : TC Bs Xp} {l : I.Laws} {Z : TC.Later Bs (I.cols l)} (w : World I l Z)
    (u : (I.rec7 l Z).what₂.Word) : Prop :=
  ∃ (W : Tower (I.rec7 l Z)) (L : Link (I.rec7 l Z) u W) (v₀ : (W.MY 0).Vec) (t : GA (I.rec7 l Z) ((I.rec7 l Z).sp.Y 0))
    (B : SBes w.S.X w.S.inst u W.ψ ((I.rec7 l Z).sp.X 0)),
    W.Is ∧ L.TopPin (w.C.forms u) ∧ ThetaVectorCompatibility w.S u W L v₀ t ∧ B.Adapted (w.S.tr u).wt ∧ ThetaIdentityOfMapsAt w.S u W L t B

example {I : Type} (τ : I → ℂ) : PropTo (fun _ => 0) τ := ⟨0, fun _ => by simp⟩

example : ¬ PropTo (fun _ : Unit => (1 : ℂ)) (fun _ => 0) := fun ⟨a, h⟩ => by simpa using h ()

end GlobalTheory.Core.Mi

end
