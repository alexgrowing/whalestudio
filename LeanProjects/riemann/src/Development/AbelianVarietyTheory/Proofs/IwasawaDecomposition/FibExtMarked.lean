import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OneMapRef

variable {D : D7} {S T : HSp D} {r g : ℕ}

def IsSet (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (hr : T.rank = r) (X : Data D.host.E r)
    (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) : Prop :=
  IsStdChar D ψ (-1) ∧ IsInfFam θ ∧ S.gram = 1 ∧ Even S.rank ∧ ModelW T hr X ∧ X.κ0 = -(2 * D.host.xi0) ∧
    (∀ ρ, (eT ρ).1 = tauE D ρ) ∧ IsSympl X bas

abbrev Fam (T : HSp D) : Type := D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ

def negM (T : HSp D) (q : ℕ) : Matrix (Fin T.rank) (Fin T.rank) ℂ :=
  Matrix.diagonal fun a : Fin T.rank => ((-(sgn q (a : ℕ)) : ℝ) : ℂ)

def IsONeg (T : HSp D) (q : ℕ) (Z : Fam T) : Prop := ∀ ρ, (Z ρ)ᴴ * gramAt D T ρ * Z ρ = negM T q

def cartZ (T : HSp D) (q : ℕ) (Z : Fam T) : Fam T := fun ρ => Z ρ * negM T q * (Z ρ)⁻¹

def mvZ (θ : InfFam D) (h : GA D T) (Z : Fam T) : Fam T := fun ρ => compAt θ ρ (Formalism.L2.Theta.mt T h) * Z ρ

def frOf (hr : T.rank = r) {X : Data D.host.E r} (eT : D.what₂.Tau ≃ X.Ψ) (Z : Fam T) : Frame X.Ψ r :=
  fun τ a b => Z (eT.symm τ) (Fin.cast hr.symm a) (Fin.cast hr.symm b)

def rePt (θ : InfFam D) (hr : T.rank = r) {X : Data D.host.E r} (eT : D.what₂.Tau ≃ X.Ψ) (w : WO S T) :
    Ker.WR X S.rank :=
  fun τ k a => compAt θ (eT.symm τ) w (Fin.cast hr.symm a) k

def Zak (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hr : T.rank = r) {X : Data D.host.E r}
    (eT : D.what₂.Tau ≃ X.Ψ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r)
    (φ : TF S.rank g) (f : WO S T → ℂ) : Prop :=
  IsThetaFunO ψ S T f ∧ ∀ w, Ker.IsRealPt w → f w = Ker.thR X bas idx φ x (rePt θ hr eT w)

def finR (S : HSp D) (hr : T.rank = r) (y : Matrix (Fin S.rank) (Fin r) D.host.E) : WO S T :=
  Ker.finW S T (y.submatrix id (Fin.cast hr))

def latW (hr : T.rank = r) (L : Lt D.host.E r) : Lt D.host.E T.rank :=
  L.comap (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr.symm))

def toP (S : HSp D) (hr : T.rank = r) {X : Data D.host.E r} (eT : D.what₂.Tau ≃ X.Ψ) {q0 : ℕ} (hq : X.p0 + q0 = r) :
    MvPolynomial (FVar D T.rank S.rank) ℂ →ₐ[ℂ] Harm.Poly ℂ X.Ψ q0 X.p0 (Fin S.rank) :=
  MvPolynomial.aeval fun v => MvPolynomial.C (((2 / fockScale D v.1 : ℝ) : ℂ)) *
    MvPolynomial.X (eT v.1, (rowIdx hq).symm (Fin.cast hr v.2.1), v.2.2)

def fv (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (q : ℕ) (Z : Fam T) (f : WO S T → ℂ)
    (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) : WO S T → ℂ :=
  pureTensorO ψ θ S T (fun _ => 1) (cartZ T q Z) (fun _ => 1) Z f Q

def ctxOf {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hn : Even S.rank)
    (X' : Data D.host.E T.rank) (m : Ker.Match S T X') {q : ℕ} (hq : X'.p0 + q = T.rank)
    (bas' : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X'.Λ) (idx' : Fin g ≃ X'.Ψ × Fin T.rank) (hs : IsSympl X' bas') : Ker.Ctx S T :=
  ⟨ψ, hψ, θ, hθ, X', m, g, q, hq, bas', idx', hs, hn⟩

section Geo

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H}

def MarkAd (hr : T.rank = r) (l : Level H) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin T.rank → D.host.E)) (h : GA D T)
    (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) : Prop :=
  ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 D.host.E) Dw.La), ∃ w ∈ latGHat T h,
    finVec T (mk a ∘ Fin.cast hr) - (finHom T h).1.mulVec (finVec T (ι a)) = (l.M : ℕ) • w

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

def Matched (c : Coeff l) (σ : c.F →+* ℂ) (X : Data D.host.E r) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) : Prop :=
  (∀ x v j, pv X idx x v j = perFr X x v (relab c σ (e j).1) (e j).2) ∧ ∀ j, rowType X (idx j) = relab c σ (e j).1

abbrev ptC (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) : @FrPt D.host.E _ _ _ H Dw l Xo c ℂ _ σ.toAlgebra :=
  unC (Formalism.L2.PjFree.Unf.ofPj U) k x

def FrConst (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S : HSp D) (hr : T.rank = r)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (f₀ : WO S T → ℂ) (U : Unf Xo c σ r)
    (dict : GA D T → Σ k, Frame (U.X k).Ψ r) (mu : GA D T → ℂ) (Z₀ : Fam T) (cc : U.Comp → ℂ) : Prop :=
  ∀ (h γ : GA D T), γ ∈ GQ T → ∀ (g : ℕ) (eT : D.what₂.Tau ≃ (U.X (dict h).1).Ψ)
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (U.X (dict h).1).Λ) (idx : Fin g ≃ (U.X (dict h).1).Ψ × Fin r) (e : Fin g ≃ Lt1 Dw),
    IsSet ψ θ S T hr (U.X (dict h).1) eT bas → Matched c σ (U.X (dict h).1) idx e →
    (dict h).2 = frOf hr eT (mvZ θ (γ * h) Z₀) → ∀ (hx : (dict h).2 ∈ (U.X (dict h).1).dom),
    letI : Algebra c.F ℂ := σ.toAlgebra
    ∀ (A : AnFib (U.X (dict h).1) bas idx e (dict h).2 (U.X (dict h).1).Λ (ptC U (dict h).1 ⟨(dict h).2, hx⟩))
      (th : (Fin g → ℂ) → ℂ), A.Reads 1 (ptC U (dict h).1 ⟨(dict h).2, hx⟩).s th →
      ∀ w : WO S T, Ker.IsRealPt w →
        om (1, γ * h) f₀ w = cc (dict h).1 * mu h *
          (Ker.gaussR (U.X (dict h).1) bas idx (dict h).2 (Ker.zR (U.X (dict h).1) idx (dict h).2 (rePt θ hr eT w)) *
            ∏ b, th (Ker.zR (U.X (dict h).1) idx (dict h).2 (rePt θ hr eT w) b))

section Field

variable {c' : Coeff l} {hle : c.F ≤ c'.F} [Algebra c.F ℂ] [Algebra c'.F ℂ] (hA : AlgOver c c' hle ℂ) {X : Data D.host.E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r}
  {L : Lt D.host.E r} {y : FrPt Xo c ℂ}

def fibExt (A : AnFib X bas idx e x L y) : AnFib X bas idx e x L (y.ext hle hA) :=
  ⟨A.ex, A.ex_add, A.ex_onto, A.ex_ker, A.ex_lin, A.hol, A.der, A.fr, A.fr_hol, A.fr_ne, A.fr_g, A.fr_0, A.χ, A.χ_norm,
    A.fr_per⟩

end Field

end Geo

section Rec

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

abbrev baseZ {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) :
    Fam (Wc D i) := x0Mat (R.MW i (sg0 D A))

def FrConstAt {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m} {Tp : Type} {tup : Tp → T0}
    (O : OMDat C R i Tp tup) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) : Prop :=
  FrConst R.ψ R.θ (Vc D i) (rank_Wc i) (R.ωP i A.μ0) (R.vacP i) (C.U ((i : ℕ) + 1) O.s0)
    O.dict O.mu (baseZ R i) cc

end Rec

end GlobalTheory.OneMapRef

end
