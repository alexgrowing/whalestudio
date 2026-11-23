import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Fischer

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate

namespace GlobalTheory.Ker

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D}

structure Match (S T : HSp D) (X : Data D.host.E T.rank) where
  gS : S.gram = 1
  gT : X.Gm = T.gramᵀ

  e : D.what₂.Tau ≃ X.Ψ
  e_emb : ∀ τ, (e τ).1 = ComplexEmbedding.conjugate (tauE D τ)
  ka : X.κ0 = 2 * D.host.xi0

structure Ctx (S T : HSp D) where
  ψ : AddChar (AF D.host.F) ℂ
  std : IsStdChar D ψ (-1)
  θ : InfFam D
  inf : IsInfFam θ
  X : Data D.host.E T.rank
  m : Match S T X
  g : ℕ
  q0 : ℕ
  hr : X.p0 + q0 = T.rank
  bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ
  idx : Fin g ≃ X.Ψ × Fin T.rank
  sympl : IsSympl X bas
  even : Even S.rank

structure IsWeak (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) : Prop where
  om_pres : ∀ p f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (om p f)
  om_heis : ∀ g h w₀ f, IsThetaFunO ψ S T f →
    om (g, h) (heisO ψ S T w₀ f) = heisO ψ S T (actO S T g h w₀) (om (g, h) f)
  om_aut : ∀ γ ∈ GQ S, ∀ γ' ∈ GQ T, ∀ f, IsThetaFunO ψ S T f → om (γ, γ') f 0 = f 0
  om_unit : ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure →
    IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ p f, IsThetaFunO ψ S T f →
      ∫⁻ w in 𝓕, ‖om p f w‖ₑ ^ 2 ∂μ = ∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ

theorem isWeak_of_datum {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (h : IsWeilDatumO ψ S T χS χT om) : IsWeak ψ S T om :=
  ⟨h.om_pres, h.om_heis, h.om_aut, h.om_unit⟩

def ipO (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (f f' : WO S T → ℂ) : ℂ := ∫ w in 𝓕, f w * conj (f' w) ∂μ

def IsRealPt (w : WO S T) : Prop := w.map (finPart D) = 0

def IsFinPt (w : WO S T) : Prop := w.map (infPart D) = 0

def finW (S T : HSp D) (y : Matrix (Fin S.rank) (Fin T.rank) D.host.E) : WO S T :=
  Matrix.of fun a k => (pairA D.host.F 0 1) ⊗ₜ[D.host.F] y k a

def hatA (S T : HSp D) (A : AddSubgroup (Matrix (Fin S.rank) (Fin T.rank) D.host.E)) : AddSubgroup (WO S T) :=
  AddSubgroup.closure {w | ∃ α ∈ intAf D.host.F, ∃ y ∈ A,
    w = Matrix.of fun a k => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] y k a}

abbrev AfE (D : D7) : Type := Af D.host.F ⊗[D.host.F] D.host.E

def fmt (V : HSp D) (g : GA D V) : Matrix (Fin V.rank) (Fin V.rank) (AfE D) := (mt V g).map (finPart D)

def fmtC (V : HSp D) (g : GA D V) : Matrix (Fin V.rank) (Fin V.rank) (AfE D) := (cM (mt V g)).map (finPart D)

def hatV {k : ℕ} (L : Lt D.host.E k) : AddSubgroup (Fin k → AfE D) :=
  latHat D.host.F D.host.E (L : Set (Fin k → D.host.E))

def toAf {k : ℕ} (v : Fin k → D.host.E) : Fin k → AfE D := fun i => (1 : Af D.host.F) ⊗ₜ[D.host.F] v i

def IsMov {k : ℕ} (m : Matrix (Fin k) (Fin k) (AfE D)) (L L' : Lt D.host.E k) : Prop :=
  ∀ u, u ∈ hatV L' ↔ ∃ u₀ ∈ hatV L, u = m *ᵥ u₀

def TrivAt (V : HSp D) (I : Ideal (𝓞 D.host.F)) (g : GA D V) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 D.host.F), I ≤ v.asIdeal → ∀ ε, IsPlaceIdem D v ε →
    ∀ i j, algebraMap (AF D.host.F) (AE D) ε * (mt V g - 1) i j = 0

def TrivOff (V : HSp D) (I : Ideal (𝓞 D.host.F)) (g : GA D V) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 D.host.F), ¬ I ≤ v.asIdeal → ∀ ε, IsPlaceIdem D v ε →
    ∀ i j, algebraMap (AF D.host.F) (AE D) ε * (mt V g - 1) i j = 0

def CongK (V : HSp D) (L : Lt D.host.E V.rank) (M : ℕ) (k : GA D V) : Prop :=
  IsMov (fmt V k) L L ∧ ∀ u ∈ hatV L, ∃ u' ∈ hatV L, fmt V k *ᵥ u - u = M • u'

def IsRatOf (V : HSp D) (ga : GL (Fin V.rank) D.host.E) (γ : GA D V) : Prop :=
  mt V γ = (ga : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (incA D)

def IsAA {k : ℕ} (Λ L : Lt D.host.E k) : Prop :=
  ∀ v, v ∈ Λ ↔ v ∈ AddSubgroup.closure {u | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ t ∈ L, u = a • t}

namespace Ctx

variable (C : Ctx S T)

abbrev Bas (_ : Ctx S T) : Type := D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ

abbrev IsTh (f : WO S T → ℂ) : Prop := IsThetaFunO C.ψ S T f

abbrev rho (w : WO S T) (f : WO S T → ℂ) : WO S T → ℂ := heisO C.ψ S T w f

def realPt (w : WO S T) : WR C.X S.rank := fun σ k a => conj (compAt C.θ (C.m.e.symm σ) w a k)

def zOf (x : Frame C.X.Ψ T.rank) (w : WO S T) : Fin S.rank → Fin C.g → ℂ := zR C.X C.idx x (C.realPt w)

def IsZak (x : Frame C.X.Ψ T.rank) (φ : TF S.rank C.g) (f : WO S T → ℂ) : Prop :=
  C.IsTh f ∧ ∀ w, IsRealPt w → f w = thR C.X C.bas C.idx φ x (C.realPt w)

open Classical in

def Th (x : Frame C.X.Ψ T.rank) (φ : TF S.rank C.g) : WO S T → ℂ :=
  if h : ∃ f, C.IsZak x φ f then h.choose else 0

def IsB (B : C.Bas) : Prop := ∀ τ, (B τ)ᴴ * gramAt D T τ * B τ = sgnM C.X

def sB (B : C.Bas) : C.Bas := fun τ => B τ * sgnM C.X * (B τ)⁻¹

def xB (B : C.Bas) : Frame C.X.Ψ T.rank := fun σ a b => conj (B (C.m.e.symm σ) a b)

def mvB (g : GA D T) (B : C.Bas) : C.Bas := fun τ => compAt C.θ τ (mt T g) * B τ

def IsFock (B : C.Bas) (f : WO S T → ℂ) : Prop :=
  ∀ τ, IsFockVacAt (heisO C.ψ S T) C.θ τ (cplxO 1 (C.sB B τ)) f

def fvec (B : C.Bas) (f : WO S T → ℂ) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ) : WO S T → ℂ :=
  pureTensorO C.ψ C.θ S T (fun _ => 1) (C.sB B) (fun _ => 1) B f Q

def toH : MvPolynomial (FVar D T.rank S.rank) ℂ →ₐ[ℂ] Harm.Poly ℂ C.X.Ψ C.q0 C.X.p0 (Fin S.rank) :=
  MvPolynomial.aeval fun v => MvPolynomial.C (((2 / fockScale D v.1 : ℝ) : ℂ)) *
    MvPolynomial.X (C.m.e v.1, (rowIdx C.hr).symm v.2.1, v.2.2)

def under (Lv : GlobalTheory.SW.Level C.X) : Ideal (𝓞 D.host.F) := Lv.𝔪.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))

def LevK (Lv : GlobalTheory.SW.Level C.X) (k : GA D T) (κ : Lv.J) : Prop :=
  k ∈ GfC T ∧ IsMov (fmt T k) C.X.Λ C.X.Λ ∧
    ∃ κ' : Matrix (Fin T.rank) (Fin T.rank) (𝓞 D.host.E),
      κ'.map (Ideal.Quotient.mk Lv.𝔪) = (κ : GL (Fin T.rank) (𝓞 D.host.E ⧸ Lv.𝔪)) ∧
      ∀ i, fmt T k *ᵥ toAf (Lv.β i) - toAf (∑ j, κ' j i • Lv.β j) ∈ hatV (Lv.𝔪 • C.X.Λ)

def uVec (Lv : GlobalTheory.SW.Level C.X) (hn : T.rank ≤ S.rank) (f' : WO S T → ℂ) : WO S T → ℂ :=
  ∑ᶠ c : tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪) • C.X.Λ) ⧸
      (tens (stdL D.host.E S.rank) ((Ideal.span {2} * conjI Lv.𝔪 * Lv.𝔪) • C.X.Λ)).addSubgroupOf _,
    Lv.dat hn (-(c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E)) •
      C.rho (finW S T (c.out : Matrix (Fin S.rank) (Fin T.rank) D.host.E)) f'

structure IsBase (Lv : GlobalTheory.SW.Level C.X) (B : C.Bas) (f' : WO S T → ℂ) : Prop where
  th : C.IsTh f'
  ne : f' ≠ 0
  fock : C.IsFock B f'
  lat : IsLatVac (heisO C.ψ S T) (hatA S T (tens (stdL D.host.E S.rank) (Lv.sh C.X.Λ))) f'

def IsFam {m : ℕ} (Q : Fin m → MvPolynomial (FVar D T.rank S.rank) ℂ) : Prop :=
  (∃ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ), ∀ j, C.toH (Q j) ∈ Harm.rowHighest ℂ c c') ∧
    InvFam fun j => C.toH (Q j)

end Ctx

end GlobalTheory.Ker

end
