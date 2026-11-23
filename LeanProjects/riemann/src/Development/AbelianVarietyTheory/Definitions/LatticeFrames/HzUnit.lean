import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlaceLaws
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

variable {D : D7} {c : Comm D}

def withMu {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s κ : ℕ} (S : SymData k s κ)
    (μ : ℕ → kˣ →* ℂˣ) (h : ∀ j, IsTame (μ j)) : SymData k s κ := { S with μ := μ, tame := h }

def VCom.withCG (v : VCom c) (a : ℕ → ℂ) : VCom c := { v with cG := a }

def Comm.VolLast (c : Comm D) : Prop :=
  ∀ j (h : j + 2 * 0 + 2 = D.R.m), (c.vol (j + 1)).μ = Measure.map (c.jac j 0 h).d.emb0 (c.x (j + 1)).vol.μ

def IntIn {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k)
    (S : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y) (L : GlobalTheory.FinPl.Lat S) : Prop :=
  ∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((F.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S L (· = q.v)

structure GLoc (v : VCom c) where
  k : Type
  [fld : Field k]
  [val : ValuativeRel k]
  [top : TopologicalSpace k]
  [loc : IsNonarchimedeanLocalField k]
  [mea : MeasurableSpace k]
  [bor : BorelSpace k]
  ν : Measure k
  unitVol : IsUnitVol ν
  q : GlobalTheory.FinPl.SplitPt D k
  unit : q.UnitAA
  s : ℕ
  hs : s + 1 + 1 = D.R.m
  S : SymData k s D.R.k
  char : (ofSplit q).IsChar c.ψ S.ψ
  FX : ∀ j, j ≤ s + 1 → Frame k (c.X j).rank (XIx (Fin D.R.k) (Fin D.R.t) j)
  FT : Frame k c.T.rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2))
  FM : Frame k (c.X (s + 1 + 1)).rank (Ix (Fin D.R.k ⊕ Fin (s + 1)) (Fin D.R.t) (s + 2) ⊕ Unit)
  FY : ∀ j a, j + a = s + 1 → Frame k (c.V j).rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin a)
  sc : ℕ → k
  sc_unit : ∀ j, valuation k (sc j) = 1
  sc_step : ∀ j, sc (j + 1 + 1) = sc j * (ofSplit q).xi
  hz_unit : ∀ j ρ h, valuation k ((ofSplit q).hz (c.B j ρ h)) = 1
  bes : ∀ j ρ h a (ha : j + a = s + 1), (ofSplit q).IsBesFrame (c.B j ρ h) (sc j) (FX j (by omega)) (FY j a ha)
  jac : ∀ j ρ h a (ha : j + 1 + a = s + 1), (ofSplit q).IsJacFrame (c.J j ρ h) (sc j)
    ((ofSplit q).hz (c.B j ρ h)) (FX (j + 1) (by omega)) (FY (j + 1) a ha)
  z₀ : Fin c.Lz.rank → k
  last : FM.β = fromCols ((c.oT (s + 1 + 1) hs).iA.map (ofSplit q).pr * FT.β)
    (Matrix.of fun r _ => ((c.oT (s + 1 + 1) hs).iB.map (ofSplit q).pr *ᵥ z₀) r)
  tau : ∀ h, (v.τ s h).map (ofSplit q).pr *ᵥ z₀ = (-((ofSplit q).xi * sc s)) • fun i => (ofSplit q).pr ((c.bes s 0 h).ζ i)
  latX : ∀ j hj, IntIn q (c.X j) (FX j hj) (c.x j).L
  latM : IntIn q (c.X (s + 1 + 1)) FM (c.x (s + 1 + 1)).L
  latY : ∀ j a ha, IntIn q (c.V j) (FY j a ha) (v.N j)
  latT : IntIn q c.T FT v.NT

  eg : ∀ j, WO (c.V j) (c.V (j + 1)) →₀ ℂ
  eg_is : ∀ j a (H : j + a = s), (ofSplit q).IsCombAt c.ψ (FY j (a + 1) (by omega)) (FY (j + 1) a (by omega)) (eg j)
    ((S.T (Fin D.R.t)).Phi j a H)
  egT : WO (c.V (s + 1)) c.T →₀ ℂ
  egT_is : (ofSplit q).IsCombAt c.ψ (FY (s + 1) 0 rfl) FT egT (S.T (Fin D.R.t)).PhiTop

  cg : ∀ j, WO (c.X j) (c.X (j + 1)) →₀ ℂ
  cg_mid : ∀ j a (H : j + 1 + a = s), (ofSplit q).IsCombAt c.ψ (FX j (by omega)) (FX (j + 1) (by omega)) (cg j)
    ((S.T (Fin D.R.t)).entry S.ψ ν j a H 1 1)
  cg_pen : (ofSplit q).IsCombAt c.ψ (FX s (by omega)) (FX (s + 1) le_rfl) (cg s)
    fun x₀ => (S.T (Fin D.R.t)).Psi 1 x₀ (S.y0 (Fin D.R.t))
  cg_top : (ofSplit q).IsCombAt c.ψ (FX (s + 1) le_rfl) FM (cg (s + 1))
    ((S.T (Fin D.R.t)).xiTop (box _ (1 : kˣ)) S.ψ ν (-1) (Submodule.Quotient.mk (S.y0 (Fin D.R.t))))

attribute [instance] GLoc.fld GLoc.val GLoc.top GLoc.loc GLoc.mea GLoc.bor

variable {v : VCom c}

def GLoc.Mat (G : GLoc v) (j a : ℕ) (ha : j + a = G.s + 1) (g : GA D (c.V j))
    (x : GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin a) G.k) : Prop :=
  (mt (c.V j) g).map G.q.pr = (G.FY j a ha).β * x.val * (G.FY j a ha).γ

structure GPin {n : ℕ} (G : Fin n → GLoc v) : Prop where
  inj : Function.Injective fun i => (G i).q.v
  places : ∀ p, p ∈ v.gP ↔ ∃ i, p = (G i).q.v
  lev : ∀ j, j < D.R.m → ∀ g, g ∈ v.JG j ↔ g ∈ GlobalTheory.FinPl.grpAt (c.V j) (· ∈ v.gP) ∧
    ∀ i a ha x, (G i).Mat j a ha g x → x ∈ (((G i).S.T (Fin D.R.t)).lev j a ha).J
  eG : ∀ j, j + 1 < D.R.m → ∀ f, IsThetaFunO c.ψ _ _ f → comb c.ψ _ _ (v.eG j) f =
    (List.finRange n).foldr (fun i f' => comb c.ψ _ _ ((G i).eg j) f') f
  eGT : ∀ j h, ∃ e : Fin n → WO (c.V (j + 1)) c.T →₀ ℂ, (∀ i, HEq (e i) (G i).egT) ∧
    ∀ f, IsThetaFunO c.ψ _ _ f → comb c.ψ _ _ (v.eGT j h) f = (List.finRange n).foldr (fun i f' => comb c.ψ _ _ (e i) f') f
  dG : ∀ j, j < D.R.m → ∀ f, IsThetaFunO c.ψ _ _ f → comb c.ψ _ _ (v.dG j) f =
    (List.finRange n).foldr (fun i f' => comb c.ψ _ _ ((G i).cg j) f') f

def GLoc.Chars (G : GLoc v) (t : Tup c) : Prop :=
  ∃ μ : ℕ → G.kˣ →* ℂˣ, (∀ j, IsTame (μ j)) ∧ (∀ j (x : G.kˣ), valuation G.k (x : G.k) = 1 → μ j x = G.S.μ j x) ∧
    (∀ j ρ h, (ofSplit G.q).IsComp (t.sBF j ρ h).χV⁻¹ (μ (j + 1)) ∧
      ∃ μ', (ofSplit G.q).IsComp (t.sBF j ρ h).χW μ' ∧ ∀ x : G.kˣ, valuation G.k (x : G.k) = 1 → μ' x * μ (j + 1) x = 1) ∧
    ∀ j σ h, (ofSplit G.q).IsComp (t.sFB j σ h).χV⁻¹ (μ (j + 1 + 1)) ∧
      ∃ μ', (ofSplit G.q).IsComp (t.sFB j σ h).χW μ' ∧ ∀ x : G.kˣ, valuation G.k (x : G.k) = 1 → μ' x * μ (j + 1 + 1) x = 1

def GLam {n : ℕ} (G : Fin n → GLoc v) (j : ℕ) (g : GA D (c.V j)) (a : ℂ) : Prop :=
  ∃ (b : Fin n → ℕ) (hb : ∀ i, j + b i = (G i).s + 1) (x : ∀ i, (((G i).S.T (Fin D.R.t)).lev j (b i) (hb i)).J),
    (∀ i, (G i).Mat j (b i) (hb i) g (x i).1) ∧ a = ∏ i, ((((G i).S.T (Fin D.R.t)).lev j (b i) (hb i)).lam (x i) : ℂ)

end GlobalTheory.SeeSaw

end
