import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
open scoped ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def dimAt (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) : ℝ :=
  ((dimK _ _ (Formalism.L2.NTheta.wtOf D (Wc D i) τ) : ℚ) : ℝ)

def ratio (D : D7) (i : Fin D.R.m) (μ : Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) : ℝ :=
  (μ 𝓕).toReal * ∏ τ, dimAt D i τ

def wtSize (D : D7) (i : Fin D.R.m) : ℝ :=
  ∑ τ, ∑ a, |((Formalism.L2.NTheta.wtOf D (Wc D i) τ a : ℤ) : ℝ) + (((D.hc τ).e i : ℚ) : ℝ)|

def Sizes (D : D7) (L : ℝ) : Prop :=
  (D.R.f : ℝ) * D.R.r * D.R.nV ≤ Real.exp L ∧ (∀ i, wtSize D i ≤ Real.exp L ^ 2) ∧
    Real.log ((D.host.g 0 : ℝ) * D.host.g 1) ≤ 30 * L ∧ Real.log D.host.rdE + |dlogL D 1| ≤ 2 * L

variable {D : D7}

abbrev levW {Tu : Type} (C : LevCh D Tu) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) :
    Subgroup (GL (Fin (Wc D i).rank) (Formalism.IndefR.Lev.EAf D)) :=
  lev D.sp.cm (Wc D i).gram (C.βW i) (C.datWp i P)

abbrev formsW {Tu : Type} (C : LevCh D Tu) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (θ : InfFam D)
    {S : D.what₂.Tau → SPar} (M : DSModel (Wc D i) S) : Submodule ℂ (MMap M) :=
  Mult θ M (levS _ (C.βW i) (C.datWp i P)) (levChi _ (C.βW i) (C.datWp i P))

def expW (D : D7) (i : Fin D.R.m) : WTZ D.host.E := wtZ (wtA (kapTop D i)) (kapTop D i).n

variable (T : CoreJ D) (i : Fin D.R.m)

def scalarForms (s : T.Q.c.F →+* ℂ) : Submodule ℂ (FDSec (T.U ((i : ℕ) + 1) s).X) :=
  holSub (T.U ((i : ℕ) + 1) s).X (modelWt (T.U ((i : ℕ) + 1) s) (expW D i))

def probSq (s : T.Q.c.F →+* ℂ) (f : FDSec (T.U ((i : ℕ) + 1) s).X) : ℝ :=
  (lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (expW D i) *
    (petE (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s) (muQ1 (T.V ((i : ℕ) + 1) s))
      (modelWt (T.U ((i : ℕ) + 1) s) (expW D i)) f).toReal) ^ 2

def adFun {s : T.Q.c.F →+* ℂ} (hV : T.V ((i : ℕ) + 1) s = Wc D i) (f : FDSec (T.U ((i : ℕ) + 1) s).X) :
    GA D (Wc D i) → ℂ :=
  hV ▸ ((lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (expW D i) : ℂ) •
    adel (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s)
      (muPin (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s) (T.mu ((i : ℕ) + 1) s) (T.cE ((i : ℕ) + 1) s)) f)

theorem probSq_rdU (s : T.Q.c.F →+* ℂ) (f : T.R ((i : ℕ) + 1)) :
    probSq T i s (rdU (T.U ((i : ℕ) + 1) s) f) =
      petAt (T.U ((i : ℕ) + 1) s) (xiR D) (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s)
        (muQ1 (T.V ((i : ℕ) + 1) s)) (expW D i) f ^ 2 := rfl

theorem adFun_rdU {s : T.Q.c.F →+* ℂ} (hV : T.V ((i : ℕ) + 1) s = Wc D i) (f : T.R ((i : ℕ) + 1)) :
    adFun T i hV (rdU (T.U ((i : ℕ) + 1) s) f) = phiC T hV (wtA (kapTop D i)) f := by
  unfold adFun phiC CoreJ.phiJ expW
  rw [lieFacZ_wtZ]

variable [Algebra T.Q.c.F D.what₂.LL]

abbrev gd (σ : D.what₂.LL →+* ℂ) : T.Q.c.F →+* ℂ := goodOf T.Q.c (res T σ)

def Corr (σ : D.what₂.LL →+* ℂ) (hV : T.V ((i : ℕ) + 1) (gd T σ) = Wc D i) {M : DSModel (Wc D i) (parAt (Wc D i) σ)}
    (F : MMap M) (f : FDSec (T.U ((i : ℕ) + 1) (gd T σ)).X) : Prop :=
  (GoodEmb T.Q.c (res T σ) ∧ ∃ v, IsExtVec M v ∧ F v = adFun T i hV f) ∨
    (¬ GoodEmb T.Q.c (res T σ) ∧ ∃ v : M.Vec, IsUnitV v ∧ F v = fun g => conj (adFun T i hV f g))

def ExactRatio {Tu : Type} (C : LevCh D Tu) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ)
    (μ : Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) : Prop :=
  ∀ (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL], LawsJ T → AlgTie T → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (σ : D.what₂.LL →+* ℂ) (M : DSModel (Wc D i) (parAt (Wc D i) σ)) (hV : T.V ((i : ℕ) + 1) (gd T σ) = Wc D i),
      ∀ F ∈ formsW C i P θ M, ∀ f ∈ scalarForms T i (gd T σ), Corr T i σ hV F f →
        (∃ c, IsMultIP M μ 𝓕 F F c) ∧ ipAt M μ 𝓕 F F = ((ratio D i μ 𝓕 * probSq T i (gd T σ) f : ℝ) : ℂ)

def RatioBound (i : Fin D.R.m) (μ : Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (L : ℝ) : Prop :=
  (∀ τ, Real.log (dimAt D i τ) ≤ 3 / 2 * (D.R.r : ℝ) ^ 2 * L) ∧
    Real.log (μ 𝓕).toReal ≤ D.R.f * (D.R.r : ℝ) ^ 2 * Real.log ((D.R.r : ℝ) + 3) + (38 + 81) * (D.R.f * (D.R.r : ℝ) ^ 2 * L) ∧
    Real.log (ratio D i μ 𝓕) ≤ 122 * (D.R.f * (D.R.r : ℝ) ^ 2 * L)

def IndexBound {Tu : Type} (C : LevCh D Tu) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) : Prop :=
  (levW C i P).relIndex (levW C i (LevelP.full _ _ _)) ≠ 0 ∧
    Real.log ((levW C i P).relIndex (levW C i (LevelP.full _ _ _))) ≤
      2 * D.R.f * (D.R.r : ℝ) ^ 2 * Real.log ((D.host.g 0 : ℝ) * D.host.g 1)

def OneMeasure (D : D7) : Prop :=
  ∀ (Tu : Type) (C : LevCh D Tu) (t0 : Tu), C.Is t0 → ∀ (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ),
    IndexBound C i P ∧ (∀ τ, 1 ≤ dimAt D i τ) ∧
      ∀ (μ : Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))), IsMeasFD (Wc D i) (levW C i P) μ 𝓕 →
        μ 𝓕 ≠ 0 ∧ μ 𝓕 ≠ ⊤ ∧ ExactRatio C i P μ 𝓕 ∧ ∀ L, Sizes D L → RatioBound i μ 𝓕 L

omit [Algebra T.Q.c.F D.what₂.LL] in

theorem OneMeasure.models (h : OneMeasure D) {G : Type} [Group G] [Fintype G] {Pl0 Tu : Type}
    {A : FamIn D.what₂.LL G Pl0 Tu D.R.m} [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
    (hl : R.toLevCh.Is A.μ0) (hm : R.IsModels) (hT : LawsJ T) (ha : AlgTie T) (large₂ : SizeData₂ D) (hs : Sizes D large₂.sc.L)
    (n : ℝ) (hn : 1 ≤ n) :
    ∃ c : ℝ, 0 < c ∧ Real.log c ≤ 122 * (D.R.f * (D.R.r : ℝ) ^ 2 * large₂.sc.L) ∧
      ∀ (σ : D.what₂.LL →+* ℂ) (hV : T.V ((i : ℕ) + 1) (gd T σ) = Wc D i) (x : (R.HW i σ).H),
        ∀ f ∈ scalarForms T i (gd T σ), Corr T i σ hV ((R.HW i σ).e x) f →
          n⁻¹ * ‖x‖ ^ 2 = c * probSq T i (gd T σ) f := by
  obtain ⟨-, hdim, hmeas⟩ := h Tu R.toLevCh A.μ0 hl i R.toLevCh.triv
  obtain ⟨h0, htop, hex, hbd⟩ := hmeas (R.νW i) (R.fdW i) (hm.νW i)
  have hpos : 0 < ratio D i (R.νW i) (R.fdW i) :=
    mul_pos (ENNReal.toReal_pos h0 htop) (Finset.prod_pos fun τ _ => lt_of_lt_of_le one_pos (hdim τ))
  have hn0 : 0 < n := lt_of_lt_of_le one_pos hn
  obtain ⟨-, -, hb3⟩ := hbd large₂.sc.L hs
  refine ⟨ratio D i (R.νW i) (R.fdW i) / n, div_pos hpos hn0, ?_, ?_⟩
  · exact (Real.log_le_log (div_pos hpos hn0) (div_le_self hpos.le hn)).trans hb3
  · intro σ hV x f hf hcorr
    have hmem : (R.HW i σ).e x ∈ R.Wall i σ := by
      rw [← (hm.HW i σ).2.1]
      exact LinearMap.mem_range_self _ x
    have hip := (hex T hT ha R.θ hm.inf σ (R.MW i σ) hV _ hmem f hf hcorr).2
    have hnorm : ((‖x‖ ^ 2 : ℝ) : ℂ) =
        ((ratio D i (R.νW i) (R.fdW i) * probSq T i (gd T σ) f : ℝ) : ℂ) := by
      rw [← hip, ← (hm.HW i σ).2.2 x x, inner_self_eq_norm_sq_to_K]
      norm_cast
    rw [Complex.ofReal_injective hnorm]
    ring

end GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes
