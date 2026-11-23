import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GlobalSchurBounds.Chosen

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions

namespace FamP

variable {eps : ℝ} (Fm : FamP eps)

def CkLow : ℝ := Fm.PK.getD 0 0
theorem params_CkLow (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : (Fm.params x hx i).CkLow = Fm.CkLow := by
  unfold CkLow; rw [← Fm.params_K x hx i]; rfl
def Ck6 : ℝ := Fm.PK.getD 1 0
theorem params_sixth_constant (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : (Fm.params x hx i).Ck6 = Fm.Ck6 := by
  unfold Ck6; rw [← Fm.params_K x hx i]; rfl
def CfL : ℝ := Fm.PK.getD 2 0
theorem params_CfL (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : (Fm.params x hx i).CfL = Fm.CfL := by
  unfold CfL; rw [← Fm.params_K x hx i]; rfl
def cLL : ℝ := Fm.PK.getD 3 0
theorem params_cLL (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : (Fm.params x hx i).cLL = Fm.cLL := by
  unfold cLL; rw [← Fm.params_K x hx i]; rfl
def CnW : ℝ := Fm.PK.getD 4 0
theorem params_CnW (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : (Fm.params x hx i).CnW = Fm.CnW := by
  unfold CnW; rw [← Fm.params_K x hx i]; rfl
def Crho : ℝ := Fm.PK.getD 5 0
theorem params_Crho (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : (Fm.params x hx i).Crho = Fm.Crho := by
  unfold Crho; rw [← Fm.params_K x hx i]; rfl
def CDelG : ℝ := Fm.PK.getD 6 0
theorem params_CDelG (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : (Fm.params x hx i).CDelG = Fm.CDelG := by
  unfold CDelG; rw [← Fm.params_K x hx i]; rfl
def CLw : ℝ := Fm.PK.getD 7 0
theorem params_CLw (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : (Fm.params x hx i).CLw = Fm.CLw := by
  unfold CLw; rw [← Fm.params_K x hx i]; rfl
def Cj0 : ℝ := Fm.PK.getD 8 0
theorem params_lift_constant (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : (Fm.params x hx i).Cj0 = Fm.Cj0 := by
  unfold Cj0; rw [← Fm.params_K x hx i]; rfl
def Cw : ℝ := Fm.PK.getD 9 0
theorem params_Cw (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : (Fm.params x hx i).Cw = Fm.Cw := by
  unfold Cw; rw [← Fm.params_K x hx i]; rfl
def cw : ℝ := Fm.PK.getD 10 0
theorem params_cw (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : (Fm.params x hx i).cw = Fm.cw := by
  unfold cw; rw [← Fm.params_K x hx i]; rfl
def CDel : ℝ := Fm.PK.getD 11 0
theorem params_CDel (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : (Fm.params x hx i).CDel = Fm.CDel := by
  unfold CDel; rw [← Fm.params_K x hx i]; rfl
def CCount : ℝ := Fm.PK.getD 12 0
theorem params_CCount (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : (Fm.params x hx i).CCount = Fm.CCount := by
  unfold CCount; rw [← Fm.params_K x hx i]; rfl
def Ch0r : ℝ := Fm.PK.getD 13 0
theorem params_height_rank_constant (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : (Fm.params x hx i).Ch0r = Fm.Ch0r := by
  unfold Ch0r; rw [← Fm.params_K x hx i]; rfl
def Ch0k : ℝ := Fm.PK.getD 14 0
theorem params_height_k_constant (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : (Fm.params x hx i).Ch0k = Fm.Ch0k := by
  unfold Ch0k; rw [← Fm.params_K x hx i]; rfl
def Ch0N : ℝ := Fm.PK.getD 15 0
theorem params_Ch0N (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : (Fm.params x hx i).Ch0N = Fm.Ch0N := by
  unfold Ch0N; rw [← Fm.params_K x hx i]; rfl
def Cgap : ℝ := Fm.PK.getD 16 0
theorem params_Cgap (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : (Fm.params x hx i).Cgap = Fm.Cgap := by
  unfold Cgap; rw [← Fm.params_K x hx i]; rfl
def CetaF : ℝ := Fm.PK.getD 17 0
theorem params_CetaF (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : (Fm.params x hx i).CetaF = Fm.CetaF := by
  unfold CetaF; rw [← Fm.params_K x hx i]; rfl
def CY : ℝ := Fm.PK.getD 18 0
theorem params_CY (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : (Fm.params x hx i).CY = Fm.CY := by
  unfold CY; rw [← Fm.params_K x hx i]; rfl
def CYL : ℝ := Fm.PK.getD 19 0
theorem params_CYL (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : (Fm.params x hx i).CYL = Fm.CYL := by
  unfold CYL; rw [← Fm.params_K x hx i]; rfl
def Cpde : ℝ := Fm.PK.getD 20 0
theorem params_Cpde (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : (Fm.params x hx i).Cpde = Fm.Cpde := by
  unfold Cpde; rw [← Fm.params_K x hx i]; rfl
def CccK : ℝ := Fm.PK.getD 21 0
theorem params_CccK (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : (Fm.params x hx i).CccK = Fm.CccK := by
  unfold CccK; rw [← Fm.params_K x hx i]; rfl

def CF : ℝ := Fm.PK.getD 22 0
theorem params_CF (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : (Fm.params x hx i).CF = Fm.CF := by
  unfold CF; rw [← Fm.params_K x hx i]; rfl
def CP : ℝ := Fm.PT.getD 0 0
theorem parT_CP (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : (Fm.parT x hx i).CP = Fm.CP := by
  unfold CP; rw [← Fm.parT_K x hx i]; rfl
def eP : ℝ := Fm.PT.getD 1 0
theorem parT_eP (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : (Fm.parT x hx i).eP = Fm.eP := by
  unfold eP; rw [← Fm.parT_K x hx i]; rfl
def Cp : ℝ := Fm.PT.getD 2 0
theorem parT_Cp (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : (Fm.parT x hx i).Cp = Fm.Cp := by
  unfold Cp; rw [← Fm.parT_K x hx i]; rfl
def Cb : ℝ := Fm.PT.getD 3 0
theorem parT_Cb (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : (Fm.parT x hx i).Cb = Fm.Cb := by
  unfold Cb; rw [← Fm.parT_K x hx i]; rfl
def cTO : ℝ := Fm.PT.getD 4 0
theorem parT_cTO (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : (Fm.parT x hx i).cTO = Fm.cTO := by
  unfold cTO; rw [← Fm.parT_K x hx i]; rfl
def ChT : ℝ := Fm.PT.getD 5 0
theorem parT_ChT (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : (Fm.parT x hx i).ChT = Fm.ChT := by
  unfold ChT; rw [← Fm.parT_K x hx i]; rfl
def CbN : ℝ := Fm.PT.getD 6 0
theorem parT_CbN (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) : (Fm.parT x hx i).CbN = Fm.CbN := by
  unfold CbN; rw [← Fm.parT_K x hx i]; rfl

def cPre : List ℝ := [Fm.CP]

def cOut : List ℝ := [Fm.Ct, Fm.Cc, Fm.CT2, Fm.CLw, Fm.Cj0, Fm.cw, Fm.CYL, Fm.Cpde, Fm.CccK,
  Fm.CP, Fm.Cp, Fm.eP, Fm.cTO, Fm.CTu, Fm.CetaF, max Fm.Co Fm.J]

def cMid (CH : ℝ) : List ℝ := [CH, Fm.CGam, Fm.Csz, Fm.Csz, Fm.Csz, Fm.Csz, Fm.Csz, Fm.cX.err.g,
  Fm.GK.La, Fm.CF]

def cLast : List ℝ := [Fm.CkLow, Fm.Ck6, Fm.CfL, Fm.cLL⁻¹, Fm.Crho, Fm.Crho, Fm.CDelG, Fm.Cw, Fm.CDel,
  Fm.CCount, Fm.Ch0r, Fm.Ch0k, Fm.Ch0N, Fm.Cgap, Fm.CY, Fm.Cb, Fm.ChT, Fm.CbN,
  Fm.GK.rho, Fm.GK.kII, Fm.GK.tII, Fm.GK.DII, Fm.GK.szII, Fm.GK.kII', Fm.GK.DI, Fm.GK.kappaThresholdOne,
  Fm.GK.kappaThresholdTwo, Fm.GK.kI, Fm.GK.CN, Fm.GK.CN, Fm.GK.CN, Fm.GK.CN]

example := @cPre.eq_1
example := @cOut.eq_1
example := @cMid.eq_1
example := @cLast.eq_1

end FamP

structure TransportedAlt where
  pre : ℝ
  t : List ℝ → ℝ
  mid : List ℝ → ℝ
  last : List ℝ → ℝ

def TransportedAlt.le (K K' : TransportedAlt) : Prop :=
  K.pre ≤ K'.pre ∧ (∀ l, K.t l ≤ K'.t l) ∧ (∀ l, K.mid l ≤ K'.mid l) ∧ ∀ l, K.last l ≤ K'.last l

def TransportedAlt.sup (K K' : TransportedAlt) : TransportedAlt :=
  ⟨max K.pre K'.pre, fun l => max (K.t l) (K'.t l), fun l => max (K.mid l) (K'.mid l), fun l => max (K.last l) (K'.last l)⟩

def FamP.Large {eps : ℝ} (Fm : FamP eps) (K : TransportedAlt) (CH : ℝ) : Prop :=
  (∀ c ∈ Fm.cPre, K.pre ≤ c) ∧ True ∧ (∀ c ∈ Fm.cMid CH, K.mid Fm.cOut ≤ c) ∧
    ∀ c ∈ Fm.cLast, K.last (Fm.cOut ++ Fm.cMid CH) ≤ c

theorem FamP.Large.mono {eps : ℝ} {Fm : FamP eps} {K K' : TransportedAlt} {CH : ℝ} (h : Fm.Large K' CH) (hK : K.le K') :
    Fm.Large K CH :=
  ⟨fun c hc => hK.1.trans (h.1 c hc), trivial, fun c hc => (hK.2.2.1 _).trans (h.2.2.1 c hc),
    fun c hc => (hK.2.2.2 _).trans (h.2.2.2 c hc)⟩

theorem FamP.large_sup {eps : ℝ} (Fm : FamP eps) (K K' : TransportedAlt) (CH : ℝ) :
    Fm.Large (K.sup K') CH ↔ Fm.Large K CH ∧ Fm.Large K' CH := by
  constructor
  · intro h
    exact ⟨h.mono ⟨le_max_left _ _, fun _ => le_max_left _ _, fun _ => le_max_left _ _, fun _ => le_max_left _ _⟩,
      h.mono ⟨le_max_right _ _, fun _ => le_max_right _ _, fun _ => le_max_right _ _, fun _ => le_max_right _ _⟩⟩
  · rintro ⟨h, h'⟩
    exact ⟨fun c hc => max_le (h.1 c hc) (h'.1 c hc), trivial,
      fun c hc => max_le (h.2.2.1 c hc) (h'.2.2.1 c hc), fun c hc => max_le (h.2.2.2 c hc) (h'.2.2.2 c hc)⟩

abbrev FamClass : Type 1 := ∀ {eps : ℝ}, FamP eps → Prop

def Closed (𝒞 : FamClass) (P : ∀ {eps : ℝ}, FamP eps → ℝ → Prop) : Prop :=
  ∃ ε1 : ℝ, 0 < ε1 ∧ ∀ eps : ℝ, 0 < eps → eps ≤ ε1 → ∃ K : TransportedAlt, ∀ (Fm : FamP eps) (CH : ℝ),
    𝒞 Fm → Fm.Large K CH → P Fm CH

theorem Closed.and {𝒞 : FamClass} {P Q : ∀ {eps : ℝ}, FamP eps → ℝ → Prop} (hP : Closed 𝒞 P) (hQ : Closed 𝒞 Q) :
    Closed 𝒞 (fun Fm CH => P Fm CH ∧ Q Fm CH) := by
  obtain ⟨a, ha, hP⟩ := hP
  obtain ⟨b, hb, hQ⟩ := hQ
  refine ⟨min a b, lt_min ha hb, fun e he hle => ?_⟩
  obtain ⟨K, hK⟩ := hP e he (hle.trans (min_le_left _ _))
  obtain ⟨K', hK'⟩ := hQ e he (hle.trans (min_le_right _ _))
  exact ⟨K.sup K', fun Fm CH hc h =>
    ⟨hK Fm CH hc ((Fm.large_sup K K' CH).1 h).1, hK' Fm CH hc ((Fm.large_sup K K' CH).1 h).2⟩⟩

theorem Closed.imp {𝒞 : FamClass} {P Q : ∀ {eps : ℝ}, FamP eps → ℝ → Prop} (hP : Closed 𝒞 P)
    (h : ∀ {eps : ℝ} (Fm : FamP eps) (CH : ℝ), 0 < eps → P Fm CH → Q Fm CH) : Closed 𝒞 Q := by
  obtain ⟨a, ha, hP⟩ := hP
  refine ⟨a, ha, fun e he hle => ?_⟩
  obtain ⟨K, hK⟩ := hP e he hle
  exact ⟨K, fun Fm CH hc hL => h Fm CH he (hK Fm CH hc hL)⟩

def TuSize {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.L x i).TuGe ∧
    ∀ u, Real.log (((Fm.D x i).mem u).A.T : ℝ) ≤ Fm.CTu * (Fm.D x i).R.m * (Fm.L x i).sc.L

def DGamSize {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, FactDGam (Fm.D x i) C

def DesignExists (𝒞 : FamClass) (C0 : ℝ) : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ eps : ℝ, 0 < eps → eps ≤ ε0 → ∀ K : TransportedAlt, ∃ (Fm : FamP eps) (CH : ℝ),
    𝒞 Fm ∧ 0 ≤ CH ∧ Fm.Large K CH ∧ ChosenE Fm C0 CH ∧ TuSize Fm ∧
      DGamSize Fm

end Formalism.MainNotions

end
