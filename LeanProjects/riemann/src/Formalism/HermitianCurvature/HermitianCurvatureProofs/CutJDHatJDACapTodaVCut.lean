import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapAGrp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutCVPresFF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

section defs

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

def colsVm (k r m : ℕ) (j : Fin m) : Fin (2 * r + k + 1) := ⟨2 * r + k - (r - 1 - j.val), by omega⟩

def kvM (k r m : ℕ) (w : ℂ) (F : Q.Mx k r → X) : Q.Mx k r → X :=
  qminorOp (Q.EH k r) (colsVm k r m) (colsVm k r m) w F

def kvTop (k r : ℕ) (y : ℂ) : ℂ := (y - ((2 * r + k : ℕ) : ℂ) / 2) + ((r : ℕ) : ℂ) - 1

def pbN (r i : ℕ) (f : (Fin r → ℂ) → X) : (Fin r → ℂ) → X := if h : i < r then pbOp ⟨i, h⟩ f else 0

def cbN (r i : ℕ) (f : (Fin r → ℂ) → X) : (Fin r → ℂ) → X := if h : i < r then cbOp ⟨i, h⟩ f else 0

def cbiN (r i : ℕ) (f : (Fin r → ℂ) → X) : (Fin r → ℂ) → X := if h : i < r then cbiOp ⟨i, h⟩ f else 0

def kvP (r : ℕ) (w : ℂ) : ℕ → (((Fin r → ℂ) → X) → (Fin r → ℂ) → X) × (((Fin r → ℂ) → X) → (Fin r → ℂ) → X)
  | 0 => (fun f => f, fun _ => 0)
  | m + 1 =>
    (fun f => (kvP r w m).1 (fun c => (w - (m : ℂ)) • f c - pbN r (r - m - 1) f c) -
        cbN r (r - m) (cbiN r (r - m - 1) ((kvP r w m).2 f)),
      (kvP r w m).1)

def kvC (r : ℕ) (w : ℂ) (m : ℕ) (f : (Fin r → ℂ) → X) : (Fin r → ℂ) → X := (kvP r w m).1 f

def gaugeF (k r : ℕ) (c : Fin r → ℂ) : ℂ := Q.resG k r (Fin.last r) (fun _ => (1 : ℂ)) c 1

end defs

def TVCoef : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ y : ℂ,
    ∀ J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs),
      ∀ c ∈ OmX P.r, ∀ g ∈ Q.Glev P.k P.r (Fin.last P.r), Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Gauge.OmB Bs →
        capAv P.k P.r y J (Q.wCell P.k P.r (Fin.last P.r) c * g) =
          drbF P.r c • kvM P.k P.r P.r (kvTop P.k P.r y) J (Q.wCell P.k P.r (Fin.last P.r) c * g)

def TVGrp : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∀ y : ℂ,
    ∀ J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs),
      ∀ c ∈ OmX P.r, ∀ g ∈ Q.Glev P.k P.r (Fin.last P.r), Q.wCell P.k P.r (Fin.last P.r) c * g ∈ Gauge.OmB Bs →
        kvM P.k P.r P.r (kvTop P.k P.r y) J (Q.wCell P.k P.r (Fin.last P.r) c * g) =
          kvC P.r (kvTop P.k P.r y) P.r (fun c' => J (Q.wCell P.k P.r (Fin.last P.r) c' * g)) c

def TVCrd : Prop :=
  ∀ (k r : ℕ) (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (y : ℂ) (Φ : (Fin r → ℂ) → X)
    (U : Set (Fin r → ℂ)) (c : Fin r → ℂ), IsOpen U → U ⊆ OmX r → c ∈ U →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun c' => gaugeF k r c' • Φ c') U →
      gaugeF k r c • kvC r (kvTop k r y) r Φ c = (vABm r y r).1 (fun c' => gaugeF k r c' • Φ c') c

open scoped ContDiff in

theorem jDACapTodaV_of_parts (h1 : TVCoef) (h2 : TVGrp) (h3 : TVCrd) : JDACapTodaV := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk y J hJ c hc g hg hcg
  have e1 := h1 Wp Wq P Bs hpl hk y J hJ c hc g hg hcg
  have e2 := h2 Wp Wq P Bs hpl hk y J hJ c hc g hg hcg
  have hD : Q.IsDom P.k P.r Bs.z Bs.z' 0 (Gauge.OmB Bs) := isDom_omP Bs.z_mem Bs.z'_mem
  have hfam := (Formalism.FourierDecayAlt.P.restriction_good_family Wp Wq P.k P.r Bs.z Bs.z' Bs.π Bs.π' (Gauge.OmB Bs) Bs.z_mem Bs.z'_mem hD J hJ
    (Fin.last P.r)).1
  obtain ⟨U, F, hUo, hx0, hF, hFeq⟩ := hfam (c, g) ⟨hc, hcg⟩ hg
  have hemb : ContDiff ℝ ∞ (fun c' : Fin P.r → ℂ => (c', g)) := contDiff_id.prodMk contDiff_const
  set U' : Set (Fin P.r → ℂ) := {c' | (c', g) ∈ U} ∩ OmX P.r with hU'
  have hU'o : IsOpen U' := (hUo.preimage hemb.continuous).inter (Formalism.FourierDecayAlt.P.Qx5.isOpen_OmX P.r)
  have hgauge : ∀ c' : Fin P.r → ℂ, gaugeF P.k P.r c' • J (Q.wCell P.k P.r (Fin.last P.r) c' * g) =
      Q.resG P.k P.r (Fin.last P.r) J c' g := by
    intro c'
    simp only [gaugeF, Q.resG, smul_eq_mul, mul_one]
  have hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun c' => gaugeF P.k P.r c' • J (Q.wCell P.k P.r (Fin.last P.r) c' * g)) U' := by
    refine ((hF.comp hemb.contDiffOn (fun c' hc' => hc'.1))).congr (fun c' hc' => ?_)
    rw [hgauge c']
    exact hFeq (c', g) hc'.1 hg
  have e3 := h3 P.k P.r (Wq →L[ℂ] Wp) y (fun c' => J (Q.wCell P.k P.r (Fin.last P.r) c' * g)) U' c hU'o
    (fun _ h => h.2) ⟨hx0, hc⟩ hsm
  have hfun : (fun c' => gaugeF P.k P.r c' • J (Q.wCell P.k P.r (Fin.last P.r) c' * g)) =
      fun c' => Q.resG P.k P.r (Fin.last P.r) J c' g := funext hgauge
  rw [hfun] at e3
  simp only [dMul, Q.crd, Q.cmp, if_true]
  rw [← e3]
  have hres : Q.resG P.k P.r (Fin.last P.r) (capAv P.k P.r y J) c g =
      gaugeF P.k P.r c • capAv P.k P.r y J (Q.wCell P.k P.r (Fin.last P.r) c * g) := by
    simp only [gaugeF, Q.resG, smul_eq_mul, mul_one]
  rw [hres, e1, e2, smul_comm]

end

end Formalism.FourierDecayAlt.P.CutMP
