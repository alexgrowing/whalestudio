import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatOpA
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeGTrChain
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeGQLFam
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeGVTr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeGVsTr

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

section defs

variable {k r : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

def dMul (d : (Fin r → ℂ) → ℂ) (Φ : Q.Fn k r X) : Q.Fn k r X := fun c g => d c • Φ c g

def drF (r : ℕ) : (Fin r → ℂ) → ℂ := fun c => ∏ a, c a

def drbF (r : ℕ) : (Fin r → ℂ) → ℂ := fun c => starRingEnd ℂ (∏ a, c a)

variable (k r)

def rhGrp (z z' : Fin (2 * r + k + 1) → ℂ) (y : ℂ) (Φ : Q.Fn k r X) : Q.Fn k r X :=
  dMul (drbF r) (Q.QL k r z z' (Fin.last r) y 1 0 (Q.crd (Q.cmp (Q.vAB r y r) 0) Φ) +
    Q.QL k r z z' (Fin.last r) y 1 1 (Q.crd (Q.cmp (Q.vAB r y r) 1) Φ))

def rhvGrp (z z' : Fin (2 * r + k + 1) → ℂ) (y : ℂ) (Φ : Q.Fn k r X) : Q.Fn k r X :=
  dMul (drF r) (Q.QL k r z z' (Fin.last r) y 0 1 (Q.crd (Q.cmp (Q.vABs r y r) 0) Φ) +
    Q.QL k r z z' (Fin.last r) y 1 1 (Q.crd (Q.cmp (Q.vABs r y r) 1) Φ))

end defs

def JDRGrp : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ → ∀ v (y : ℝ),
      ∃ Θ Θv : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)),
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θ ∧
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θv ∧
        B.Commutes (T v).base (B.GPos (T v).base) Θ ∧ B.Commutes (T v).base (B.GPos (T v).base) Θv ∧
        ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
          ∀ c ∈ OmX S.G.r, ∀ g ∈ Q.Glev S.G.k S.G.r (Fin.last S.G.r),
            Q.wCell S.G.k S.G.r (Fin.last S.G.r) c * g ∈ OmP S T v →
            Q.resG S.G.k S.G.r (Fin.last S.G.r) (B.opApply Θ J) c g =
                rhGrp S.G.k S.G.r (T v).base.z (T v).base.z' (y : ℂ) (Q.resG S.G.k S.G.r (Fin.last S.G.r) J) c g ∧
              Q.resG S.G.k S.G.r (Fin.last S.G.r) (B.opApply Θv J) c g =
                rhvGrp S.G.k S.G.r (T v).base.z (T v).base.z' (y : ℂ) (Q.resG S.G.k S.G.r (Fin.last S.G.r) J) c g

def JDRDrTr : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), Gauge.IsFrameB P Bs e →
    ∀ L : R.LevelData (MA.A P (MA.DQ P)) P.r, MA.IsModelLevel P (MA.DQ P) L →
    ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), Gauge.FamR P Bs Dc Φ →
      (∀ ρ, MA.toSm P (Gauge.rawR P Bs.μsec e (dMul (drbF P.r) Φ) ρ) =
        MA.actA P L.Drb (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ')) ρ) ∧
      ∀ ρ, MA.toSm P (Gauge.rawR P Bs.μsec e (dMul (drF P.r) Φ) ρ) =
        MA.actA P L.Dr (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ')) ρ

def JDRModelV : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), MA.IsModelLevel P (MA.DQ P) L → ∀ y : ℝ,
    (∀ b : Fin 2, Wd.v0 (MA.sites P (MA.DQ P)) (y : ℂ) b = L.Tprod (y : ℂ) b 0) ∧
    ∀ a : Fin 2, star (Wd.v0 (MA.sites P (MA.DQ P)) (y : ℂ) a) = L.Tvprod (y : ℂ) a 0

def JDRGrpP : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ → ∀ v (y : ℝ),
      ∃ Θ : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)),
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θ ∧
        B.Commutes (T v).base (B.GPos (T v).base) Θ ∧
        ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
          ∀ c ∈ OmX S.G.r, ∀ g ∈ Q.Glev S.G.k S.G.r (Fin.last S.G.r),
            Q.wCell S.G.k S.G.r (Fin.last S.G.r) c * g ∈ OmP S T v →
            Q.resG S.G.k S.G.r (Fin.last S.G.r) (B.opApply Θ J) c g =
                rhGrp S.G.k S.G.r (T v).base.z (T v).base.z' (y : ℂ) (Q.resG S.G.k S.G.r (Fin.last S.G.r) J) c g

def JDRGrpM : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ → ∀ v (y : ℝ),
      ∃ Θv : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)),
        PolyOp (2 * S.G.r + S.G.k + 1) ((S.G.r + 1) * (2 * S.G.r + S.G.k + 1)) Θv ∧
        B.Commutes (T v).base (B.GPos (T v).base) Θv ∧
        ∀ J ∈ Q.FFl S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' 0 (OmP S T v),
          ∀ c ∈ OmX S.G.r, ∀ g ∈ Q.Glev S.G.k S.G.r (Fin.last S.G.r),
            Q.wCell S.G.k S.G.r (Fin.last S.G.r) c * g ∈ OmP S T v →
            Q.resG S.G.k S.G.r (Fin.last S.G.r) (B.opApply Θv J) c g =
                rhvGrp S.G.k S.G.r (T v).base.z (T v).base.z' (y : ℂ) (Q.resG S.G.k S.G.r (Fin.last S.G.r) J) c g

theorem jDRGrp_of_halves (hP : JDRGrpP) (hM : JDRGrpM) : JDRGrp := by
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v y
  obtain ⟨Θ, h1, h3, hR⟩ := hP Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v y
  obtain ⟨Θv, h2, h4, hRv⟩ := hM Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v y
  exact ⟨Θ, Θv, h1, h2, h3, h4, fun J hJ c hc g hg hcg => ⟨hR J hJ c hc g hg hcg, hRv J hJ c hc g hg hcg⟩⟩

section assembly

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem jdr_tr_at (hD : JDRDrTr) (hM : JDRModelV) (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (he : Gauge.IsFrameB P Bs e)
    (hQQ : ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), Gauge.FamR P Bs Dc Φ →
      ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
        MA.toSm P (Gauge.rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
          MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ')) ρ)
    (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (hL : MA.IsModelLevel P (MA.DQ P) L)
    (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (hΦ : Gauge.FamR P Bs Dc Φ)
    (y : ℝ) :
    Gauge.VLem.trR P Bs.μsec e (rhGrp P.k P.r Bs.z Bs.z' (y : ℂ) Φ) =
        MA.actA P (RhM P L y) (Gauge.VLem.trR P Bs.μsec e Φ) ∧
      Gauge.VLem.trR P Bs.μsec e (rhvGrp P.k P.r Bs.z Bs.z' (y : ℂ) Φ) =
        MA.actA P (RhvM P L y) (Gauge.VLem.trR P Bs.μsec e Φ) := by
  have hV := fun b => Gauge.gauge_vector_transition_holds Wp Wq P Bs hpl hk e he Dc Φ hΦ y b
  have hVs := fun a => Gauge.gauge_conj_vector_transition Wp Wq P Bs hpl hk e he Dc Φ hΦ y a
  have hsm := fun (Dc' : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp))
    (hΨ : Gauge.FamR P Bs Dc' Ψ) => Gauge.raw_gauge_smoothness_holds Wp Wq P Bs hpl hk e he Dc' Ψ hΨ
  have hql := fun (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (hΨ : Gauge.FamR P Bs Dc Ψ) (a b : Fin 2) =>
    Gauge.quadratic_local_family_holds Wp Wq P Bs hpl hk Dc Ψ hΨ y a b
  obtain ⟨hMv, hMs⟩ := hM P L hL y
  have hsum : ∀ (Ψ₀ Ψ₁ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), Gauge.FamR P Bs Dc Ψ₀ → Gauge.FamR P Bs Dc Ψ₁ →
      Gauge.FamR P Bs Dc (Ψ₀ + Ψ₁) := fun _ _ h₀ h₁ => Gauge.VLem.famR_add h₀ h₁
  constructor
  · have hF0 := hql _ (hV 0).1 1 0
    have hF1 := hql _ (hV 1).1 1 1
    funext ρ
    show MA.toSm P (Gauge.rawR P Bs.μsec e (dMul (drbF P.r) _) ρ) = _
    rw [(hD Wp Wq P Bs hpl hk e he L hL Dc _ (hsum _ _ hF0 hF1)).1 ρ]
    have e1 : (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e
        (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (y : ℂ) 1 0 (Q.crd (Q.cmp (Q.vAB P.r (y : ℂ) P.r) 0) Φ) +
          Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (y : ℂ) 1 1 (Q.crd (Q.cmp (Q.vAB P.r (y : ℂ) P.r) 1) Φ)) ρ')) =
        MA.actA P (MA.QQr P (MA.DQ P) (y : ℂ) 1 0 * L.Ar (y : ℂ) + MA.QQr P (MA.DQ P) (y : ℂ) 1 1 * L.Br (y : ℂ))
          (Gauge.VLem.trR P Bs.μsec e Φ) := by
      have := Gauge.VLem.trR_add Bs.μsec e _ _ (hsm _ _ hF0) (hsm _ _ hF1)
      unfold Gauge.VLem.trR at this
      rw [this, Gauge.actA_add, Gauge.actA_mul, Gauge.actA_mul, R.LevelData.Ar, R.LevelData.Br, ← hMv 0, ← hMv 1]
      congr 1
      · funext ρ'; rw [hQQ _ _ (hV 0).1 y 1 0 ρ']; congr 1; funext ρ''; exact (hV 0).2 ρ''
      · funext ρ'; rw [hQQ _ _ (hV 1).1 y 1 1 ρ']; congr 1; funext ρ''; exact (hV 1).2 ρ''
    rw [e1, ← Gauge.actA_mul]
    rfl
  · have hF0 := hql _ (hVs 0).1 0 1
    have hF1 := hql _ (hVs 1).1 1 1
    funext ρ
    show MA.toSm P (Gauge.rawR P Bs.μsec e (dMul (drF P.r) _) ρ) = _
    rw [(hD Wp Wq P Bs hpl hk e he L hL Dc _ (hsum _ _ hF0 hF1)).2 ρ]
    have e1 : (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e
        (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (y : ℂ) 0 1 (Q.crd (Q.cmp (Q.vABs P.r (y : ℂ) P.r) 0) Φ) +
          Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (y : ℂ) 1 1 (Q.crd (Q.cmp (Q.vABs P.r (y : ℂ) P.r) 1) Φ)) ρ')) =
        MA.actA P (MA.QQr P (MA.DQ P) (y : ℂ) 0 1 * L.Avr (y : ℂ) + MA.QQr P (MA.DQ P) (y : ℂ) 1 1 * L.Bvr (y : ℂ))
          (Gauge.VLem.trR P Bs.μsec e Φ) := by
      have := Gauge.VLem.trR_add Bs.μsec e _ _ (hsm _ _ hF0) (hsm _ _ hF1)
      unfold Gauge.VLem.trR at this
      rw [this, Gauge.actA_add, Gauge.actA_mul, Gauge.actA_mul, R.LevelData.Avr, R.LevelData.Bvr, ← hMs 0, ← hMs 1]
      congr 1
      · funext ρ'; rw [hQQ _ _ (hVs 0).1 y 0 1 ρ']; congr 1; funext ρ''; exact (hVs 0).2 ρ''
      · funext ρ'; rw [hQQ _ _ (hVs 1).1 y 1 1 ρ']; congr 1; funext ρ''; exact (hVs 1).2 ρ''
    rw [e1, ← Gauge.actA_mul]
    rfl

end assembly

theorem jDCapR_of_parts (hG : JDRGrp) (hD : JDRDrTr) (hM : JDRModelV) : JDCapR := by
  intro Cc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hQQ hL y
  obtain ⟨Θ, Θv, h1, h2, h3, h4, hR⟩ := hG Cc E Wp Wq S T f χ ν' m₀ top A₀ hB v y
  refine ⟨Θ, Θv, h1, h2, h3, h4, fun J hJ => ?_⟩
  obtain ⟨hIB, -, -, -⟩ := hB
  obtain ⟨-, -, -, hIsB, -, -, -, -, -, -, hk, -⟩ := hIB
  have hpl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hIsB.2 v).2.2.2.1
  have hF := Gauge.tc_famR (D.parOf S v) (T v).base hpl J hJ
  obtain ⟨tR, tRv⟩ := jdr_tr_at hD hM (D.parOf S v) (T v).base hpl hk e hFr
    (fun Dc Φ hΦ Y a b ρ => hQQ Dc Φ hΦ Y a b ρ) L hL _ _ hF y
  have hJR : trJ S T v e J = Gauge.VLem.trR (D.parOf S v) (T v).base.μsec e
      (Q.resG S.G.k S.G.r (Fin.last S.G.r) J) := by
    funext ρ
    show MA.toSm _ (Gauge.rawJ (D.parOf S v) (T v).base e J ρ) = _
    rw [Gauge.tc_rawJ]
    rfl
  have hpt : ∀ (Θ' : B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (F : Q.Fn S.G.k S.G.r (Wq (S.pl v) →L[ℂ] Wp (S.pl v))),
      (∀ c ∈ OmX S.G.r, ∀ g ∈ Q.Glev S.G.k S.G.r (Fin.last S.G.r),
        Q.wCell S.G.k S.G.r (Fin.last S.G.r) c * g ∈ OmP S T v →
        Q.resG S.G.k S.G.r (Fin.last S.G.r) (B.opApply Θ' J) c g = F c g) →
      trJ S T v e (B.opApply Θ' J) = Gauge.VLem.trR (D.parOf S v) (T v).base.μsec e F := by
    intro Θ' F hF'
    funext ρ
    show MA.toSm _ (Gauge.rawJ (D.parOf S v) (T v).base e (B.opApply Θ' J) ρ) = _
    rw [Gauge.tc_rawJ]
    show MA.toSm _ _ = MA.toSm _ _
    congr 1
    funext q
    have hmu := Gauge.tc_mu (D.parOf S v) (T v).base hpl q
    simp only [Gauge.rawR]
    rw [hF' q.1.1 q.2.1 _ hmu.1 hmu.2]
  constructor
  · rw [hpt Θ _ (fun c hc g hg hcg => (hR J hJ c hc g hg hcg).1), hJR]
    exact tR
  · rw [hpt Θv _ (fun c hc g hg hcg => (hR J hJ c hc g hg hcg).2), hJR]
    exact tRv

end

end Formalism.FourierDecayAlt.P.CutMP
