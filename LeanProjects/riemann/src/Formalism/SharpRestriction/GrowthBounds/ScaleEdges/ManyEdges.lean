import Formalism.SharpRestriction.GrowthBounds.TableLineDegreeFive
import Formalism.SharpRestriction.GrowthBounds.SourceCleaning
import Formalism.SharpRestriction.GrowthBounds.Lemma5aAt

noncomputable section

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility

def ValLe {O Kf : Type*} [CommRing O] [Field Kf] [Algebra O Kf] (π : O) (D : ℕ) (x : Kf) : Prop :=
  ∃ a b : O, x = algebraMap O Kf a ∧ a * b = π ^ D

section Loc

variable {W Qq O Kf : Type} [CommRing W] [Field Qq] [Algebra W Qq] [CommRing O] [Field Kf] [Algebra O Kf]

def SrcTests (p n' : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) {m : ℕ} (r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (t D : ℕ) (κ : ℝ) (cStar : ℕ) (L : Submodule W (Fin (m + 1) → Qq)) : Prop :=
  ∃ (E : Finset (Edge W Qq (m + 1))) (nE : Edge W Qq (m + 1) → ℕ)
    (F : ∀ e : Edge W Qq (m + 1), Fin (nE e) → Vsp Kf lam0),
    (∀ e ∈ E, IsEdge p n' r e ∧ e.tgt = L) ∧
    (∀ e ∈ E, ∀ i, F e i ∈ Nsrc p n' ι σ w r lam0 t e.src) ∧
    (∀ e ∈ E, ∀ i, ∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.src = e.src → e' ≠ e →
      F e i ∈ scale (algebraMap O Kf w ^ (cStar : ℤ)) (Re p ι σ w r lam0 e')) ∧
    (∀ e ∈ E, ∀ c : Fin (nE e) → O, (∃ i, IsUnit (c i)) →
      ∃ G ∈ Ntgt p n' ι σ w r lam0 t L,
        ValLe (p : O) D (be p r lam0 (∑ i, c i • F e i) G) ∧
        ∀ e' ∈ E, e' ≠ e → G ∈ scale (algebraMap O Kf w ^ (cStar : ℤ)) (Re' p ι σ w r lam0 e')) ∧
    (1 - κ) * (dimV Kf lam0 : ℝ) ≤ ((∑ e ∈ E, nE e : ℕ) : ℝ)

def EdgeFam (p n' : ℕ) (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (w : O) {m : ℕ} (r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ)
    (tS tT D cStar : ℕ) (e : Edge W Qq (m + 1)) (n : ℕ) : Prop :=
  ∃ F : Fin n → Vsp Kf lam0,
    (∀ i, F i ∈ scale (algebraMap O Kf w ^ (-(tS : ℤ))) (HL (O := O) ι σ lam0 e.src) ∧ F i ∈ Re p ι σ w r lam0 e) ∧
    (∀ i, ∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.src = e.src → e' ≠ e →
      F i ∈ scale (algebraMap O Kf w ^ (cStar : ℤ)) (Re p ι σ w r lam0 e')) ∧
    ∀ c : Fin n → O, (∃ i, IsUnit (c i)) →
      ∃ G : Module.Dual Kf (Vsp Kf lam0),
        G ∈ scale (algebraMap O Kf w ^ (-(tT : ℤ))) (dualLat O Kf (HL (O := O) ι σ lam0 e.tgt)) ∧
        G ∈ Re' p ι σ w r lam0 e ∧
        (∀ e' : Edge W Qq (m + 1), IsEdge p n' r e' → e'.tgt = e.tgt → e' ≠ e →
          G ∈ scale (algebraMap O Kf w ^ (cStar : ℤ)) (Re' p ι σ w r lam0 e')) ∧
        ValLe (p : O) D (be p r lam0 (∑ i, c i • F i) G)

end Loc

def Hyps (C : ℝ) (p n' m r : ℕ) (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ) : Prop :=
  13 ≤ p ∧ 2 ≤ r ∧
    tableLineDegreeFive.OrbitHyp n' TT r L₁ L₂ de h x ∧
    orbitWindowCount r de h x ^ 2 ≤ r * TT.card ∧
    tableLineDegreeFive.WeightHyp TT aT bT cpp c0 a lam0 ∧
    (r : ℝ) ≤ Y ∧
    tableLineDegreeFive.La C (orbitWindowCount r de h x) a ≤ ((m + 1 : ℕ) : ℝ) ∧
    orbitWindowCount r de h x + 2 * r ≤ (m + 1) - r ∧
    256 * ((m + 1 : ℕ) : ℝ) ^ 2 * (TT.card : ℝ) * Y ^ 2 ≤ (p : ℝ) ^ ((L₁ : ℤ) - 1) ∧
    C * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a ≤ Dp ∧
    8 * (Dp + 1) ≤ cStar ∧
    C * ((m + 1 : ℕ) : ℝ) ^ 3 * (r : ℝ) ^ 2 * (TT.card : ℝ) * ((p : ℝ) ^ goodG' r de h x) ^ 5 *
        ((cStar : ℝ) + ((r : ℝ) * TT.card * c0 + 2 * r * n' * cpp)) * Y ≤ a

def t0 (C Ct0 : ℝ) (p N N₁ L₁ G' k : ℕ) (a : ℝ) : ℝ :=
  Ct0 * N * (tableLineDegreeFive.La C N₁ a * a / (p * k) + a * (p : ℝ) ^ (-(L₁ : ℤ)) + k * (p : ℝ) ^ G')

def om (r N n' c0 cpp : ℕ) : ℝ := (r : ℝ) * N * c0 + 2 * r * n' * cpp

def EdgeStep (C Ct0 CD1 Cr : ℝ) : Prop :=
  ∀ (p : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O)
    (n' m r : ℕ) (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
    UnramifiedQuadraticSetting p n' W Qq O Kf ι σ j w →
    Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
    ∀ e : Edge W Qq (m + 1), IsEdge p n' r e → e.tgt = colSpan W (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) →
      ∃ n tS tT D1 : ℕ,
        (tS : ℝ) ≤ t0 C Ct0 p TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a + om r TT.card n' c0 cpp ∧
        (tT : ℝ) ≤ t0 C Ct0 p TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a + (TT.card : ℝ) * c0 +
          om r TT.card n' c0 cpp ∧
        (D1 : ℝ) ≤ CD1 * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a ∧
        (1 - Cr * (TT.card : ℝ) * (r : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) / Y) *
            (1 - ((m + 1 : ℕ) : ℝ) * c0 / a) ^ TT.card * (dimV Kf lam0 : ℝ) / ((p : ℝ) ^ (n' * (r * (m + 1 - r)))) ≤ n ∧
        EdgeFam (W := W) (O := O) p n' ι σ w r lam0 tS tT D1 cStar e n

def RestEdge (D : Formalism.BasicNotions.D7) (CLa Ck Crk Cdeg CLa' CD Csz CH CE C6 C18 : ℝ) : Prop :=
  tableLineDegreeFive.admitted D CLa Ck Crk Cdeg → SourceCleaning.aux₃ D CLa' CD Csz → PlaneGramData.aux₃ D CH CE C6 C18 →
    ∃ Ct0 CD1 Cr C₁ : ℝ, 0 < Ct0 ∧ 0 < CD1 ∧ 0 < Cr ∧ 0 < C₁ ∧ ∀ C : ℝ, C₁ ≤ C → EdgeStep C Ct0 CD1 Cr

def ManyEdges : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ j w →
    ∀ (k r : ℕ), r ≤ k →
      ∃ E : Finset (Edge W Qq k),
        (∀ e ∈ E, IsEdge p n' r e ∧ e.tgt = colSpan W (1 : Matrix (Fin k) (Fin k) Qq)) ∧
        p ^ (n' * (r * (k - r))) ≤ E.card

def S7 : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ j w → BePerfect →
    ∀ (m r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (t D : ℕ) (κ : ℝ) (cStar : ℕ)
      (L : Submodule W (Fin (m + 1) → Qq)), IsDominant lam0 → 2 * (D + 1) ≤ cStar →
      SrcTests (O := O) p n' ι σ w r lam0 t D κ cStar L → LPprimeAt (O := O) p n' ι σ w r lam0 t D κ cStar L

def Asm : Prop :=
  ∀ (p n' : ℕ) (W Qq O Kf : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq]
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    (ι : Qq →+* Kf) (σ : Qq ≃+* Qq) (j : W →+* O) (w : O),
    HidaSetting p n' W Qq O Kf ι σ j w →
    ∀ (m r : ℕ) (lam0 : Fin n' → Fin (m + 1) → ℤ) (t D : ℕ) (κ : ℝ) (cStar : ℕ)
      (L : Submodule W (Fin (m + 1) → Qq)) (E : Finset (Edge W Qq (m + 1))) (nE : Edge W Qq (m + 1) → ℕ),
      (∀ e ∈ E, IsEdge p n' r e ∧ e.tgt = L) →
      (∀ e ∈ E, ∃ tS tT D1 : ℕ, tS ≤ t ∧ tT ≤ t ∧ D1 ≤ D ∧
        EdgeFam (W := W) (O := O) p n' ι σ w r lam0 tS tT D1 cStar e (nE e)) →
      (1 - κ) * (dimV Kf lam0 : ℝ) ≤ ((∑ e ∈ E, nE e : ℕ) : ℝ) →
      SrcTests (O := O) p n' ι σ w r lam0 t D κ cStar L

def Num : Prop :=
  ∀ (C Ct0 CD1 Cr : ℝ), 0 < Ct0 → 0 < CD1 → 0 < Cr → 2 ≤ C → Ct0 ≤ C → CD1 ≤ C → Cr + 1 ≤ C →
    ∀ (p n' m r : ℕ) (TT : Finset (Fin n')) (L₁ L₂ : ℕ) (de h x : ℝ)
      (lam0 : Fin n' → Fin (m + 1) → ℤ) (aT bT : Fin n' → ℤ) (a Y : ℝ) (cpp c0 Dp cStar : ℕ),
      Hyps C p n' m r TT L₁ L₂ de h x lam0 aT bT a Y cpp c0 Dp cStar →
      t0 C Ct0 p TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) (m + 1) a + (TT.card : ℝ) * c0 +
          om r TT.card n' c0 cpp ≤
        tableLineDegreeFive.tBound C p r TT.card (orbitWindowCount r de h x) L₁ (goodG' r de h x) n' (m + 1) cpp c0 a ∧
      0 ≤ (TT.card : ℝ) * c0 ∧
      CD1 * (TT.card : ℝ) * ((m + 1 : ℕ) : ℝ) ^ 2 * Real.logb p a ≤ Dp ∧
      1 - C * TT.card * (r : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) / Y ≤
        (1 - Cr * (TT.card : ℝ) * (r : ℝ) ^ 2 * ((m + 1 : ℕ) : ℝ) / Y) * (1 - ((m + 1 : ℕ) : ℝ) * c0 / a) ^ TT.card

end Formalism.MainNotions.Pf14
