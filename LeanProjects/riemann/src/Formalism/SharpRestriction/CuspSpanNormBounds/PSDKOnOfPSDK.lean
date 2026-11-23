import Formalism.SharpRestriction.CuspSpanNormBounds.LocalDataRealPlace
import Formalism.SharpRestriction.CuspSpanNormBounds.IsGramNorm

open Matrix MeasureTheory NumberField Filter Topology

noncomputable section

namespace Formalism.MainNotions.S.LocalFrameAxioms

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

def LocMatch (D : D7) (T T' : ℝ) (x : LocalDataRealPlace D) (B : LocBessel D.R.k D.R.rS) : Prop :=
  B.lam = x.lam ∧ B.u = x.u ∧ B.u' = x.u' ∧ Tz D.R.k D.R.rS B.z = T ∧ Tz D.R.k D.R.rS B.z' = T' ∧
    B.ε = epsSH D.R

def FrameAx (D : D7) (δ : D.host.E) (L : LatticeDataWithDual D) (B : D.what₂.Tau → LocBessel D.R.k D.R.rS) : Prop :=
  ∃ ϱ : ℝ, IsFrameScale D L ϱ ∧ ∀ v, (B v).c = cPsi D δ v / (ϱ : ℂ)

def PsiAx (D : D7) (δ : D.host.E) : Prop :=
  δ ≠ 0 ∧ ((∀ v, (plEmb D v δ).re = 0) ∨ ∀ v, (plEmb D v δ).im = 0)

theorem k_le_nS (D : D7) : D.R.k ≤ 2 * D.R.rS + D.R.k + 1 := by omega

def Nlet (D : D7) (Kst : ℕ) : ℝ := 4 * (Kst : ℝ) * ((D.R.rS : ℝ) + 1)

section Arith

open scoped ComplexOrder

variable (D : D7)

def InProd (Sg : ℕ → ℕ → Finset D.host.E) : ℕ → List (D.host.E × ℕ) → Prop
  | _, [] => True
  | a, (t, s) :: bs => t ∈ Sg (a + 1) s ∧ InProd Sg (a + s) bs

def headsOf (Sg : ℕ → ℕ → Finset D.host.E) (j : ℕ) : Set (Point D.host.E j) := {h | InProd D Sg 0 h.1}

def PSDKOn {α : Type*} (S : Set α) (K : α → α → ℂ) : Prop :=
  ∀ (X : Finset α) (a : α → ℂ), (∀ p ∈ X, p ∈ S) → 0 ≤ ∑ p ∈ X, ∑ q ∈ X, star (a p) * K p q * a q

def KLEOn {α : Type*} (S : Set α) (K L : α → α → ℂ) : Prop := PSDKOn S (fun p q => L p q - K p q)

theorem PSDKOn_of_PSDK {α : Type*} {K : α → α → ℂ} (h : PSDK K) (S : Set α) : PSDKOn S K := fun X a _ => h X a

def ArithAxF (L : LatticeDataWithDual D) (Kd : KernelData D) : Prop :=
  (∀ p q, Kd.K 0 p q = 1) ∧
  (∀ i, i ≤ D.R.rS + 1 → PSDK (Kd.K i)) ∧
  (∀ i, 1 ≤ i → i ≤ D.R.rS + 1 → 0 ≤ Kd.e i ∧ Kd.e i ≤ 1) ∧

  (∀ (j s : ℕ) (hs : 1 ≤ s), j + s ≤ D.R.rS + 1 → ∀ (h h' : Point D.host.E j) (t t' : D.host.E)
      (ht : t ≠ 0) (ht' : t' ≠ 0),
      Kd.K (j + s) (ptSnoc D h t ht s hs) (ptSnoc D h' t' ht' s hs) ≠ 0 →
        (if j + s = D.R.rS + 1 ∧ s = 1 then t = t' else t⁻¹ - t'⁻¹ ∈ L.La' (j + 1) s)) ∧

  ∀ Sg : ℕ → ℕ → Finset D.host.E,
    ∃ Th : (j s : ℕ) → D.host.E → Point D.host.E j → Point D.host.E j → ℂ,
    ∀ (j s : ℕ) (hs : 1 ≤ s), j + s ≤ D.R.rS + 1 →
      (∀ (t : D.host.E) (ht : t ≠ 0), t ∈ Sg (j + 1) s →
        KLEOn (headsOf D Sg j)
          (fun h h' : Point D.host.E j => Kd.K (j + s) (ptSnoc D h t ht s hs) (ptSnoc D h' t ht s hs)) (Th j s t)) ∧
      (∀ t, ∀ l ∈ L.La (j + 1) s, ∀ h ∈ headsOf D Sg j, ∀ h' ∈ headsOf D Sg j, Th j s (t + l) h h' = Th j s t h h') ∧
      (∀ t, PSDKOn (headsOf D Sg j) (Th j s t)) ∧
      (∀ X : Finset D.host.E, (∀ t ∈ X, ∀ t' ∈ X, t - t' ∈ L.La (j + 1) s → t = t') →
        KLEOn (headsOf D Sg j) (fun h h' => ∑ t ∈ X, Th j s t h h')
          (fun h h' => (1 + (Kd.e (j + s) : ℂ)) * Kd.K j h h'))

variable {D}

theorem _root_.Formalism.MainNotions.S.ArithAx.toF {L : LatticeDataWithDual D} {Kd : KernelData D} (h : ArithAx D L Kd) : ArithAxF D L Kd := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  refine ⟨h0, h1, h2, h3, fun Sg => ⟨Kd.Th, fun j s hs hjs => ?_⟩⟩
  obtain ⟨a, b, c, d⟩ := h4 j s hs hjs
  exact ⟨fun t ht _ => PSDKOn_of_PSDK (a t ht) _, fun t l hl _ _ _ _ => by rw [b t l hl],
    fun t => PSDKOn_of_PSDK (c t) _, fun X hX => PSDKOn_of_PSDK (d X hX) _⟩

end Arith

def stThmA (D : D7) (C C' : ℝ) (Kst : ℕ) (Vm : ValMap D.R.k D.R.rS) : Prop :=
  ∀ (δ : D.host.E) (T T' : ℝ) (x : D.what₂.Tau → LocalDataRealPlace D) (L : LatticeDataWithDual D) (Kd : KernelData D)
    (B : D.what₂.Tau → LocBessel D.R.k D.R.rS)
    (f : ∀ v, Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → ((B v).Wq →L[ℂ] (B v).Wp))
    (μsec : D.what₂.Tau → ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ)
    (ι : Type) [Countable ι] (c : ι → Point D.host.E (D.R.rS + 1) → ℂ),
    4 ≤ Kst → 1 ≤ D.host.v →
    PsiAx D δ → LatAx D δ L → FrameAx D δ L B → ArithAxF D L Kd →
    (∀ v, LocMatch D T T' (x v) (B v) ∧ IsKFinCoefH (B v).σ (f v) ∧
      IsSection D.R.k D.R.rS (B v).z (B v).z' (μsec v)) →
    (∀ v, InterlaceS (k_le_nS D) (x v).u (x v).lam ∧ InterlaceS (k_le_nS D) (x v).u' (x v).lam) →
    (∀ v, (x v).u ≠ (x v).u') →
    (∀ v, GapAtLeast (epsSH D.R) (x v).lam
      (C * (D.R.m : ℝ) ^ ((9 : ℝ) / 2) * (Nlet D Kst * (D.R.r : ℝ) ^ 2 + (D.R.r : ℝ) ^ 3))) →
    (∀ v, IsCutS (x v).u (x v).u' (Set.Icc (x v).a (x v).b)) →
    (∀ v, (x v).a ≤ (x v).a1 ∧ (x v).a1 ≤ (x v).b1 ∧ (x v).b1 ≤ (x v).b ∧
      Nlet D Kst ^ 3 / 2 ≤ (x v).b1 - (x v).a1) →
    (∀ v, C * ((D.R.k : ℝ) * Nlet D Kst * ((D.R.rS : ℝ) + 1) ^ 2 +
        Nlet D Kst ^ 2 * ((D.R.rS : ℝ) + 1) ^ 2 + Nlet D Kst ^ 3) ≤ (x v).b - (x v).a) →
    ((D.R.rS : ℝ) + 1) * (C / ThS D C C (Nlet D Kst) T T' δ x L) ^ D.R.f ≤ 1 →
    C' ≤ ThS D C C (Nlet D Kst) T T' δ x L →
    RowsAx (fun v => (B v).Wq →L[ℂ] (B v).Wp) (fun _ => hsInner) (Kd.K (D.R.rS + 1))
      (fun h => ptWeightG D L.ρ T T' h.1) c (fun v h => Vm.V (B v) (f v) (locBlocks D L.ρ v h.1)) →
    SRowForm (fun v => (B v).Wq →L[ℂ] (B v).Wp) (fun _ => hsInner) (fun h => ptWeightG D L.ρ T T' h.1) c
        (fun v h => Vm.V (B v) (f v) (locBlocks D L.ρ v h.1)) ≤
      ENNReal.ofReal ((1 + C * ((D.R.rS : ℝ) + 1) *
          (C / ThS D C C (Nlet D Kst) T T' δ x L) ^ D.R.f) *
          ∏ i ∈ Finset.Icc 1 (D.R.rS + 1), (1 + Kd.e i)) *
        jNorm2One (fun v => (B v).Wq →L[ℂ] (B v).Wp) (fun _ => hsNormSq) D.R.k D.R.rS T T' L.κ
          (fun v p => (B v).J (f v) (bigCell D.R.k D.R.rS p.1 (μsec v p.2)))

end Formalism.MainNotions.S.LocalFrameAxioms

end
