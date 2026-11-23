import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.SegmentReductionOfColumnWords

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

def ellP (R : Type) [CommRing R] (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) : MvPolynomial (ℤ × Fin r) R :=
  ∏ x ∈ X.toLate j, ∏ c : Fin r, MvPolynomial.X (x, c) ^ e (x, Fin.castAdd K c)

def ellN (R : Type) [CommRing R] (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) : MvPolynomial (ℤ × Fin K) R :=
  ∏ x ∈ X.toLate j, ∏ c : Fin K, MvPolynomial.X (x, c) ^ e (x, Fin.natAdd r c)

def dS (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) : ℕ :=
  ∑ x ∈ X.toLate j, if Even x then 0 else ∑ c : Fin r, e (x, Fin.castAdd K c)

def dV (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) : ℕ :=
  ∑ x ∈ X.toLate j, if Even x then ∑ c : Fin K, e (x, Fin.natAdd r c) else 0

def Aw (R : Type) [CommRing R] (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) (nu : Fin (segN X.F j + 1) → Fin r → ℤ)
    (I' : ℤ → Finset (Fin r)) : MvPolynomial (ℤ × Fin r) R :=
  (segRen X.F j R r (Psi R nu I')) ^ (p ^ X.Rj p K j) * X.ellP K R j e * X.DlSeg p K R j

def Gw (R : Type) [CommRing R] (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) (ka : Fin (segN X.F j + 1) → Fin K → ℤ)
    (I'' : ℤ → Finset (Fin K)) : MvPolynomial (ℤ × Fin K) R :=
  (segRen X.F j R K (Psi R ka I'')) ^ (p ^ X.Rj p K j) * X.ellN K R j e

def Mw [NeZero K] (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) (ka : Fin (segN X.F j + 1) → Fin K → ℤ) : ℤ → ℤ :=
  Function.extend (segE X.F j)
    (fun i => ((p ^ X.Rj p K j : ℕ) : ℤ) * (if Even (segE X.F j i) then ka i.succ 0 else ka i.castSucc 0) +
      (X.dV K j e : ℤ)) 0

end Dat

structure WCtx (C₀ : ℝ) (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r)
    (j : ℤ) (b : ℤ → ℕ) (e : ℤ × Fin (r + K) →₀ ℕ)
    (q : (Fin (segN X.F j + 1) → Fin r → ℤ) × (Fin (segN X.F j + 1) → Fin K → ℤ))
    (I' : ℤ → Finset (Fin r)) (I'' : ℤ → Finset (Fin K)) : Prop where
  hX : X.Hyp p K
  hLa : C₀ ≤ X.CLa
  hk : C₀ ≤ X.Ck
  he : X.IsEll p K j e
  h2 : X.Step2 p K j b
  hq : q ∈ segPairs X.F j K (fun _ => (X.m0 K : ℤ)) (X.thc p K j b) (X.oc p K j)
  hI' : IsSt q.1 I'
  hI'' : IsSt q.2 I''

def FrobeniusReductionProduct (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → ∀ j b e q I' I'', WCtx C₀ p n' r K X j b e q I' I'' →
    MvPolynomial.map (IsLocalRing.residue O)
        (X.zSeg p K O j (segRen X.F j O (r + K) (PsiPl O q.1 I' * PsiTan O q.2 I'')) e) =
      plEmb (FF O) r K (X.Aw p K (FF O) j e q.1 I') * nmEmb (FF O) r K (X.Gw p K (FF O) j e q.2 I'')

def ProductAllowedLetters (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → ∀ j b e q I' I'', WCtx C₀ p n' r K X j b e q I' I'' →
    X.Aw p K (FF O) j e q.1 I' ∈ supported (FF O) {v : ℤ × Fin r | v.1 ∈ X.F.letters j} ∧
    X.Gw p K (FF O) j e q.2 I'' ∈ supported (FF O) {v : ℤ × Fin K | v.1 ∈ X.F.letters j ∧ ¬ X.F.IsW j v.1}

def ColumnConditionsWithMargin (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → ∀ j b e q I' I'', WCtx C₀ p n' r K X j b e q I' I'' →
    ∀ x ∈ X.F.letters j, ¬ X.F.IsW j x →
      (Even x → lam1S LZ {y | y ≤ x} (X.Gw p K (FF O) j e q.2 I'') ≤ ((X.Mw p K j e q.2 x : ℤ) : WithBot ℤ) ∧
          ((X.Mw p K j e q.2 x + X.mg p K j x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y < x} (X.Aw p K (FF O) j e q.1 I')) ∧
      (¬ Even x → lam1S LZ {y | y < x} (X.Gw p K (FF O) j e q.2 I'') ≤ ((X.Mw p K j e q.2 x : ℤ) : WithBot ℤ) ∧
          ((X.Mw p K j e q.2 x + X.mg p K j x : ℤ) : WithTop ℤ) ≤ valS LZ {y | y ≤ x} (X.Aw p K (FF O) j e q.1 I')) ∧
      geR (valS LZ {y | y < x} (X.Aw p K (FF O) j e q.1 I')) (X.th p j x)

def ProductOrdersBounded (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → ∀ j b e q I' I'', WCtx C₀ p n' r K X j b e q I' I'' →
    ∀ mm ∈ (plEmb (FF O) r K (X.Aw p K (FF O) j e q.1 I') * nmEmb (FF O) r K (X.Gw p K (FF O) j e q.2 I'')).support,
      ∀ x ∈ X.F.letters j, ¬ X.F.IsW j x → (ordDeg mm x : ℝ) ≤ X.o p K j x

theorem column_word_reduction_of_four (D : Formalism.BasicNotions.D7) (hB12 : NestedTypeBound D) (C₀ : ℝ) (h1 : FrobeniusReductionProduct C₀) (h2 : ProductAllowedLetters C₀)
    (h3 : ColumnConditionsWithMargin C₀) (h4 : ProductOrdersBounded C₀) : ColumnWordReductionLifts C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk j b e he hs2 q hq I' I'' hI' hI''
  have : Fact p.Prime := ⟨hX.prime⟩
  have hc : WCtx C₀ p n' r K X j b e q I' I'' := ⟨hX, hLa, hk, he, hs2, hq, hI', hI''⟩
  have hseg : segN X.F j + r ≤ K := le_trans (Nat.add_le_add_right (hX.card j) r) hX.NsK
  have h6 := (hB12 p O S n' r K X.F X.L₁ X.N₁ j (X.mg p K j) (X.th p j) (X.o p K j) hX.valid hseg
    (fun x => by unfold Dat.mg; positivity)).2.2.2.2.2
  obtain ⟨P, hP, hPe⟩ := h6 (X.Aw p K (FF O) j e q.1 I') (X.Gw p K (FF O) j e q.2 I'') (X.Mw p K j e q.2)
    (h2 p n' r K X O S j b e q I' I'' hc).1 (h2 p n' r K X O S j b e q I' I'' hc).2
    (h3 p n' r K X O S j b e q I' I'' hc) (h4 p n' r K X O S j b e q I' I'' hc)
  exact ⟨P, hP, hPe.trans (h1 p n' r K X O S j b e q I' I'' hc).symm⟩

end Formalism.MainNotions.SelectionLemmas.Pf
