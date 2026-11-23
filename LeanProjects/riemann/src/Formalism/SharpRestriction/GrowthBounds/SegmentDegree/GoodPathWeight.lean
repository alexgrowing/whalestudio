import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.RestCountOf

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

open Classical in

def restr (j : ℤ) (b : ℤ → ℕ) : ℤ → ℕ := fun x => if x ∈ X.toLate j then b x else 0

open Classical in

def Bdeg (j : ℤ) (b : ℤ → ℕ) (x : ℤ) : ℕ :=
  if X.F.IsW j x then (X.Bw p K j x - (X.m0 K : ℤ)).toNat else b x

def beS (j : ℤ) (b : ℤ → ℕ) : ℕ := ∑ x ∈ (X.F.letters j).filter (· < X.F.fr j 0), X.Bdeg p K j b x

structure IsPATH (j : ℤ) (b : ℤ → ℕ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ)
    (dd : Fin (segN X.F j) → ℕ) : Prop where
  path : ∃ P : PPath (r + K) (segN X.F j) (segLL X.F j) dd, P.mu = μ
  degs : ∀ i, segE X.F j i < X.F.fr j 0 → dd i = X.Bdeg p K j b (segE X.F j i)
  head : ∀ (i : Fin (segN X.F j)) (i' : Fin r), segE X.F j i = X.F.fr j i'.val →
    ∀ m : Fin (r + K), m.val ≤ i'.val → μ i.succ m = (X.beS p K j b : ℤ)

def IsGood [NeZero r] (j : ℤ) (b : ℤ → ℕ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ) : Prop :=
  ∀ i : Fin (segN X.F j), ¬ X.F.IsW j (segE X.F j i) →
    X.thc p K j b (segE X.F j i) ≤ ((plPart μ i.castSucc (lastIdx r) : ℤ) : ℝ) ∧
    (Even (segE X.F j i) →
      ((∑ c, (tanPart μ i.succ c - tanPart μ i.castSucc c) : ℤ) : ℝ) ≤ X.oc p K j (segE X.F j i)) ∧
    (¬ Even (segE X.F j i) →
      ((∑ c, (plPart μ i.castSucc c - plPart μ i.succ c) : ℤ) : ℝ) ≤ X.oc p K j (segE X.F j i))

def Tset [NeZero r] (j : ℤ) (b : ℤ → ℕ) : Type :=
  {q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) //
    ∃ dd, X.IsPATH p K j b q.1 dd ∧ X.IsGood p K j b q.1 ∧ IsSt (tanPart q.1) q.2}

def Idx [NeZero r] (j : ℤ) (b : ℤ → ℕ) : Type :=
  {q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ) //
    ∃ dd, X.IsPATH p K j b q.1 dd ∧ X.IsGood p K j b q.1 ∧ IsSt (tanPart q.1) q.2.1 ∧
      (∀ v, q.2.2 v + 2 * X.beS p K j b < X.Qc p K j) ∧
      ∀ (i : Fin (segN X.F j)) (i' : Fin r), segE X.F j i = X.F.fr j i'.val →
        dd i + ∑ c, q.2.2 (i', c) = b (X.F.fr j i'.val)}

omit [NeZero n'] in

def Dw (O : Type) [CommRing O] (j : ℤ) : MvPolynomial (ℤ × Fin r) O :=
  Matrix.det (Matrix.of fun a c : Fin r => (MvPolynomial.X (X.F.fr (j - 1) a.val, c) : MvPolynomial (ℤ × Fin r) O))

def famEl [NeZero r] (O : Type) [CommRing O] (j : ℤ) (b : ℤ → ℕ)
    (q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ)) : SegRing O r K :=
  plEmb O r K (X.Dw O j ^ X.m0 K *
      (∏ i : Fin r, MvPolynomial.X (X.F.fr (j - 1) i.val, (0 : Fin r)) ^
        ((b (X.F.fr (j - 1) i.val) : ℤ) - X.Bw p K j (X.F.fr (j - 1) i.val)).toNat) *
      ∏ v : Fin r × Fin r, MvPolynomial.X (X.F.fr j v.1.val, v.2) ^ q.2.2 v) *
    segRen X.F j O (r + K) (PsiPl O (plPart q.1) (Ican (plPart q.1)) * PsiTan O (tanPart q.1) q.2.1)

def BOK (j : ℤ) (b : ℤ → ℕ) : Prop :=
  (∀ x, x ∉ X.F.letters j → b x = 0) ∧
  (∀ x ∈ X.F.letters j, X.F.IsW j x → X.Bw p K j x ≤ (b x : ℤ)) ∧ X.AdmLL p K j b

end Dat

def RestMem (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.BOK p K j b → ∀ q : X.Idx p K j (X.restr j b), X.famEl p K O j b q.1 ∈ X.Mj p K O j b

def RestInd (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.BOK p K j b →
      LinearIndependent O fun q : X.Idx p K j (X.restr j b) => X.famEl p K O j b q.1

def RestFin : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (j : ℤ) (b : ℤ → ℕ), (∀ x, x ∉ X.F.letters j → b x = 0) →
    Module.Finite O (X.Mj p K O j b)

def GoodPathWeight (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r),
    X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.AdmLL p K j b → Finite (X.Tset p K j (X.restr j b)) ∧
      (1 - 1 / X.a ^ (X.Ns ^ 2)) *
        (∏ x ∈ X.F.LLset j, ((Nat.choose (b x + (r + K) - 1) (r + K - 1) : ℕ) : ℝ)) *
        (∏ i : Fin r, ((Nat.choose ((X.Bw p K j (X.F.fr (j - 1) i.val) - (X.m0 K : ℤ)).toNat + (r + K) - 1)
          (r + K - 1) : ℕ) : ℝ)) ≤ (Nat.card (X.Tset p K j (X.restr j b)) : ℝ)

open Classical in

def RestMon (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r),
    X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.AdmLL p K j b → Finite (X.Tset p K j (X.restr j b)) → ∀ ρ : Fin r → ℕ,
      (Nat.card (X.Tset p K j (X.restr j b)) : ℝ) *
          (((X.Qc p K j : ℕ) : ℝ) ^ (r - 1) * max 0 (1 - (r : ℝ) / (2 * X.Y))) ^ r ≤
        ∑ e ∈ Fintype.piFinset fun i : Fin r =>
          (Finset.range (r * X.Qc p K j)).filter fun e => e % X.Qc p K j = ρ i % X.Qc p K j,
            (Nat.card (X.Idx p K j (X.restr j (X.setTau j b e))) : ℝ)

theorem restSeg_of (C₀ : ℝ) (hM : RestMem C₀) (hI : RestInd C₀) (hF : RestFin) (hT : GoodPathWeight C₀) (hN : RestMon C₀) :
    RestSeg C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk j
  refine ⟨fun b => (Nat.card (X.Idx p K j (X.restr j b)) : ℝ), fun b => Nat.cast_nonneg _, ?_, ?_, ?_⟩
  · intro b b' hbb
    have : X.restr j b = X.restr j b' := by
      funext x
      unfold Dat.restr
      split_ifs with hx
      · exact hbb x hx
      · rfl
    simp only [this]
  · intro b h0 hW hA
    have hB : X.BOK p K j b := ⟨h0, hW, hA⟩
    have hfin := hF p n' r K X O j b h0
    have hli := hI p n' r K X O S hX hLa hk j b hB
    have hmem := hM p n' r K X O S hX hLa hk j b hB
    have hli' : LinearIndependent O
        (fun q : X.Idx p K j (X.restr j b) => (⟨X.famEl p K O j b q.1, hmem q⟩ : X.Mj p K O j b)) := by
      refine LinearIndependent.of_comp (X.Mj p K O j b).subtype ?_
      exact hli
    have hfinI : Finite (X.Idx p K j (X.restr j b)) := hli'.finite
    have := Fintype.ofFinite (X.Idx p K j (X.restr j b))
    have h := hli'.fintype_card_le_finrank
    beta_reduce
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast h
  · intro b hA ρ
    obtain ⟨hfin, hT1⟩ := hT p n' r K X hX hLa hk j b hA
    refine le_trans ?_ (hN p n' r K X hX hLa hk j b hA hfin ρ)
    unfold Dat.segBound
    exact mul_le_mul_of_nonneg_right hT1 (by positivity)

end Formalism.MainNotions.SelectionLemmas.Pf
