import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Coarse

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

def Pz (j x : ℤ) : ℕ := p ^ (X.F.dist j x + X.Rj p K j)

open Classical in

def laSet (t : Fin n') : Finset (Fin (r + K) → ℕ) :=
  (Fintype.piFinset fun _ : Fin (r + K) => Finset.range (X.a' p K t + 1)).filter fun v =>
    ∑ c, v c ≤ X.a' p K t ∧ ∀ j : ℤ, ∀ x ∈ X.toLate j, posOf n' x = t →
      (∀ c, v c < X.Pz p K j x) ∧ (∑ c, v c) % X.Pz p K j x = X.a' p K t % X.Pz p K j x

def LA : Finset (Fin n' → Fin (r + K) → ℕ) := Fintype.piFinset (X.laSet p K)

def nz (la : Fin n' → Fin (r + K) → ℕ) (j x : ℤ) : ℕ :=
  (X.a' p K (posOf n' x) - ∑ c, la (posOf n' x) c) / X.Pz p K j x

open Classical in

def EE (la : Fin n' → Fin (r + K) → ℕ) : Finset (Fin X.F.J → Fin r → ℕ) :=
  Fintype.piFinset fun j : Fin X.F.J => Fintype.piFinset fun i : Fin r =>
    (Finset.range (r * X.Qc p K (j.val : ℤ))).filter fun e =>
      e % X.Qc p K (j.val : ℤ) = X.nz p K la (j.val : ℤ) (X.F.fr (j.val : ℤ) i.val) % X.Qc p K (j.val : ℤ)

omit [NeZero n'] in

def eZ (e : Fin X.F.J → Fin r → ℕ) (j : ℤ) : Fin r → ℕ :=
  if h : 0 < X.F.J then e ⟨(j % (X.F.J : ℤ)).toNat % X.F.J, Nat.mod_lt _ h⟩ else 0

open Classical in

def bfam (la : Fin n' → Fin (r + K) → ℕ) (e : Fin X.F.J → Fin r → ℕ) (j : ℤ) : ℤ → ℕ := fun x =>
  if x ∈ X.F.letters j then
    if X.F.IsW j x then
      ∑ i : Fin r, if x = X.F.fr (j - 1) i.val then
        (X.nz p K la (j - 1) x - X.eZ e (j - 1) i) / X.Qc p K (j - 1) else 0
    else if X.F.fr j 0 ≤ x then ∑ i : Fin r, if x = X.F.fr j i.val then X.eZ e j i else 0
    else X.nz p K la j x
  else 0

open Classical in

def setTau (j : ℤ) (b : ℤ → ℕ) (e : Fin r → ℕ) : ℤ → ℕ := fun x =>
  if X.F.fr j 0 ≤ x ∧ x ≤ X.F.fr j (r - 1) then ∑ i : Fin r, if x = X.F.fr j i.val then e i else 0 else b x

def AdmLL (j : ℤ) (b : ℤ → ℕ) : Prop :=
  ∀ x ∈ X.F.LLset j, (X.a' p K (posOf n' x) : ℝ) / (X.Pz p K j x : ℝ) - k (r := r) K < (b x : ℝ) ∧
    (b x : ℝ) ≤ (X.a' p K (posOf n' x) : ℝ) / (X.Pz p K j x : ℝ)

def segBound (j : ℤ) (b : ℤ → ℕ) : ℝ :=
  (1 - 1 / X.a ^ (X.Ns ^ 2)) *
    (∏ x ∈ X.F.LLset j, ((Nat.choose (b x + (r + K) - 1) (r + K - 1) : ℕ) : ℝ)) *
    (∏ i : Fin r, ((Nat.choose ((X.Bw p K j (X.F.fr (j - 1) i.val) - (X.m0 K : ℤ)).toNat + (r + K) - 1) (r + K - 1) : ℕ) : ℝ)) *
    (((X.Qc p K j : ℕ) : ℝ) ^ (r - 1) * max 0 (1 - (r : ℝ) / (2 * X.Y))) ^ r

open Classical in

def SegOK [NeZero r] [NeZero K] (O : Type) [CommRing O] (j : ℤ) (G : (ℤ → ℕ) → ℝ) : Prop :=
  (∀ b, 0 ≤ G b) ∧
  (∀ b b' : ℤ → ℕ, (∀ x ∈ X.toLate j, b x = b' x) → G b = G b') ∧
  (∀ b : ℤ → ℕ, (∀ x, x ∉ X.F.letters j → b x = 0) →
    (∀ x ∈ X.F.letters j, X.F.IsW j x → X.Bw p K j x ≤ (b x : ℤ)) → X.AdmLL p K j b →
    G b ≤ (Module.finrank O (X.Mj p K O j b) : ℝ)) ∧
  (∀ b : ℤ → ℕ, X.AdmLL p K j b → ∀ ρ : Fin r → ℕ,
    X.segBound p K j b ≤ ∑ e ∈ Fintype.piFinset fun i : Fin r =>
      (Finset.range (r * X.Qc p K j)).filter fun e => e % X.Qc p K j = ρ i % X.Qc p K j, G (X.setTau j b e))

end Dat

def RestLam (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∑ la ∈ X.LA p K, ∑ e ∈ X.EE p K la, ∏ j : Fin X.F.J,
        Module.finrank O (X.Mj p K O (j.val : ℤ) (X.bfam p K la e (j.val : ℤ))) ≤
      Module.finrank (FF O) (X.LamBar p K O)

def RestSeg (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ j : ℤ, ∃ G : (ℤ → ℕ) → ℝ, X.SegOK p K O j G

def RestPad (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r),
    X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ la ∈ X.LA p K, ∀ e ∈ X.EE p K la, ∀ j : ℤ,
      (∀ x ∈ X.F.letters j, X.F.IsW j x → X.Bw p K j x ≤ (X.bfam p K la e j x : ℤ)) ∧
      X.AdmLL p K j (X.bfam p K la e j)

def RestSum (C₀ Crk : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r),
    X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ G : ℤ → (ℤ → ℕ) → ℝ,
      (∀ j b, 0 ≤ G j b) →
      (∀ j, ∀ b b' : ℤ → ℕ, (∀ x ∈ X.toLate j, b x = b' x) → G j b = G j b') →
      (∀ j, ∀ b : ℤ → ℕ, X.AdmLL p K j b → ∀ ρ : Fin r → ℕ,
        X.segBound p K j b ≤ ∑ e ∈ Fintype.piFinset fun i : Fin r =>
          (Finset.range (r * X.Qc p K j)).filter fun e => e % X.Qc p K j = ρ i % X.Qc p K j,
            G j (X.setTau j b e)) →
      ((p : ℝ) ^ n') ^ (-((r * K : ℕ) : ℤ)) * X.bound K Crk ≤
        ∑ la ∈ X.LA p K, ∑ e ∈ X.EE p K la, ∏ j : Fin X.F.J, G (j.val : ℤ) (X.bfam p K la e (j.val : ℤ))

theorem restCount_of (C₀ Crk : ℝ) (hL : RestLam C₀) (hS : RestSeg C₀) (hP : RestPad C₀) (hSum : RestSum C₀ Crk) :
    RestCount C₀ Crk := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk
  choose G hG using hS p n' r K X O S hX hLa hk
  refine le_trans (hSum p n' r K X hX hLa hk G (fun j => (hG j).1) (fun j => (hG j).2.1) (fun j => (hG j).2.2.2)) ?_
  refine le_trans ?_ (Nat.cast_le.mpr (hL p n' r K X O S hX hLa hk))
  push_cast
  refine Finset.sum_le_sum fun la hla => Finset.sum_le_sum fun e he => ?_
  refine Finset.prod_le_prod (fun j _ => (hG _).1 _) fun j _ => ?_
  obtain ⟨h1, h2⟩ := hP p n' r K X hX hLa hk la hla e he (j.val : ℤ)
  refine (hG _).2.2.1 _ ?_ h1 h2
  intro x hx
  simp [Dat.bfam, hx]

end Formalism.MainNotions.SelectionLemmas.Pf
