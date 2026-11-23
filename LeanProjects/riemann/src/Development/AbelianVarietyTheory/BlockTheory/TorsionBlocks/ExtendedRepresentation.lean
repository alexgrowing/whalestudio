import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Formalism.WeaklyAdmissibleFiltrations.Statement

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.JumpWindowClusters

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

def jumpWindow (up : Bool) (β S η : ℕ) : Set ℤ :=
  (if up = true then Set.Icc (β : ℤ) ((β : ℤ) + S) else Set.Icc (-(β : ℤ) - S) (-(β : ℤ))) ∪
    Set.Icc (-(η : ℤ)) (η : ℤ)

def Thick {n : ℕ} (size : ZMod n → ℕ) (b η : ℕ) (i : ZMod n) : Prop :=
  b ≤ size i ∧ size i ≤ b + η

def cycDist {n : ℕ} (x y : ZMod n) : ℕ := min (y - x).val (x - y).val

def IsClusterFrom {n : ℕ} (thick : ZMod n → Prop) (j : ℕ) (c : Set (ZMod n)) (f : ZMod n) : Prop :=
  thick f ∧ (c = {f} ∨ ∃ f' : ZMod n, f' ≠ f ∧ thick f' ∧ c = {f, f'} ∧
    (∀ q : ℕ, 0 < q → q < (f' - f).val → ¬ thick (f + (q : ZMod n))) ∧ cycDist f f' ≤ j)

def Clustered {n : ℕ} (thick : ZMod n → Prop) (j : ℕ) : Prop :=
  ∃ 𝒞 : Set (Set (ZMod n)),
    (∀ c ∈ 𝒞, ∃ f : ZMod n, IsClusterFrom thick j c f ∧
      ∀ q : ℕ, 1 ≤ q → q ≤ j → ¬ thick (f - (q : ZMod n))) ∧
    ∀ i : ZMod n, thick i → ∃! c : Set (ZMod n), c ∈ 𝒞 ∧ i ∈ c

def parG (w S η : ℕ) : ℕ := w + S + η

def parg (w S η : ℕ) : ℕ := max (parG w S η) 1

open Classical in

def parh {n : ℕ} (size : ZMod n → ℕ) (w S η b : ℕ) : ℕ :=
  if ∃ i, Thick size b η i then b + η + S else max (parG w S η) 1

def WordHyp (n : ℕ) (size : ZMod n → ℕ) (w S η b j : ℕ) : Prop :=
  1 ≤ j ∧
  (∀ i, ¬ Thick size b η i → size i ≤ w) ∧
  ((∃ i, Thick size b η i) → 40 * (j + 1) * (parG w S η + 1) ≤ b) ∧
  j + 1 ≤ n ∧
  Clustered (Thick size b η) j

def bound₁ (l n r j g h : ℕ) : ℝ :=
  ((n : ℝ) + 1) * r * (24 * (h : ℝ) / ((l : ℝ) - 1) ^ (j + 1) + 134 * (g : ℝ) * (3 * (j : ℝ)) +
    16 * Real.logb l h)

def bound₂ (l n r j G h : ℕ) : ℝ :=
  402 * ((n : ℝ) + 1) * r * ((h : ℝ) / ((l : ℝ) - 1) ^ (j + 1) + ((G : ℝ) + 1) * ((j : ℝ) + 1) +
    Real.logb l h)

variable {l : ℕ} [Fact l.Prime]

abbrev Lat (K LL : FinExt l) : Type 1 := LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)

def IsLetters (P : LocPrime l) (K : FinExt l) {L : Type} [Field L] [Algebra ℚ_[l] L] {n : ℕ}
    (τ : ZMod n → (↥K.1 →ₐ[ℚ_[l]] L)) : Prop :=
  Function.Bijective τ ∧
    ∀ (i : ZMod n) (x : ↥(K0 K)),
      τ (i + 1) (algebraMap ↥(K0 K) ↥K.1 ((P.PD K).σ x)) = τ i (algebraMap ↥(K0 K) ↥K.1 x)

def ColLeReal (P : LocPrime l) {K LL : FinExt l} {T₁ T₂ : Lat K LL} (F : LatHom T₁.L T₂.L)
    (β : ℝ) : Prop :=
  ∃ m k : ℕ, F.col (P.PD K) = m ∧ lenOl (P.PD K) (O := ↥(OL LL)) = k ∧ (m : ℝ) ≤ β * k

def Concl (P : LocPrime l) {K LL : FinExt l} {T₁ T₂ : Lat K LL} (F : LatHom T₁.L T₂.L)
    (n : ℕ) (size : ZMod n → ℕ) (w S η b j : ℕ) : Prop :=
  ColLeReal P F
      (bound₁ l n (Module.finrank ↥(OL LL) ↥T₂.L.T) j (parg w S η) (parh size w S η b)) ∧
    bound₁ l n (Module.finrank ↥(OL LL) ↥T₂.L.T) j (parg w S η) (parh size w S η b) ≤
      bound₂ l n (Module.finrank ↥(OL LL) ↥T₂.L.T) j (parG w S η) (parh size w S η b)

def LongOrbitAt (P : LocPrime l) (K LL : FinExt l) : Prop :=
  ∀ (n : ℕ), n = Module.finrank ℚ_[l] ↥K.1 →
  ∀ (τ : ZMod n → (↥K.1 →ₐ[ℚ_[l]] ↥LL.1)), IsLetters P K τ →
  ∀ (T₁ T₂ : Lat K LL) (F : LatHom T₁.L T₂.L),
    IsCrys (P.PD K) T₁.ρ → IsCrys (P.PD K) T₂.ρ → F.Onto →
  ∀ (w S η b j : ℕ) (up : ZMod n → Bool) (size : ZMod n → ℕ),
    (∀ i, JumpsInV (P.PD K) T₁.ρ (τ i) (jumpWindow (up i) (size i) S η)) →
    WordHyp n size w S η b j →
    Concl P F n size w S η b j

def LongOrbitColength (l : ℕ) [Fact l.Prime] (P : LocPrime l) : Prop :=
  11 ≤ l → ∀ (K LL : FinExt l), K.1 ≤ MaximalUnramifiedExtension l → LongOrbitAt P K LL

def LongOrbitColengthCaseA (l : ℕ) [Fact l.Prime] (P : LocPrime l) : Prop :=
  11 ≤ l → ∀ (K LL : FinExt l), CaseA K LL → LongOrbitAt P K LL

def extRep {K LL : FinExt l} (T : Lat K LL) :
    Representation (Om l) ↥(GK K) (Om l ⊗[↥LL.1] T.V) where
  toFun g := (T.ρ g).baseChange (Om l)
  map_one' := by rw [map_one]; exact LinearMap.baseChange_one _ _
  map_mul' g h := by rw [map_mul]; exact LinearMap.baseChange_mul _ _

def LongOrbitColengthAnyCoeff (l : ℕ) [Fact l.Prime] (P : LocPrime l) : Prop :=
  11 ≤ l → ∀ (K LL : FinExt l), K.1 ≤ MaximalUnramifiedExtension l →
  ∀ (n : ℕ), n = Module.finrank ℚ_[l] ↥K.1 →
  ∀ (τ : ZMod n → (↥K.1 →ₐ[ℚ_[l]] Om l)), IsLetters P K τ →
  ∀ (T₁ T₂ : Lat K LL) (F : LatHom T₁.L T₂.L),
    IsCrys (P.PD K) T₁.ρ → IsCrys (P.PD K) T₂.ρ → F.Onto →
  ∀ (w S η b j : ℕ) (up : ZMod n → Bool) (size : ZMod n → ℕ),
    (∀ i, JumpsInV (P.PD K) (extRep T₁) (τ i) (jumpWindow (up i) (size i) S η)) →
    WordHyp n size w S η b j →
    Concl P F n size w S η b j

example : WordHyp 3 (fun i => if i = 2 then 0 else 80) 0 0 0 80 1 := by
  have ht : ∀ i : ZMod 3, Thick (fun i => if i = 2 then 0 else 80) 80 0 i ↔ i ≠ 2 := by
    unfold Thick; decide
  refine ⟨le_rfl, ?_, fun _ => by simp [parG], by norm_num, {{0, 1}}, ?_, ?_⟩
  · intro i hi
    rw [ht, not_not] at hi
    simp [hi]
  · rintro c rfl
    refine ⟨0, ⟨(ht _).2 (by decide), Or.inr ⟨1, by decide, (ht _).2 (by decide), rfl, ?_, by decide⟩⟩, ?_⟩
    · intro q h0 h1
      have : ((1 : ZMod 3) - 0).val = 1 := by decide
      omega
    · intro q h0 h1
      obtain rfl : q = 1 := by omega
      rw [ht]; decide
  · intro i hi
    rw [ht] at hi
    refine ⟨{0, 1}, ⟨rfl, ?_⟩, fun c hc => hc.1⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    revert i; decide

end GlobalTheory.IndefiniteRowSideFullHecke.JumpWindowClusters
