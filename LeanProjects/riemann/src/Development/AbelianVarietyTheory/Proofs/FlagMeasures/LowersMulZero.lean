import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst

open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.RadCov

section Defs

variable {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {n : ℕ}

def lowers (F : ℕ → Submodule R (Fin n → K)) (c : ℕ) : Submodule R (Matrix (Fin n) (Fin n) K) where
  carrier := {T | ∀ b, ∀ y ∈ F (b + c + 1), T *ᵥ y ∈ F b}
  zero_mem' := fun b y _ => by simp
  add_mem' := fun {S T} hS hT b y hy => by
    rw [Matrix.add_mulVec]
    exact add_mem (hS b y hy) (hT b y hy)
  smul_mem' := fun r T hT b y hy => by
    rw [Matrix.smul_mulVec]
    exact Submodule.smul_mem _ _ (hT b y hy)

theorem mem_lowers {F : ℕ → Submodule R (Fin n → K)} {c : ℕ} {T : Matrix (Fin n) (Fin n) K} :
    T ∈ lowers F c ↔ ∀ b, ∀ y ∈ F (b + c + 1), T *ᵥ y ∈ F b := Iff.rfl

def IsDualFlag [StarRing K] (J : Matrix (Fin n) (Fin n) K) (F : ℕ → Submodule R (Fin n → K)) (m : ℕ) : Prop :=
  Monotone F ∧ F 0 = ⊥ ∧ (∀ b, m ≤ b → F b = F m) ∧
    ∀ b, b ≤ m → ∀ y, y ∈ F (m - b) ↔ y ∈ F m ∧ ∀ x ∈ F b, star x ⬝ᵥ (J *ᵥ y) = 0

def Biorth (r : ℕ → ℕ) (m : ℕ) (T : ∀ b, Matrix (Fin n) (Fin (r b)) K)
    (T' : ∀ b, Matrix (Fin (r b)) (Fin n) K) : Prop :=
  (∀ b, T' b * T b = 1) ∧ (∀ b b', b ≠ b' → T' b * T b' = 0) ∧ ∑ b ∈ Finset.range m, T b * T' b = 1

theorem lowers_succ_le {F : ℕ → Submodule R (Fin n → K)} (hF : Monotone F) (c : ℕ) :
    lowers F (c + 1) ≤ lowers F c := by
  intro T hT
  rw [mem_lowers] at hT ⊢
  intro b y hy
  exact hT b y (hF (by omega) hy)

theorem lowers_anti {F : ℕ → Submodule R (Fin n → K)} (hF : Monotone F) : Antitone (lowers F) :=
  antitone_nat_of_succ_le (lowers_succ_le hF)

theorem lowers_mul {F : ℕ → Submodule R (Fin n → K)} {c c' : ℕ} {X Y : Matrix (Fin n) (Fin n) K}
    (hX : X ∈ lowers F c) (hY : Y ∈ lowers F c') : X * Y ∈ lowers F (c + c' + 1) := by
  rw [mem_lowers] at hX hY ⊢
  intro b y hy
  rw [← Matrix.mulVec_mulVec]
  apply hX b
  apply hY (b + c + 1)
  have e : b + c + 1 + c' + 1 = b + (c + c' + 1) + 1 := by omega
  rw [e]
  exact hy

theorem lowers_mul_zero {F : ℕ → Submodule R (Fin n → K)} {c : ℕ} {X Y : Matrix (Fin n) (Fin n) K}
    (hX : X ∈ lowers F c) (hY : Y ∈ lowers F 0) :
    X * Y ∈ lowers F (c + 1) ∧ Y * X ∈ lowers F (c + 1) := by
  have h1 := lowers_mul hX hY
  have h2 := lowers_mul hY hX
  rw [Nat.add_zero] at h1
  rw [Nat.zero_add] at h2
  exact ⟨h1, h2⟩

theorem lowers_eq_bot {F : ℕ → Submodule R (Fin n → K)} {m : ℕ} (h0 : F 0 = ⊥)
    (hm : ∀ b, m ≤ b → F b = F m) (hsp : Submodule.span K (F m : Set (Fin n → K)) = ⊤) :
    lowers F m = ⊥ := by
  rw [eq_bot_iff]
  intro T hT
  rw [mem_lowers] at hT
  have hzero : ∀ y ∈ (F m : Set (Fin n → K)), T *ᵥ y = 0 := by
    intro y hy
    have hy' : y ∈ F (0 + m + 1) := by
      rw [hm (0 + m + 1) (by omega)]
      exact hy
    have h := hT 0 y hy'
    rw [h0] at h
    exact (Submodule.mem_bot R).1 h
  have hlin : Matrix.toLin' T = 0 := by
    apply LinearMap.ext_on hsp
    intro y hy
    simpa [Matrix.toLin'_apply] using hzero y hy
  have hT0 : T = 0 := by
    apply Matrix.toLin'.injective
    rw [hlin, map_zero]
  exact (Submodule.mem_bot R).2 hT0

theorem lowers_adj [StarRing K] {J : Matrix (Fin n) (Fin n) K} (hJ : Jᴴ = J)
    {F : ℕ → Submodule R (Fin n → K)} {m : ℕ} (hF : IsDualFlag J F m) {c : ℕ}
    {T T' : Matrix (Fin n) (Fin n) K} (hT : T ∈ lowers F c) (hadj : J * T' = Tᴴ * J)
    (htop : ∀ y ∈ F m, T' *ᵥ y ∈ F m) : T' ∈ lowers F c := by
  obtain ⟨hmono, h0, hstab, hdual⟩ := hF
  have hleM : ∀ k, F k ≤ F m := by
    intro k
    rcases le_total k m with h | h
    · exact hmono h
    · exact (hstab k h).le
  rw [mem_lowers] at hT ⊢
  intro b y hy
  have hyM : y ∈ F m := hleM _ hy
  rcases le_total m b with hb | hb
  · rw [hstab b hb]
    exact htop y hyM
  ·
    have key : ∀ x ∈ F (m - b), star x ⬝ᵥ (J *ᵥ (T' *ᵥ y)) = 0 := by
      intro x hx
      have e : star x ⬝ᵥ (J *ᵥ (T' *ᵥ y)) = star (T *ᵥ x) ⬝ᵥ (J *ᵥ y) := by
        rw [Matrix.mulVec_mulVec, hadj, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
          Matrix.star_mulVec]
      rw [e]
      rcases le_or_gt (b + c + 1) m with hc | hc
      · have hTx : T *ᵥ x ∈ F (m - (b + c + 1)) := by
          apply hT
          have e' : m - (b + c + 1) + c + 1 = m - b := by omega
          rw [e']
          exact hx
        have hy' : y ∈ F (m - (m - (b + c + 1))) := by
          rw [show m - (m - (b + c + 1)) = b + c + 1 by omega]
          exact hy
        exact ((hdual _ (Nat.sub_le _ _) y).1 hy').2 _ hTx
      ·
        have hTx : T *ᵥ x ∈ F 0 := hT 0 x (hmono (by omega) hx)
        rw [h0] at hTx
        rw [(Submodule.mem_bot R).1 hTx, star_zero, zero_dotProduct]
    have hd := hdual (m - b) (Nat.sub_le _ _) (T' *ᵥ y)
    rw [show m - (m - b) = b by omega] at hd
    exact hd.2 ⟨htop y hyM, key⟩

end Defs

section Loc

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def locFlag (φ : E →+* ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (b : ℕ) :
    Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ ((fun y : Fin n → E => P⁻¹ *ᵥ fun l => φ (y l)) '' (F b : Set _))

def PlaceMatch {ι : Type} (φ : ι → E →+* ℂ) (P : ι → Matrix (Fin n) (Fin n) ℂ)
    (X : InfinitePlace E → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  Function.Bijective (fun v => InfinitePlace.mk (φ v)) ∧
    ∀ v, ((InfinitePlace.mk (φ v)).embedding = φ v ∧ X (InfinitePlace.mk (φ v)) = P v) ∨
      ((InfinitePlace.mk (φ v)).embedding = (starRingEnd ℂ).comp (φ v) ∧
        X (InfinitePlace.mk (φ v)) = (P v).map (starRingEnd ℂ))

def pieceHt [StarRing E] (X : InfinitePlace E → Matrix (Fin n) (Fin n) ℂ)
    (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (b : ℕ) : ℝ :=
  Formalism.HN.ht (Pi.basisFun E (Fin n)) X (F (b + 1)) / Formalism.HN.ht (Pi.basisFun E (Fin n)) X (F b)

def covStd (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)) : ℝ :=
  GlobalTheory.FlagBase.covAt E j (GlobalTheory.FlagBase.latAt E j Λ fun _ a b => if a = b then 1 else 0)

end Loc

end GlobalTheory.RadCov
