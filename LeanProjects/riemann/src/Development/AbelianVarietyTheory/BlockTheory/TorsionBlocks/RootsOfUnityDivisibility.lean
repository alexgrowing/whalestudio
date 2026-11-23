import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.OneSquareLeaf.LeafOneSquareFree

noncomputable section

open NumberField IsDedekindDomain Finset
open Formalism.PairingDivisionLocalBalance (wt Pl)
open Formalism.DivisionValues (vw conjPl)
open Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts (SquareCoefficientsCondition)

namespace GlobalTheory.IndefiniteRowSideFullHecke.RootsOfUnityDivisibility

section Field

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def ValGe_vw (w : Pl K) (x : K) (t : ℝ) : Prop := x = 0 ∨ -t ≤ (vw w x : ℝ)

def IsRootOfOne (x : K) : Prop := ∃ n : ℕ, 0 < n ∧ x ^ n = 1

def DividesPow (q c : ℕ) (g : K) : Prop :=
  IsIntegral ℤ g ∧ ∃ g' : K, IsIntegral ℤ g' ∧ g * g' = (q : K) ^ c

def UnitAway (q : ℕ) (x : K) : Prop := x ≠ 0 ∧ ∀ w : Pl K, vw w (q : K) = 0 → vw w x = 0

def NewPlaceFactor (q : ℕ) (x : K) : Prop :=
  ∃ (g a : K) (c : ℕ) (n : ℤ), DividesPow q c g ∧ UnitAway q a ∧
    (x = g * (q : K) ^ n * a ∨ x = g⁻¹ * (q : K) ^ n * a)

def EpsShape {Sq : Type} (Q : Finset Sq) (qq : Sq → ℕ) (E : K) : Prop :=
  ∃ (ζ : K) (x : Sq → Fin 2 → K), IsRootOfOne ζ ∧ (∀ v ∈ Q, ∀ i, NewPlaceFactor (qq v) (x v i)) ∧
    E = ζ * ∏ v ∈ Q, ∏ i, x v i

def UShape {Sq : Type} (S0 Q : Finset Sq) (cc qq : Sq → ℕ) (U : K) : Prop :=
  ∃ (ζ : K) (g g' x : Sq → K), IsRootOfOne ζ ∧
    (∀ v ∈ S0, DividesPow (qq v) (cc v) (g v) ∧ DividesPow (qq v) (cc v) (g' v)) ∧
    (∀ v ∈ Q, NewPlaceFactor (qq v) (x v)) ∧
    U = ζ * (∏ v ∈ S0, g v / g' v) * ∏ v ∈ Q, x v

end Field

def classNorm {H : Type} {D : ℕ} (G : Matrix (Fin D) (Fin D) ℚ) (R : Finset H) (Γ : H → ℕ)
    (I : H → Fin D → ℂ) : ℂ :=
  ∑ x ∈ R, (∑ k, ∑ l, I x k * (starRingEnd ℂ) (I x l) * (G k l : ℂ)) / (Γ x : ℂ)

def SquareInputs {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) {Mu Sq H : Type}
    (μ0 : Mu) (μD : Bool → Mu) (μ : Pl K → Mu) (W1 : Set (Pl K)) (ch : Pl K → Bool)
    (S0 : Finset Sq) (QQ : Pl K → Finset Sq) (cc qq : Sq → ℕ) (Se Sd : Finset ℕ) (dl : Pl K → ℝ)
    (a' e p q : ℕ) (c c0 : Mu → ℂ) (u : Mu → ℕ → ℂ) (L eps : Mu → ℤ → ℂ) (Gam : ℤ → ℂ)
    (D : ℕ) (G : Matrix (Fin D) (Fin D) ℚ) (I I' : Mu → H → Fin D → ℂ) (R : Mu → Pl K → Finset H)
    (Γ : Mu → H → ℕ) (Om Om' A A' : ℂ)
    (zA zA' : K) (zT : ℤ → K) (zTd : Bool → ℤ → K) (zTw : Pl K → ℤ → K) (gT : ℤ → Pl K → ℤ)
    (N0 : ℤ → ℕ → ℝ) : Prop :=

  (2 * (p + q) + 1 < e ∧ 2 * (p + q) + 1 < a') ∧

  (Om ≠ 0 ∧ Om' ≠ 0 ∧ A ≠ 0 ∧ A' ≠ 0 ∧ G.PosDef ∧
    ∀ s ∈ Icc (1 - ((e : ℤ) + q - p)) 0, Gam s ≠ 0 ∧ Gam (1 - s) ≠ 0) ∧

  (∀ w : Pl K, ∀ ν : Mu, (ν = μ0 ∨ ν = μ w) →

    (∀ s ∈ Icc (1 : ℤ) ((a' : ℤ) + e), L ν s ≠ 0) ∧ (∀ k ∈ Icc 1 (p + q), u ν k ≠ 0) ∧

    c ν * ∏ k ∈ Icc (1 : ℤ) q, L ν (e + k) =
      (∏ k ∈ Icc 1 (p + q), u ν k) * c0 ν * ∏ k ∈ Icc (1 : ℤ) p, L ν ((e : ℤ) + q - k + 1) ∧

    ((∀ h k, I ν h k = c0 ν * I' ν h k) ∧ I ν ≠ 0 ∧ I' ν ≠ 0) ∧

    (∀ x ∈ R ν w, 0 < Γ ν x ∧
      (∀ k, ∃ z z' : K, I ν x k = Om * σ z ∧ I' ν x k = Om' * σ z' ∧
        ValGe_vw w z (dl w) ∧ ValGe_vw (conjPl w) z (dl w) ∧
        ValGe_vw w z' (dl w) ∧ ValGe_vw (conjPl w) z' (dl w)) ∧
      ∀ k l, ValGe_vw w (((G k l / (Γ ν x : ℚ) : ℚ)) : K) (dl w)) ∧

    classNorm G (R ν w) (Γ ν) (I ν) =
      A * ∏ s ∈ Icc (1 - ((e : ℤ) + q - p)) ((a' : ℤ) + e - (p + q)), L ν s ∧
    classNorm G (R ν w) (Γ ν) (I' ν) =
      A' * ∏ s ∈ Icc (1 + ((e : ℤ) + q - p)) ((a' : ℤ) + e - (p + q)), L ν s ∧

    (∀ s ∈ Icc (1 - ((e : ℤ) + q - p)) 0,
      eps ν s ≠ 0 ∧ Gam s * L ν s = eps ν s * Gam (1 - s) * L ν (1 - s))) ∧

  (∀ w : Pl K,
    σ zA * ((‖Om‖ ^ 2 : ℝ) : ℂ) = classNorm G (R μ0 w) (Γ μ0) (I μ0) ∧
    σ zA' * ((‖Om'‖ ^ 2 : ℝ) : ℂ) = classNorm G (R μ0 w) (Γ μ0) (I' μ0)) ∧

  (∀ s ∈ Icc (1 : ℤ) ((a' : ℤ) + e),
    zT s ≠ 0 ∧ (∀ l ∈ Sd, 0 ≤ N0 s l) ∧
    (∀ b, zTd b s ≠ 0 ∧ σ (zTd b s) * L μ0 s = σ (zT s) * L (μD b) s) ∧
    ∀ w : Pl K, -wt Sd (N0 s) w ≤ ((vw w (zT s) + gT s w : ℤ) : ℝ) ∧
      ∀ b, -wt Sd (N0 s) w ≤ ((vw w (zTd b s) + gT s w : ℤ) : ℝ)) ∧

  (∀ w ∈ W1,
    (∀ s ∈ Icc (1 : ℤ) ((a' : ℤ) + e),
      σ (zTw w s) * L μ0 s = σ (zT s) * L (μ w) s ∧
      -wt Sd (N0 s) w ≤ ((vw w (zTw w s) + gT s w : ℤ) : ℝ) ∧
      ((vw w (zTw w s) + gT s w : ℤ) : ℝ) ≤
        ((vw w (zTd (ch w) s) + gT s w : ℤ) : ℝ) + wt Se (fun l => 1 / (l : ℝ) ^ 2) w) ∧
    (∀ s ∈ Icc (1 - ((e : ℤ) + q - p)) 0,
      ∃ E : K, EpsShape (QQ w) qq E ∧ eps (μ w) s = σ E * eps μ0 s) ∧
    (∀ k ∈ Icc 1 (p + q), ∃ U : K, UShape S0 (QQ w) cc qq U ∧ u (μ w) k = σ U * u μ0 k))

def CommonInputs {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) {Mu Sq : Type}
    (μ0 : Mu) (μ : Pl K → Mu) (W1 : Set (Pl K)) (S0 : Finset Sq) (QQ : Pl K → Finset Sq)
    (cc qq ee : Sq → ℕ) (Se Sd : Finset ℕ) (dl : Pl K → ℝ) : Prop :=
  (∀ x : K, σ (star x) = (starRingEnd ℂ) (σ x)) ∧
  (∀ w, w ∉ W1 → μ w = μ0) ∧
  (∀ v ∈ S0, IsPrimePow (qq v) ∧ cc v ≤ ee v) ∧
  (∀ w ∈ W1, Disjoint (QQ w) S0 ∧ ∀ v ∈ QQ w, IsPrimePow (qq v) ∧ vw w (qq v : K) = 0) ∧
  (∀ l ∈ Se, l.Prime) ∧ (∀ l ∈ Sd, l.Prime) ∧
  (∀ w, 0 ≤ dl w ∧ dl (conjPl w) = dl w)

def ValuationOfRatio : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (m N : ℕ) (Mu Sq : Type)
    (H : Fin m × Fin m → Type)
    (μ0 : Mu) (μD : Bool → Mu) (μ : Pl K → Mu) (W1 : Set (Pl K)) (ch : Pl K → Bool)
    (S0 : Finset Sq) (QQ : Pl K → Finset Sq) (cc qq ee : Sq → ℕ) (Se Sd : Finset ℕ) (dl : Pl K → ℝ)
    (a' e p q : Fin m × Fin m → ℕ) (c c0 : Fin m × Fin m → Mu → ℂ) (u : Fin m × Fin m → Mu → ℕ → ℂ)
    (L eps : Fin m × Fin m → Mu → ℤ → ℂ) (Gam : Fin m × Fin m → ℤ → ℂ)
    (D : Fin m × Fin m → ℕ) (G : ∀ ij, Matrix (Fin (D ij)) (Fin (D ij)) ℚ)
    (I I' : ∀ ij, Mu → H ij → Fin (D ij) → ℂ) (R : ∀ ij, Mu → Pl K → Finset (H ij))
    (Γ : ∀ ij, Mu → H ij → ℕ) (Om Om' A A' : Fin m × Fin m → ℂ)
    (zA zA' : Fin m × Fin m → K) (zT : Fin m × Fin m → ℤ → K) (zTd : Fin m × Fin m → Bool → ℤ → K)
    (zTw : Fin m × Fin m → Pl K → ℤ → K) (gT : Fin m × Fin m → ℤ → Pl K → ℤ)
    (N0 : Fin m × Fin m → ℤ → ℕ → ℝ)
    (r0 : Fin m × Fin m → K) (rw : Pl K → Fin m × Fin m → K),
    CommonInputs σ μ0 μ W1 S0 QQ cc qq ee Se Sd dl →
    (∀ ij, SquareInputs σ μ0 μD μ W1 ch S0 QQ cc qq Se Sd dl (a' ij) (e ij) (p ij) (q ij)
      (c ij) (c0 ij) (u ij) (L ij) (eps ij) (Gam ij) (D ij) (G ij) (I ij) (I' ij) (R ij) (Γ ij)
      (Om ij) (Om' ij) (A ij) (A' ij) (zA ij) (zA' ij) (zT ij) (zTd ij) (zTw ij) (gT ij) (N0 ij)) →

    (∀ ij, (a' ij + 2 * e ij) + a' ij ≤ 2 * N) → (∀ ij, p ij + q ij + 1 ≤ m) →

    (∀ ij, σ (r0 ij) * c ij μ0 = c ij μ0) →
    (∀ w ij, σ (rw w ij) * c ij μ0 = c ij (μ w)) →
    SquareCoefficientsCondition r0 rw Se Sd (fun ij => (a' ij + 2 * e ij) + a' ij) (fun ij => a' ij + e ij)
      (fun ij => p ij + q ij) N S0 cc qq ee zA zA' zT zTd gT ch N0 dl

def RatioInField : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (Mu Sq H : Type)
    (μ0 : Mu) (μD : Bool → Mu) (μ : Pl K → Mu) (W1 : Set (Pl K)) (ch : Pl K → Bool)
    (S0 : Finset Sq) (QQ : Pl K → Finset Sq) (cc qq ee : Sq → ℕ) (Se Sd : Finset ℕ) (dl : Pl K → ℝ)
    (a' e p q : ℕ) (c c0 : Mu → ℂ) (u : Mu → ℕ → ℂ) (L eps : Mu → ℤ → ℂ) (Gam : ℤ → ℂ)
    (D : ℕ) (G : Matrix (Fin D) (Fin D) ℚ) (I I' : Mu → H → Fin D → ℂ) (R : Mu → Pl K → Finset H)
    (Γ : Mu → H → ℕ) (Om Om' A A' : ℂ)
    (zA zA' : K) (zT : ℤ → K) (zTd : Bool → ℤ → K) (zTw : Pl K → ℤ → K) (gT : ℤ → Pl K → ℤ)
    (N0 : ℤ → ℕ → ℝ),
    CommonInputs σ μ0 μ W1 S0 QQ cc qq ee Se Sd dl →
    SquareInputs σ μ0 μD μ W1 ch S0 QQ cc qq Se Sd dl a' e p q c c0 u L eps Gam D G I I' R Γ
      Om Om' A A' zA zA' zT zTd zTw gT N0 →
    c μ0 ≠ 0 ∧ ∀ w, ∃ r : K, r ≠ 0 ∧ σ r * c μ0 = c (μ w)

section Basic₂

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem vw_one' (w : Pl K) : vw w (1 : K) = 0 := by
  simp [vw, FractionalIdeal.count_one]

example (σ : K →+* ℂ) :
    SquareInputs σ (Mu := Unit) (Sq := Unit) (H := Unit) () (fun _ => ()) (fun _ => ()) Set.univ
      (fun _ => true) ∅ (fun _ => ∅) (fun _ => 0) (fun _ => 2) ∅ ∅ (fun _ => 0) 6 6 1 1
      (fun _ => 3) (fun _ => 3) (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 1) (fun _ => 1)
      1 1 (fun _ _ _ => 3) (fun _ _ _ => 1) (fun _ _ => {()}) (fun _ _ => 1) 3 1 9 1
      1 1 (fun _ => 1) (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => 0) := by
  refine ⟨by norm_num, ⟨by norm_num, by norm_num, by norm_num, by norm_num, Matrix.PosDef.one, by simp⟩,
    ?_, ?_, ?_, ?_⟩
  · intro w ν _
    refine ⟨by simp, by simp, by simp, ⟨by simp, ?_, ?_⟩, ?_, ?_, ?_, by simp⟩
    · intro h; have := congrFun (congrFun h ()) 0; simp at this
    · intro h; have := congrFun (congrFun h ()) 0; simp at this
    · intro x _
      refine ⟨one_pos, fun k => ⟨1, 1, by simp, by simp, ?_, ?_, ?_, ?_⟩, fun k l => ?_⟩
      all_goals first
        | (right; simp [vw_one']; done)
        | (right; rw [Subsingleton.elim k l]; simp [vw_one'])
    · simp [classNorm, map_ofNat]; norm_num
    · simp [classNorm]
  · intro w
    constructor
    · simp [classNorm, map_ofNat]; norm_num
    · simp [classNorm]
  · intro s _
    simp [wt, vw_one']
  · intro w _
    refine ⟨fun s _ => by simp [wt, vw_one'], fun s _ => ⟨1, ⟨1, fun _ _ => 1, ⟨1, one_pos, by simp⟩, by simp, by simp⟩, by simp⟩,
      fun k _ => ⟨1, ⟨1, fun _ => 1, fun _ => 1, fun _ => 1, ⟨1, one_pos, by simp⟩, by simp, by simp, by simp⟩, by simp⟩⟩

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.RootsOfUnityDivisibility
