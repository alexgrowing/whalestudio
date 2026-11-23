import Formalism.ThetaLogCoordinates.DualWeylCoordinates.StatementC

noncomputable section

open MvPolynomial Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Classical in

def strUp {n : ℕ} (mu : Fin n → ℤ) (b : ℕ) : Finset (Fin n → ℤ) :=
  (Fintype.piFinset fun i => Finset.Icc (mu i) (mu i + b)).filter fun nu => HStrip mu nu b

open Classical in

def strDown {n : ℕ} (mu : Fin n → ℤ) (b : ℕ) : Finset (Fin n → ℤ) :=
  (Fintype.piFinset fun i => Finset.Icc (mu i - b) (mu i)).filter fun nu => HStrip nu mu b

open Classical in

def strVert {n : ℕ} (mu : Fin n → ℤ) (b : ℕ) : Finset (Fin n → ℤ) :=
  (Fintype.piFinset fun i => Finset.Icc (mu i) (mu i + 1)).filter fun nu =>
    Dominant nu ∧ ∑ a, (nu a - mu a) = (b : ℤ)

def IsStripData {n : ℕ} [NeZero n] {κ : Type} [Fintype κ] [DecidableEq κ] (B : Matrix κ κ (GLCoord ℤ n))
    (be : κ → Fin n → ℤ) (Str : (Fin n → ℤ) → Finset (Fin n → ℤ))
    (ps : (mu nu : Fin n → ℤ) → Matrix (TIdx mu × κ) (TIdx nu) ℤ) : Prop :=
  Function.Injective be ∧
  (∀ k l, evGL (torusPt n) (B k l) = if k = l then AddMonoidAlgebra.single (be k) 1 else 0) ∧
  (∀ mu, Dominant mu → ∀ nu ∈ Str mu, Dominant nu) ∧
  (∀ mu, Dominant mu → ∀ nu ∈ Str mu,
    (Matrix.of fun (x y : TIdx mu × κ) => TMat mu x.1 y.1 * B x.2 y.2) * (ps mu nu).map (Int.castRingHom _) =
      (ps mu nu).map (Int.castRingHom _) * TMat nu) ∧
  (∀ mu, Dominant mu → ∀ nu ∈ Str mu, ∃ k0, be k0 = nu - mu ∧
    (ps mu nu (canT mu, k0) (canT nu) = 1 ∨ ps mu nu (canT mu, k0) (canT nu) = -1)) ∧
  (∀ mu, Dominant mu → dMu mu * Fintype.card κ = ∑ nu ∈ Str mu, dMu nu)

def StripDataTensorColumnFamilies : Prop :=
  ∀ (n : ℕ) [NeZero n] (κ : Type) [Fintype κ] [DecidableEq κ] (B : Matrix κ κ (GLCoord ℤ n))
    (be : κ → Fin n → ℤ) (Str : (Fin n → ℤ) → Finset (Fin n → ℤ))
    (ps : (mu nu : Fin n → ℤ) → Matrix (TIdx mu × κ) (TIdx nu) ℤ), IsStripData B be Str ps →
    ∀ (M M' : GLMod n) (e : M'.ι ≃ M.ι × κ), IsTensor M M' B e → Nonempty (ColFam M) → Nonempty (ColFam M')

def SymStrip : Prop :=
  ∀ (n : ℕ) [NeZero n] (b : ℕ), ∃ be ps, IsStripData (SymMat n b) be (fun mu => strUp mu b) ps

def SymDStrip : Prop :=
  ∀ (n : ℕ) [NeZero n] (b : ℕ), ∃ be ps, IsStripData (SymDMat n b) be (fun mu => strDown mu b) ps

def LamStrip : Prop :=
  ∀ (n : ℕ) [NeZero n] (b : ℕ), ∃ be ps, IsStripData (LamMat n b) be (fun mu => strVert mu b) ps

def CntSym : Prop :=
  ∀ (n : ℕ) [NeZero n] (mu : Fin n → ℤ) (b : ℕ), Dominant mu →
    dMu mu * Fintype.card (SymIdx n b) = ∑ nu ∈ strUp mu b, dMu nu

def CntSymD : Prop :=
  ∀ (n : ℕ) [NeZero n] (mu : Fin n → ℤ) (b : ℕ), Dominant mu →
    dMu mu * Fintype.card (SymIdx n b) = ∑ nu ∈ strDown mu b, dMu nu

def CntLam : Prop :=
  ∀ (n : ℕ) [NeZero n] (mu : Fin n → ℤ) (b : ℕ), Dominant mu →
    dMu mu * Fintype.card (LamIdx n b) = ∑ nu ∈ strVert mu b, dMu nu

def CntBranch : Prop :=
  ∀ (m : ℕ) [NeZero m] (lam : Fin (m + 1) → ℤ), Dominant lam → ∀ Sg : Finset (Fin m → ℤ),
    (∀ nu : Fin m → ℤ, nu ∈ Sg ↔ Dominant nu ∧ Interl lam nu) → dMu lam = ∑ nu ∈ Sg, dMu nu

theorem closure_tensor_of_strip_data (h : StripDataTensorColumnFamilies) (h1 : SymStrip) (h2 : SymDStrip) (h3 : LamStrip) : ClosureTensorPowers := by
  intro n _ M M' b hM
  refine ⟨fun e he => ?_, fun e he => ?_, fun e he => ?_⟩
  · obtain ⟨be, ps, hd⟩ := h1 n b
    exact h n _ _ be _ ps hd M M' e he hM
  · obtain ⟨be, ps, hd⟩ := h2 n b
    exact h n _ _ be _ ps hd M M' e he hM
  · obtain ⟨be, ps, hd⟩ := h3 n b
    exact h n _ _ be _ ps hd M M' e he hM

end Formalism.InvariantFactorPaths.ColumnFamilies
