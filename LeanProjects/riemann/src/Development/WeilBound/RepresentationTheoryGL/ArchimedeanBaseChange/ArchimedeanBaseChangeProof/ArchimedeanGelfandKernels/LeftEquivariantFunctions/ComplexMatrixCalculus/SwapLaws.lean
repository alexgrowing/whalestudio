import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InstBorelUK

noncomputable section

open Matrix
open scoped ComplexConjugate Kronecker ContDiff

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def HbOrtho : Prop := ∀ n : ℕ, (∀ p q : Md n, (hbM p * hbM q).trace = if p = q then 1 else 0) ∧ ∀ p : Md n, (hbM p).IsHermitian

def HbExp : Prop := ∀ (n : ℕ) (H : Mat n), H.IsHermitian → H = ∑ m, cf n H m • hbM m

def CfPair : Prop := ∀ (n : ℕ) (H H' : Mat n), H.IsHermitian → H'.IsHermitian → ∑ m, cf n H m * cf n H' m = (H * H').trace

def MtLaws : Prop := ∀ n : ℕ, Mt (1 : Mat n) = 1 ∧ (∀ x y : Mat n, Mt (x * y) = Mt x * Mt y) ∧
  (∀ (x H : Mat n), H.IsHermitian → Mt x *ᵥ cf n H = cf n (x * H * xᴴ)) ∧
  (∀ (x H : Mat n), H.IsHermitian → (Mt x)ᵀ *ᵥ cf n H = cf n (xᴴ * H * x))

def GamMul : Prop := ∀ n : ℕ, gamM (1 : Matrix (Md n) (Md n) ℂ) = 1 ∧ ∀ g h : Matrix (Md n) (Md n) ℂ, gamM (g * h) = gamM g * gamM h

def Car : Prop := ∀ (n : ℕ) (v w : Md n → ℂ), annL n w * creL n v + creL n v * annL n w = (w ⬝ᵥ v) • 1

def GamCre : Prop := ∀ (n : ℕ) (g : Matrix (Md n) (Md n) ℂ) (v w : Md n → ℂ),
  gamM g * creL n v = creL n (g *ᵥ v) * gamM g ∧ annL n w * gamM g = gamM g * annL n (gᵀ *ᵥ w)

def GamScal : Prop := ∀ (n : ℕ) (s : ℂ), gamM (s • (1 : Matrix (Md n) (Md n) ℂ)) = Matrix.diagonal fun A => s ^ A.card

def Number : Prop := ∀ (n : ℕ) (s : ℂ),
  ∑ m : Md n, creL n (Pi.single m 1) * gamM (s • (1 : Matrix (Md n) (Md n) ℂ)) * annL n (Pi.single m 1) =
    Matrix.diagonal fun A => (A.card : ℂ) * s ^ (A.card - 1)

def GamDer : Prop := ∀ n : ℕ, ContDiff ℂ ∞ (gamM (n := n)) ∧
  ∀ B : Matrix (Md n) (Md n) ℂ, fderiv ℂ (gamM (n := n)) 1 B = ∑ r, ∑ s, B r s • (creL n (Pi.single r 1) * annL n (Pi.single s 1))

def RmLaws : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), Rm lam (1 : Mat n) = 1 ∧
  (∀ x y : Mat n, IsUnit x.det → IsUnit y.det → Rm lam (x * y) = Rm lam x * Rm lam y) ∧ ContDiffOn ℝ ∞ (Rm lam) (GLs n)

def RmChar : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ t : Fin n → ℂ, (∀ a, t a ≠ 0) → Function.Injective t →
  (Rm lam (diagonal t)).trace = weylChar lam t

def RmHol : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ (M : Matrix (Jd n lam) (Jd n lam) ℂ) (i j : Jd n lam),
  ∀ g ∈ GLs n, (∀ m, gel true m (fun x => (Rm lam x * M) i j) g = GlobalTheory.Dec.gelfVal (infOf lam true) m * (Rm lam g * M) i j) ∧
    ∀ a b, Eu false a b (fun x => (Rm lam x * M) i j) g = 0

def RmAnti : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ (M : Matrix (Jd n lam) (Jd n lam) ℂ) (i j : Jd n lam),
  ∀ g ∈ GLs n, (∀ m, gel false m (fun x => (Rm lam (x⁻¹)ᴴ * M) i j) g = GlobalTheory.Dec.gelfVal (infOf lam false) m * (Rm lam (g⁻¹)ᴴ * M) i j) ∧
    ∀ a b, Eu true a b (fun x => (Rm lam (x⁻¹)ᴴ * M) i j) g = 0

def EigProd : Prop := ∀ (n : ℕ) (χ : Inf n) (ι V : Type) [Fintype ι] [NormedAddCommGroup V] [NormedSpace ℂ V]
  (h a : ι → Mat n → ℂ) (v : ι → V), (∀ i, ContDiffOn ℝ ∞ (h i) (GLs n)) → (∀ i, ContDiffOn ℝ ∞ (a i) (GLs n)) →
  (∀ i, ∀ g ∈ GLs n, (∀ m, gel true m (h i) g = GlobalTheory.Dec.gelfVal (χ true) m * h i g) ∧ ∀ b c, Eu false b c (h i) g = 0) →
  (∀ i, ∀ g ∈ GLs n, (∀ m, gel false m (a i) g = GlobalTheory.Dec.gelfVal (χ false) m * a i g) ∧ ∀ b c, Eu true b c (a i) g = 0) →
  IsEig χ fun x => ∑ i, (h i x * a i x) • v i

def Avg : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), IsUnit (sqQ lam) ∧ IsSelfAdjoint (sqQ lam) ∧ sqQ lam * sqQ lam = gramQ lam ∧
  (∀ k : Matrix.unitaryGroup (Fin n) ℂ, ContinuousLinearMap.adjoint (clm lam (fr0 lam k.1)) * gramQ lam * clm lam (fr0 lam k.1) = gramQ lam) ∧
  ∀ U : Matrix (Ix n lam) (Ix n lam) ℂ, U ∈ Matrix.unitaryGroup (Ix n lam) ℂ →
    (∀ k : Matrix.unitaryGroup (Fin n) ℂ, U * fr0 lam k.1 = fr0 lam k.1 * U) → clm lam U * sqQ lam = sqQ lam * clm lam U

def MatrixFrechetDerivativeAtZeroLaws : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), fr0 lam (1 : Mat n) = 1 ∧
  (∀ x y : Mat n, IsUnit x.det → IsUnit y.det → fr0 lam (x * y) = fr0 lam x * fr0 lam y) ∧ ContDiffOn ℝ ∞ (fr0 lam) (GLs n)

def SwapLaws : Prop := ∀ (n : ℕ) (lam : Fin n → ℤ), swapJ lam * swapJ lam = 1 ∧ swapJ lam ∈ Matrix.unitaryGroup _ ℂ ∧
  (∀ x : Mat n, IsUnit x.det → swapJ lam * rhoW lam (xᴴ)⁻¹ = rhoW lam x * swapJ lam) ∧
  (∀ X : Mat n, X.IsHermitian → swapJ lam * fderiv ℝ (rhoW lam) 1 X = -(fderiv ℝ (rhoW lam) 1 X * swapJ lam)) ∧
  ∀ A B : Matrix (Jd n lam) (Jd n lam) ℂ, ((A ⊗ₖ B) * swapJ lam).trace = (A * B).trace

def WedgeDer : Prop := ∀ n : ℕ, ∑ p : Fin n × Fin n, creL n (cf n (hb p)) *
  fderiv ℝ (fun x : Mat n => gamM (Mt x⁻¹)ᵀ) 1 (hb p) = 0

end PositivityTheory.RgBcC
