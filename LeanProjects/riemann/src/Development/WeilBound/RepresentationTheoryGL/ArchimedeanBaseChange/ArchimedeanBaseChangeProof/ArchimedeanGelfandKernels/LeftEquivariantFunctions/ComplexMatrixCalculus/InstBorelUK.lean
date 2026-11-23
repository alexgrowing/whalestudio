import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv

noncomputable section

open Matrix
open scoped ComplexConjugate Kronecker

namespace PositivityTheory.RgBcC

open PositivityTheory.RgTw (Mat hb)

variable {n : ℕ}

abbrev Md (n : ℕ) := Fin (n * n)

def hbM (m : Md n) : Mat n := hb (finProdFinEquiv.symm m)

def cf (n : ℕ) : Mat n →ₗ[ℝ] (Md n → ℂ) where
  toFun H m := (((H * hbM m).trace).re : ℂ)
  map_add' H H' := by ext m; simp [Matrix.add_mul, Matrix.trace_add]
  map_smul' r H := by ext m; simp [Matrix.trace_smul]

def Mt (y : Mat n) : Matrix (Md n) (Md n) ℂ := fun p q => cf n (y * hbM q * yᴴ) p

abbrev abelian₂ (n : ℕ) := ExteriorAlgebra ℂ (Md n → ℂ)

def fb (n : ℕ) : Module.Basis (Finset (Md n)) ℂ (abelian₂ n) := (Pi.basisFun ℂ (Md n)).ExteriorAlgebra

def matL (n : ℕ) : (abelian₂ n →ₗ[ℂ] abelian₂ n) ≃ₗ[ℂ] Matrix (Finset (Md n)) (Finset (Md n)) ℂ := LinearMap.toMatrix (fb n) (fb n)

def dualOf (w : Md n → ℂ) : Module.Dual ℂ (Md n → ℂ) where
  toFun v := w ⬝ᵥ v
  map_add' v v' := dotProduct_add w v v'
  map_smul' c v := dotProduct_smul c w v

def creL (n : ℕ) : (Md n → ℂ) →ₗ[ℂ] Matrix (Finset (Md n)) (Finset (Md n)) ℂ :=
  (matL n).toLinearMap ∘ₗ (LinearMap.mul ℂ (abelian₂ n)) ∘ₗ ExteriorAlgebra.ι ℂ

def annL (n : ℕ) : (Md n → ℂ) →ₗ[ℂ] Matrix (Finset (Md n)) (Finset (Md n)) ℂ where
  toFun w := matL n (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm ℂ (Md n → ℂ))) (dualOf w))
  map_add' w w' := by
    rw [← map_add, ← map_add]; congr 2; ext v; simp [dualOf, add_dotProduct]
  map_smul' c w := by
    rw [RingHom.id_apply, ← map_smul, ← map_smul]; congr 2; ext v; simp [dualOf, smul_dotProduct]

def gamM (g : Matrix (Md n) (Md n) ℂ) : Matrix (Finset (Md n)) (Finset (Md n)) ℂ :=
  matL n (ExteriorAlgebra.map (Matrix.toLin' g)).toLinearMap

def dw (lam : Fin n → ℤ) : Formalism.BasicNotions.DomWeight n :=
  if h : Antitone lam then ⟨lam, h⟩ else ⟨fun _ => 0, fun _ _ _ => le_rfl⟩

abbrev Jd (n : ℕ) (lam : Fin n → ℤ) := Fin (Module.finrank ℂ (Formalism.BasicNotions.nablaSq ℂ n (dw lam)))

def wb (lam : Fin n → ℤ) : Module.Basis (Jd n lam) ℂ (Formalism.BasicNotions.nablaSq ℂ n (dw lam)) := Module.finBasis ℂ _

open Classical in

def Rm (lam : Fin n → ℤ) (x : Mat n) : Matrix (Jd n lam) (Jd n lam) ℂ :=
  if h : IsUnit x.det then LinearMap.toMatrix (wb lam) (wb lam) (GlobalTheory.Branching.sqRep ℂ n (dw lam) (Matrix.nonsingInvUnit x h))
  else 0

def rhoW (lam : Fin n → ℤ) (x : Mat n) : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ :=
  ((Rm lam x)⁻¹)ᵀ ⊗ₖ (Rm lam xᴴ)ᵀ

def swapJ (lam : Fin n → ℤ) : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ :=
  fun i j => if i.1 = j.2 ∧ i.2 = j.1 then 1 else 0

abbrev Ix (n : ℕ) (lam : Fin n → ℤ) := Finset (Md n) × (Jd n lam × Jd n lam)

abbrev EV (n : ℕ) (lam : Fin n → ℤ) := EuclideanSpace ℂ (Ix n lam)

def clm (lam : Fin n → ℤ) (A : Matrix (Ix n lam) (Ix n lam) ℂ) : EV n lam →L[ℂ] EV n lam := Matrix.toEuclideanCLM (𝕜 := ℂ) A

def fr0 (lam : Fin n → ℤ) (x : Mat n) : Matrix (Ix n lam) (Ix n lam) ℂ := gamM (Mt x⁻¹)ᵀ ⊗ₖ rhoW lam x

instance instMeasUK : MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ) := borel _
instance instBorelUK : BorelSpace (Matrix.unitaryGroup (Fin n) ℂ) := ⟨rfl⟩

def gramQ (lam : Fin n → ℤ) : EV n lam →L[ℂ] EV n lam :=
  ∫ k : Matrix.unitaryGroup (Fin n) ℂ, ContinuousLinearMap.adjoint (clm lam (fr0 lam k.1)) * clm lam (fr0 lam k.1)
    ∂MeasureTheory.Measure.haar

def sqQ (lam : Fin n → ℤ) : EV n lam →L[ℂ] EV n lam := CFC.sqrt (gramQ lam)

def cjL (lam : Fin n → ℤ) : Matrix (Ix n lam) (Ix n lam) ℂ →ₗ[ℂ] (EV n lam →L[ℂ] EV n lam) :=
  (LinearMap.mulLeft ℂ (sqQ lam) ∘ₗ LinearMap.mulRight ℂ (Ring.inverse (sqQ lam))) ∘ₗ
    { toFun := clm lam, map_add' := fun A B => map_add _ A B, map_smul' := fun c A => map_smul _ c A }

def krL (n : ℕ) (lam : Fin n → ℤ) :
    Matrix (Finset (Md n)) (Finset (Md n)) ℂ →ₗ[ℂ] Matrix (Ix n lam) (Ix n lam) ℂ where
  toFun A := A ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ)
  map_add' A B := Matrix.add_kronecker A B _
  map_smul' c A := by simp [Matrix.smul_kronecker]

def lefFr (n : ℕ) (lam : Fin n → ℤ) (x : Mat n) : EV n lam →L[ℂ] EV n lam := cjL lam (fr0 lam x)

def lefε (n : ℕ) (lam : Fin n → ℤ) : Mat n →ₗ[ℝ] (EV n lam →L[ℂ] EV n lam) :=
  ((cjL lam ∘ₗ krL n lam ∘ₗ
    creL n).restrictScalars ℝ) ∘ₗ cf n

def lefι (n : ℕ) (lam : Fin n → ℤ) : Mat n →ₗ[ℝ] (EV n lam →L[ℂ] EV n lam) :=
  ((cjL lam ∘ₗ krL n lam ∘ₗ
    annL n).restrictScalars ℝ) ∘ₗ cf n

def lefS (n : ℕ) (lam : Fin n → ℤ) (s : ℝ) : EV n lam →L[ℂ] EV n lam :=
  cjL lam (gamM ((s : ℂ) • (1 : Matrix (Md n) (Md n) ℂ)) ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ))

def lefΓ (n : ℕ) (lam : Fin n → ℤ) : EV n lam →L[ℂ] EV n lam :=
  cjL lam (gamM (-1 : Matrix (Md n) (Md n) ℂ) ⊗ₖ (1 : Matrix (Jd n lam × Jd n lam) (Jd n lam × Jd n lam) ℂ))

def lefT (n : ℕ) (lam : Fin n → ℤ) : EV n lam →L[ℂ] EV n lam :=
  cjL lam ((1 : Matrix (Finset (Md n)) (Finset (Md n)) ℂ) ⊗ₖ swapJ lam)

end PositivityTheory.RgBcC
