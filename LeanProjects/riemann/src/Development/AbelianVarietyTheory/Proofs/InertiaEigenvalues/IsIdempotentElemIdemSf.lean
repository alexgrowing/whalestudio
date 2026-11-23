import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicWhittakerEquivariantBumpMirabolic

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep
open scoped ContDiff

namespace GlobalTheory.SchurExt

def idemHom {R : Type} [CommRing R] (e : R) (he : IsIdempotentElem e) : R →ₙ+* R where
  toFun x := e * x
  map_mul' x y := by
    change e * (x * y) = e * x * (e * y)
    calc e * (x * y) = (e * e) * (x * y) := by rw [he.eq]
      _ = e * x * (e * y) := by ring
  map_zero' := mul_zero e
  map_add' x y := mul_add e x y

variable {E : Type} [Field E] [NumberField E]

open Classical in

def idemSf (S : Finset (HeightOneSpectrum (𝓞 E))) : Af E :=
  ⟨fun w => if w ∈ S then 1 else 0, Filter.Eventually.of_forall fun w => by
    by_cases h : w ∈ S
    · simp only [h, if_true]; exact one_mem _
    · simp only [h, if_false]; exact zero_mem _⟩

theorem isIdempotentElem_idemSf (S : Finset (HeightOneSpectrum (𝓞 E))) : IsIdempotentElem (idemSf S) := by
  classical
  refine Subtype.ext (funext fun w => ?_)
  change (if w ∈ S then (1 : w.adicCompletion E) else 0) * (if w ∈ S then 1 else 0) = if w ∈ S then 1 else 0
  split_ifs <;> simp

def idemS (S : Finset (HeightOneSpectrum (𝓞 E))) : Ad E := ((1 : InfiniteAdeleRing E), idemSf S)

theorem isIdempotentElem_idemS (S : Finset (HeightOneSpectrum (𝓞 E))) : IsIdempotentElem (idemS S) :=
  Prod.ext (mul_one _) (isIdempotentElem_idemSf S).eq

def prS (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) : GA E a →* GA E a :=
  cornerGL a (idemHom (idemS S) (isIdempotentElem_idemS S))

def prO (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) : GA E a →* GA E a :=
  cornerGL a (idemHom (1 - idemS S) (isIdempotentElem_idemS S).one_sub)

def prSf (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) : GL (Fin a) (Af E) →* GL (Fin a) (Af E) :=
  cornerGL a (idemHom (idemSf S) (isIdempotentElem_idemSf S))

def prOf (S : Finset (HeightOneSpectrum (𝓞 E))) (a : ℕ) : GL (Fin a) (Af E) →* GL (Fin a) (Af E) :=
  cornerGL a (idemHom (1 - idemSf S) (isIdempotentElem_idemSf S).one_sub)

def eqv (m r : ℕ) : Fin (m + r + 1 + 1) ≃ Fin (m + 1) ⊕ Fin (r + 1) :=
  (finCongr (by omega)).trans finSumFinEquiv.symm

section Blocks

variable {R : Type} [CommRing R] {m r : ℕ}

def blk (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) :
    Matrix (Fin (m + 1) ⊕ Fin (r + 1)) (Fin (m + 1) ⊕ Fin (r + 1)) R :=
  M.submatrix (eqv m r).symm (eqv m r).symm

def unblk (P : Matrix (Fin (m + 1) ⊕ Fin (r + 1)) (Fin (m + 1) ⊕ Fin (r + 1)) R) :
    Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R :=
  P.submatrix (eqv m r) (eqv m r)

def Aof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  (blk M).toBlocks₁₁

def Bof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Matrix (Fin (m + 1)) (Fin (r + 1)) R :=
  (blk M).toBlocks₁₂

def Cof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Matrix (Fin (r + 1)) (Fin (m + 1)) R :=
  (blk M).toBlocks₂₁

def Dof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Matrix (Fin (r + 1)) (Fin (r + 1)) R :=
  (blk M).toBlocks₂₂

def Xof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Matrix (Fin (m + 1)) (Fin (r + 1)) R :=
  Bof M * (Dof M)⁻¹

def Yof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Matrix (Fin (r + 1)) (Fin (m + 1)) R :=
  (Dof M)⁻¹ * Cof M

def Scof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : Matrix (Fin (m + 1)) (Fin (m + 1)) R :=
  Aof M - Bof M * (Dof M)⁻¹ * Cof M

theorem unblk_blk (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) : unblk (blk M) = M := by
  ext i j; simp [unblk, blk]

theorem blk_unblk (P : Matrix (Fin (m + 1) ⊕ Fin (r + 1)) (Fin (m + 1) ⊕ Fin (r + 1)) R) : blk (unblk P) = P := by
  ext i j; simp [unblk, blk]

end Blocks

open Classical in

def mkGL {R : Type} [CommRing R] {k : ℕ} (M : Matrix (Fin k) (Fin k) R) : GL (Fin k) R :=
  if h : IsUnit M.det then Matrix.nonsingInvUnit M h else 1

theorem coe_mkGL {R : Type} [CommRing R] {k : ℕ} {M : Matrix (Fin k) (Fin k) R} (h : IsUnit M.det) :
    ((mkGL M : GL (Fin k) R) : Matrix (Fin k) (Fin k) R) = M := by
  rw [mkGL, dif_pos h]; rfl

def psi (x : Ad E) : ℂ := (GroundTheory.Global.adelicChar E x : ℂ)

variable [IsTotallyComplex E]

def chiF {m r : ℕ} (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ) (Y : Matrix (Fin (r + 1)) (Fin (m + 1)) (Ad E)) : ℂ :=
  open Classical in
  (χ (fun i j => pInf E (Y i j)) : ℂ) *
    (if ∀ i j, pFin E (Y i j) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E then 1 else 0)

def schurF {m r : ℕ} (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ)
    (g : GA E (m + r + 1 + 1)) : ℂ :=
  open Classical in
  if IsUnit (Dof (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E))).det then
    psi (Xof (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) (Fin.last m) 0) *
      β (mkGL (Scof (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))) *
      b₁ (mkGL (Dof (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))) *
      chiF χ (Yof (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)))
  else 0

def extB {m r : ℕ} (S : Finset (HeightOneSpectrum (𝓞 E))) (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ)
    (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ) (Φ : GA E (m + r + 1 + 1) → ℂ) (g : GA E (m + r + 1 + 1)) : ℂ :=
  schurF β b₁ χ (prS S _ g) * Φ (prO S _ g)

end GlobalTheory.SchurExt
