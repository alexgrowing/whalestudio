import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.RepresentationOverSumChar

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N

section Generic

variable {O Γ : Type} [CommRing O] [Group Γ]

def blockSum {r : ℕ} (t : ℕ) (ρ : Γ →* GL (Fin r) O) (χ : ℕ → (Γ →* Oˣ)) :
    Γ →* Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O where
  toFun g := Matrix.fromBlocks ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O) 0 0
    (Matrix.diagonal fun c : Fin t => ((χ ((c : ℕ) + 1) g : Oˣ) : O))
  map_one' := by simp
  map_mul' g h := by
    simp [Matrix.fromBlocks_multiply, Matrix.diagonal_mul_diagonal]

def repOver (K : Type) [CommRing K] [Algebra O K] {n : Type} [Fintype n] [DecidableEq n]
    (M : Γ →* Matrix n n O) : Representation K Γ (n → K) where
  toFun g := Matrix.toLin' ((M g).map (algebraMap O K))
  map_one' := by
    rw [map_one, Matrix.map_one _ (map_zero _) (map_one _), Matrix.toLin'_one]
    rfl
  map_mul' g h := by
    rw [map_mul, Matrix.map_mul, Matrix.toLin'_mul]
    rfl

theorem charpoly_blockSum {r : ℕ} (t : ℕ) (ρ : Γ →* GL (Fin r) O) (χ : ℕ → (Γ →* Oˣ)) (g : Γ) :
    (blockSum t ρ χ g).charpoly =
      ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).charpoly *
        ∏ c ∈ Finset.Icc 1 t, (X - C ((χ c g : Oˣ) : O)) := by
  have h : (blockSum t ρ χ g).charpoly =
      ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).charpoly *
        (Matrix.diagonal fun c : Fin t => ((χ ((c : ℕ) + 1) g : Oˣ) : O)).charpoly :=
    Matrix.charpoly_fromBlocks_zero₂₁ _ _ _
  rw [h, Matrix.charpoly_diagonal, Fin.prod_univ_eq_prod_range (fun c => X - C ((χ (c + 1) g : Oˣ) : O)) t,
    Finset.range_eq_Ico, Finset.prod_Ico_add' (fun c => X - C ((χ c g : Oˣ) : O)) 0 t 1]
  rfl

theorem continuous_blockSum_iff [TopologicalSpace O] [TopologicalSpace Γ] {r : ℕ} (t : ℕ)
    (ρ : Γ →* GL (Fin r) O) (χ : ℕ → (Γ →* Oˣ)) (hχ : ∀ c, Continuous fun g => ((χ c g : Oˣ) : O)) :
    Continuous (fun g => blockSum t ρ χ g) ↔
      Continuous (fun g => ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O)) := by
  constructor
  · intro h
    refine continuous_pi fun a => continuous_pi fun b => ?_
    exact (continuous_apply (Sum.inl b)).comp ((continuous_apply (Sum.inl a)).comp h)
  · intro h
    refine continuous_pi fun a => continuous_pi fun b => ?_
    rcases a with a | a <;> rcases b with b | b
    · exact (continuous_apply b).comp ((continuous_apply a).comp h)
    · exact continuous_const
    · exact continuous_const
    · by_cases hab : a = b
      · subst hab
        simpa [blockSum] using hχ ((a : ℕ) + 1)
      · simpa [blockSum, Matrix.diagonal_apply_ne _ hab] using continuous_const

end Generic

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)

def FrobeniusMatrixCompatible (i : N.Loc) (x : N.X i) {n : Type} [Fintype n] [DecidableEq n]
    (M : GE N →* Matrix n n (N.O i)) : Prop :=
  ∀ w : PlE H, SplitOut N i w → ∀ (B : ValuationSubring N.Om) (σ : GE N),
    IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ → (M σ).charpoly = heckePol N i x w

def IsRx (i : N.Loc) (x : N.X i) {n : Type} [Fintype n] [DecidableEq n]
    (M : GE N →* Matrix n n (N.O i)) : Prop :=
  Continuous (fun g => M g) ∧ (repOver (KK N i) M).IsSemisimpleRepresentation ∧ FrobeniusMatrixCompatible N i x M

def sumChi (i : N.Loc) (ρ : GE N →* GL (Fin R.r) (N.O i)) :
    GE N →* Matrix (Fin R.r ⊕ Fin R.t) (Fin R.r ⊕ Fin R.t) (N.O i) :=
  blockSum R.t ρ (N.chi i)

def IsContRep (i : N.Loc) (ρ : GE N →* GL (Fin R.r) (N.O i)) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i)))

def IsRhoAt (i : N.Loc) (π : N.X i) (ρ : GE N →* GL (Fin R.r) (N.O i)) : Prop :=
  FrobeniusMatrixCompatible N i π (sumChi N i ρ)

def IsSSSum (i : N.Loc) (ρ : GE N →* GL (Fin R.r) (N.O i)) : Prop :=
  (repOver (KK N i) (sumChi N i ρ)).IsSemisimpleRepresentation

def IsComplement (i : N.Loc) (π : N.X i) (ρ : GE N →* GL (Fin R.r) (N.O i)) : Prop :=
  IsRhoAt N i π ρ ∧ IsSSSum N i ρ ∧ IsContRep N i ρ

def IsComplementOnZ (i : N.Loc) (ρ : N.X i → (GE N →* GL (Fin R.r) (N.O i))) : Prop :=
  ∀ π ∈ N.Z i, IsComplement N i π (ρ π)

def SplitsAs (i : N.Loc) (rπ : GE N →* GL (Fin R.nV) (N.O i)) (ρ : GE N →* GL (Fin R.r) (N.O i)) : Prop :=
  ∃ e : (Fin R.nV → KK N i) ≃ₗ[KK N i] (Fin R.r ⊕ Fin R.t → KK N i), ∀ g u,
    e (repOver (KK N i) ((Units.coeHom _).comp rπ) g u) = repOver (KK N i) (sumChi N i ρ) g (e u)

theorem isComplement_iff (i : N.Loc) (π : N.X i) (ρ : GE N →* GL (Fin R.r) (N.O i)) :
    IsComplement N i π ρ ↔ IsRx N i π (sumChi N i ρ) := by
  have h := continuous_blockSum_iff R.t ρ (N.chi i) (N.chi_cont i)
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h.2 h3, h2, h1⟩
  · rintro ⟨h3, h2, h1⟩
    exact ⟨h1, h2, h.1 h3⟩

theorem isRhoAt_iff (i : N.Loc) (π : N.X i) (ρ : GE N →* GL (Fin R.r) (N.O i)) :
    IsRhoAt N i π ρ ↔ ∀ w : PlE H, SplitOut N i w → ∀ (B : ValuationSubring N.Om) (σ : GE N),
      IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ →
      ((ρ σ : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i)).charpoly *
        ∏ c ∈ Finset.Icc 1 R.t, (X - C ((N.chi i c σ : (N.O i)ˣ) : N.O i)) = heckePol N i π w := by
  simp only [IsRhoAt, FrobeniusMatrixCompatible, sumChi, charpoly_blockSum]

theorem isRhoAt_of_splitsAs (i : N.Loc) (π : N.X i) (rπ : GE N →* GL (Fin R.nV) (N.O i))
    (ρ : GE N →* GL (Fin R.r) (N.O i)) (hr : FrobeniusMatrixCompatible N i π ((Units.coeHom _).comp rπ))
    (hs : SplitsAs N i rπ ρ) : IsRhoAt N i π ρ := by
  obtain ⟨e, he⟩ := hs
  intro w hw B σ hB hσ
  rw [← hr w hw B σ hB hσ]
  apply Polynomial.map_injective (algebraMap (N.O i) (KK N i)) (IsFractionRing.injective _ _)
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_map, ← Matrix.charpoly_toLin', ← Matrix.charpoly_toLin',
    ← LinearEquiv.charpoly_conj e]
  congr 1
  refine LinearMap.ext fun u => ?_
  have := he σ (e.symm u)
  rw [LinearEquiv.apply_symm_apply] at this
  exact this.symm

example (ρ : Multiplicative (ZMod 2) →* GL (Fin 3) ℤ) (χ : ℕ → (Multiplicative (ZMod 2) →* ℤˣ)) :
    (repOver ℚ (blockSum 5 ρ χ)).IsSemisimpleRepresentation := by
  haveI : NeZero ((Nat.card (Multiplicative (ZMod 2)) : ℕ) : ℚ) := ⟨by simp⟩
  infer_instance

end GlobalTheory.IndefiniteRowSideFullHecke.RepresentationOverSumChar

end
