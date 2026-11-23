import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagGrassSteps
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ImageCoord
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 Matrix

namespace FlagImageGrass

section Cone

variable {K : Type} {ι : K → Type}

theorem mConeMap_apply [Fintype K] [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω)
    (F : MRing ι) :
    mConeMap y F = eval₂ (Int.castRingHom _) (fun p => C (y p) * X p.1 : (Σ k, ι k) → MvPolynomial K Ω) F := by
  rw [mConeMap, aeval_def, RingHom.ext_int (algebraMap ℤ (MvPolynomial K Ω)) (Int.castRingHom _)]

theorem cone_map {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (y : (Σ k, ι k) → A)
    (F : MvPolynomial (Σ k, ι k) ℤ) :
    eval₂ (Int.castRingHom _) (fun p => C (φ (y p)) * X p.1 : (Σ k, ι k) → MvPolynomial K B) F =
      map φ (eval₂ (Int.castRingHom _) (fun p => C (y p) * X p.1 : (Σ k, ι k) → MvPolynomial K A) F) := by
  induction F using MvPolynomial.induction_on with
  | C a => simp only [eval₂_C, Int.coe_castRingHom, map_intCast]
  | add p q hp hq => simp only [eval₂_add, map_add, hp, hq]
  | mul_X p q hp => simp only [eval₂_mul, map_mul, hp, eval₂_X, map_C, map_X]

theorem cone_map_eq_zero {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (y : (Σ k, ι k) → A)
    (F : MvPolynomial (Σ k, ι k) ℤ) (h : eval₂ (Int.castRingHom _) (fun p => C (y p) * X p.1 : (Σ k, ι k) → MvPolynomial K A) F = 0) :
    eval₂ (Int.castRingHom _) (fun p => C (φ (y p)) * X p.1 : (Σ k, ι k) → MvPolynomial K B) F = 0 := by
  rw [cone_map, h, map_zero]

theorem cone_map_eq_zero_iff {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B)
    (hφ : Function.Injective φ) (y : (Σ k, ι k) → A) (F : MvPolynomial (Σ k, ι k) ℤ) :
    eval₂ (Int.castRingHom _) (fun p => C (φ (y p)) * X p.1 : (Σ k, ι k) → MvPolynomial K B) F = 0 ↔
      eval₂ (Int.castRingHom _) (fun p => C (y p) * X p.1 : (Σ k, ι k) → MvPolynomial K A) F = 0 := by
  rw [cone_map]
  exact ⟨fun h => map_injective φ hφ (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩

theorem cone_smul_eq_zero_iff {Ω : Type} [Field Ω] (c : K → Ω) (hc : ∀ k, c k ≠ 0)
    (y : (Σ k, ι k) → Ω) (F : MvPolynomial (Σ k, ι k) ℤ) :
    eval₂ (Int.castRingHom _) (fun p => C (c p.1 * y p) * X p.1 : (Σ k, ι k) → MvPolynomial K Ω) F = 0 ↔
      eval₂ (Int.castRingHom _) (fun p => C (y p) * X p.1 : (Σ k, ι k) → MvPolynomial K Ω) F = 0 := by
  let D : (K → Ω) → MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω := fun c => aeval fun k => C (c k) * X k
  have hD : eval₂ (Int.castRingHom _) (fun p => C (c p.1 * y p) * X p.1 : (Σ k, ι k) → MvPolynomial K Ω) F =
      D c (eval₂ (Int.castRingHom _) (fun p => C (y p) * X p.1 : (Σ k, ι k) → MvPolynomial K Ω) F) := by
    induction F using MvPolynomial.induction_on with
    | C a => simp only [eval₂_C, Int.coe_castRingHom, map_intCast]
    | add p q hp hq => simp only [eval₂_add, map_add, hp, hq]
    | mul_X p q hp =>
      rw [eval₂_mul, eval₂_mul, map_mul, hp]
      simp only [eval₂_X, aeval_X, D, map_mul, aeval_C, algebraMap_eq, C_mul]
      ring
  have hinv : ∀ G, D (fun k => (c k)⁻¹) (D c G) = G := by
    intro G
    have : (D fun k => (c k)⁻¹).comp (D c) = AlgHom.id Ω _ := by
      apply MvPolynomial.algHom_ext
      intro k
      simp only [D, AlgHom.comp_apply, aeval_X, map_mul, aeval_C, algebraMap_eq, AlgHom.id_apply]
      rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]
    exact congrArg (fun φ => φ G) this
  rw [hD]
  exact ⟨fun h => by rw [← hinv (eval₂ _ _ F), h, map_zero], fun h => by rw [h, map_zero]⟩

end Cone

section Rows

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (hN : j + (N - j) = N)

def genTop (τ : Ψ) : Matrix (Fin j) (Fin (j + (N - j))) (MvPolynomial (Ψ × Fin N × Fin N) ℚ) :=
  Matrix.of fun a b => X (τ, Fin.castLE (by omega) a, Fin.cast hN b)

theorem yFl_grFlV (hj : 1 ≤ j) (hjN : j ≤ N - 1) (p : Σ _ : Fin (Fintype.card Ψ), PlIdx j (N - j)) :
    yFl Ψ N (grFlV Ψ N j hj hjN p) =
      algebraMap _ (ΩFl Ψ N) (colsOf (genTop Ψ N j hN ((Fintype.equivFin Ψ).symm p.1)) p.2).det := by
  have hs : j - 1 + 1 = j := by omega
  unfold yFl
  congr 1
  rw [← Matrix.det_submatrix_equiv_self (finCongr hs)]
  congr 1

def genZ (t : Fin (Fintype.card Ψ)) :
    Matrix (Fin j) (Fin (N - j)) (MvPolynomial (Fin (Fintype.card Ψ) × Fin j × Fin (N - j)) ℚ) :=
  Matrix.of fun a b => X (t, a, b)

def toOnePipe : MvPolynomial (Ψ × Fin N × Fin N) ℚ →ₐ[ℚ]
    MvPolynomial (Fin (Fintype.card Ψ) × Fin j × Fin (N - j)) ℚ :=
  aeval fun x => if h : (x.2.1 : ℕ) < j then
    onePipe (genZ Ψ N j (Fintype.equivFin Ψ x.1)) ⟨x.2.1, h⟩ (Fin.cast hN.symm x.2.2) else 0

theorem toOnePipe_genTop (τ : Ψ) :
    (genTop Ψ N j hN τ).map (toOnePipe Ψ N j hN) = onePipe (genZ Ψ N j (Fintype.equivFin Ψ τ)) := by
  ext a b
  simp [toOnePipe, genTop]

theorem toOnePipe_minor (p : Σ _ : Fin (Fintype.card Ψ), PlIdx j (N - j)) :
    toOnePipe Ψ N j hN (colsOf (genTop Ψ N j hN ((Fintype.equivFin Ψ).symm p.1)) p.2).det =
      GroundTheory.Heights₂.Heights.grassPolyCoord (Fintype.card Ψ) j (N - j) p := by
  rw [AlgHom.map_det, AlgHom.mapMatrix_apply]
  have : (colsOf (genTop Ψ N j hN ((Fintype.equivFin Ψ).symm p.1)) p.2).map (toOnePipe Ψ N j hN) =
      colsOf ((genTop Ψ N j hN ((Fintype.equivFin Ψ).symm p.1)).map (toOnePipe Ψ N j hN)) p.2 := rfl
  rw [this, toOnePipe_genTop, Equiv.apply_symm_apply]
  rfl

def genTopF (τ : Ψ) : Matrix (Fin j) (Fin (j + (N - j))) (ΩFl Ψ N) :=
  (genTop Ψ N j hN τ).map (algebraMap (MvPolynomial (Ψ × Fin N × Fin N) ℚ) (ΩFl Ψ N))

def genLead (τ : Ψ) : Matrix (Fin j) (Fin j) (ΩFl Ψ N) :=
  (genTopF Ψ N j hN τ).submatrix id (Fin.castAdd (N - j))

theorem genLead_det_ne_zero (τ : Ψ) : (genLead Ψ N j hN τ).det ≠ 0 := by
  have hA : genLead Ψ N j hN τ = (algebraMap (MvPolynomial (Ψ × Fin N × Fin N) ℚ) (ΩFl Ψ N)).mapMatrix
      ((genTop Ψ N j hN τ).submatrix id (Fin.castAdd (N - j))) := by
    ext a c
    rfl
  rw [hA, ← RingHom.map_det]
  intro h0
  have h1 : ((genTop Ψ N j hN τ).submatrix id (Fin.castAdd (N - j))).det = 0 :=
    IsFractionRing.injective (MvPolynomial (Ψ × Fin N × Fin N) ℚ) (ΩFl Ψ N) (by rw [h0, map_zero])
  have h2 := congrArg (MvPolynomial.eval fun x : Ψ × Fin N × Fin N => if (x.2.1 : ℕ) = x.2.2 then (1 : ℚ) else 0) h1
  rw [RingHom.map_det, map_zero] at h2
  have h3 : (MvPolynomial.eval fun x : Ψ × Fin N × Fin N => if (x.2.1 : ℕ) = x.2.2 then (1 : ℚ) else 0).mapMatrix
      ((genTop Ψ N j hN τ).submatrix id (Fin.castAdd (N - j))) = 1 := by
    ext a c
    simp [genTop, Matrix.one_apply, Fin.ext_iff]
  rw [h3, det_one] at h2
  exact one_ne_zero h2

def toFlag : MvPolynomial (Fin (Fintype.card Ψ) × Fin j × Fin (N - j)) ℚ →ₐ[ℚ] ΩFl Ψ N :=
  aeval fun x => ((genLead Ψ N j hN ((Fintype.equivFin Ψ).symm x.1))⁻¹ *
    genTopF Ψ N j hN ((Fintype.equivFin Ψ).symm x.1)) x.2.1 (Fin.natAdd j x.2.2)

theorem toFlag_onePipe (t : Fin (Fintype.card Ψ)) :
    (onePipe (genZ Ψ N j t)).map (toFlag Ψ N j hN) =
      (genLead Ψ N j hN ((Fintype.equivFin Ψ).symm t))⁻¹ * genTopF Ψ N j hN ((Fintype.equivFin Ψ).symm t) := by
  have hAA := nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (genLead_det_ne_zero Ψ N j hN ((Fintype.equivFin Ψ).symm t)))
  ext a b
  refine Fin.addCases (fun c => ?_) (fun c => ?_) b
  · have : ((genLead Ψ N j hN ((Fintype.equivFin Ψ).symm t))⁻¹ * genTopF Ψ N j hN ((Fintype.equivFin Ψ).symm t))
        a (Fin.castAdd (N - j) c) = ((genLead Ψ N j hN ((Fintype.equivFin Ψ).symm t))⁻¹ *
          genLead Ψ N j hN ((Fintype.equivFin Ψ).symm t)) a c := rfl
    rw [this, hAA]
    simp [onePipe, Matrix.one_apply]
  · simp [onePipe, toFlag, genZ]

theorem toFlag_minor (hj : 1 ≤ j) (hjN : j ≤ N - 1) (p : Σ _ : Fin (Fintype.card Ψ), PlIdx j (N - j)) :
    toFlag Ψ N j hN (GroundTheory.Heights₂.Heights.grassPolyCoord (Fintype.card Ψ) j (N - j) p) =
      (genLead Ψ N j hN ((Fintype.equivFin Ψ).symm p.1)).det⁻¹ * yFl Ψ N (grFlV Ψ N j hj hjN p) := by
  rw [yFl_grFlV Ψ N j hN hj hjN p]
  have e1 : GroundTheory.Heights₂.Heights.grassPolyCoord (Fintype.card Ψ) j (N - j) p =
      (colsOf (onePipe (genZ Ψ N j p.1)) p.2).det := rfl
  rw [e1, AlgHom.map_det, AlgHom.mapMatrix_apply]
  have e2 : (colsOf (onePipe (genZ Ψ N j p.1)) p.2).map (toFlag Ψ N j hN) =
      colsOf ((onePipe (genZ Ψ N j p.1)).map (toFlag Ψ N j hN)) p.2 := rfl
  rw [e2, toFlag_onePipe]
  have e3 : colsOf ((genLead Ψ N j hN ((Fintype.equivFin Ψ).symm p.1))⁻¹ *
      genTopF Ψ N j hN ((Fintype.equivFin Ψ).symm p.1)) p.2 =
      (genLead Ψ N j hN ((Fintype.equivFin Ψ).symm p.1))⁻¹ *
        colsOf (genTopF Ψ N j hN ((Fintype.equivFin Ψ).symm p.1)) p.2 := rfl
  rw [e3, det_mul, det_nonsing_inv, Ring.inverse_eq_inv', RingHom.map_det, RingHom.mapMatrix_apply]
  rfl

end Rows

theorem image_eq (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (hj : 1 ≤ j) (hjN : j ≤ N - 1) :
    imageZ (grFlV Ψ N j hj hjN) (PFl Ψ N) = mCoordIdeal (yFl Ψ N ∘ grFlV Ψ N j hj hjN) := by
  have hκ : Function.Injective (grFlKappa Ψ N j hj hjN) := fun a b h =>
    (Fintype.equivFin Ψ).symm.injective (congrArg Prod.fst h)
  ext F
  simp only [PFl, imageZ, mCoordIdeal, Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, GroundTheory.Heights₂.Heights.Targets.ImageCoord.mConeMap_rename (grFlKappa Ψ N j hj hjN)
      (grFlV Ψ N j hj hjN) (fun _ => rfl) (yFl Ψ N) F]
  exact ⟨fun h => rename_injective _ hκ (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩

theorem proof : FlagImageGrass.Statement := by
  intro Ψ _ _ N j hj hjN
  have hN : j + (N - j) = N := by omega
  rw [image_eq]
  ext F
  simp only [GroundTheory.Heights₂.Heights.grassIdeal, mCoordIdeal, RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, mConeMap_apply, Function.comp_apply]

  have ha : ∀ F : MvPolynomial (Σ _ : Fin (Fintype.card Ψ), PlIdx j (N - j)) ℤ,
      eval₂ (Int.castRingHom _) (fun p => C (yFl Ψ N (grFlV Ψ N j hj hjN p)) * X p.1 :
        _ → MvPolynomial (Fin (Fintype.card Ψ)) (ΩFl Ψ N)) F = 0 ↔
      eval₂ (Int.castRingHom _) (fun p => C (colsOf (genTop Ψ N j hN ((Fintype.equivFin Ψ).symm p.1)) p.2).det * X p.1 :
        _ → MvPolynomial (Fin (Fintype.card Ψ)) (MvPolynomial (Ψ × Fin N × Fin N) ℚ)) F = 0 := by
    intro F
    simp only [yFl_grFlV Ψ N j hN hj hjN]
    exact cone_map_eq_zero_iff (algebraMap (MvPolynomial (Ψ × Fin N × Fin N) ℚ) (ΩFl Ψ N))
      (IsFractionRing.injective _ _)
      (fun p : (Σ _ : Fin (Fintype.card Ψ), PlIdx j (N - j)) =>
        (colsOf (genTop Ψ N j hN ((Fintype.equivFin Ψ).symm p.1)) p.2).det) F

  have hb : ∀ F : MvPolynomial (Σ _ : Fin (Fintype.card Ψ), PlIdx j (N - j)) ℤ,
      eval₂ (Int.castRingHom _) (fun p => C (GroundTheory.Heights₂.Heights.grassCoord (Fintype.card Ψ) j (N - j) p) * X p.1 :
        _ → MvPolynomial (Fin (Fintype.card Ψ)) (GroundTheory.Heights₂.Heights.GrassField (Fintype.card Ψ) j (N - j))) F = 0 ↔
      eval₂ (Int.castRingHom _) (fun p => C (GroundTheory.Heights₂.Heights.grassPolyCoord (Fintype.card Ψ) j (N - j) p) * X p.1 :
        _ → MvPolynomial (Fin (Fintype.card Ψ))
          (MvPolynomial (Fin (Fintype.card Ψ) × Fin j × Fin (N - j)) ℚ)) F = 0 :=
    fun F => cone_map_eq_zero_iff
      (algebraMap (MvPolynomial (Fin (Fintype.card Ψ) × Fin j × Fin (N - j)) ℚ)
        (GroundTheory.Heights₂.Heights.GrassField (Fintype.card Ψ) j (N - j)))
      (IsFractionRing.injective _ _) (GroundTheory.Heights₂.Heights.grassPolyCoord (Fintype.card Ψ) j (N - j)) F
  rw [ha, hb]
  constructor
  · intro h
    have h' := cone_map_eq_zero (toOnePipe Ψ N j hN).toRingHom _ F h
    simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, toOnePipe_minor] using h'
  · intro h
    have h' := cone_map_eq_zero (toFlag Ψ N j hN).toRingHom _ F h
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, toFlag_minor Ψ N j hN hj hjN] at h'
    rw [← ha]
    exact (cone_smul_eq_zero_iff (fun t => (genLead Ψ N j hN ((Fintype.equivFin Ψ).symm t)).det⁻¹)
      (fun _ => inv_ne_zero (genLead_det_ne_zero Ψ N j hN _)) _ F).mp h'

end FlagImageGrass

end GroundTheory.Heights₂.Heights.LowerBoundFree
