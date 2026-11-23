import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtVecMulVecRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianSetAdditiveSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviMapPreservesRationalPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianDeterminantNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrAEMixedNondeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTraceOrth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumThreeComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTensEqTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTensVmvLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedMatrixDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticPairingAdaptedFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSkewAdaptedPairingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSkewAdaptedPairingSecondStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch GlobalTheory.ArchSchB

noncomputable section
namespace GlobalTheory.ArchSchB.CoisoS

theorem decX : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E)
    {n d n₁ : ℕ} (X : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ),
    X.IsHerm σ B r s → H.IsAdapted σ B X X₁ i₀ i₁ → ∀ w : Matrix (Fin n) (Fin d) (AE F E), At (evI F) w →
    ∃ (α β : Fin d → AE F E) (C : Matrix (Fin n₁) (Fin d) (AE F E)), At (evI F) α ∧ At (evI F) β ∧ At (evI F) C ∧
      w = Matrix.vecMulVec (incV F H.x) α + incM F H.ι * C + Matrix.vecMulVec (incV F H.y) β := GlobalTheory.T.hermitian_adapted_matrix_decomposition

theorem pairX : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E)
    {n d n₁ : ℕ} (X : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ) (JW : Matrix (Fin d) (Fin d) E),
    B.IsGood σ → X.IsHerm σ B r s → H.IsAdapted σ B X X₁ i₀ i₁ →
    ∀ (α β a : Fin d → AE F E) (C : Matrix (Fin n₁) (Fin d) (AE F E)),
    symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F JW)
      (Matrix.vecMulVec (incV F H.x) α + incM F H.ι * C + Matrix.vecMulVec (incV F H.y) β) (Matrix.vecMulVec (incV F H.x) a) =
    -Algebra.trace (AF F) (AE F E) (β ⬝ᵥ (incM F JW *ᵥ fun k => cA σ (a k))) := GlobalTheory.T.symplectic_pairing_adapted_formula

theorem nondeg : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E), J.det ≠ 0 → ∀ b : Fin n → AE F E, At (evI F) b →
    (∀ c : Fin n → AE F E, At (evI F) c → Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (evI F (Algebra.trace (AF F) (AE F E) (b ⬝ᵥ (incM F J *ᵥ fun k => cA σ (c k))))) = 0) → b = 0 := by
  intro F E _ _ _ _ _ σ n J hJ b hb hc
  have hdet : IsUnit (incM F J).det := by
    have h : (incM F J).det = inclR (F := F) (AF F) J.det := by
      rw [RingHom.map_det]; rfl
    rw [h]
    exact (isUnit_iff_ne_zero.2 hJ).map _
  have hv : b ᵥ* incM F J = 0 := by
    funext k
    apply GlobalTheory.ArchSch.trAE_nondeg _ (GlobalTheory.ArchTraceNondeg.at_vecMul hb _ k)
    intro t ht
    have h := hc (Pi.single k (GlobalTheory.ArchTraceNondeg.cAinv σ t))
      (GlobalTheory.ArchTraceNondeg.at_single k (GlobalTheory.ArchTraceNondeg.at_cAinv σ ht))
    rw [Matrix.dotProduct_mulVec] at h
    have hw : (fun j => cA σ ((Pi.single k (GlobalTheory.ArchTraceNondeg.cAinv σ t) : Fin n → AE F E) j)) = Pi.single k t := by
      funext j
      by_cases hj : j = k
      · subst hj; simp [GlobalTheory.ArchTraceNondeg.cA_cAinv]
      · simp [Pi.single_apply, hj]
    rw [hw, dotProduct_single] at h
    exact h
  calc b = b ᵥ* (incM F J * (incM F J)⁻¹) := by rw [Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]
    _ = (b ᵥ* incM F J) ᵥ* (incM F J)⁻¹ := (Matrix.vecMul_vecMul _ _ _).symm
    _ = 0 := by rw [hv, Matrix.zero_vecMul]

theorem pairC : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E)
    {n d n₁ d₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁)
    (r s r' s' i₀ i₁ j₀ j₁ : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → H.IsAdapted σ B X X₁ i₀ i₁ → H'.IsAdapted σ B W W₁ j₀ j₁ →
    ∀ (α : Fin d → AE F E) (c₁ c₂ c : Fin n₁ → AE F E) (Z : Matrix (Fin n₁) (Fin d₁) (AE F E)),
    symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)
      (Matrix.vecMulVec (incV F H.x) α + Matrix.vecMulVec (incM F H.ι *ᵥ c₁) (incV F H'.x) +
        incM F H.ι * Z * (incM F H'.ι)ᵀ + Matrix.vecMulVec (incM F H.ι *ᵥ c₂) (incV F H'.y))
      (Matrix.vecMulVec (incM F H.ι *ᵥ c) (incV F H'.x)) =
    Algebra.trace (AF F) (AE F E) (c₂ ⬝ᵥ (incM F X₁.J *ᵥ fun k => cA σ (c k))) := GlobalTheory.T.hermitian_skew_adapted_pairing

theorem pairZ : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E)
    {n d n₁ d₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (H : Plane E n n₁) (H' : Plane E d d₁)
    (r s r' s' i₀ i₁ j₀ j₁ : ℕ),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → H.IsAdapted σ B X X₁ i₀ i₁ → H'.IsAdapted σ B W W₁ j₀ j₁ →
    ∀ (α : Fin d → AE F E) (c₁ : Fin n₁ → AE F E) (Z z' : Matrix (Fin n₁) (Fin d₁) (AE F E)),
    symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)
      (Matrix.vecMulVec (incV F H.x) α + Matrix.vecMulVec (incM F H.ι *ᵥ c₁) (incV F H'.x) +
        incM F H.ι * Z * (incM F H'.ι)ᵀ) (incM F H.ι * z' * (incM F H'.ι)ᵀ) =
    symp (R := AF F) (cA σ) (-1) (incM F X₁.J) (incM F W₁.J) Z z' := GlobalTheory.T.hermitian_skew_adapted_pairing_second

end GlobalTheory.ArchSchB.CoisoS

namespace GlobalTheory.ArchSchB
open GlobalTheory.ArchSchB.CoisoS

theorem evI_neg' {F : Type} [Field F] [NumberField F] (a : AF F) : evI F (-a) = -evI F a := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F (-a.1) = -InfiniteAdeleRing.ringEquiv_mixedSpace F a.1
  exact map_neg _ _

theorem mul_vecMulVec' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m k l : ℕ}
    (P : Matrix (Fin m) (Fin k) (AE F E)) (c : Fin k → AE F E) (x : Fin l → AE F E) :
    P * Matrix.vecMulVec c x = Matrix.vecMulVec (P *ᵥ c) x := by
  ext i j
  simp [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]

theorem lagSetB_coisotropic : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} (M : Model σ X W) (M₁ : Model σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → H.IsAdapted σ B X X₁ i₀ i₁ → H'.IsAdapted σ B W W₁ j₀ j₁ →
    ∀ v, (∀ l ∈ lagSetB M M₁ H H', trP F _ v.1 l.2 = trP F _ l.1 v.2) → v ∈ lagSetB M M₁ H H' := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ M M₁ H H' hB hX hW hH hH' v hv
  have hω := fun w w' => GlobalTheory.ArchSch.trace_evI_darboux M.co w w'
  have hω₁ := fun z z' => GlobalTheory.ArchSch.trace_evI_darboux M₁.co z z'
  obtain ⟨w, hwA, hw1, hw2⟩ := GlobalTheory.ArchSch.exists_darboux_lift M.co v.1 v.2
  have key : ∀ w', (arch F (M.co.e w').1, arch F (M.co.e w').2) ∈ lagSetB M M₁ H H' →
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (evI F (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) w w')) = 0 := by
    intro w' hl
    have := hv _ hl
    rw [hω, hw1, hw2]
    exact sub_eq_zero.mpr this
  obtain ⟨α, β, C, hα, hβ, hC, rfl⟩ := decX B X X₁ H r s i₀ i₁ hX hH w hwA
  have hβ0 : β = 0 := by
    refine nondeg σ W.J (GlobalTheory.SkewGramDet.det_ne_zero F E σ B d W r' s' hW) β hβ fun a ha => ?_
    have h := key _ (mem_lagSetB_x M M₁ H H' ha)
    rw [pairX B X X₁ H r s i₀ i₁ W.J hB hX hH, evI_neg', map_neg, neg_eq_zero] at h
    exact h
  subst hβ0
  obtain ⟨c₁, c₂, Z, hc₁, hc₂, hZ, rfl⟩ := GlobalTheory.ThK.DecW.decompose B W W₁ H' r' s' j₀ j₁ hW hH' C hC
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨-, -, -, h⟩ := hB.cm
    let τ : E →+* ℂ := Classical.choice (inferInstance : Nonempty (E →+* ℂ))
    apply τ.injective
    rw [h τ, h τ, star_star]
  have hwe : Matrix.vecMulVec (incV F H.x) α + incM F H.ι * (Matrix.vecMulVec c₁ (incV F H'.x) +
      incM F (1 : Matrix (Fin n₁) (Fin n₁) E) * Z * (incM F H'.ι)ᵀ + Matrix.vecMulVec c₂ (incV F H'.y)) +
      Matrix.vecMulVec (incV F H.y) 0 =
      Matrix.vecMulVec (incV F H.x) α + Matrix.vecMulVec (incM F H.ι *ᵥ c₁) (incV F H'.x) +
        incM F H.ι * Z * (incM F H'.ι)ᵀ + Matrix.vecMulVec (incM F H.ι *ᵥ c₂) (incV F H'.y) := by
    rw [vecMulVec_zero', add_zero, GlobalTheory.ArchSch.OrthPlane.incM_one, Matrix.one_mul, Matrix.mul_add, Matrix.mul_add,
      mul_vecMulVec', mul_vecMulVec', ← Matrix.mul_assoc]
    abel
  rw [hwe] at key hw1 hw2
  clear hwe
  have hc₂0 : c₂ = 0 := by
    refine nondeg σ X₁.J (GlobalTheory.LeviRatHerm.det_low_ne_zero hσ hX.herm
      (GlobalTheory.ArchTraceNondeg.det_J_ne_zero B hX) hX.lat hH) c₂ hc₂ fun c hc => ?_
    have h := key _ (mem_lagSetB_c M M₁ H H' hc)
    rwa [pairC B X W X₁ W₁ H H' r s r' s' i₀ i₁ j₀ j₁ hB hX hW hH hH'] at h
  subst hc₂0
  have hz0 : Matrix.vecMulVec (incM F H.ι *ᵥ (0 : Fin n₁ → AE F E)) (incV F H'.y) = 0 := by
    rw [Matrix.mulVec_zero, Matrix.zero_vecMulVec]
  rw [hz0, add_zero] at key hw1 hw2
  have hp : arch F (M₁.co.e Z).1 = 0 := by
    funext i
    refine GlobalTheory.mixedSpace_traceForm_nondegenerate F _ fun η => ?_
    obtain ⟨z', hz'A, hz'1, hz'2⟩ := GlobalTheory.ArchSch.exists_darboux_lift M₁.co 0 (Pi.single i η)
    have := key _ (mem_lagSetB_z M M₁ H H' hz'A hz'1)
    rw [pairZ B X W X₁ W₁ H H' r s r' s' i₀ i₁ j₀ j₁ hB hX hW hH hH', hω₁, hz'1, hz'2] at this
    simpa [mixedTracePairing_apply, Pi.single_apply] using this
  refine ⟨α, c₁, Z, hα, hc₁, hZ, hp, ?_⟩
  refine Prod.ext ?_ ?_ <;> simp [← hw1, ← hw2]

end GlobalTheory.ArchSchB
