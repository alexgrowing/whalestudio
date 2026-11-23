import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemImLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddHaarLeftRightMulAdelicMatricesModule
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRestrictScalarsMatrixLeftRightMulAdeleTens

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviModulus

theorem sigR_eq_cA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (x : AE F E) : sigR (AF F) σ x = cA σ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem absE_det_UA (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {b : ℕ} (J₁ : Matrix (Fin b) (Fin b) E) (hJ : J₁.det ≠ 0) (g : UA σ J₁) :
    absE F E (Matrix.GeneralLinearGroup.det (g : GL (Fin b) (AE F E))) = 1 := by
  have hM : ((g : GL (Fin b) (AE F E)) : Matrix (Fin b) (Fin b) (AE F E))ᵀ * incM F J₁ *
      ((g : GL (Fin b) (AE F E)) : Matrix (Fin b) (Fin b) (AE F E)).map (cA σ) = incM F J₁ := g.2
  have hdet := congrArg Matrix.det hM
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hdet
  have hmap : (((g : GL (Fin b) (AE F E)) : Matrix (Fin b) (Fin b) (AE F E)).map (cA σ)).det =
      cA σ ((g : GL (Fin b) (AE F E)) : Matrix (Fin b) (Fin b) (AE F E)).det :=
    (RingHom.map_det (cA σ).toRingHom _).symm
  have hJu : IsUnit (incM F J₁).det := by
    have : (incM F J₁).det = inclR (F := F) (AF F) J₁.det := (RingHom.map_det _ _).symm
    rw [this]
    exact (isUnit_iff_ne_zero.2 hJ).map _
  rw [hmap] at hdet
  have key : cA σ ((g : GL (Fin b) (AE F E)) : Matrix (Fin b) (Fin b) (AE F E)).det *
      ((g : GL (Fin b) (AE F E)) : Matrix (Fin b) (Fin b) (AE F E)).det = 1 := by
    have e2 : cA σ ((g : GL (Fin b) (AE F E)) : Matrix (Fin b) (Fin b) (AE F E)).det *
        ((g : GL (Fin b) (AE F E)) : Matrix (Fin b) (Fin b) (AE F E)).det * (incM F J₁).det =
        1 * (incM F J₁).det := by
      rw [one_mul]; nth_rewrite 2 [← hdet]; ring
    exact hJu.mul_right_cancel e2
  have hu : GlobalTheory.Doubling.conjUnit σ (Matrix.GeneralLinearGroup.det (g : GL (Fin b) (AE F E))) *
      Matrix.GeneralLinearGroup.det (g : GL (Fin b) (AE F E)) = 1 := by
    ext
    show sigR (AF F) σ _ * _ = 1
    rw [sigR_eq_cA]
    exact key
  have h2 := congrArg (absE F E) hu
  rw [map_mul, GlobalTheory.Doubling.absE_conjUnit, map_one, ← sq] at h2
  exact (pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).1 h2

def colCE (R : Type) [TopologicalSpace R] [AddCommGroup R] (b : ℕ) : Matrix (Fin b) (Fin 1) R ≃ₜ+ (Fin b → R) where
  toFun u i := u i 0
  invFun x := Matrix.of fun i _ => x i
  left_inv u := by
    ext i j
    rw [Subsingleton.elim j 0]
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  continuous_toFun := continuous_pi fun i => continuous_id.matrix_elem i 0
  continuous_invFun := continuous_pi fun i => continuous_pi fun _ => continuous_apply i

theorem modulus_levi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (b : ℕ) (J₁ : Matrix (Fin b) (Fin b) E), J₁.det ≠ 0 → ∀ (l : (AE F E)ˣ) (g₀ : UA σ J₁)
    [IsTopologicalAddGroup (Fin b → AE F E)] [LocallyCompactSpace (Fin b → AE F E)] [MeasurableSpace (Fin b → AE F E)]
    [BorelSpace (Fin b → AE F E)] (A : (Fin b → AE F E) ≃ₜ+ (Fin b → AE F E)),
    (∀ a, A a = l.1 • ((mat g₀⁻¹)ᵀ *ᵥ a)) → addEquivAddHaarChar A = absE F E l ^ b := by
  intro F E _ _ _ _ _ σ hCM b J₁ hJ l g₀ _ _ _ _ A hA
  haveI : IsTotallyReal F := hCM.1
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  letI : MeasurableSpace (Matrix (Fin b) (Fin 1) (AF F ⊗[F] E)) := borel _
  haveI : BorelSpace (Matrix (Fin b) (Fin 1) (AF F ⊗[F] E)) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Matrix (Fin b) (Fin 1) (AF F ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin b → Fin 1 → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin b) (Fin 1) (AF F ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin b → Fin 1 → AE F E))
  let M : Matrix (Fin b) (Fin b) (AE F E) := l.1 • (mat g₀⁻¹)ᵀ
  have hMdet : M.det = l.1 ^ b * (Matrix.GeneralLinearGroup.det ((g₀⁻¹ : UA σ J₁) : GL (Fin b) (AE F E))).1 := by
    simp only [M, Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin, Matrix.GeneralLinearGroup.val_det_apply]
    rfl
  have hMu : IsUnit M.det := by
    rw [hMdet]
    exact (l.isUnit.pow b).mul (Units.isUnit _)
  let G : GL (Fin b) (AE F E) := Matrix.nonsingInvUnit M hMu
  have hG : Matrix.GeneralLinearGroup.det G = l ^ b * Matrix.GeneralLinearGroup.det ((g₀⁻¹ : UA σ J₁) : GL (Fin b) (AE F E)) := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul, Units.val_pow_eq_pow_val]
    exact hMdet
  have hAeq : A = ((colCE (AE F E) b).symm.trans (GlobalTheory.ModuLR.lrCE G 1)).trans (colCE (AE F E) b) := by
    ext x i
    rw [hA]
    show (l.1 • ((mat g₀⁻¹)ᵀ *ᵥ x)) i = (M * Matrix.of (fun i (_ : Fin 1) => x i) * (1 : Matrix (Fin 1) (Fin 1) (AE F E))) i 0
    rw [Matrix.mul_one]
    simp only [M, Matrix.mulVec, Matrix.mul_apply, dotProduct, Matrix.of_apply, Pi.smul_apply, Matrix.smul_apply,
      smul_eq_mul, Finset.mul_sum, mul_assoc]
  rw [hAeq, GlobalTheory.ModuLR.addEquivAddHaarChar_transport, GlobalTheory.ModuLR.chi_lr F E b 1 G 1, hG]
  simp only [map_one, one_pow, mul_one, pow_one, map_mul, map_pow, absE_det_UA F E σ J₁ hJ]

end GlobalTheory.LeviModulus
