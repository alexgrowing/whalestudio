import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.RationalEmbedding
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagGLConjApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelPlacesNotIsConjPlaceRealDat
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BunExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BSlotD
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead
open GlobalTheory.SeeConjGroup Formalism.L2.SG.HidaSetting
open scoped Matrix

noncomputable section
namespace GlobalTheory.SeeConjGroup

section RedLemmas
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem redV_eq_of_int (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Pl E) (v : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)
    (h : ∀ i, ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).mulVec v i ∈
      Formalism.L2.Herm.intAf F E) (i : Fin n) :
    redV β PP v i = resS F PP ⟨_, h i⟩ := by
  unfold redV
  rw [dif_pos (h i)]

end RedLemmas

theorem redV_add_smul_stab : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)), IsFrame β Λ → ∀ PP : Pl E, (∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, ∀ w ∈ Formalism.L2.Herm.hatL (F := F) Λ, redV β PP (v + w) = redV β PP v + redV β PP w) ∧ (∀ (c : Formalism.L2.Herm.intAf F E), ∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, redV β PP ((c : E ⊗[F] Formalism.L2.Herm.Af F) • v) = resS F PP c • redV β PP v) ∧ (∀ M ∈ St β, ∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, redV β PP ((M : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ v) = ((redFn β PP M : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) *ᵥ redV β PP v) := by
  intro F E _ _ _ _ _ n β Λ hF PP
  have hint : ∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, ∀ i,
      ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).mulVec v i ∈
        Formalism.L2.Herm.intAf F E := fun v hv => (hF v).1 hv
  refine ⟨?_, ?_, ?_⟩
  · intro v hv w hw
    have hs : ∀ i, ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).mulVec (v + w) i ∈
        Formalism.L2.Herm.intAf F E := by
      intro i
      rw [Matrix.mulVec_add]
      exact Subring.add_mem _ (hint v hv i) (hint w hw i)
    funext i
    rw [Pi.add_apply, redV_eq_of_int β PP _ hs, redV_eq_of_int β PP _ (hint v hv), redV_eq_of_int β PP _ (hint w hw),
      ← map_add]
    congr 1
    apply Subtype.ext
    simp [Matrix.mulVec_add]
  · intro c v hv
    have hs : ∀ i, ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).mulVec
        ((c : E ⊗[F] Formalism.L2.Herm.Af F) • v) i ∈ Formalism.L2.Herm.intAf F E := by
      intro i
      rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      exact Subring.mul_mem _ c.2 (hint v hv i)
    funext i
    rw [Pi.smul_apply, smul_eq_mul, redV_eq_of_int β PP _ hs, redV_eq_of_int β PP _ (hint v hv), ← map_mul]
    congr 1
    apply Subtype.ext
    simp [Matrix.mulVec_smul]
  · rintro M ⟨y, rfl⟩ v hv
    set X : Fin n → Formalism.L2.Herm.intAf F E := fun j => ⟨_, hint v hv j⟩ with hX
    have hM : ((frGL β y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) =
        (β : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) * ((intGL F E n y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *
          ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
      simp [frGL, MulAut.conj_apply]
    have hkey : ∀ i, ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).mulVec
        (((frGL β y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ v) i =
        ((((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) *ᵥ X) i : Formalism.L2.Herm.intAf F E) : E ⊗[F] Formalism.L2.Herm.Af F) := by
      intro i
      rw [hM, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.one_mul, ← Matrix.mulVec_mulVec]
      simp only [Matrix.mulVec, dotProduct, hX]
      rw [AddSubmonoidClass.coe_finset_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rfl
    have hs : ∀ i, ((β⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)).mulVec
        (((frGL β y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ v) i ∈
          Formalism.L2.Herm.intAf F E := fun i => by rw [hkey i]; exact Subtype.property _
    funext i
    rw [redV_eq_of_int β PP _ hs, redFn_frGL]
    have e1 : (⟨_, hs i⟩ : Formalism.L2.Herm.intAf F E) = ((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) *ᵥ X) i :=
      Subtype.ext (hkey i)
    rw [e1]
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [redV_eq_of_int β PP _ (hint v hv) j]
    rfl

end GlobalTheory.SeeConjGroup
