import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsRationalDblCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TsumEnormTermMulLeft

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory.AutomorphicL2Unitary

namespace GlobalTheory.DefDoubling

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

instance isTopologicalRing_adeleE : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)

instance t2Space_adeles_E : T2Space (AE F E) :=
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  GlobalTheory.Doubling.t2Space_tensorProduct_finiteExtension

instance borelSpace_adelicU (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : BorelSpace (UA σ J) := ⟨rfl⟩

theorem transpose_blkMat' {A m k ι : Type} [CommRing A] (e : m ⊕ k ≃ ι) (x : Matrix m m A) (y : Matrix k k A) :
    (blkMat e x y)ᵀ = blkMat e xᵀ yᵀ := by
  simp [blkMat, Matrix.fromBlocks_transpose, Matrix.transpose_submatrix]

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem incM_dblGram : incM F (dblGram finSumFinEquiv J) = dblGram finSumFinEquiv (incM F J) := by
  rw [incM, dblGram, blkMat_map _ _ (map_zero _), Matrix.map_neg _ (map_neg _)]; rfl

theorem blkGL_mem_UG {x y : GL (Fin n) (AE F E)} :
    blkGL finSumFinEquiv (x, y) ∈ UG (cA σ) (incM F (dblGram finSumFinEquiv J)) ↔
      x ∈ UG (cA σ) (incM F J) ∧ y ∈ UG (cA σ) (incM F J) := by
  rw [incM_dblGram]
  change (blkMat finSumFinEquiv x.1 y.1)ᵀ * blkMat finSumFinEquiv (incM F J) (-incM F J) *
      (blkMat finSumFinEquiv x.1 y.1).map (cA σ) = blkMat finSumFinEquiv (incM F J) (-incM F J) ↔
    (x.1ᵀ * incM F J * x.1.map (cA σ) = incM F J) ∧ (y.1ᵀ * incM F J * y.1.map (cA σ) = incM F J)
  rw [blkMat_map _ _ (map_zero _), transpose_blkMat', blkMat_mul, blkMat_mul, blkMat_inj, Matrix.mul_neg,
    Matrix.neg_mul, neg_inj]

def ioA : UA σ J × UA σ J →* UA σ (dblGram finSumFinEquiv J) :=
  ((blkGL finSumFinEquiv).comp ((UG (cA σ) (incM F J)).subtype.prodMap (UG (cA σ) (incM F J)).subtype)).codRestrict _
    fun g => (blkGL_mem_UG σ J).2 ⟨g.1.2, g.2.2⟩

def detA : UA σ J →* (AE F E)ˣ := Matrix.GeneralLinearGroup.det.comp (UG (cA σ) (incM F J)).subtype

theorem countable_ratU : Countable (ratU σ J) := by
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  haveI : Countable (GL (Fin n) E) := Units.val_injective.countable
  refine Function.Injective.countable (f := fun x : ratU σ J =>
    (Classical.choose (Subgroup.mem_subgroupOf.1 x.2) : GL (Fin n) E)) ?_
  intro x y h
  have hx := Classical.choose_spec (Subgroup.mem_subgroupOf.1 x.2)
  have hy := Classical.choose_spec (Subgroup.mem_subgroupOf.1 y.2)
  apply Subtype.ext; apply Subtype.ext
  rw [← hx, ← hy]
  exact congrArg _ h

theorem ioA_one_mem_ratU {γ : UA σ J} (hγ : γ ∈ ratU σ J) : ioA σ J (1, γ) ∈ ratU σ (dblGram finSumFinEquiv J) := by
  obtain ⟨B, hB⟩ := Subgroup.mem_subgroupOf.1 hγ
  refine Subgroup.mem_subgroupOf.2 ⟨blkGL finSumFinEquiv (1, B), Units.ext ?_⟩
  change (blkMat finSumFinEquiv (1 : Matrix (Fin n) (Fin n) E) B.1).map (inclR (F := F) (AF F)) =
    blkMat finSumFinEquiv (1 : Matrix (Fin n) (Fin n) (AE F E)) ((γ : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E))
  rw [blkMat_map _ _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _), ← hB]
  rfl

def ioRat (γ : ratU σ J) : ratU σ (dblGram finSumFinEquiv J) := ⟨ioA σ J (1, γ), ioA_one_mem_ratU σ J γ.2⟩

def chiDetInv (χ : Chr F E) : UA σ J →* Circle := (χ.comp (detA σ J))⁻¹

end GlobalTheory.DefDoubling
