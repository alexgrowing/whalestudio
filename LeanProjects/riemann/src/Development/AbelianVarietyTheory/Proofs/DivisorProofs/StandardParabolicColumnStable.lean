import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockCentre
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalFieldNormValuation
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct
open Matrix

namespace GlobalTheory.StdPar.UnipCrit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ} {r : ℕ}

omit [NumberField E] in

theorem colSpan_mono (X : Matrix (Fin n) (Fin r) E) {I I' : Set (Fin r)} (h : I ⊆ I') :
    GlobalTheory.StdPar.colSpan F X I ≤ GlobalTheory.StdPar.colSpan F X I' :=
  Submodule.span_mono (Set.image_mono h)

omit [NumberField E] in

theorem colPerp_anti (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (X : Matrix (Fin n) (Fin r) E)
    {I I' : Set (Fin r)} (h : I ⊆ I') :
    GlobalTheory.StdPar.colPerp σ J X I' ≤ GlobalTheory.StdPar.colPerp σ J X I :=
  biInf_mono h

omit [NumberField E] in

theorem mulVec_mem (X : Matrix (Fin n) (Fin r) E) (M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (i : Fin r)
    (hM : ∀ j : Fin r, M *ᵥ (adMat F X)ᵀ j - (adMat F X)ᵀ j ∈ GlobalTheory.StdPar.colSpan F X {l | l < j ∧ l ≤ i})
    (I : Set (Fin r)) (hI : ∀ l ∈ I, ∀ m < l, m ∈ I) :
    ∀ y ∈ GlobalTheory.StdPar.colSpan F X I, M *ᵥ y ∈ GlobalTheory.StdPar.colSpan F X I := by
  have : GlobalTheory.StdPar.colSpan F X I ≤ (GlobalTheory.StdPar.colSpan F X I).comap M.mulVecLin := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨l, hl, rfl⟩
    have h1 : (adMat F X)ᵀ l ∈ GlobalTheory.StdPar.colSpan F X I := Submodule.subset_span ⟨l, hl, rfl⟩
    have h2 := colSpan_mono (F := F) X (I' := I) (fun m hm => hI l hl m hm.1) (hM l)
    have h3 := add_mem h2 h1
    rw [sub_add_cancel] at h3
    exact h3
  exact fun y hy => this hy

theorem mem_unip :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X : Matrix (Fin n) (Fin r) E)
    (S : Finset (Fin r)), (∀ k ∈ S, ∀ i ≤ k, i ∈ S) → ∀ i ∈ S, ∀ h : GAd σ J,
    (∀ h' ∈ ({h, h⁻¹} : Set (GAd σ J)),
      (∀ j : Fin r, (matHom _ σ J h').1 *ᵥ (adMat F X)ᵀ j - (adMat F X)ᵀ j ∈ GlobalTheory.StdPar.colSpan F X {l | l < j ∧ l ≤ i}) ∧
      ∀ y ∈ GlobalTheory.StdPar.colPerp σ J X {l | l ≤ i}, (matHom _ σ J h').1 *ᵥ y - y ∈ GlobalTheory.StdPar.colSpan F X {l | l ≤ i}) →
    h ∈ GlobalTheory.StdPar.unip σ J X S := by
  intro F E _ _ _ _ _ σ n J r X S hS i hi h H
  obtain ⟨h1, h2⟩ := H h (Or.inl rfl)
  obtain ⟨h3, -⟩ := H h⁻¹ (Or.inr rfl)
  have e : ∀ y, (matHom _ σ J h⁻¹).1 *ᵥ (matHom _ σ J h).1 *ᵥ y = y := fun y => by
    rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_mulVec]
  have key : ∀ I : Set (Fin r), (∀ l ∈ I, ∀ m < l, m ∈ I) → ∀ y,
      y ∈ GlobalTheory.StdPar.colSpan F X I ↔ (matHom _ σ J h).1 *ᵥ y ∈ GlobalTheory.StdPar.colSpan F X I := fun I hI y =>
    ⟨mulVec_mem X _ i h1 I hI y, fun hy => by
      have := mulVec_mem X _ i h3 I hI _ hy
      rwa [e] at this⟩
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun j => ⟨key _ ?_, fun y hy => ?_⟩, key _ ?_, fun y hy => ?_⟩
  · rintro l ⟨k, hk, hlk, hkj⟩ m hm
    exact ⟨k, hk, hm.le.trans hlk, hkj⟩
  · unfold GlobalTheory.StdPar.colSpan at hy
    rw [Set.image_singleton, Submodule.mem_span_singleton] at hy
    obtain ⟨a, rfl⟩ := hy
    rw [mulVec_smul, ← smul_sub]
    refine Submodule.smul_mem _ a (colSpan_mono X ?_ (h1 j))
    rintro m ⟨hmj, hmi⟩
    exact ⟨m, hS i hi m hmi, le_rfl, hmj⟩
  · rintro l ⟨k, hk, hlk⟩ m hm
    exact ⟨k, hk, hm.le.trans hlk⟩
  · have hsub : {l : Fin r | l ≤ i} ⊆ {l | ∃ k ∈ S, l ≤ k} := fun l hl => ⟨i, hi, hl⟩
    exact colSpan_mono X hsub (h2 y (colPerp_anti σ J X hsub hy))

end GlobalTheory.StdPar.UnipCrit
