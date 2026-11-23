import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleOfLinearReductive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleUnitaryIrreducibleRep
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaOfLinearReductive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlkConjTranspose
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSetOfDetLineEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalIsoPartOfSimple

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.AdmGL

variable {ι : Type} [Fintype ι] [DecidableEq ι] {a n : ℕ}

open scoped Classical in

def toGL (M : Matrix (Fin a) (Fin a) (ι → ℂ)) : GL (Fin a) (ι → ℂ) :=
  if h : IsUnit M then h.unit else 1

theorem coe_toGL {M : Matrix (Fin a) (Fin a) (ι → ℂ)} (h : IsUnit M) : (toGL M : Matrix (Fin a) (Fin a) (ι → ℂ)) = M := by
  simp [toGL, h]

theorem toGL_coe (u : GL (Fin a) (ι → ℂ)) : toGL (u : Matrix (Fin a) (Fin a) (ι → ℂ)) = u :=
  Units.ext (coe_toGL u.isUnit)

def blkRep {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e : Fin a × ι ≃ Fin n)
    (σ : GL (Fin a) (ι → ℂ) →* (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ) : H →L[ℂ] H :=
  σ (toGL (unblk e g))

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem blkRep_blk (e : Fin a × ι ≃ Fin n) (σ : GL (Fin a) (ι → ℂ) →* (H →L[ℂ] H)) (u : GL (Fin a) (ι → ℂ)) :
    blkRep e σ (blk e (u : Matrix (Fin a) (Fin a) (ι → ℂ))) = σ u := by
  rw [blkRep, unblk_blk, toGL_coe]

theorem blk_coe_mem (e : Fin a × ι ≃ Fin n) (u : GL (Fin a) (ι → ℂ)) :
    blk e (u : Matrix (Fin a) (Fin a) (ι → ℂ)) ∈ blkG e := ⟨_, u.isUnit, rfl⟩

theorem exists_gl_of_mem (e : Fin a × ι ≃ Fin n) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ blkG e) :
    ∃ u : GL (Fin a) (ι → ℂ), g = blk e (u : Matrix (Fin a) (Fin a) (ι → ℂ)) := by
  obtain ⟨M, hM, rfl⟩ := hg
  exact ⟨hM.unit, rfl⟩

theorem continuousOn_toGL_unblk (e : Fin a × ι ≃ Fin n) :
    ContinuousOn (fun g => toGL (unblk e g) : Matrix (Fin n) (Fin n) ℂ → GL (Fin a) (ι → ℂ)) (blkG e) := by
  rw [continuousOn_iff_continuous_restrict]
  have hval : ∀ g : blkG e, ((toGL (unblk e g.1) : GL (Fin a) (ι → ℂ)) : Matrix (Fin a) (Fin a) (ι → ℂ)) = unblk e g.1 := by
    rintro ⟨_, M, hM, rfl⟩
    rw [unblk_blk]
    exact coe_toGL hM
  have hinv : ∀ g : blkG e, (((toGL (unblk e g.1))⁻¹ : GL (Fin a) (ι → ℂ)) : Matrix (Fin a) (Fin a) (ι → ℂ)) =
      unblk e (g.1.det⁻¹ • g.1.adjugate) := by
    rintro ⟨_, M, hM, rfl⟩
    have h := blk_inv e hM
    rw [Matrix.inv_def, Ring.inverse_eq_inv'] at h
    simp only [h, unblk_blk]
    rw [Matrix.coe_units_inv, coe_toGL hM]
  have hdet : ∀ g : blkG e, g.1.det ≠ 0 := fun g =>
    ((Matrix.isUnit_iff_isUnit_det _).1 ((mem_blkG_iff e).1 g.2).1).ne_zero
  have hc : Continuous fun g : blkG e => g.1.det⁻¹ • g.1.adjugate :=
    (Continuous.inv₀ continuous_subtype_val.matrix_det hdet).smul continuous_subtype_val.matrix_adjugate
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact ((continuous_unblk e).comp continuous_subtype_val).congr fun g => (hval g).symm
  · exact ((continuous_unblk e).comp hc).congr fun g => (hinv g).symm

theorem isURepOn_blkRep (e : Fin a × ι ≃ Fin n) {σ : GL (Fin a) (ι → ℂ) →* (H →L[ℂ] H)} (hσ : IsUnitaryRep σ) :
    Formalism.MainNotions.S.IsURepOn (blkG e) (blkRep e σ) := by
  refine ⟨⟨?_, ?_⟩, fun g _ v => hσ.norm_apply _ v, fun v =>
    (hσ.continuous_apply v).comp_continuousOn (continuousOn_toGL_unblk e)⟩
  · have h := blkRep_blk e σ 1
    simpa using h
  · intro g hg h hh
    obtain ⟨u, rfl⟩ := exists_gl_of_mem e hg
    obtain ⟨v, rfl⟩ := exists_gl_of_mem e hh
    rw [← blk_mul, ← Units.val_mul, blkRep_blk, blkRep_blk, blkRep_blk, map_mul]
    rfl

theorem isIrredOn_blkRep (e : Fin a × ι ≃ Fin n) {σ : GL (Fin a) (ι → ℂ) →* (H →L[ℂ] H)}
    (hi : IsTopIrreducible σ) : Formalism.MainNotions.S.IsIrredOn (blkG e) (blkRep e σ) := fun S hS hinv =>
  hi.2 S ⟨hS, fun u v hv => by
    have h := hinv _ (blk_coe_mem e u) v hv
    rwa [blkRep_blk] at h⟩

theorem blk_mem_maxCpt (e : Fin a × ι ≃ Fin n) (k : Matrix.unitaryGroup (Fin a) (ι → ℂ)) :
    blk e k.1 ∈ GlobalTheory.LinRed.maxCpt (blkG e) := by
  refine ⟨blk_coe_mem e (Unitary.toUnits k), ?_⟩
  rw [SetLike.mem_coe, Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← blk_conjTranspose, ← blk_mul,
    ← Matrix.star_eq_conjTranspose, (Matrix.mem_unitaryGroup_iff).1 k.2, blk_one]

theorem exists_unitary_of_mem_maxCpt (e : Fin a × ι ≃ Fin n) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ GlobalTheory.LinRed.maxCpt (blkG e)) :
    ∃ k : Matrix.unitaryGroup (Fin a) (ι → ℂ), g = blk e k.1 := by
  obtain ⟨⟨M, -, rfl⟩, hu⟩ := hg
  refine ⟨⟨M, ?_⟩, rfl⟩
  rw [SetLike.mem_coe, Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← blk_conjTranspose, ← blk_mul,
    ← blk_one e, ← Matrix.star_eq_conjTranspose] at hu
  rw [Matrix.mem_unitaryGroup_iff]
  exact blk_injective e hu

theorem finiteDimensional_isoPart_gl [CompleteSpace H] {σ : GL (Fin a) (ι → ℂ) →* (H →L[ℂ] H)}
    (hσ : IsUnitaryRep σ) (hi : IsTopIrreducible σ) {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin a) (ι → ℂ)) W) :
    FiniteDimensional ℂ (isoPart (σ.comp Unitary.toUnits) ρ) := by
  let e := Fintype.equivFin (Fin a × ι)
  have hLR := isLinRed_blkG e
  have hA := GlobalTheory.CompanionTheory.admitted.isAdmissible_of_unitary_irreducible hLR
    (GlobalTheory.CompanionTheory.AdmIwa.RamifiedPrimeLengthBound hLR (GlobalTheory.CompanionTheory.IwaGen.iwaOn_of_isLinRed hLR)) H (blkRep e σ)
    (isURepOn_blkRep e hσ) (isIrredOn_blkRep e hi)
  have hrep : ∀ k : Matrix.unitaryGroup (Fin a) (ι → ℂ),
      blkRep e σ (blk e k.1) = (σ.comp Unitary.toUnits) k := fun k => blkRep_blk e σ (Unitary.toUnits k)
  refine finiteDimensional_isoPart (π := σ.comp Unitary.toUnits) (fun k v => hσ.norm_apply _ v) ?_ _ W ρ rfl
  intro S hfd hS hirr
  have hKS : GlobalTheory.LinRed.IsKStable (blkG e) (blkRep e σ) S := by
    intro g hg w hw
    obtain ⟨k, rfl⟩ := exists_unitary_of_mem_maxCpt e hg
    rw [hrep]
    exact hS k w hw
  have hirr' : ∀ S' : Submodule ℂ H, S' ≤ S → GlobalTheory.LinRed.IsKStable (blkG e) (blkRep e σ) S' → S' = ⊥ ∨ S' = S :=
    fun S' hle hst => hirr S' hle fun k w hw => by
      have h := hst _ (blk_mem_maxCpt e k) w hw
      rwa [hrep] at h
  have hfin := hA.2.2.2 S hfd hKS hirr'
  have heq : {S' : Submodule ℂ H | ∃ T : H →ₗ[ℂ] H, S' = S.map T ∧
      ∀ k, ∀ w ∈ S, T ((σ.comp Unitary.toUnits) k w) = (σ.comp Unitary.toUnits) k (T w)} =
      {S' | ∃ T : H →ₗ[ℂ] H, S' = S.map T ∧ ∀ k ∈ GlobalTheory.LinRed.maxCpt (blkG e), ∀ w ∈ S,
        T (blkRep e σ k w) = blkRep e σ k (T w)} := by
    ext S'
    constructor
    · rintro ⟨T, rfl, hT⟩
      refine ⟨T, rfl, fun g hg w hw => ?_⟩
      obtain ⟨k, rfl⟩ := exists_unitary_of_mem_maxCpt e hg
      rw [hrep]
      exact hT k w hw
    · rintro ⟨T, rfl, hT⟩
      refine ⟨T, rfl, fun k w hw => ?_⟩
      rw [← hrep]
      exact hT _ (blk_mem_maxCpt e k) w hw
  rw [heq]
  exact hfin

theorem admissible_GL_Cinf : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : GL (Fin a) (Cinf E) →* (H →L[ℂ] H)), IsUnitaryRep σ → IsTopIrreducible σ → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Kinf E a) W), FiniteDimensional ℂ ↥(⨆ (T : W →ₗ[ℂ] H) (_ : ∀ k w, T (ρ k w) = σ (Unitary.toUnits k) (T w)), LinearMap.range T : Submodule ℂ H) := by
  intro E _ _ _ a H _ _ _ σ hσ hi W _ _ _ ρ
  classical
  exact finiteDimensional_isoPart_gl hσ hi ρ

end GlobalTheory.CompanionTheory.AdmGL

end
