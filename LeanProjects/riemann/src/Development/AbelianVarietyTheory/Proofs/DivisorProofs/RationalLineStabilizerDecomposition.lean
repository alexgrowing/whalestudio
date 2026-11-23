import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParabolicLeviUnipotentSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentNormalizerRational
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameDualGram

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

noncomputable section

namespace GlobalTheory.RatStabLevi

open Matrix

theorem rat_levi_dec : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) {n d₁ : ℕ} (W : Spc F E n) (W₁ : Spc F E d₁) (H' : Plane E n d₁) (r s i₀ i₁ : ℕ), IsCMExt F E σ →
    W.IsSkew σ B r s → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ p ∈ ratU σ W.J, ∀ t : (AE F E)ˣ, mat p *ᵥ incV F H'.x = t.1 • incV F H'.x →
    ∃ u ∈ unip σ W H', ∃ h₁ ∈ ratU σ W₁.J, ∃ m : UA σ W.J, IsLevi (W₁ := W₁) H' t h₁ m ∧ p = u * m := by
  intro F E _ _ _ _ _ σ B n d₁ W W₁ H' r s i₀ i₁ hcm hW hH p hp t hpt
  obtain ⟨u, hu, m₁, hm₁, h₁, m₂, hm₂, hpe⟩ :=
    GlobalTheory.StabLineLevi.stab_line_eq_unip_mul_levi F E σ B W W₁ H' r s i₀ i₁ hcm hW hH p t hpt
  obtain ⟨π, hπι, hdec, -⟩ := GlobalTheory.PlaneFrame.frame_dual_gram F E σ B n W r s d₁ W₁ H' i₀ i₁ hcm hW hH
  have hπx : π *ᵥ H'.x = 0 := GlobalTheory.StabLineLevi.proj_x (c := σ.toRingHom) hdec hπι hH.xx hH.xy
  have hπxa : incM F π *ᵥ incV F H'.x = 0 := by
    rw [← GlobalTheory.StabNormal.incM_mulVec, hπx]; funext i; simp [incV]
  have hπιa : incM F π * incM F H'.ι = 1 := by
    rw [← GlobalTheory.LeviUnitary.incM_mul, hπι, GlobalTheory.StabLineLevi.incM_one]

  have hu1 : incM F π * mat u * incM F H'.ι = 1 := by
    refine Matrix.ext_of_mulVec_single fun j => ?_
    obtain ⟨a, ha⟩ := (GlobalTheory.StabNormal.prop_of_mem_unip' H' hu).2 (Pi.single j 1)
    rw [← mulVec_mulVec, ← mulVec_mulVec, ha, mulVec_add, mulVec_smul, hπxa, smul_zero, add_zero,
      mulVec_mulVec, hπιa]
  have hm₁ι : mat m₁ * incM F H'.ι = incM F H'.ι := by rw [hm₁.2.2]; exact Matrix.mul_one _
  have hh₁ : mat h₁ = incM F π * mat p * incM F H'.ι := by
    have e : mat p * incM F H'.ι = mat u * incM F H'.ι * mat h₁ := by
      rw [hpe, GlobalTheory.StabLineLevi.mat_mul', GlobalTheory.StabLineLevi.mat_mul', Matrix.mul_assoc, hm₂.2.2,
        ← Matrix.mul_assoc (mat u * mat m₁), Matrix.mul_assoc (mat u), hm₁ι]
    rw [Matrix.mul_assoc, e, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hu1, Matrix.one_mul]
  rw [ratU, Subgroup.mem_subgroupOf] at hp
  obtain ⟨g, hg⟩ := hp
  have hpg : mat p = incM F (g : Matrix (Fin n) (Fin n) E) := by
    show ((p : GL (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E)) = _
    rw [← hg]; rfl
  set A : Matrix (Fin d₁) (Fin d₁) E := π * (g : Matrix (Fin n) (Fin n) E) * H'.ι with hA
  have hAm : incM F A = mat h₁ := by
    rw [hh₁, hpg, hA, GlobalTheory.LeviUnitary.incM_mul, GlobalTheory.LeviUnitary.incM_mul]
  have hdet : A.det ≠ 0 := by
    intro h0
    have hu' : IsUnit (mat h₁).det := (Matrix.isUnit_iff_isUnit_det _).mp ⟨h₁.1, rfl⟩
    have e : (A.map (inclR (F := F) (AF F))).det = inclR (F := F) (AF F) A.det := (RingHom.map_det _ A).symm
    rw [← hAm, incM, e, h0, map_zero] at hu'
    haveI : Nontrivial (AF F ⊗[F] E) :=
      (Algebra.TensorProduct.includeRight_injective (R := F) (A := AF F) (B := E)
        (AdeleRing.algebraMap_injective (𝓞 F) F)).nontrivial
    exact not_isUnit_zero hu'
  refine ⟨u, hu, h₁, ?_, m₁ * m₂, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [ratU, Subgroup.mem_subgroupOf]
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hdet, Units.ext ?_⟩
    show _ = mat h₁
    rw [← hAm]; rfl
  · rw [GlobalTheory.StabLineLevi.mat_mul', ← mulVec_mulVec, hm₂.1, Units.val_one, one_smul, hm₁.1]
  · rw [GlobalTheory.StabLineLevi.mat_mul', ← mulVec_mulVec, hm₂.2.1, inv_one, Units.val_one, map_one, one_smul, hm₁.2.1]
  · rw [GlobalTheory.StabLineLevi.mat_mul', Matrix.mul_assoc, hm₂.2.2, ← Matrix.mul_assoc, hm₁ι]
  · rw [hpe, mul_assoc]

end GlobalTheory.RatStabLevi
