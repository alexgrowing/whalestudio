import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInvertibleUnitaryAdelicMatrixOfRationalUnitary

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published GlobalTheory.TamUnf

namespace GlobalTheory.TamUnf.RatIn

theorem exists_rat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E)
    (Ψ : Finset (E →+* ℂ)) (θ : Ψ → (Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E →+* ℂ)),
    (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ ρ : Ψ, IsInfEmb ρ.1 (θ ρ)) →
    ∀ γ : SUAdelic (IsCMField.complexConj E).toAlgHom Gᵀ,
      γ ∈ (SURat (IsCMField.complexConj E).toAlgHom Gᵀ).subgroupOf (SUAdelic (IsCMField.complexConj E).toAlgHom Gᵀ) →
      ∃ δ : Matrix (Fin r) (Fin r) E, IsSA G (GlobalTheory.UCls.ratM (maximalRealSubfield E) δ) ∧
        (∀ ρ : Ψ, infMat (IsCMField.complexConj E).toAlgHom Gᵀ (θ ρ) γ.1 = δ.map ρ.1) ∧
        finMat (IsCMField.complexConj E).toAlgHom Gᵀ γ.1 = GlobalTheory.UCls.ratM (maximalRealSubfield E) δ := by
  intro E _ _ _ r G Ψ θ _ hθ γ hγ
  obtain ⟨δ, hδ, hδγ⟩ := (Subgroup.mem_subgroupOf.1 hγ).2
  have hm : ((HA.mat (AF (maximalRealSubfield E)) (IsCMField.complexConj E).toAlgHom Gᵀ γ.1 :
      GL (Fin r) (AF (maximalRealSubfield E) ⊗[maximalRealSubfield E] E)) :
        Matrix (Fin r) (Fin r) (AF (maximalRealSubfield E) ⊗[maximalRealSubfield E] E)) =
      (δ : Matrix (Fin r) (Fin r) E).map (inclR (F := maximalRealSubfield E) (AF (maximalRealSubfield E))) :=
    (congrArg Units.val hδγ).symm
  have hdet : ((HA.mat (AF (maximalRealSubfield E)) (IsCMField.complexConj E).toAlgHom Gᵀ γ.1 :
      GL (Fin r) (AF (maximalRealSubfield E) ⊗[maximalRealSubfield E] E)) :
        Matrix (Fin r) (Fin r) (AF (maximalRealSubfield E) ⊗[maximalRealSubfield E] E)).det = 1 :=
    congrArg Units.val (MonoidHom.mem_ker.1 γ.2)
  have hfin : finMat (IsCMField.complexConj E).toAlgHom Gᵀ γ.1 =
      GlobalTheory.UCls.ratM (maximalRealSubfield E) (δ : Matrix (Fin r) (Fin r) E) := by
    unfold finMat
    rw [hm]
    ext a b
    simp [inclR, GlobalTheory.UCls.ratM]
  refine ⟨δ, ⟨GlobalTheory.RatUnit.isUA_ratM E r G _ δ.det_ne_zero fun x y => ?_, ?_⟩, fun ρ => ?_, hfin⟩
  · have hu : Formalism.UG.cT ((IsCMField.complexConj E).toAlgHom : E →+* E) (δ : Matrix (Fin r) (Fin r) E) * Gᵀ *
        (δ : Matrix (Fin r) (Fin r) E) = Gᵀ := hδ
    have hG : (δ : Matrix (Fin r) (Fin r) E)ᵀ * G *
        (δ : Matrix (Fin r) (Fin r) E).map ((IsCMField.complexConj E).toAlgHom : E →+* E) = G := by
      have := congrArg Matrix.transpose hu
      simpa [Formalism.UG.cT, Matrix.transpose_mul, Matrix.mul_assoc] using this
    have := GlobalTheory.RatUnit.dot_mulVec ((IsCMField.complexConj E).toAlgHom : E →+* E) G δ x y
    rw [hG, ← GlobalTheory.RatUnit.sum_eq_dot, ← GlobalTheory.RatUnit.sum_eq_dot] at this
    exact this
  · rw [← hfin]
    unfold finMat
    have := (Algebra.TensorProduct.map (sndA (maximalRealSubfield E))
      (AlgHom.id (maximalRealSubfield E) E)).map_det
      ((HA.mat (AF (maximalRealSubfield E)) (IsCMField.complexConj E).toAlgHom Gᵀ γ.1 :
      GL (Fin r) (AF (maximalRealSubfield E) ⊗[maximalRealSubfield E] E)) :
        Matrix (Fin r) (Fin r) (AF (maximalRealSubfield E) ⊗[maximalRealSubfield E] E))
    rw [hdet, map_one] at this
    exact this.symm
  · unfold infMat
    rw [hm]
    ext a b
    simp only [Matrix.map_apply]
    rw [← (hθ ρ).1]
    simp [inclR]

end GlobalTheory.TamUnf.RatIn
