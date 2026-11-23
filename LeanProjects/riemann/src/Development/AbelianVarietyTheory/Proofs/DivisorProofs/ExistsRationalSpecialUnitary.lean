import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignatureUnitaryLatticeFamily
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published GlobalTheory.TamUnf

noncomputable section

namespace GlobalTheory.TamUnf.RatEx

open ReciprocityTheory.ChartRestriction.G.FD in

theorem cT_transpose_of_herm {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    {G δ : Matrix (Fin r) (Fin r) E} (h : ∀ x y, herm G (δ *ᵥ x) (δ *ᵥ y) = herm G x y) :
    Formalism.UG.cT ((IsCMField.complexConj E).toAlgHom : E →+* E) δ * Gᵀ * δ = Gᵀ := by
  ext i j
  have hij := h (Pi.single j 1) (Pi.single i 1)
  simp only [herm, mulVec_single_one, transpose_apply, Pi.single_apply] at hij
  simp only [Formalism.UG.cT, Matrix.mul_apply, transpose_apply, map_apply, Finset.sum_mul] at hij ⊢
  have e : ∀ x, ((IsCMField.complexConj E).toAlgHom : E →+* E) x = cc x := fun x => rfl
  simp only [Matrix.col_apply, ite_mul, zero_mul, one_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hij
  simp only [cc, apply_ite (IsCMField.complexConj E), map_one, map_zero, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at hij
  have hij' := hij.trans (by simp : _ = G j i)
  rw [← hij']
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  change (IsCMField.complexConj E) (δ b i) * G a b * δ a j = _
  ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem sigR_inclR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (x : E) :
    sigR R σ (inclR R x) = inclR R (σ x) := by
  simp [sigR, inclR, Algebra.TensorProduct.map_tmul]

theorem bc_mem_HR (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ}
    {J : Matrix (Fin M) (Fin M) E} {u : GL (Fin M) E} (hu : u ∈ Formalism.UG.UJ (σ : E →+* E) J) :
    Formalism.UG.bc (inclR R) u ∈ HR R σ J := by
  have hu' : Formalism.UG.cT (σ : E →+* E) (u : Matrix (Fin M) (Fin M) E) * J * (u : Matrix (Fin M) (Fin M) E) = J := hu
  show Formalism.UG.cT (sigR R σ) ((u : Matrix (Fin M) (Fin M) E).map (inclR R)) * JR R J *
    (u : Matrix (Fin M) (Fin M) E).map (inclR R) = JR R J
  have hc : Formalism.UG.cT (sigR R σ) ((u : Matrix (Fin M) (Fin M) E).map (inclR R)) =
      (Formalism.UG.cT (σ : E →+* E) (u : Matrix (Fin M) (Fin M) E)).map (inclR R) := by
    ext a b
    simp only [Formalism.UG.cT, transpose_apply, map_apply]
    exact sigR_inclR R σ _
  rw [hc, JR, ← Matrix.map_mul, ← Matrix.map_mul, hu']

theorem exists_SURat_of_isSA : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E)
    (Ψ : Finset (E →+* ℂ)) (θ : Ψ → (Ainf (maximalRealSubfield E) ⊗[maximalRealSubfield E] E →+* ℂ)),
    (∀ ρ : Ψ, IsInfEmb ρ.1 (θ ρ)) →
    ∀ δ : Matrix (Fin r) (Fin r) E, IsSA G (GlobalTheory.UCls.ratM (maximalRealSubfield E) δ) →
      ∃ γ : SUAdelic (IsCMField.complexConj E).toAlgHom Gᵀ,
        γ ∈ (SURat (IsCMField.complexConj E).toAlgHom Gᵀ).subgroupOf (SUAdelic (IsCMField.complexConj E).toAlgHom Gᵀ) ∧
        (∀ ρ : Ψ, infMat (IsCMField.complexConj E).toAlgHom Gᵀ (θ ρ) γ.1 = δ.map ρ.1) ∧
        finMat (IsCMField.complexConj E).toAlgHom Gᵀ γ.1 = GlobalTheory.UCls.ratM (maximalRealSubfield E) δ := by
  intro E _ _ _ r G Ψ θ hθ δ hδ
  obtain ⟨hdet, hherm⟩ := GlobalTheory.SUCount.rat_of_isSA hδ
  let u : GL (Fin r) E := Matrix.GeneralLinearGroup.mk'' δ (by rw [hdet]; exact isUnit_one)
  have hu : u ∈ Formalism.UG.UJ ((IsCMField.complexConj E).toAlgHom : E →+* E) Gᵀ := cT_transpose_of_herm hherm
  let g0 : HR (AF (maximalRealSubfield E)) (IsCMField.complexConj E).toAlgHom Gᵀ :=
    ⟨Formalism.UG.bc (inclR (AF (maximalRealSubfield E))) u, bc_mem_HR _ _ hu⟩
  let g : HA (AF (maximalRealSubfield E)) (IsCMField.complexConj E).toAlgHom Gᵀ := g0
  have hgm : ((HA.mat (AF (maximalRealSubfield E)) (IsCMField.complexConj E).toAlgHom Gᵀ g :
      GL (Fin r) (AF (maximalRealSubfield E) ⊗[maximalRealSubfield E] E)) :
      Matrix (Fin r) (Fin r) (AF (maximalRealSubfield E) ⊗[maximalRealSubfield E] E)) =
      δ.map (inclR (AF (maximalRealSubfield E))) := rfl
  have hgS : g ∈ SUAdelic (IsCMField.complexConj E).toAlgHom Gᵀ := by
    rw [StrongApprox.mem_SUAdelic, hgm]
    have h1 := RingHom.map_det (inclR (F := maximalRealSubfield E) (AF (maximalRealSubfield E))) δ
    rw [hdet, map_one] at h1
    exact h1.symm
  refine ⟨⟨g, hgS⟩, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    refine ⟨hgS, ?_⟩
    exact (Subgroup.mem_subgroupOf (h := g0)).2 (Subgroup.mem_map_of_mem _ hu)
  · intro ρ
    ext a b
    simp only [infMat, map_apply]
    rw [hgm, map_apply]
    simp only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
    exact (hθ ρ).1 (δ a b)
  · ext a b
    simp only [finMat, map_apply]
    rw [hgm, map_apply]
    simp only [inclR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply, GlobalTheory.UCls.ratM]
    rfl

end GlobalTheory.TamUnf.RatEx
