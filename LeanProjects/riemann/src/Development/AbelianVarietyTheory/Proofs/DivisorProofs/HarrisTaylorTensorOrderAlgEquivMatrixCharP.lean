import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrysActApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QActMSubAlgebraMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CharPMatrix

variable (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]

def redHom : ℤ_[p] →+* k := (ZMod.castHom (dvd_refl p) k).comp PadicInt.toZMod

lemma exists_nat_add (z : ℤ_[p]) : ∃ n : ℕ, ∃ w : ℤ_[p], z = n + p * w := by
  have h := PadicInt.sub_zmodRepr_mem z
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h
  obtain ⟨w, hw⟩ := h
  exact ⟨PadicInt.zmodRepr z, w, by rw [mul_comm, hw]; ring⟩

variable (B : Type) [Ring B] [Algebra k B]

def tensorPadicEquiv : B ⊗[ℤ] ℤ_[p] ≃ₐ[k] B :=
  AlgEquiv.ofAlgHom
    (Algebra.TensorProduct.lift (AlgHom.id k B)
      (((algebraMap k B).comp (redHom p k)).toIntAlgHom)
      (by intro x y; exact Algebra.commute_algebraMap_right _ _))
    Algebra.TensorProduct.includeLeft
    (by ext b; simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply]; erw [Algebra.TensorProduct.lift_tmul]; simp)
    (by
      apply Algebra.TensorProduct.ext'
      intro b z
      obtain ⟨n, w, rfl⟩ := exists_nat_add p z
      have hp : (p : B) = 0 := by
        rw [← map_natCast (algebraMap k B), CharP.cast_eq_zero, map_zero]
      simp [redHom, Algebra.TensorProduct.lift_tmul]
      have h1 : b ⊗ₜ[ℤ] ((p : ℤ_[p]) * w) = 0 := by
        rw [show ((p : ℤ_[p]) * w) = (p : ℤ) • w by simp, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul', Algebra.smul_def, eq_intCast, Int.cast_natCast, hp, zero_mul,
          TensorProduct.zero_tmul]
      have h2 : b ⊗ₜ[ℤ] (n : ℤ_[p]) = (b * n) ⊗ₜ[ℤ] 1 := by
        rw [show (n : ℤ_[p]) = (n : ℤ) • (1 : ℤ_[p]) by simp, TensorProduct.tmul_smul,
          TensorProduct.smul_tmul', Algebra.smul_def, eq_intCast, Int.cast_natCast, Nat.cast_comm]
      rw [TensorProduct.tmul_add, h1, h2, add_zero])

def matrixBaseChange (R : Type) [CommRing R] (K : Type) [CommRing K] [Algebra R K]
    (n : Type) [Fintype n] [DecidableEq n] : K ⊗[R] Matrix n n R ≃ₐ[K] Matrix n n K :=
  AlgEquiv.ofRingEquiv (f := (matrixEquivTensor n R K).symm.toRingEquiv) (by
    intro c
    simp only [AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply, matrixEquivTensor_apply_symm, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [Algebra.algebraMap_eq_smul_one])

end GlobalTheory.CharPMatrix

namespace GlobalTheory.UPel.HT

open GlobalTheory.CharPMatrix in

theorem Datum.charP_tensor_matrix : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (k : Type) [Field k]
    [CharP k p] [Algebra (𝓞 D.F) k], Nonempty ((k ⊗[𝓞 D.F] D.O) ≃ₐ[k] Matrix (Fin D.m) (Fin D.m) k) := by
  intro p _ D k _ _ _
  obtain ⟨e⟩ := D.splitP
  have E0 : k ⊗[𝓞 D.F] (𝓞 D.F ⊗[ℤ] ℤ_[p]) ≃ₐ[k] k :=
    (Algebra.TensorProduct.cancelBaseChange ℤ (𝓞 D.F) k k ℤ_[p]).trans (tensorPadicEquiv p k k)
  have E1 := (Algebra.TensorProduct.assoc ℤ (𝓞 D.F) (𝓞 D.F) D.O (𝓞 D.F) ℤ_[p]).symm.trans
    (Algebra.TensorProduct.congr (Algebra.TensorProduct.rid (𝓞 D.F) (𝓞 D.F) D.O) (AlgEquiv.refl (R := ℤ) (A₁ := ℤ_[p])))
  have E2 := E1.trans e
  exact ⟨(Algebra.TensorProduct.congr E0.symm (AlgEquiv.refl (R := 𝓞 D.F) (A₁ := D.O))).trans
    ((Algebra.TensorProduct.assoc (𝓞 D.F) (𝓞 D.F) k k (𝓞 D.F ⊗[ℤ] ℤ_[p]) D.O).trans
    ((Algebra.TensorProduct.congr AlgEquiv.refl
      ((Algebra.TensorProduct.comm (𝓞 D.F) (𝓞 D.F ⊗[ℤ] ℤ_[p]) D.O).trans
        (E2.trans (matrixEquivTensor (Fin D.m) (𝓞 D.F) (𝓞 D.F ⊗[ℤ] ℤ_[p]))))).trans
    ((Algebra.TensorProduct.assoc (𝓞 D.F) (𝓞 D.F) k k (𝓞 D.F ⊗[ℤ] ℤ_[p])
      (Matrix (Fin D.m) (Fin D.m) (𝓞 D.F))).symm.trans
    ((Algebra.TensorProduct.congr E0 AlgEquiv.refl).trans
    (matrixBaseChange (𝓞 D.F) k (Fin D.m))))))⟩

end GlobalTheory.UPel.HT
