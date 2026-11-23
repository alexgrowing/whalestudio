import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.ProdFirstProjectionSmul

noncomputable section

namespace MassDataMassesW.SplitW

open scoped TensorProduct
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Measures

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem HA_ext {R : Type} [CommRing R] [Algebra F R] {g h : HA R σ J}
    (e : ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = HA.mat R σ J h) :
    g = h := Subtype.ext (Units.ext e)

theorem continuous_haMap {R R' : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] [CommRing R']
    [Algebra F R'] [TopologicalSpace R'] (φ : R →ₐ[F] R') (hφ : Continuous (tensMap (E := E) φ)) :
    Continuous (haMap σ J φ) := by
  refine continuous_induced_rng.2 ?_
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · have hc : Continuous fun g : HA R σ J =>
        ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
      Units.continuous_val.comp continuous_subtype_val
    exact hc.matrix_map hφ
  · have hc : Continuous fun g : HA R σ J =>
        (((HA.mat R σ J g)⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
      Units.continuous_coe_inv.comp continuous_subtype_val
    exact hc.matrix_map hφ

variable (R1 R2 : Type) [CommRing R1] [Algebra F R1] [CommRing R2] [Algebra F R2]

def mix (M1 : Matrix (Fin n) (Fin n) (R1 ⊗[F] E)) (M2 : Matrix (Fin n) (Fin n) (R2 ⊗[F] E)) :
    Matrix (Fin n) (Fin n) ((R1 × R2) ⊗[F] E) :=
  Matrix.of fun i j => (QQ R1 R2).symm (M1 i j, M2 i j)

theorem mix_mul (M1 N1 : Matrix (Fin n) (Fin n) (R1 ⊗[F] E)) (M2 N2 : Matrix (Fin n) (Fin n) (R2 ⊗[F] E)) :
    mix R1 R2 M1 M2 * mix R1 R2 N1 N2 = mix R1 R2 (M1 * N1) (M2 * N2) := by
  ext i j
  simp only [mix, Matrix.mul_apply, Matrix.of_apply, ← map_mul, Prod.mk_mul_mk, ← map_sum]
  congr 1
  ext
  · simp only [Prod.fst_sum]
  · simp only [Prod.snd_sum]

theorem mix_one : mix (n := n) (F := F) (E := E) R1 R2 1 1 = 1 := by
  ext i j
  simp only [mix, Matrix.of_apply, Matrix.one_apply]
  split_ifs
  · exact map_one _
  · exact map_zero _

theorem mixMatrix_map_first (M1 : Matrix (Fin n) (Fin n) (R1 ⊗[F] E)) (M2 : Matrix (Fin n) (Fin n) (R2 ⊗[F] E)) :
    (mix R1 R2 M1 M2).map (q1 R1 R2) = M1 := by
  ext i j
  simp only [Matrix.map_apply, mix, Matrix.of_apply]
  exact congrArg Prod.fst ((QQ R1 R2).apply_symm_apply (M1 i j, M2 i j))

theorem mixMatrix_map_second (M1 : Matrix (Fin n) (Fin n) (R1 ⊗[F] E)) (M2 : Matrix (Fin n) (Fin n) (R2 ⊗[F] E)) :
    (mix R1 R2 M1 M2).map (q2 R1 R2) = M2 := by
  ext i j
  simp only [Matrix.map_apply, mix, Matrix.of_apply]
  exact congrArg Prod.snd ((QQ R1 R2).apply_symm_apply (M1 i j, M2 i j))

theorem mix_split (M : Matrix (Fin n) (Fin n) ((R1 × R2) ⊗[F] E)) :
    mix R1 R2 (M.map (q1 R1 R2)) (M.map (q2 R1 R2)) = M := by
  ext i j
  simp only [Matrix.map_apply, mix, Matrix.of_apply]
  exact (QQ R1 R2).symm_apply_apply (M i j)

def mixGL (g1 : GL (Fin n) (R1 ⊗[F] E)) (g2 : GL (Fin n) (R2 ⊗[F] E)) : GL (Fin n) ((R1 × R2) ⊗[F] E) where
  val := mix R1 R2 (g1 : Matrix (Fin n) (Fin n) (R1 ⊗[F] E)) g2
  inv := mix R1 R2 ((g1⁻¹ : GL (Fin n) (R1 ⊗[F] E)) : Matrix (Fin n) (Fin n) (R1 ⊗[F] E)) (g2⁻¹ : GL (Fin n) (R2 ⊗[F] E))
  val_inv := by rw [mix_mul, Units.mul_inv, Units.mul_inv, mix_one]
  inv_val := by rw [mix_mul, Units.inv_mul, Units.inv_mul, mix_one]

theorem formMatrix_map_first : (JR (R1 × R2) J).map (q1 (F := F) R1 R2) = JR R1 J := by
  ext i j
  simp [JR, inclR, q1, tensMap, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]

theorem formMatrix_map_second : (JR (R1 × R2) J).map (q2 (F := F) R1 R2) = JR R2 J := by
  ext i j
  simp [JR, inclR, q2, tensMap, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]

theorem unitary_map {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (φ : R →ₐ[F] R')
    (X : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    (Formalism.UG.cT (sigR R σ) X * JR R J * X).map (tensMap (E := E) φ) =
      Formalism.UG.cT (sigR R' σ) (X.map (tensMap φ)) * (JR R J).map (tensMap φ) * X.map (tensMap φ) := by
  have hc : ∀ x : R ⊗[F] E, tensMap (E := E) φ (sigR R σ x) = sigR R' σ (tensMap (E := E) φ x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [tensMap, sigR, Algebra.TensorProduct.map_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 2
  ext i j
  simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, hc]

theorem mixGL_mem (g1 : GL (Fin n) (R1 ⊗[F] E)) (g2 : GL (Fin n) (R2 ⊗[F] E)) (h1 : g1 ∈ HR R1 σ J)
    (h2 : g2 ∈ HR R2 σ J) : mixGL R1 R2 g1 g2 ∈ HR (R1 × R2) σ J := by
  show Formalism.UG.cT (sigR (R1 × R2) σ) (mix R1 R2 (g1 : Matrix (Fin n) (Fin n) (R1 ⊗[F] E)) g2) *
      JR (R1 × R2) J * mix R1 R2 (g1 : Matrix (Fin n) (Fin n) (R1 ⊗[F] E)) g2 = JR (R1 × R2) J
  have e1 := unitary_map σ J (AlgHom.fst F R1 R2) (mix R1 R2 (g1 : Matrix (Fin n) (Fin n) (R1 ⊗[F] E)) g2)
  have e2 := unitary_map σ J (AlgHom.snd F R1 R2) (mix R1 R2 (g1 : Matrix (Fin n) (Fin n) (R1 ⊗[F] E)) g2)
  rw [mixMatrix_map_first, formMatrix_map_first] at e1
  rw [mixMatrix_map_second, formMatrix_map_second] at e2
  have h1' : Formalism.UG.cT (sigR R1 σ) (g1 : Matrix (Fin n) (Fin n) (R1 ⊗[F] E)) * JR R1 J *
      (g1 : Matrix (Fin n) (Fin n) (R1 ⊗[F] E)) = JR R1 J := h1
  have h2' : Formalism.UG.cT (sigR R2 σ) (g2 : Matrix (Fin n) (Fin n) (R2 ⊗[F] E)) * JR R2 J *
      (g2 : Matrix (Fin n) (Fin n) (R2 ⊗[F] E)) = JR R2 J := h2
  rw [h1', ← formMatrix_map_first J R1 R2] at e1
  rw [h2', ← formMatrix_map_second J R1 R2] at e2
  ext i j
  apply (QQ R1 R2).injective
  rw [QQ_apply, QQ_apply]
  exact Prod.ext (congrFun (congrFun e1 i) j) (congrFun (congrFun e2 i) j)

def unsplit (p : HA R1 σ J × HA R2 σ J) : HA (R1 × R2) σ J :=
  (⟨mixGL R1 R2 (HA.mat R1 σ J p.1) (HA.mat R2 σ J p.2),
    mixGL_mem σ J R1 R2 _ _ (show ↥(HR R1 σ J) from p.1).2 (show ↥(HR R2 σ J) from p.2).2⟩ : HR (R1 × R2) σ J)

theorem continuous_mix {X : Type} [TopologicalSpace X] [TopologicalSpace R1] [TopologicalSpace R2]
    {A : X → Matrix (Fin n) (Fin n) (R1 ⊗[F] E)} {B : X → Matrix (Fin n) (Fin n) (R2 ⊗[F] E)}
    (hA : Continuous A) (hB : Continuous B) : Continuous fun x => mix R1 R2 (A x) (B x) := by
  refine continuous_matrix fun i j => ?_
  exact (continuous_QQ_symm R1 R2).comp ((hA.matrix_elem i j).prodMk (hB.matrix_elem i j))

theorem continuous_matHA (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] :
    Continuous fun g : HA R σ J => ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := Units.continuous_val.comp continuous_subtype_val

theorem continuous_matHA_inv (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] :
    Continuous fun g : HA R σ J =>
      (((HA.mat R σ J g)⁻¹ : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)) := Units.continuous_coe_inv.comp continuous_subtype_val

theorem splitIso_gen [TopologicalSpace R1] [TopologicalSpace R2] :
    ∃ e : HA (R1 × R2) σ J ≃ₜ* HA R1 σ J × HA R2 σ J,
      ⇑e = fun g => (haMap σ J (AlgHom.fst F R1 R2) g, haMap σ J (AlgHom.snd F R1 R2) g) := by
  let f : HA (R1 × R2) σ J →* HA R1 σ J × HA R2 σ J :=
    MonoidHom.prod (haMap σ J (AlgHom.fst F R1 R2)) (haMap σ J (AlgHom.snd F R1 R2))
  have hl : ∀ g, unsplit σ J R1 R2 (f g) = g := by
    intro g
    apply HA_ext σ J
    exact mix_split R1 R2 _
  have hr : ∀ p, f (unsplit σ J R1 R2 p) = p := by
    intro p
    refine Prod.ext ?_ ?_
    · apply HA_ext σ J
      exact mixMatrix_map_first R1 R2 _ _
    · apply HA_ext σ J
      exact mixMatrix_map_second R1 R2 _ _
  let e0 : HA (R1 × R2) σ J ≃* HA R1 σ J × HA R2 σ J :=
    MulEquiv.mk ⟨⇑f, unsplit σ J R1 R2, hl, hr⟩ f.map_mul
  have c1 : Continuous e0 :=
    (continuous_haMap σ J _ (continuous_first_factor_proj R1 R2)).prodMk (continuous_haMap σ J _ (continuous_second_factor_proj R1 R2))
  have c2 : Continuous e0.symm := by
    refine continuous_induced_rng.2 ?_
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact continuous_mix R1 R2 ((continuous_matHA σ J R1).comp continuous_fst)
        ((continuous_matHA σ J R2).comp continuous_snd)
    · exact continuous_mix R1 R2 ((continuous_matHA_inv σ J R1).comp continuous_fst)
        ((continuous_matHA_inv σ J R2).comp continuous_snd)
  exact ⟨⟨e0, c1, c2⟩, rfl⟩

end MassDataMassesW.SplitW

namespace MassDataMassesW

open NumberField

theorem splitIso_holds : SplitIso := by
  intro F E _ _ _ _ σ n J
  exact SplitW.splitIso_gen σ J _ _

end MassDataMassesW
