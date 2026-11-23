import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactLevelOffFinEmpty
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv

noncomputable section

namespace GlobalTheory.AdelicU

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.UG (bc stabGL GLint princ cT)

section Pure

variable {K : Type} [Field K] {m : Type} [Fintype m] [DecidableEq m]

def dualConj (A : GL m K) : GL m K →* GL m K where
  toFun x :=
    { val := (A * x⁻¹ * A⁻¹).1ᵀ
      inv := (A * x * A⁻¹).1ᵀ
      val_inv := by rw [← Matrix.transpose_mul, ← Units.val_mul]; group; simp
      inv_val := by rw [← Matrix.transpose_mul, ← Units.val_mul]; group; simp }
  map_one' := Units.ext (by simp)
  map_mul' x y := Units.ext (by
    change (A * (x * y)⁻¹ * A⁻¹).1ᵀ = (A * x⁻¹ * A⁻¹).1ᵀ * (A * y⁻¹ * A⁻¹).1ᵀ
    rw [← Matrix.transpose_mul, ← Units.val_mul]
    exact congrArg (fun z : GL m K => z.1ᵀ) (by group))

theorem dualConj_val (A x : GL m K) : (dualConj A x).1 = (A.1 * (x⁻¹).1 * (A⁻¹).1)ᵀ := rfl

theorem eq_dualConj_iff {A x y : GL m K} : y = dualConj A x ↔ y.1ᵀ * A.1 * x.1 = A.1 := by
  rw [Units.ext_iff, dualConj_val, ← Matrix.transpose_inj, Matrix.transpose_transpose, Units.eq_mul_inv_iff_mul_eq,
    Units.eq_mul_inv_iff_mul_eq]

theorem continuous_dualConj_val [TopologicalSpace K] [IsTopologicalRing K] (A : GL m K) :
    Continuous fun x : GL m K => (dualConj A x).1 :=
  ((continuous_const.matrix_mul Units.continuous_coe_inv).matrix_mul continuous_const).matrix_transpose

theorem mem_GLint_iff {O : Subring K} {x : GL m K} :
    x ∈ GLint m O ↔ (∀ i j, x.1 i j ∈ O) ∧ ∀ i j, (x⁻¹).1 i j ∈ O := by
  refine ⟨?_, fun h => ⟨⟨Matrix.of fun i j => ⟨_, h.1 i j⟩, Matrix.of fun i j => ⟨_, h.2 i j⟩, ?_, ?_⟩, rfl⟩⟩
  · rintro ⟨y, rfl⟩
    exact ⟨fun i j => (y.1 i j).2, fun i j => ((y⁻¹).1 i j).2⟩
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

theorem bc_injective {A B : Type} [CommRing A] [CommRing B] {φ : A →+* B} (hφ : Function.Injective φ) :
    Function.Injective (bc (n := m) φ) := fun _ _ e =>
  Units.ext (Matrix.map_injective hφ (congrArg Units.val e))

theorem bc_residue_surjective (O : Type) [CommRing O] [IsLocalRing O] :
    Function.Surjective (bc (n := m) (IsLocalRing.residue O)) := fun g => by
  choose M hM using fun a b => IsLocalRing.residue_surjective (R := O) (g.1 a b)
  have hM' : (Matrix.of M).map (IsLocalRing.residue O) = g.1 := Matrix.ext hM
  have hdet : IsUnit (Matrix.of M).det := (isUnit_map_iff (IsLocalRing.residue O) _).1 (by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hM']
    exact (Matrix.GeneralLinearGroup.det g).isUnit)
  exact ⟨Matrix.GeneralLinearGroup.mk'' _ hdet, Units.ext hM'⟩

end Pure

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}

section Vec

omit [NumberField E] in

def splitVec (τ : E →ₐ[F] Fv F v) (y : Fin n → Fv F v ⊗[F] E) : Fin n → Fv F v := fun i => splitProj τ (y i)

def splitIncl (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (u : Fin n → Fv F v) : Fin n → Fv F v ⊗[F] E :=
  fun i => u i • splitIdem h τ

omit [NumberField E] in
theorem splitVec_add (τ : E →ₐ[F] Fv F v) (y z : Fin n → Fv F v ⊗[F] E) :
    splitVec τ (y + z) = splitVec τ y + splitVec τ z := funext fun _ => map_add _ _ _

omit [NumberField E] in
theorem splitVec_smul (τ : E →ₐ[F] Fv F v) (c : Fv F v ⊗[F] E) (y : Fin n → Fv F v ⊗[F] E) :
    splitVec τ (c • y) = splitProj τ c • splitVec τ y := funext fun _ => map_mul _ _ _

omit [NumberField E] in
theorem splitVec_mulVec (τ : E →ₐ[F] Fv F v) (M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    (y : Fin n → Fv F v ⊗[F] E) : splitVec τ (M *ᵥ y) = M.map (splitProj τ) *ᵥ splitVec τ y :=
  funext fun i => RingHom.map_mulVec (splitProj τ : Fv F v ⊗[F] E →+* Fv F v) M y i

@[simp] theorem splitVec_splitIncl (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (u : Fin n → Fv F v) :
    splitVec τ (splitIncl h τ u) = u := funext fun i => by simp [splitVec, splitIncl]

@[simp] theorem splitVec_comp_splitIncl (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (u : Fin n → Fv F v) :
    splitVec (τ.comp σ) (splitIncl h τ u) = 0 := funext fun i => by simp [splitVec, splitIncl]

@[simp] theorem splitVec_splitIncl_comp (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (u : Fin n → Fv F v) :
    splitVec τ (splitIncl h (τ.comp σ) u) = 0 := funext fun i => by simp [splitVec, splitIncl, splitIdem_comp]

theorem splitIncl_splitVec (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (y : Fin n → Fv F v ⊗[F] E) :
    splitIncl h τ (splitVec τ y) = splitIdem h τ • y := funext fun i => (splitIdem_mul h τ (y i)).symm

theorem splitVec_ext (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {y z : Fin n → Fv F v ⊗[F] E}
    (h1 : splitVec τ y = splitVec τ z) (h2 : splitVec (τ.comp σ) y = splitVec (τ.comp σ) z) : y = z :=
  funext fun i => split_ext h τ (congrFun h1 i) (congrFun h2 i)

def splitVecEquiv (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) :
    (Fin n → Fv F v ⊗[F] E) ≃ₗ[Fv F v] (Fin n → Fv F v) × (Fin n → Fv F v) where
  toFun y := (splitVec τ y, splitVec (τ.comp σ) y)
  invFun p := splitIncl h τ p.1 + splitIncl h (τ.comp σ) p.2
  map_add' y z := by simp [splitVec_add]
  map_smul' c y := Prod.ext (funext fun i => map_smul (splitProj τ) c (y i))
    (funext fun i => map_smul (splitProj (τ.comp σ)) c (y i))
  left_inv y := splitVec_ext h τ (by simp [splitVec_add]) (by simp [splitVec_add])
  right_inv p := by simp [splitVec_add]

omit [NumberField E] in

def splitGram (hJ : IsHermND σ J) (τ : E →ₐ[F] Fv F v) : GL (Fin n) (Fv F v) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (J.map τ) (by
    rw [← AlgHom.mapMatrix_apply, ← AlgHom.map_det]; exact (map_ne_zero τ).2 hJ.2)

omit [NumberField E] in
@[simp] theorem splitGram_val (hJ : IsHermND σ J) (τ : E →ₐ[F] Fv F v) : (splitGram hJ τ).1 = J.map τ := rfl

omit [NumberField E] in

theorem map_comp_conj (hJ : IsHermND σ J) (τ : E →ₐ[F] Fv F v) : J.map (τ.comp σ) = (J.map τ)ᵀ :=
  Matrix.ext fun i j => congrArg τ (hJ.1 j i)

omit [NumberField E] in
theorem JR_map_splitProj (J : Matrix (Fin n) (Fin n) E) (τ : E →ₐ[F] Fv F v) :
    (JR (Fv F v) J).map (splitProj τ) = J.map τ := Matrix.ext fun i j => splitProj_inclR τ (J i j)

omit [NumberField E] in

theorem splitProj_hLin (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (τ : E →ₐ[F] Fv F v)
    (y x : Fin n → Fv F v ⊗[F] E) :
    splitProj τ (hLin σ J (Fv F v) y x) = splitVec (τ.comp σ) x ⬝ᵥ J.map τ *ᵥ splitVec τ y := by
  simp only [hLin, hR, Formalism.UG.hform, map_sum, map_mul, ← splitProj_comp, JR, Matrix.map_apply, splitProj_inclR,
    dotProduct, Matrix.mulVec, splitVec, Finset.mul_sum, mul_assoc]

theorem splitProj_comp_hLin (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : E →ₐ[F] Fv F v)
    (y x : Fin n → Fv F v ⊗[F] E) :
    splitProj (τ.comp σ) (hLin σ J (Fv F v) y x) = splitVec (τ.comp σ) y ⬝ᵥ J.map τ *ᵥ splitVec τ x := by
  rw [splitProj_hLin, comp_conj_conj h, map_comp_conj hJ, Matrix.mulVec_transpose, dotProduct_comm,
    ← Matrix.dotProduct_mulVec]

end Vec

section Group

omit [NumberField E] in
variable (σ J) in

def splitHom (τ : E →ₐ[F] Fv F v) : GLoc σ J v →* GL (Fin n) (Fv F v) :=
  (bc (splitProj τ : Fv F v ⊗[F] E →+* Fv F v)).comp (matHom _ σ J)

omit [NumberField E] in
theorem splitHom_val (τ : E →ₐ[F] Fv F v) (g : GLoc σ J v) :
    (splitHom σ J τ g).1 = (matHom _ σ J g).1.map (splitProj τ) := rfl

omit [NumberField E] in
theorem splitVec_matHom_mulVec (τ : E →ₐ[F] Fv F v) (g : GLoc σ J v) (y : Fin n → Fv F v ⊗[F] E) :
    splitVec τ ((matHom _ σ J g).1 *ᵥ y) = (splitHom σ J τ g).1 *ᵥ splitVec τ y := splitVec_mulVec τ _ y

theorem matHom_mulVec_splitIncl (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (g : GLoc σ J v) (u : Fin n → Fv F v) :
    (matHom _ σ J g).1 *ᵥ splitIncl h τ u = splitIncl h τ ((splitHom σ J τ g).1 *ᵥ u) :=
  splitVec_ext h τ (by simp [splitVec_matHom_mulVec]) (by simp [splitVec_matHom_mulVec])

omit [NumberField E] in
theorem map_unitary (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (τ : E →ₐ[F] Fv F v)
    (M : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :
    (cT (sigR _ σ) M * JR (Fv F v) J * M).map (splitProj τ) =
      (M.map (splitProj (τ.comp σ)))ᵀ * J.map τ * M.map (splitProj τ) := by
  rw [Matrix.map_mul, Matrix.map_mul, JR_map_splitProj]
  congr 2
  exact Matrix.ext fun i j => (splitProj_comp τ σ _).symm

omit [NumberField E] in

theorem splitHom_unitary (τ : E →ₐ[F] Fv F v) (g : GLoc σ J v) :
    (splitHom σ J (τ.comp σ) g).1ᵀ * J.map τ * (splitHom σ J τ g).1 = J.map τ := by
  have hg : cT (sigR _ σ) (matHom _ σ J g).1 * JR (Fv F v) J * (matHom _ σ J g).1 = JR (Fv F v) J := g.2
  rw [splitHom_val, splitHom_val, ← map_unitary, hg, JR_map_splitProj]

omit [NumberField E] in

theorem pairing_splitHom (τ : E →ₐ[F] Fv F v) (g : GLoc σ J v) (u' u : Fin n → Fv F v) :
    ((splitHom σ J (τ.comp σ) g).1 *ᵥ u') ⬝ᵥ J.map τ *ᵥ ((splitHom σ J τ g).1 *ᵥ u) = u' ⬝ᵥ J.map τ *ᵥ u := by
  conv_rhs => rw [← splitHom_unitary τ g]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u', Matrix.vecMul_transpose]

omit [NumberField E] in

theorem splitHom_comp (hJ : IsHermND σ J) (τ : E →ₐ[F] Fv F v) (g : GLoc σ J v) :
    splitHom σ J (τ.comp σ) g = dualConj (splitGram hJ τ) (splitHom σ J τ g) :=
  eq_dualConj_iff.2 (splitHom_unitary τ g)

theorem splitMat_ext (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {M N : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)}
    (h1 : M.map (splitProj τ) = N.map (splitProj τ))
    (h2 : M.map (splitProj (τ.comp σ)) = N.map (splitProj (τ.comp σ))) : M = N :=
  Matrix.ext fun i j => split_ext h τ (congrFun₂ h1 i j) (congrFun₂ h2 i j)

def splitPairMat (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (a b : Matrix (Fin n) (Fin n) (Fv F v)) :
    Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := fun i j => (splitAlgEquiv h τ).symm (a i j, b i j)

@[simp] theorem splitPairMat_map (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (a b : Matrix (Fin n) (Fin n) (Fv F v)) :
    (splitPairMat h τ a b).map (splitProj τ) = a := Matrix.ext fun _ _ => splitProj_symm h τ _

@[simp] theorem splitPairMat_map_comp (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v)
    (a b : Matrix (Fin n) (Fin n) (Fv F v)) :
    (splitPairMat h τ a b).map (splitProj (τ.comp σ)) = b := Matrix.ext fun _ _ => splitProj_comp_symm h τ _

theorem splitPairMat_mul_inv (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (x y : GL (Fin n) (Fv F v)) :
    splitPairMat h τ x.1 y.1 * splitPairMat h τ (x⁻¹).1 (y⁻¹).1 = 1 :=
  splitMat_ext h τ
    (by rw [Matrix.map_mul, splitPairMat_map, splitPairMat_map, Units.mul_inv,
      Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [Matrix.map_mul, splitPairMat_map_comp, splitPairMat_map_comp, Units.mul_inv,
      Matrix.map_one _ (map_zero _) (map_one _)])

def splitPairGL (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (x y : GL (Fin n) (Fv F v)) : GL (Fin n) (Fv F v ⊗[F] E) :=
  ⟨splitPairMat h τ x.1 y.1, splitPairMat h τ (x⁻¹).1 (y⁻¹).1, splitPairMat_mul_inv h τ x y,
    splitPairMat_mul_inv h τ x⁻¹ y⁻¹⟩

theorem splitPairMat_unitary (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : E →ₐ[F] Fv F v)
    {a b : Matrix (Fin n) (Fin n) (Fv F v)} (e : bᵀ * J.map τ * a = J.map τ) :
    cT (sigR _ σ) (splitPairMat h τ a b) * JR (Fv F v) J * splitPairMat h τ a b = JR (Fv F v) J := by
  refine splitMat_ext h τ ?_ ?_
  · rw [map_unitary, splitPairMat_map, splitPairMat_map_comp, JR_map_splitProj, e]
  · rw [map_unitary, comp_conj_conj h, splitPairMat_map, splitPairMat_map_comp, JR_map_splitProj, map_comp_conj hJ,
      ← Matrix.transpose_inj, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_transpose, ← Matrix.mul_assoc, e]

def splitLift (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : E →ₐ[F] Fv F v) (x : GL (Fin n) (Fv F v)) : GLoc σ J v :=
  (⟨splitPairGL h τ x (dualConj (splitGram hJ τ) x),
    splitPairMat_unitary h hJ τ ((eq_dualConj_iff (A := splitGram hJ τ)).1 rfl)⟩ : HR (Fv F v) σ J)

theorem matHom_splitLift (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : E →ₐ[F] Fv F v) (x : GL (Fin n) (Fv F v)) :
    matHom _ σ J (splitLift h hJ τ x) = splitPairGL h τ x (dualConj (splitGram hJ τ) x) := rfl

theorem splitHom_splitLift (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : E →ₐ[F] Fv F v) (x : GL (Fin n) (Fv F v)) :
    splitHom σ J τ (splitLift h hJ τ x) = x := Units.ext (splitPairMat_map h τ _ _)

theorem splitHom_injective (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : E →ₐ[F] Fv F v) :
    Function.Injective (splitHom σ J τ) := fun g g' e =>
  matHom_injective _ σ J (Units.ext (splitMat_ext h τ (congrArg Units.val e) (by
    rw [← splitHom_val, ← splitHom_val, splitHom_comp hJ, splitHom_comp hJ, e])))

theorem continuous_splitHom (τ : E →ₐ[F] Fv F v) : Continuous (splitHom σ J τ) :=
  have h1 := (isEmbedding_matHom (Fv F v) σ J).continuous
  Units.continuous_iff.2 ⟨(Units.continuous_val.comp h1).matrix_map (continuous_splitProj τ),
    (Units.continuous_coe_inv.comp h1).matrix_map (continuous_splitProj τ)⟩

theorem continuous_splitLift (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : E →ₐ[F] Fv F v) :
    Continuous (splitLift h hJ τ) := by
  have h1 : Continuous fun x : GL (Fin n) (Fv F v) => splitPairMat h τ x.1 (dualConj (splitGram hJ τ) x).1 :=
    continuous_matrix fun i j => (continuous_splitAlgEquiv_symm h τ).comp
      ((Units.continuous_val.matrix_elem i j).prodMk ((continuous_dualConj_val _).matrix_elem i j))
  exact (isEmbedding_matHom (Fv F v) σ J).continuous_iff.2 (Units.continuous_iff.2
    ⟨h1, (h1.comp continuous_inv).congr fun x => by
      simp only [Function.comp, map_inv, matHom_splitLift]; rfl⟩)

def splitEquiv (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : E →ₐ[F] Fv F v) : GLoc σ J v ≃ₜ* GL (Fin n) (Fv F v) where
  toFun := splitHom σ J τ
  invFun := splitLift h hJ τ
  left_inv g := splitHom_injective h hJ τ (splitHom_splitLift h hJ τ _)
  right_inv := splitHom_splitLift h hJ τ
  map_mul' := map_mul _
  continuous_toFun := continuous_splitHom τ
  continuous_invFun := continuous_splitLift h hJ τ

variable (h : IsCMExt F E σ) (hJ : IsHermND σ J) (τ : E →ₐ[F] Fv F v)

theorem splitEquiv_apply (g : GLoc σ J v) : splitEquiv h hJ τ g = splitHom σ J τ g := rfl

theorem splitEquiv_val (g : GLoc σ J v) : (splitEquiv h hJ τ g).1 = (matHom _ σ J g).1.map (splitProj τ) := rfl

theorem splitEquiv_symm_apply (x : GL (Fin n) (Fv F v)) : (splitEquiv h hJ τ).symm x = splitLift h hJ τ x := rfl

theorem splitEquiv_comp (g : GLoc σ J v) :
    splitEquiv h hJ (τ.comp σ) g = dualConj (splitGram hJ τ) (splitEquiv h hJ τ g) := splitHom_comp hJ τ g

theorem splitEquiv_ratLoc (γ : GRat σ J) : (splitEquiv h hJ τ (ratLoc σ J v γ)).1 = γ.1.1.map τ :=
  Matrix.ext fun i j => splitProj_inclR τ (γ.1.1 i j)

def splitEquivIn (β : GL (Fin n) (Fv F v)) : GLoc σ J v ≃ₜ* GL (Fin n) (Fv F v) :=
  (splitEquiv h hJ τ).trans
    { MulAut.conj β⁻¹ with
      continuous_toFun := (continuous_const.mul continuous_id).mul continuous_const
      continuous_invFun := (continuous_const.mul continuous_id).mul continuous_const }

theorem splitEquivIn_apply (β : GL (Fin n) (Fv F v)) (g : GLoc σ J v) :
    splitEquivIn h hJ τ β g = β⁻¹ * splitHom σ J τ g * β := rfl

theorem splitHom_splitEquivIn_symm (β x : GL (Fin n) (Fv F v)) :
    splitHom σ J τ ((splitEquivIn h hJ τ β).symm x) = β * x * β⁻¹ := by
  have := (splitEquivIn h hJ τ β).apply_symm_apply x
  rw [splitEquivIn_apply] at this
  generalize splitHom σ J τ _ = y at this
  rw [← this]; group

end Group

section Level

omit [NumberField E] in

def splitLat (τ : E →ₐ[F] Fv F v) (L : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (v.adicCompletionIntegers F) (Fin n → Fv F v) where
  carrier := splitVec τ '' latLoc F L v
  zero_mem' := ⟨0, zero_mem _, funext fun _ => map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨y, hy, rfl⟩ ⟨z, hz, rfl⟩
    exact ⟨y + z, add_mem hy hz, splitVec_add τ y z⟩
  smul_mem' := by
    rintro c _ ⟨y, hy, rfl⟩
    refine ⟨_, (latLoc F L v).smul_mem ⟨_, tmul_mem_intLoc c.2 1⟩ hy, (splitVec_smul τ _ y).trans ?_⟩
    rw [splitProj_tmul]
    simp
    rfl

variable {τ : E →ₐ[F] Fv F v} {L : Submodule (𝓞 E) (Fin n → E)} {β : GL (Fin n) (Fv F v)}

omit [NumberField E] in
theorem mem_splitLat {u : Fin n → Fv F v} : u ∈ splitLat τ L ↔ ∃ y ∈ latLoc F L v, splitVec τ y = u := Iff.rfl

theorem splitIncl_mem_latLoc_iff (h : IsCMExt F E σ) {u : Fin n → Fv F v} :
    splitIncl h τ u ∈ latLoc F L v ↔ u ∈ splitLat τ L := by
  refine ⟨fun hu => ⟨_, hu, splitVec_splitIncl h τ u⟩, ?_⟩
  rintro ⟨y, hy, rfl⟩
  rw [splitIncl_splitVec]
  exact (latLoc F L v).smul_mem ⟨_, splitIdem_mem h τ⟩ hy

variable (τ) in

theorem mem_latLoc_iff_split (h : IsCMExt F E σ) {y : Fin n → Fv F v ⊗[F] E} :
    y ∈ latLoc F L v ↔ splitVec τ y ∈ splitLat τ L ∧ splitVec (τ.comp σ) y ∈ splitLat (τ.comp σ) L := by
  refine ⟨fun hy => ⟨⟨y, hy, rfl⟩, ⟨y, hy, rfl⟩⟩, fun hy => ?_⟩
  rw [← (splitVecEquiv h τ).symm_apply_apply y]
  exact add_mem ((splitIncl_mem_latLoc_iff h).2 hy.1) ((splitIncl_mem_latLoc_iff h).2 hy.2)

theorem mem_splitLat_stdLattice (h : IsCMExt F E σ) {u : Fin n → Fv F v} :
    u ∈ splitLat τ (stdLattice E n) ↔ ∀ i, u i ∈ v.adicCompletionIntegers F := by
  rw [← splitIncl_mem_latLoc_iff h, mem_latLoc_stdLattice]
  simp [mem_intLoc_iff_split h τ, splitIncl]

theorem mem_splitLat_comp_iff (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hL : IsSelfDualAt σ J L v)
    {u' : Fin n → Fv F v} :
    u' ∈ splitLat (τ.comp σ) L ↔ ∀ u ∈ splitLat τ L, u' ⬝ᵥ J.map τ *ᵥ u ∈ v.adicCompletionIntegers F := by
  rw [← splitIncl_mem_latLoc_iff h, hL]
  change (∀ x ∈ latLoc F L v, hLin σ J (Fv F v) _ x ∈ intLoc F E v) ↔ _
  simp only [mem_intLoc_iff_split h τ, splitProj_comp_hLin h hJ, splitProj_hLin σ J τ, splitVec_splitIncl,
    splitVec_splitIncl_comp, Matrix.mulVec_zero, dotProduct_zero, zero_mem, true_and]
  exact ⟨by rintro H _ ⟨x, hx, rfl⟩; exact H x hx, fun H x hx => H _ ⟨x, hx, rfl⟩⟩

omit [NumberField E] in
theorem splitHom_mulVec_mem {g : GLoc σ J v} (hg : g ∈ stabLoc σ J L v) {u : Fin n → Fv F v} (hu : u ∈ splitLat τ L) :
    (splitHom σ J τ g).1 *ᵥ u ∈ splitLat τ L := by
  obtain ⟨y, hy, rfl⟩ := hu
  exact ⟨_, (mem_stabLoc.1 hg y).1 hy, splitVec_matHom_mulVec τ g y⟩

omit [NumberField E] in
theorem splitHom_inv_mulVec (g : GLoc σ J v) (u : Fin n → Fv F v) :
    (splitHom σ J τ g⁻¹).1 *ᵥ ((splitHom σ J τ g).1 *ᵥ u) = u := by
  rw [Matrix.mulVec_mulVec, map_inv, Units.inv_mul, Matrix.one_mulVec]

omit [NumberField E] in
theorem splitHom_mulVec_inv (g : GLoc σ J v) (u : Fin n → Fv F v) :
    (splitHom σ J τ g).1 *ᵥ ((splitHom σ J τ g⁻¹).1 *ᵥ u) = u := by
  rw [Matrix.mulVec_mulVec, map_inv, Units.mul_inv, Matrix.one_mulVec]

omit [NumberField E] in

theorem splitHom_mem_stabGL {g : GLoc σ J v} (hg : g ∈ stabLoc σ J L v) : splitHom σ J τ g ∈ stabGL (splitLat τ L) :=
  fun u => ⟨splitHom_mulVec_mem hg, fun hu => splitHom_inv_mulVec (τ := τ) g u ▸ splitHom_mulVec_mem (inv_mem hg) hu⟩

variable (τ) in

theorem mem_stabLoc_iff_splitLat (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hL : IsSelfDualAt σ J L v)
    {g : GLoc σ J v} : g ∈ stabLoc σ J L v ↔ splitHom σ J τ g ∈ stabGL (splitLat τ L) := by
  refine ⟨splitHom_mem_stabGL, fun hg => mem_stabLoc.2 fun y => ?_⟩
  rw [mem_latLoc_iff_split τ h, mem_latLoc_iff_split τ h, splitVec_matHom_mulVec, splitVec_matHom_mulVec,
    mem_splitLat_comp_iff h hJ hL, mem_splitLat_comp_iff h hJ hL]
  refine and_congr (hg _) ⟨fun H u hu => ?_, fun H u hu => ?_⟩
  · rw [← splitHom_mulVec_inv (τ := τ) g u, pairing_splitHom]
    exact H _ ((hg _).2 (by rwa [splitHom_mulVec_inv]))
  · rw [← pairing_splitHom τ g]
    exact H _ ((hg u).1 hu)

omit [NumberField E] in
variable (τ L β) in

def IsSplitBasis : Prop :=
  ∀ u : Fin n → Fv F v, (∀ i, u i ∈ v.adicCompletionIntegers F) ↔ β.1 *ᵥ u ∈ splitLat τ L

variable (τ) in
theorem isSplitBasis_stdLattice (h : IsCMExt F E σ) : IsSplitBasis τ (stdLattice E n) 1 := fun u => by
  rw [Units.val_one, Matrix.one_mulVec, mem_splitLat_stdLattice h]

variable (τ) in

theorem IsLatticeFrame.isSplitBasis (h : IsCMExt F E σ) {a : GL (Fin n) (AF F ⊗[F] E)} (ha : IsLatticeFrame L a) :
    IsSplitBasis τ L (bc (splitProj τ : Fv F v ⊗[F] E →+* Fv F v) (bc (compFin F E v) a)) := fun u => by
  have e : (bc (compFin F E v) a).1 *ᵥ splitIncl h τ u =
      splitIncl h τ ((bc (splitProj τ : Fv F v ⊗[F] E →+* Fv F v) (bc (compFin F E v) a)).1 *ᵥ u) :=
    splitVec_ext h τ (by rw [splitVec_mulVec, splitVec_splitIncl, splitVec_splitIncl]; rfl)
      (by rw [splitVec_mulVec, splitVec_comp_splitIncl, splitVec_comp_splitIncl, Matrix.mulVec_zero])
  rw [← splitIncl_mem_latLoc_iff h, ← e, ← ha v, ← mem_latLoc_stdLattice, splitIncl_mem_latLoc_iff,
    mem_splitLat_stdLattice h]

variable (τ L) in

theorem exists_isSplitBasis (h : IsCMExt F E σ) [Submodule.IsLattice E L] : ∃ β, IsSplitBasis τ L β :=
  (Frames.exists_isLatticeFrame (F := F) L).elim fun _ ha => ⟨_, ha.isSplitBasis τ h⟩

theorem mem_GLint_iff_mulVec {x : GL (Fin n) (Fv F v)} :
    x ∈ GLint (Fin n) (v.adicCompletionIntegers F).toSubring ↔
      ∀ u : Fin n → Fv F v, (∀ i, u i ∈ v.adicCompletionIntegers F) ↔
        ∀ i, (x.1 *ᵥ u) i ∈ v.adicCompletionIntegers F := by
  have h1 : ∀ i j : Fin n, (Pi.single j 1 : Fin n → Fv F v) i ∈ v.adicCompletionIntegers F := fun i j => by
    by_cases e : i = j
    · subst e; simp
    · simp [e]
  have h2 : ∀ M : Matrix (Fin n) (Fin n) (Fv F v), (∀ i j, M i j ∈ v.adicCompletionIntegers F) →
      ∀ u : Fin n → Fv F v, (∀ i, u i ∈ v.adicCompletionIntegers F) → ∀ i, (M *ᵥ u) i ∈ v.adicCompletionIntegers F :=
    fun M hM u hu i => sum_mem fun j _ => mul_mem (hM i j) (hu j)
  rw [mem_GLint_iff]
  refine ⟨fun H u => ⟨h2 _ H.1 u, fun hu => ?_⟩, fun H => ⟨fun i j => ?_, fun i j => ?_⟩⟩
  · have := h2 _ H.2 _ hu
    rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this
  · simpa using (H _).1 (h1 · j) i
  · have := (H ((x⁻¹).1 *ᵥ Pi.single j 1)).2 (by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]; exact (h1 · j)) i
    rwa [Matrix.mulVec_single_one] at this

omit [NumberField E] in
theorem IsSplitBasis.mem_iff (hβ : IsSplitBasis τ L β) {u : Fin n → Fv F v} :
    u ∈ splitLat τ L ↔ ∀ i, ((β⁻¹).1 *ᵥ u) i ∈ v.adicCompletionIntegers F := by
  rw [hβ, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

omit [NumberField E] in

theorem IsSplitBasis.iff_mem_GLint (hβ : IsSplitBasis τ L β) {β' : GL (Fin n) (Fv F v)} :
    IsSplitBasis τ L β' ↔ β⁻¹ * β' ∈ GLint (Fin n) (v.adicCompletionIntegers F).toSubring := by
  simp only [mem_GLint_iff_mulVec, IsSplitBasis, hβ.mem_iff, Units.val_mul, Matrix.mulVec_mulVec]

omit [NumberField E] in
theorem IsSplitBasis.mem_stabGL_iff (hβ : IsSplitBasis τ L β) {x : GL (Fin n) (Fv F v)} :
    x ∈ stabGL (splitLat τ L) ↔ β⁻¹ * x * β ∈ GLint (Fin n) (v.adicCompletionIntegers F).toSubring := by
  rw [mul_assoc, ← hβ.iff_mem_GLint]
  refine ⟨fun H u => ?_, fun H u => ?_⟩
  · rw [hβ, Units.val_mul, ← Matrix.mulVec_mulVec]; exact H _
  · rw [hβ.mem_iff, H, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_right]

variable (h : IsCMExt F E σ) (hJ : IsHermND σ J)

theorem mem_stabLoc_iff_GLint (hL : IsSelfDualAt σ J L v) (hβ : IsSplitBasis τ L β) {g : GLoc σ J v} :
    g ∈ stabLoc σ J L v ↔ splitEquivIn h hJ τ β g ∈ GLint (Fin n) (v.adicCompletionIntegers F).toSubring :=
  (mem_stabLoc_iff_splitLat τ h hJ hL).trans hβ.mem_stabGL_iff

theorem map_stabLoc (hL : IsSelfDualAt σ J L v) (hβ : IsSplitBasis τ L β) :
    (stabLoc σ J L v).map (splitEquivIn h hJ τ β : GLoc σ J v →* GL (Fin n) (Fv F v)) =
      GLint (Fin n) (v.adicCompletionIntegers F).toSubring := by
  ext x
  obtain ⟨g, rfl⟩ := (splitEquivIn h hJ τ β).surjective x
  rw [← mem_stabLoc_iff_GLint h hJ hL hβ]
  exact Subgroup.mem_map_iff_mem (splitEquivIn h hJ τ β).injective

end Level

section Red

variable {τ : E →ₐ[F] Fv F v} {L : Submodule (𝓞 E) (Fin n → E)} {β : GL (Fin n) (Fv F v)}

omit [NumberField E] in
variable (σ J τ L) in

def stabLocOne : Subgroup (GLoc σ J v) where
  carrier := {g | g ∈ stabLoc σ J L v ∧ ∀ u ∈ splitLat τ L, (splitHom σ J τ g).1 *ᵥ u - u ∈
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) • splitLat τ L}
  one_mem' := ⟨one_mem _, fun u _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun u hu => ?_⟩
    rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← sub_add_sub_cancel _ ((splitHom σ J τ b).1 *ᵥ u)]
    exact add_mem (ha' _ (splitHom_mulVec_mem hb hu)) (hb' u hu)
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun u hu => ?_⟩
    have := neg_mem (ha' _ (splitHom_mulVec_mem (inv_mem ha) hu))
    rwa [splitHom_mulVec_inv, neg_sub] at this

omit [NumberField E] in
theorem mem_stabLocOne {g : GLoc σ J v} : g ∈ stabLocOne σ J τ L ↔ g ∈ stabLoc σ J L v ∧ ∀ u ∈ splitLat τ L,
    (splitHom σ J τ g).1 *ᵥ u - u ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) • splitLat τ L := Iff.rfl

omit [NumberField E] in

theorem IsSplitBasis.mem_smul_iff (hβ : IsSplitBasis τ L β) {u : Fin n → Fv F v} :
    u ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) • splitLat τ L ↔
      ∀ i, Valued.v (((β⁻¹).1 *ᵥ u) i) < 1 := by
  constructor
  refine fun hu => Submodule.smul_induction_on (p := fun u => ∀ i, Valued.v (((β⁻¹).1 *ᵥ u) i) < 1) hu
    (fun c hc z hz i => ?_) fun y z hy hz i => ?_
  · rw [Matrix.mulVec_smul]
    change Valued.v ((c : Fv F v) * _) < 1
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hβ.mem_iff.1 hz i)) (mem_maximalIdeal_iff_valued.1 hc)
  · rw [Matrix.mulVec_add]; exact Valuation.map_add_lt _ (hy i) (hz i)
  · intro hu
    have e : u = ∑ i, (⟨_, (hu i).le⟩ : v.adicCompletionIntegers F) • (β.1 *ᵥ Pi.single i 1) := by
      conv_lhs => rw [← Matrix.one_mulVec u, ← β.mul_inv, ← Matrix.mulVec_mulVec,
        ← Finset.univ_sum_single ((β⁻¹).1 *ᵥ u), Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      change _ = ((β⁻¹).1 *ᵥ u) i • (β.1 *ᵥ Pi.single i 1)
      rw [← Matrix.mulVec_smul, ← Pi.single_smul, smul_eq_mul, mul_one]
    rw [e]
    refine sum_mem fun i _ => Submodule.smul_mem_smul (mem_maximalIdeal_iff_valued.2 (hu i)) ((hβ _).1 fun j => ?_)
    by_cases e : j = i
    · subst e; simp
    · simp [e]

omit [NumberField E] in

theorem IsSplitBasis.mem_stabLocOne_iff (hβ : IsSplitBasis τ L β) {g : GLoc σ J v} :
    g ∈ stabLocOne σ J τ L ↔
      g ∈ stabLoc σ J L v ∧ ∀ i j, Valued.v (((β⁻¹ * splitHom σ J τ g * β).1 - 1) i j) < 1 := by
  have e : ∀ u, (β⁻¹).1 *ᵥ ((splitHom σ J τ g).1 *ᵥ u - u) =
      ((β⁻¹ * splitHom σ J τ g * β).1 - 1) *ᵥ ((β⁻¹).1 *ᵥ u) := fun u => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      ← Units.val_mul, ← Units.val_mul, mul_inv_cancel_right]
  simp only [mem_stabLocOne, hβ.mem_smul_iff, hβ.mem_iff, e]
  refine and_congr_right fun _ => ⟨fun H i j => ?_, fun H u hu i => ?_⟩
  · have := H (β.1 *ᵥ Pi.single j 1) (fun l => by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      by_cases e : l = j
      · subst e; simp
      · simp [e]) i
    rwa [Matrix.mulVec_mulVec _ (β⁻¹).1, Units.inv_mul, Matrix.one_mulVec, Matrix.mulVec_single_one] at this
  · refine Valuation.map_sum_lt (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))) one_ne_zero fun j _ => ?_
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (hu j)) (H i j)

theorem bc_residue_eq_one_iff {y : GL (Fin n) (v.adicCompletionIntegers F)} :
    bc (IsLocalRing.residue (v.adicCompletionIntegers F)) y = 1 ↔
      ∀ i j, Valued.v (((bc (v.adicCompletionIntegers F).subtype y).1 - 1) i j) < 1 := by
  rw [Units.ext_iff, Units.val_one, ← Matrix.map_one (IsLocalRing.residue (v.adicCompletionIntegers F)) (map_zero _)
    (map_one _), ← Matrix.map_one (v.adicCompletionIntegers F).subtype (map_zero _) (map_one _), ← Matrix.ext_iff]
  exact forall₂_congr fun i j => Ideal.Quotient.eq.trans mem_maximalIdeal_iff_valued

theorem mem_princ_iff {x : GL (Fin n) (Fv F v)} :
    x ∈ princ (v.adicCompletionIntegers F).subtype (IsLocalRing.maximalIdeal _) ↔
      x ∈ GLint (Fin n) (v.adicCompletionIntegers F).toSubring ∧ ∀ i j, Valued.v ((x.1 - 1) i j) < 1 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, rfl⟩, bc_residue_eq_one_iff.1 hy⟩
  · rintro ⟨hx, hy⟩
    obtain ⟨y, rfl⟩ : ∃ y : GL (Fin n) (v.adicCompletionIntegers F), bc (v.adicCompletionIntegers F).subtype y = x := hx
    have h1 := (bc_residue_eq_one_iff (y := y)).2 hy
    exact ⟨y, Subgroup.mem_comap.2 (Subgroup.mem_bot.2 h1), rfl⟩

variable (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hL : IsSelfDualAt σ J L v) (hβ : IsSplitBasis τ L β)

def stabLocEquiv : stabLoc σ J L v ≃* GL (Fin n) (v.adicCompletionIntegers F) :=
  ((splitEquivIn h hJ τ β).toMulEquiv.subgroupMap (stabLoc σ J L v)).trans
    ((MulEquiv.subgroupCongr (map_stabLoc h hJ hL hβ)).trans
      (MonoidHom.ofInjective (bc_injective (v.adicCompletionIntegers F).subtype_injective)).symm)

theorem bc_stabLocEquiv (k : stabLoc σ J L v) :
    bc (v.adicCompletionIntegers F).subtype (stabLocEquiv h hJ hL hβ k) = splitEquivIn h hJ τ β k :=
  MonoidHom.apply_ofInjective_symm (bc_injective (v.adicCompletionIntegers F).subtype_injective) _

theorem coe_stabLocEquiv (k : stabLoc σ J L v) (i j : Fin n) :
    ((stabLocEquiv h hJ hL hβ k).1 i j : Fv F v) = (splitEquivIn h hJ τ β k).1 i j :=
  congrArg (fun x => x.1 i j) (bc_stabLocEquiv h hJ hL hβ k)

def splitRed : stabLoc σ J L v →* GL (Fin n) (IsLocalRing.ResidueField (v.adicCompletionIntegers F)) :=
  (bc (IsLocalRing.residue _)).comp (stabLocEquiv h hJ hL hβ).toMonoidHom

theorem splitRed_val (k : stabLoc σ J L v) :
    (splitRed h hJ hL hβ k).1 = (stabLocEquiv h hJ hL hβ k).1.map (IsLocalRing.residue _) := rfl

theorem splitRed_surjective : Function.Surjective (splitRed h hJ hL hβ) :=
  (bc_residue_surjective _).comp (stabLocEquiv h hJ hL hβ).surjective

theorem splitRed_eq_one_iff (k : stabLoc σ J L v) : splitRed h hJ hL hβ k = 1 ↔ k.1 ∈ stabLocOne σ J τ L := by
  rw [hβ.mem_stabLocOne_iff, and_iff_right k.2, ← splitEquivIn_apply h hJ, ← bc_stabLocEquiv h hJ hL hβ]
  exact bc_residue_eq_one_iff

theorem ker_splitRed : (splitRed h hJ hL hβ).ker = (stabLocOne σ J τ L).subgroupOf (stabLoc σ J L v) :=
  Subgroup.ext (splitRed_eq_one_iff h hJ hL hβ)

end Red

section Swap

variable {τ : E →ₐ[F] Fv F v} {L : Submodule (𝓞 E) (Fin n → E)} {β : GL (Fin n) (Fv F v)}
  (h : IsCMExt F E σ) (hJ : IsHermND σ J)

theorem dualConj_one_val {K : Type} [Field K] (x : GL (Fin n) K) : (dualConj 1 x).1 = (x⁻¹).1ᵀ := by
  simp only [dualConj_val, inv_one, Units.val_one, one_mul, mul_one]

include h in

theorem IsSplitBasis.dual (hL : IsSelfDualAt σ J L v) (hβ : IsSplitBasis τ L β) :
    IsSplitBasis (τ.comp σ) L (dualConj 1 (splitGram hJ τ * β)) := fun c => by
  have e : ∀ u, ((dualConj 1 (splitGram hJ τ * β)).1 *ᵥ c) ⬝ᵥ J.map τ *ᵥ u = c ⬝ᵥ (β⁻¹).1 *ᵥ u := fun u => by
    rw [dualConj_one_val, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      ← splitGram_val hJ, ← Units.val_mul, mul_inv_rev, inv_mul_cancel_right]
  simp only [mem_splitLat_comp_iff h hJ hL, e, hβ.mem_iff]
  refine ⟨fun H u hu => sum_mem fun j _ => mul_mem (H j) (hu j), fun H i => ?_⟩
  have := H (β.1 *ᵥ Pi.single i 1) (fun l => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    by_cases e : l = i
    · subst e; simp
    · simp [e])
  rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, dotProduct_single, mul_one] at this

theorem splitEquivIn_comp (τ : E →ₐ[F] Fv F v) (β : GL (Fin n) (Fv F v)) (g : GLoc σ J v) :
    splitEquivIn h hJ (τ.comp σ) (dualConj 1 (splitGram hJ τ * β)) g = dualConj 1 (splitEquivIn h hJ τ β g) := by
  have e : ∀ x, dualConj (splitGram hJ τ) x = dualConj 1 (splitGram hJ τ * x * (splitGram hJ τ)⁻¹) := fun x =>
    Units.ext (by
      rw [dualConj_one_val, dualConj_val, mul_inv_rev, mul_inv_rev, inv_inv, ← mul_assoc, Units.val_mul, Units.val_mul])
  rw [splitEquivIn_apply, splitEquivIn_apply, splitHom_comp hJ, e, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  group

omit [NumberField E] in

theorem conj_mem_stabLocOne {k g : GLoc σ J v} (hk : k ∈ stabLoc σ J L v) (hg : g ∈ stabLocOne σ J τ L) :
    k * g * k⁻¹ ∈ stabLocOne σ J τ L := by
  refine ⟨mul_mem (mul_mem hk hg.1) (inv_mem hk), fun u hu => ?_⟩
  have h1 := hg.2 _ (splitHom_mulVec_mem (inv_mem hk) hu)
  have h2 : ∀ z ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) • splitLat τ L,
      (splitHom σ J τ k).1 *ᵥ z ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) • splitLat τ L :=
    fun z hz => Submodule.smul_induction_on (p := fun z => (splitHom σ J τ k).1 *ᵥ z ∈ _) hz
      (fun c hc y hy => by rw [Matrix.mulVec_smul]; exact Submodule.smul_mem_smul hc (splitHom_mulVec_mem hk hy))
      fun y z hy hz => by rw [Matrix.mulVec_add]; exact add_mem hy hz
  have h3 := h2 _ h1
  rwa [Matrix.mulVec_sub, splitHom_mulVec_inv, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul,
    ← Units.val_mul, ← map_mul, ← map_mul] at h3

omit [NumberField E] in
instance normal_stabLocOne : ((stabLocOne σ J τ L).subgroupOf (stabLoc σ J L v)).Normal :=
  ⟨fun _ hg k => conj_mem_stabLocOne k.2 hg⟩

include h in
variable (J τ L) in

theorem isOpen_stabLocOne [Submodule.IsLattice E L] : IsOpen (stabLocOne σ J τ L : Set (GLoc σ J v)) := by
  obtain ⟨β, hβ⟩ := exists_isSplitBasis τ L h
  have hU : IsOpen {z : Fv F v | Valued.v z < 1} := by
    simpa using Valued.isOpen_ball (Fv F v) 1
  have e : (stabLocOne σ J τ L : Set (GLoc σ J v)) = (stabLoc σ J L v : Set (GLoc σ J v)) ∩ ⋂ i, ⋂ j,
      (fun g => ((β⁻¹ * splitHom σ J τ g * β).1 - 1) i j) ⁻¹' {z : Fv F v | Valued.v z < 1} :=
    Set.ext fun g => by rw [Set.mem_inter_iff]; simp only [Set.mem_iInter]; exact hβ.mem_stabLocOne_iff
  rw [e]
  refine (isOpen_stabLoc σ J L v).inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    hU.preimage ?_)
  exact ((Units.continuous_val.comp ((continuous_const.mul (continuous_splitHom τ)).mul continuous_const)).sub
    continuous_const).matrix_elem i j

end Swap

section Ties

open ValuativeRel in

theorem GLint_eq_KO_and_princ_eq_KOne (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    letI := GlobalTheory.LocalData.complRel v
    haveI := GlobalTheory.LocalData.isLocalField v
    GLint (Fin n) (v.adicCompletionIntegers F).toSubring = GlobalTheory.SplitWeil.KO (Fv F v) (Fin n) ∧
      princ (v.adicCompletionIntegers F).subtype (IsLocalRing.maximalIdeal _) = GlobalTheory.SplitWeil.KOne (Fv F v) (Fin n) := by
  letI := GlobalTheory.LocalData.complRel v
  haveI := GlobalTheory.LocalData.isLocalField v
  haveI : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (Fv F v)) (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ)))
  have hO : 𝒪[Fv F v] = (v.adicCompletionIntegers F).toSubring := by
    ext y
    rw [Valuation.mem_integer_iff, he.le_one_iff_le_one]
    exact Iff.rfl
  have key : ∀ (O O' : Subring (Fv F v)) [IsLocalRing O] [IsLocalRing O'], O = O' →
      princ (n := Fin n) O.subtype (IsLocalRing.maximalIdeal _) = princ O'.subtype (IsLocalRing.maximalIdeal _) := by
    rintro O _ _ _ rfl; rfl
  haveI : IsLocalRing (v.adicCompletionIntegers F).toSubring :=
    inferInstanceAs (IsLocalRing (v.adicCompletionIntegers F))
  exact ⟨hO ▸ rfl, key _ _ hO.symm⟩

end Ties

section Chart

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.NTheta GlobalTheory.SplitHecke

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {e : AE D} {v : HeightOneSpectrum (𝓞 D.host.F)} {π : AE D →+* Fv D.host.F v}

def chartEmb (hπ : Chart e v π) : D.host.E →ₐ[D.host.F] Fv D.host.F v :=
  { π.comp (incA D) with
    commutes' := fun c => by
      have h1 : incA D (algebraMap D.host.F D.host.E c) =
          algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) c) :=
        (Algebra.TensorProduct.includeRight.commutes c).trans (IsScalarTower.algebraMap_apply _ _ _ c)
      exact (congrArg π h1).trans ((hπ.2.2.1 _).trans ((evFin D.host.F v).commutes c)) }

theorem chartEmb_apply (hπ : Chart e v π) (x : D.host.E) : chartEmb hπ x = π (incA D x) := rfl

theorem chart_eq_splitProj (hπ : Chart e v π) (z : AE D) :
    π z = splitProj (chartEmb hπ) (compFin D.host.F D.host.E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
    have h1 : (a ⊗ₜ[D.host.F] x : AE D) = algebraMap (AF D.host.F) (AE D) a * incA D x :=
      ((Algebra.TensorProduct.tmul_mul_tmul a 1 1 x).trans (by rw [mul_one, one_mul])).symm
    exact (congrArg π h1).trans ((map_mul π _ _).trans (congrArg (· * π (incA D x)) (hπ.2.2.1 a)))

theorem rho_eq_splitEquivIn (hπ : Chart e v π) (V : HSp D) (hJ : IsHermND D.sp.cm.sig V.gram)
    (β : GL (Fin V.rank) (Fv D.host.F v)) (g : GA D V) :
    rho V π β g = splitEquivIn (isCMExt_host D) hJ (chartEmb hπ) β (proj D.sp.cm.sig V.gram v g) := by
  refine Units.ext ?_
  rw [rho_val, splitEquivIn_apply, Units.val_mul, Units.val_mul]
  congr 2
  exact Matrix.ext fun i j => chart_eq_splitProj hπ _

theorem compFin_eq_splitIdem (he : IsSplitIdem D e) (hπ : Chart e v π) :
    compFin D.host.F D.host.E v e = splitIdem (isCMExt_host D) (chartEmb hπ) := by
  refine split_ext (isCMExt_host D) (chartEmb hπ) ?_ ?_
  · have := (hπ.2.1 (1 - e)).2 (by rw [mul_sub, mul_one, he.1, sub_self])
    rw [map_sub, map_one, sub_eq_zero] at this
    rw [splitProj_splitIdem, ← chart_eq_splitProj, ← this]
  · have h1 : ∀ z : AE D, sigR _ D.sp.cm.sig (compFin D.host.F D.host.E v z) =
        compFin D.host.F D.host.E v (cA D z) := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul a x => rfl
    rw [splitProj_comp_splitIdem, splitProj_comp, h1, ← chart_eq_splitProj]
    exact (hπ.2.1 _).2 he.2.1

end Chart

section Inhab

theorem exists_integer_conj_eq_neg (h : IsCMExt F E σ) : ∃ a : 𝓞 E, a ≠ 0 ∧ σ a = -a := by
  obtain ⟨x, hx⟩ := exists_cm_conj_ne h
  obtain ⟨m, hm, he⟩ := exists_integral_multiples ℤ ℚ ({σ x - x} : Finset E)
  refine ⟨⟨m • (σ x - x), he _ (Finset.mem_singleton_self _)⟩, fun e => ?_, ?_⟩
  · exact smul_ne_zero hm (sub_ne_zero.2 hx) (congrArg Subtype.val e)
  · change σ (m • (σ x - x)) = -(m • (σ x - x))
    rw [map_zsmul, map_sub, cm_conj_conj h, ← smul_neg, neg_sub]

theorem one_lt_infinitePlace (h : IsCMExt F E σ) {a : E} (ha0 : a ≠ 0) (ha : σ a = -a) (w : InfinitePlace E) :
    1 < w (1 + 2 * a) := by
  have h2 := h.2.2.2 w.embedding a
  rw [ha, map_neg] at h2
  have h3 : (w.embedding a).re = 0 := by
    have := congrArg Complex.re h2
    rw [Complex.neg_re, Complex.star_def, Complex.conj_re] at this
    linarith
  have h4 : (w.embedding a).im ≠ 0 := fun e => (map_ne_zero _).2 ha0 (Complex.ext h3 e)
  rw [← InfinitePlace.norm_embedding_eq, map_add, map_one, map_mul, map_ofNat, ← Complex.one_lt_normSq_iff,
    Complex.normSq_apply]
  simp [h3, h4]

theorem not_isUnit_of_one_lt {x : 𝓞 E} (hx : ∀ w : InfinitePlace E, 1 < w x) : ¬ IsUnit x := fun hu => by
  have h1 := InfinitePlace.prod_eq_abs_norm (x : E)
  have h2 := isUnit_iff_norm.1 hu
  rw [RingOfIntegers.coe_norm] at h2
  rw [h2, Rat.cast_one, ← Finset.prod_const_one (s := (Finset.univ : Finset (InfinitePlace E)))] at h1
  exact (Finset.prod_lt_prod_of_nonempty (fun _ _ => one_pos)
    (fun w _ => one_lt_pow₀ (hx w) InfinitePlace.mult_pos.ne') Finset.univ_nonempty).ne' h1

theorem exists_split_place (h : IsCMExt F E σ) : ∃ v : HeightOneSpectrum (𝓞 F), Nonempty (E →ₐ[F] Fv F v) := by
  obtain ⟨a, ha0, ha⟩ := exists_integer_conj_eq_neg h
  obtain ⟨s, hs⟩ : ∃ s : 𝓞 E →+* 𝓞 E, ∀ x, (s x : E) = σ x := ⟨RingOfIntegers.mapRingHom (σ : E →+* E), fun _ => rfl⟩
  have hsa : s a = -a := RingOfIntegers.ext ((hs a).trans ha)
  have hlt : ∀ w : InfinitePlace E, 1 < w ((1 + 2 * a : 𝓞 E) : E) :=
    one_lt_infinitePlace h (RingOfIntegers.coe_ne_zero_iff.2 ha0) ha
  obtain ⟨P, hP, hle⟩ := exists_max_ideal_of_mem_nonunits (not_isUnit_of_one_lt hlt)
  have h0 : (1 + 2 * a : 𝓞 E) ≠ 0 := fun e => by
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    have := hlt w
    rw [e] at this
    norm_num at this
  have hs1 : s (1 - 2 * a) = 1 + 2 * a := by rw [map_sub, map_one, map_mul, map_ofNat, hsa]; ring
  have hm : 1 - 2 * a ∈ P.comap s := by rwa [Ideal.mem_comap, hs1]
  have := hP.isPrime
  have hb : P ≠ ⊥ := fun e => h0 (by rwa [e, Ideal.mem_bot] at hle)
  have hb' : P.comap s ≠ ⊥ := fun e => h0 (by rw [e, Ideal.mem_bot] at hm; rw [← hs1, hm, map_zero])
  obtain ⟨τ, -⟩ := existsUnique_splitPrime_eq h (w := ⟨P, hP.isPrime, hb⟩) (w' := ⟨P.comap s, inferInstance, hb'⟩)
    (fun e => hP.ne_top ((Ideal.eq_top_iff_one _).2 (by
      have e' : P = P.comap s := congrArg HeightOneSpectrum.asIdeal e
      rw [← e'] at hm
      convert sub_mem hle (P.mul_mem_right a (add_mem hle hm)) using 1
      ring))) rfl
    (HeightOneSpectrum.ext (Ideal.ext fun c => by
      have : s (algebraMap (𝓞 F) (𝓞 E) c) = algebraMap (𝓞 F) (𝓞 E) c :=
        RingOfIntegers.ext ((hs _).trans (σ.commutes (c : F)))
      change s (algebraMap (𝓞 F) (𝓞 E) c) ∈ P ↔ algebraMap (𝓞 F) (𝓞 E) c ∈ P
      rw [this]))
  exact ⟨_, ⟨τ⟩⟩

omit [NumberField F] [NumberField E] in
theorem isHermND_one (σ : E →ₐ[F] E) (n : ℕ) : IsHermND σ (1 : Matrix (Fin n) (Fin n) E) :=
  ⟨fun i j => by by_cases e : i = j <;> simp [Matrix.one_apply, e, eq_comm], by simp⟩

theorem exists_split_data (h : IsCMExt F E σ) (n : ℕ) :
    ∃ (v : HeightOneSpectrum (𝓞 F)) (τ : E →ₐ[F] Fv F v), IsHermND σ (1 : Matrix (Fin n) (Fin n) E) ∧
      IsSelfDualAt σ 1 (stdLattice E n) v ∧ IsSplitBasis τ (stdLattice E n) 1 := by
  obtain ⟨v, ⟨τ⟩⟩ := exists_split_place h
  exact ⟨v, τ, isHermND_one σ n, isSelfDualAt_stdLattice_one σ v, isSplitBasis_stdLattice τ h⟩

example : ∃ v : HeightOneSpectrum (𝓞 (maximalRealSubfield (CyclotomicField 4 ℚ))),
    Nonempty (CyclotomicField 4 ℚ →ₐ[maximalRealSubfield (CyclotomicField 4 ℚ)] Fv _ v) :=
  haveI : IsCMField (CyclotomicField 4 ℚ) := IsCyclotomicExtension.Rat.isCMField _ (S := {4}) ⟨4, rfl, by norm_num⟩
  exists_split_place (isCMExt_of_isCMField _)

example (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (g : GLoc σ (1 : Matrix (Fin n) (Fin n) E) v) :
    (splitEquiv h (isHermND_one σ n) (τ.comp σ) g).1 = ((splitEquiv h (isHermND_one σ n) τ g)⁻¹).1ᵀ := by
  have e : splitGram (isHermND_one σ n) τ = 1 := Units.ext (Matrix.map_one _ (map_zero τ) (map_one τ))
  rw [splitEquiv_comp, e, dualConj_one_val]

example (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) :
    stabLocOne σ 1 τ (stdLattice E 2) ≠ stabLoc σ (1 : Matrix (Fin 2) (Fin 2) E) (stdLattice E 2) v := fun e => by
  obtain ⟨k, hk⟩ := splitRed_surjective h (isHermND_one σ 2) (isSelfDualAt_stdLattice_one σ v)
    (isSplitBasis_stdLattice τ h) (Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 1; 0, 1] (by simp))
  rw [(splitRed_eq_one_iff _ _ _ _ k).2 (e.ge k.2)] at hk
  simpa using congrArg (fun x => x.1 0 1) hk

example (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) :
    stabLoc σ (1 : Matrix (Fin 1) (Fin 1) E) (stdLattice E 1) v ≠ ⊤ := fun e => by
  obtain ⟨p, hp⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (1 : ℤ))
  have h0 : p ≠ 0 := fun e => WithZero.exp_ne_zero (hp.symm.trans ((congrArg _ e).trans (map_zero _)))
  obtain ⟨g, hg⟩ := (splitEquivIn h (isHermND_one σ 1) τ 1).surjective
    (Matrix.GeneralLinearGroup.mkOfDetNeZero !![p] (by simpa using h0))
  have h1 := (mem_stabLoc_iff_GLint h (isHermND_one σ 1) (isSelfDualAt_stdLattice_one σ v)
    (isSplitBasis_stdLattice τ h)).1 (e ▸ Subgroup.mem_top g)
  rw [hg] at h1
  have h2 : Valued.v p ≤ 1 := (mem_GLint_iff.1 h1).1 0 0
  rw [hp, ← WithZero.exp_zero, WithZero.exp_le_exp] at h2
  omega

end Inhab

end GlobalTheory.AdelicU

end
