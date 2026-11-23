import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaBijections.SySmulRight

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl

namespace PositivityTheory.SiegelWeilFormula.TBij

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace Adp

variable (d : SD σ)

abbrev Ix : Type := Fin d.m × Fin d.n × Fin 2

theorem cmb_crd (X : Mx F E d.m d.n) : d.cmb (d.crd X) = X := by
  ext i j
  simp only [SD.cmb, SD.crd]
  conv_rhs => rw [← (Algebra.TensorProduct.basis (AF F) d.bs).sum_repr (X i j)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem crd_cmb (c : Ix d → AF F) : d.crd (d.cmb c) = c := by
  funext ⟨i, j, k⟩
  simp only [SD.crd, SD.cmb]
  have h : ∑ k', c (i, j, k') ⊗ₜ[F] d.bs k' = ∑ k', c (i, j, k') • (Algebra.TensorProduct.basis (AF F) d.bs) k' := by
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h]
  exact congrFun (Module.Basis.repr_sum_self _ (fun k' => c (i, j, k'))) k

theorem crd_add (X X' : Mx F E d.m d.n) : d.crd (X + X') = d.crd X + d.crd X' := by
  funext k; simp [SD.crd]

theorem crd_smul (a : AF F) (X : Mx F E d.m d.n) : d.crd (a • X) = a • d.crd X := by
  funext k; simp [SD.crd]

def cmbL : (Ix d → AF F) →ₗ[AF F] Mx F E d.m d.n where
  toFun := d.cmb
  map_add' c c' := by ext i j; simp [SD.cmb, TensorProduct.add_tmul, Finset.sum_add_distrib]
  map_smul' a c := by ext i j; simp [SD.cmb, Finset.smul_sum, TensorProduct.smul_tmul']

def ek (k : Ix d) : Mx F E d.m d.n := d.cmb fun j => if k = j then 1 else 0

theorem cmb_sum (c : Ix d → AF F) : d.cmb c = ∑ k, c k • ek d k :=
  LinearMap.pi_apply_eq_sum_univ (cmbL d) c

theorem ek_rat (k : Ix d) : ∃ M : Matrix (Fin d.m) (Fin d.n) E, ek d k = incM F M := by
  refine ⟨Matrix.of fun i j => (∑ k', (if k = (i, j, k') then (1 : F) else 0) • d.bs k' : E), ?_⟩
  ext i j
  simp only [ek, SD.cmb, incM, Matrix.map_apply, Matrix.of_apply, map_sum]
  refine Finset.sum_congr rfl fun k' _ => ?_
  show _ = (1 : AF F) ⊗ₜ[F] _
  split_ifs <;> simp

theorem crd_incM (M : Matrix (Fin d.m) (Fin d.n) E) (k : Ix d) :
    d.crd (incM F M) k = algebraMap F (AF F) (d.bs.repr (M k.1 k.2.1) k.2.2) := by
  simp only [SD.crd, incM, Matrix.map_apply]
  rw [show inclR (F := F) (AF F) (M k.1 k.2.1) = (1 : AF F) ⊗ₜ[F] M k.1 k.2.1 from rfl,
    Algebra.TensorProduct.basis_repr_tmul]
  simp

theorem xs_incM (x : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) E) :
    xs d (incM F x) = incM F ((x * ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E).1)ᵀ).toCols₂) := by
  rw [xs, ← incM_transpose, ← incM_mul]
  rfl

theorem om_ratV {κ : Type} [Fintype κ] (y z y' z' : κ → F) :
    om (ratV y z) (ratV y' z') = algebraMap F (AF F) (om (y, z) (y', z')) := by
  simp [om, ratV, dotProduct, map_sum, map_mul, map_sub]

theorem dot_sv {κ : Type} [Fintype κ] (τ : κ ≃ Ix d) (X : Mx F E d.m d.n)
    (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    (fun k => d.crd X (τ k)) ⬝ᵥ (fun k => sy d (ek d (τ k) * (yy d)ᵀ) w) = sy d (X * (yy d)ᵀ) w := by
  rw [dotProduct, Equiv.sum_comp τ (fun i => d.crd X i * sy d (ek d i * (yy d)ᵀ) w), ← sy_sum_left]
  congr 1
  conv_rhs => rw [← cmb_crd d X, cmb_sum, Matrix.sum_mul]
  simp only [Matrix.smul_mul]

def c0 {κ : Type} [Fintype κ] (τ : κ ≃ Ix d) :
    Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E) →ₗ[AF F] (κ → AF F) × (κ → AF F) where
  toFun w := (fun k => d.crd (xs d w) (τ k), fun k => sy d (ek d (τ k) * (yy d)ᵀ) w)
  map_add' w w' := by
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · simp [xs_add, crd_add]
    · simp [sy_add_right]
  map_smul' a w := by
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · simp [xs_smul, crd_smul]
    · simp [sy_smul_right]

theorem coordinates_apply {κ : Type} [Fintype κ] (τ : κ ≃ Ix d) (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    c0 d τ w = (fun k => d.crd (xs d w) (τ k), fun k => sy d (ek d (τ k) * (yy d)ᵀ) w) := rfl

theorem symplecticForm_coordinates {κ : Type} [Fintype κ] (τ : κ ≃ Ix d) (w w' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    om (c0 d τ w) (c0 d τ w') = sy d w w' := by
  rw [coordinates_apply, coordinates_apply, om, dot_sv, dot_sv]
  exact (sy_split d w w').symm

theorem coordinates_frame {κ : Type} [Fintype κ] (τ : κ ≃ Ix d) (X : Mx F E d.m d.n) :
    c0 d τ (X * (yy d)ᵀ) = (fun k => d.crd X (τ k), 0) := by
  rw [coordinates_apply, xs_frame]
  refine Prod.ext rfl (funext fun k => ?_)
  exact sy_frame d _ _

theorem coordinates_fst_eq_zero {κ : Type} [Fintype κ] (τ : κ ≃ Ix d) (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E))
    (h : (c0 d τ w).1 = 0) : ∃ Z : Mx F E d.m d.n, w = Z * (dg d)ᵀ := by
  have h1 : d.crd (xs d w) = 0 := by
    funext i
    have := congrFun h (τ.symm i)
    simpa [coordinates_apply] using this
  have h2 : xs d w = 0 := by
    rw [← cmb_crd d (xs d w), h1]
    exact (cmbL d).map_zero
  obtain ⟨Z, hZ⟩ := decomp d w
  exact ⟨Z, by rw [hZ, h2, Matrix.zero_mul, add_zero]⟩

theorem coordinates_rational {κ : Type} [Fintype κ] (τ : κ ≃ Ix d) (x : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) E) :
    ∃ y z : κ → F, c0 d τ (incM F x) = ratV y z := by
  have hs : ∀ k, ∃ r : F, sy d (ek d (τ k) * (yy d)ᵀ) (incM F x) = algebraMap F (AF F) r := by
    intro k
    obtain ⟨M, hM⟩ := ek_rat d (τ k)
    rw [hM, yy, ← incM_transpose, ← incM_mul, sy_eq]
    obtain ⟨y, z, h⟩ := d.ok.dbl.rat (M * (d.b.1.toCols₂)ᵀ)
    obtain ⟨y', z', h'⟩ := d.ok.dbl.rat x
    exact ⟨om (y, z) (y', z'), by rw [h, h']; exact om_ratV y z y' z'⟩
  choose r hr using hs
  refine ⟨fun k => d.bs.repr (((x * ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E).1)ᵀ).toCols₂) (τ k).1 (τ k).2.1) (τ k).2.2, r, ?_⟩
  rw [coordinates_apply, xs_incM]
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · exact crd_incM d _ (τ k)
  · exact hr k

end Adp

end PositivityTheory.SiegelWeilFormula.TBij

end
