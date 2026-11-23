import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaBijections.SymplecticFormCoordinates
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTbijFrame

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.TBij
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
namespace Adp
variable (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ)
abbrev _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix : Type := Fin d.m × Fin d.n × Fin 2
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_crd (X : Mx F E d.m d.n) : d.cmb (d.crd X) = X := by
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb, _root_.PositivityTheory.SiegelWeilFormula.SD_k.crd]
  conv_rhs => rw [← (Algebra.TensorProduct.basis (AF F) d.bs).sum_repr (X i j)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_cmb (c : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d → AF F) : d.crd (d.cmb c) = c := by
  funext ⟨i, j, k⟩
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb]
  have h : ∑ k', c (i, j, k') ⊗ₜ[F] d.bs k' = ∑ k', c (i, j, k') • (Algebra.TensorProduct.basis (AF F) d.bs) k' := by
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h]
  exact congrFun (Module.Basis.repr_sum_self _ (fun k' => c (i, j, k'))) k
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_add (X X' : Mx F E d.m d.n) : d.crd (X + X') = d.crd X + d.crd X' := by
  funext k; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd]
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_smul (a : AF F) (X : Mx F E d.m d.n) : d.crd (a • X) = a • d.crd X := by
  funext k; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd]
def _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmbL : (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d → AF F) →ₗ[AF F] Mx F E d.m d.n where
  toFun := d.cmb
  map_add' c c' := by ext i j; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb, TensorProduct.add_tmul, Finset.sum_add_distrib]
  map_smul' a c := by ext i j; simp [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb, Finset.smul_sum, TensorProduct.smul_tmul']
def _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek (k : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) : Mx F E d.m d.n := d.cmb fun j => if k = j then 1 else 0
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_sum (c : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d → AF F) : d.cmb c = ∑ k, c k • _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek d k :=
  LinearMap.pi_apply_eq_sum_univ (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmbL d) c
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek_rat (k : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) : ∃ M : Matrix (Fin d.m) (Fin d.n) E, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek d k = incM F M := by
  refine ⟨Matrix.of fun i j => (∑ k', (if k = (i, j, k') then (1 : F) else 0) • d.bs k' : E), ?_⟩
  ext i j
  simp only [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek, _root_.PositivityTheory.SiegelWeilFormula.SD_k.cmb, incM, Matrix.map_apply, Matrix.of_apply, map_sum]
  refine Finset.sum_congr rfl fun k' _ => ?_
  show _ = (1 : AF F) ⊗ₜ[F] _
  split_ifs <;> simp
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_incM (M : Matrix (Fin d.m) (Fin d.n) E) (k : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) :
    d.crd (incM F M) k = algebraMap F (AF F) (d.bs.repr (M k.1 k.2.1) k.2.2) := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, incM, Matrix.map_apply]
  rw [show inclR (F := F) (AF F) (M k.1 k.2.1) = (1 : AF F) ⊗ₜ[F] M k.1 k.2.1 from rfl,
    Algebra.TensorProduct.basis_repr_tmul]
  simp
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs_incM (x : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) E) :
    _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d (incM F x) = incM F ((x * ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E).1)ᵀ).toCols₂) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs, ← incM_transpose, ← incM_mul]
  rfl
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dot_sv {κ : Type} [Fintype κ] (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (X : Mx F E d.m d.n)
    (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    (fun k => d.crd X (τ k)) ⬝ᵥ (fun k => _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek d (τ k) * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) w) = _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (X * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) w := by
  rw [dotProduct, Equiv.sum_comp τ (fun i => d.crd X i * _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek d i * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) w), ← _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_sum_left]
  congr 1
  conv_rhs => rw [← _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_crd d X, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_sum, Matrix.sum_mul]
  simp only [Matrix.smul_mul]
def _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 {κ : Type} [Fintype κ] (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) :
    Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E) →ₗ[AF F] (κ → AF F) × (κ → AF F) where
  toFun w := (fun k => d.crd (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w) (τ k), fun k => _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek d (τ k) * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) w)
  map_add' w w' := by
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · simp [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs_add, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_add]
    · simp [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_add_right]
  map_smul' a w := by
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · simp [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs_smul, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_smul]
    · simp [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_smul_right]
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_apply {κ : Type} [Fintype κ] (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w = (fun k => d.crd (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w) (τ k), fun k => _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek d (τ k) * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) w) := rfl
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.symplecticForm_coordinates {κ : Type} [Fintype κ] (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (w w' : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E)) :
    om (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w) (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w') = _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d w w' := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_apply, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_apply, om, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dot_sv, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dot_sv]
  exact (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_split d w w').symm
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_frame {κ : Type} [Fintype κ] (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (X : Mx F E d.m d.n) :
    _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ (X * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) = (fun k => d.crd X (τ k), 0) := by
  rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_apply, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs_frame]
  refine Prod.ext rfl (funext fun k => ?_)
  exact _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_frame d _ _
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_fst_eq_zero {κ : Type} [Fintype κ] (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (w : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) (AE F E))
    (h : (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ w).1 = 0) : ∃ Z : Mx F E d.m d.n, w = Z * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.dg d)ᵀ := by
  have h1 : d.crd (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w) = 0 := by
    funext i
    have := congrFun h (τ.symm i)
    simpa [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_apply] using this
  have h2 : _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w = 0 := by
    rw [← _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmb_crd d (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs d w), h1]
    exact (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.cmbL d).map_zero
  obtain ⟨Z, hZ⟩ := _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.decomp d w
  exact ⟨Z, by rw [hZ, h2, Matrix.zero_mul, add_zero]⟩
theorem _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_rational {κ : Type} [Fintype κ] (τ : κ ≃ _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.Ix d) (x : Matrix (Fin d.m) (Fin d.n ⊕ Fin d.n) E) :
    ∃ y z : κ → F, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.c0 d τ (incM F x) = ratV y z := by
  have hs : ∀ k, ∃ r : F, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy d (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek d (τ k) * (_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy d)ᵀ) (incM F x) = algebraMap F (AF F) r := by
    intro k
    obtain ⟨M, hM⟩ := _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.ek_rat d (τ k)
    rw [hM, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.yy, ← incM_transpose, ← incM_mul, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.sy_eq]
    obtain ⟨y, z, h⟩ := d.ok.dbl.rat (M * (d.b.1.toCols₂)ᵀ)
    obtain ⟨y', z', h'⟩ := d.ok.dbl.rat x
    exact ⟨om (y, z) (y', z'), by rw [h, h']; exact om_ratV y z y' z'⟩
  choose r hr using hs
  refine ⟨fun k => d.bs.repr (((x * ((d.b⁻¹ : GL (Fin d.n ⊕ Fin d.n) E).1)ᵀ).toCols₂) (τ k).1 (τ k).2.1) (τ k).2.2, r, ?_⟩
  rw [_root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.coordinates_apply, _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.xs_incM]
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · exact _root_.PositivityTheory.SiegelWeilFormula.TBij_k.Adp.crd_incM d _ (τ k)
  · exact hr k
end Adp
end PositivityTheory.SiegelWeilFormula.TBij
end
end
