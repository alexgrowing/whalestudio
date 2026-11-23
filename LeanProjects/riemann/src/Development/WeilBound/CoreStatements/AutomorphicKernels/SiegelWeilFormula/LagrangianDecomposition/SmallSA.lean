import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SiegelSmall

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def cmbE (bs : Module.Basis (Fin 2) F E) (c : Fin 2 → AF F) : AE F E := ∑ t, c t • ((1 : AF F) ⊗ₜ[F] bs t)

theorem cmbE_eq (bs : Module.Basis (Fin 2) F E) (c : Fin 2 → AF F) :
    cmbE bs c = ∑ t, c t • (Algebra.TensorProduct.basis (AF F) bs) t := by
  simp [cmbE, Algebra.TensorProduct.basis_apply]

theorem repr_cmbE_apply (bs : Module.Basis (Fin 2) F E) (c : Fin 2 → AF F) (t : Fin 2) :
    (Algebra.TensorProduct.basis (AF F) bs).repr (cmbE bs c) t = c t := by
  rw [cmbE_eq, Module.Basis.repr_sum_self]

theorem cmbE_repr (bs : Module.Basis (Fin 2) F E) (z : AE F E) :
    cmbE bs (fun t => (Algebra.TensorProduct.basis (AF F) bs).repr z t) = z := by
  rw [cmbE_eq]
  exact (Algebra.TensorProduct.basis (AF F) bs).sum_repr z

def cmbB {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (y : Fin m × Fin n × Fin 2 → AF F) : Mx F E m n :=
  fun a i => cmbE bs fun t => y (a, i, t)

theorem crdB_cmbB {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (y : Fin m × Fin n × Fin 2 → AF F) :
    crdB bs (cmbB bs y) = y := by
  funext k
  simp only [crdB, cmbB, repr_cmbE_apply]

theorem cmbB_crdB {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (X : Mx F E m n) : cmbB bs (crdB bs X) = X := by
  funext a i
  simp only [cmbB, crdB, cmbE_repr]

def Lk {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (M : Matrix (Fin m) (Fin m) (AE F E)) (y : Fin m × Fin n × Fin 2 → AF F) :
    Fin m × Fin n × Fin 2 → AF F := crdB bs (M * cmbB bs y)

theorem Lk_crdB {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (M : Matrix (Fin m) (Fin m) (AE F E)) (X : Mx F E m n) :
    Lk bs M (crdB bs X) = crdB bs (M * X) := by rw [Lk, cmbB_crdB]

theorem Lk_one {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (y : Fin m × Fin n × Fin 2 → AF F) : Lk bs 1 y = y := by
  rw [Lk, Matrix.one_mul, crdB_cmbB]

theorem Lk_mul {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (M M' : Matrix (Fin m) (Fin m) (AE F E))
    (y : Fin m × Fin n × Fin 2 → AF F) : Lk bs (M * M') y = Lk bs M (Lk bs M' y) := by
  rw [Lk, Lk, Lk, cmbB_crdB, Matrix.mul_assoc]

theorem Lk_zero {m n : ℕ} (bs : Module.Basis (Fin 2) F E) (M : Matrix (Fin m) (Fin m) (AE F E)) :
    Lk (n := n) bs M 0 = 0 := by
  have : cmbB (m := m) (n := n) bs 0 = 0 := by
    funext a i; simp [cmbB, cmbE]
  funext k
  simp [Lk, this, crdB]

def Lc {m : ℕ} (bs : Module.Basis (Fin 2) F E) (M : Matrix (Fin m) (Fin m) (AE F E)) (v : Fin m × Fin 2 → AF F) :
    Fin m × Fin 2 → AF F :=
  fun p => (Algebra.TensorProduct.basis (AF F) bs).repr ((M *ᵥ fun a => cmbE bs fun t => v (a, t)) p.1) p.2

theorem Lc_zero {m : ℕ} (bs : Module.Basis (Fin 2) F E) (M : Matrix (Fin m) (Fin m) (AE F E)) : Lc bs M 0 = 0 := by
  funext p
  have hz : (fun _ : Fin m => (0 : AE F E)) = 0 := rfl
  simp [Lc, cmbE, hz, Matrix.mulVec_zero]

theorem triple_index_symm_embedded {m n N : ℕ} (h : n + 1 = N) (a : Fin m) (j : Fin n) (t : Fin 2) :
    (eK m h).symm (a, em0 h j, t) = Sum.inl (a, j, t) := by
  rw [Equiv.symm_apply_eq]; rfl

theorem triple_index_symm_last {m n N : ℕ} (h : n + 1 = N) (a : Fin m) (t : Fin 2) :
    (eK m h).symm (a, i0 h, t) = Sum.inr (a, t) := by
  rw [Equiv.symm_apply_eq]; rfl

theorem Lk_eK {m n N : ℕ} (h : n + 1 = N) (bs : Module.Basis (Fin 2) F E) (M : Matrix (Fin m) (Fin m) (AE F E))
    (x : K1 m n → AF F) :
    Lk bs M (x ∘ (eK m h).symm) ∘ eK m h = Sum.elim (Lk bs M (x ∘ Sum.inl)) (Lc bs M (x ∘ Sum.inr)) := by
  funext k
  rcases k with ⟨a, j, t⟩ | ⟨a, t⟩
  · have hk : eK m h (Sum.inl (a, j, t)) = (a, em0 h j, t) := rfl
    simp only [Function.comp_apply, hk, Sum.elim_inl, Lk, crdB, cmbB, Matrix.mul_apply, triple_index_symm_embedded]
  · have hk : eK m h (Sum.inr (a, t)) = (a, i0 h, t) := rfl
    simp only [Function.comp_apply, hk, Sum.elim_inr, Lk, Lc, crdB, cmbB, Matrix.mul_apply, Matrix.mulVec,
      dotProduct, triple_index_symm_last]

end PositivityTheory.SiegelWeilFormula.Ald

end
