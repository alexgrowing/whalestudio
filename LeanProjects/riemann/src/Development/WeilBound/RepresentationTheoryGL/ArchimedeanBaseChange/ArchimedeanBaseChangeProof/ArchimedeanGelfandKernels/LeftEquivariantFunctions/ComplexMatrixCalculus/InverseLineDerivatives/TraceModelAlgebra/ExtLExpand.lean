import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InverseLineDerivatives.TraceModelAlgebra.TraceOnModel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrETransposeEqPhiSeq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandValueNegation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandOperatorCenterExpansion

noncomputable section

open Matrix MvPolynomial

namespace PositivityTheory.RgBcC.Cxd2.Alg

open GlobalTheory.Mem.Gelf (rowE GlRel gelfC)

variable {n : ℕ}

def matB (lam : Fin n → ℤ) (F : Module.End ℂ (MvPolynomial (Fin n × Fin n) ℂ)) : Matrix (Jd n lam) (Jd n lam) ℂ :=
  fun i j => Cxc.extL lam i (F ((wb lam j : Formalism.BasicNotions.nablaSq ℂ n (dw lam)) : MvPolynomial (Fin n × Fin n) ℂ))

theorem extL_wb (lam : Fin n → ℤ) (i j : Jd n lam) :
    Cxc.extL lam i ((wb lam j : Formalism.BasicNotions.nablaSq ℂ n (dw lam)) : MvPolynomial (Fin n × Fin n) ℂ) =
      (1 : Matrix (Jd n lam) (Jd n lam) ℂ) i j := by
  rw [Cxc.extL_spec, Module.Basis.repr_self, Finsupp.single_apply, Matrix.one_apply]
  split_ifs <;> simp_all [eq_comm]

theorem extL_expand (lam : Fin n → ℤ) (i : Jd n lam) (F : Module.End ℂ (MvPolynomial (Fin n × Fin n) ℂ))
    {g : MvPolynomial (Fin n × Fin n) ℂ} (hg : g ∈ Formalism.BasicNotions.nablaSq ℂ n (dw lam)) :
    ∑ l, Cxc.extL lam i (F ((wb lam l : Formalism.BasicNotions.nablaSq ℂ n (dw lam)) : MvPolynomial (Fin n × Fin n) ℂ)) *
      Cxc.extL lam l g = Cxc.extL lam i (F g) := by
  have hs := (wb lam).sum_repr ⟨g, hg⟩
  have e : g = ∑ l, (wb lam).repr ⟨g, hg⟩ l • ((wb lam l : Formalism.BasicNotions.nablaSq ℂ n (dw lam)) : MvPolynomial (Fin n × Fin n) ℂ) := by
    have h2 : ((∑ l, (wb lam).repr ⟨g, hg⟩ l • wb lam l : Formalism.BasicNotions.nablaSq ℂ n (dw lam)) :
        MvPolynomial (Fin n × Fin n) ℂ) = g := by rw [hs]
    conv_lhs => rw [← h2]
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul]
  conv_rhs => rw [e]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, map_smul, smul_eq_mul, mul_comm, Cxc.extL_spec lam l ⟨g, hg⟩]

theorem matB_mul (lam : Fin n → ℤ) (F G : Module.End ℂ (MvPolynomial (Fin n × Fin n) ℂ))
    (hG : ∀ g ∈ Formalism.BasicNotions.nablaSq ℂ n (dw lam), G g ∈ Formalism.BasicNotions.nablaSq ℂ n (dw lam)) :
    matB lam (F * G) = matB lam F * matB lam G := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [matB, Module.End.mul_apply]
  rw [extL_expand lam i F (hG _ (wb lam j).2)]

theorem matB_add (lam : Fin n → ℤ) (F G : Module.End ℂ (MvPolynomial (Fin n × Fin n) ℂ)) :
    matB lam (F + G) = matB lam F + matB lam G := by
  ext i j; simp [matB]

theorem matB_sub (lam : Fin n → ℤ) (F G : Module.End ℂ (MvPolynomial (Fin n × Fin n) ℂ)) :
    matB lam (F - G) = matB lam F - matB lam G := by
  ext i j; simp [matB]

theorem matB_zero (lam : Fin n → ℤ) : matB lam 0 = 0 := by
  ext i j; simp [matB]

theorem matB_one (lam : Fin n → ℤ) : matB lam 1 = 1 := by
  ext i j; simp only [matB, Module.End.one_apply]; exact extL_wb lam i j

theorem matB_smul (lam : Fin n → ℤ) (s : ℂ) (F : Module.End ℂ (MvPolynomial (Fin n × Fin n) ℂ)) :
    matB lam (s • F) = s • matB lam F := by
  ext i j; simp [matB]

theorem At_eq (lam : Fin n → ℤ) (a b : Fin n) : At lam a b = matB lam (Et lam a b) := rfl

theorem At_pow (lam : Fin n → ℤ) (k : ℕ) (a b : Fin n) : (At lam ^ k) a b = matB lam ((Et lam ^ k) a b) := by
  induction k generalizing a b with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    split_ifs
    · exact (matB_one lam).symm
    · exact (matB_zero lam).symm
  | succ k ih =>
    rw [pow_succ', pow_succ', Matrix.mul_apply, Matrix.mul_apply]
    rw [show (∑ c, Et lam a c * (Et lam ^ k) c b) = ∑ c, Et lam a c * (Et lam ^ k) c b from rfl]
    have hs : ∀ (s : Finset (Fin n)), matB lam (∑ c ∈ s, Et lam a c * (Et lam ^ k) c b) =
        ∑ c ∈ s, matB lam (Et lam a c) * matB lam ((Et lam ^ k) c b) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp [matB_zero]
      | insert x s hx ih2 =>
        rw [Finset.sum_insert hx, Finset.sum_insert hx, matB_add, ih2,
          matB_mul lam _ _ (fun g hg => Etpow_mem lam k x b hg)]
    rw [hs]
    exact Finset.sum_congr rfl fun c _ => by rw [ih, At_eq]

theorem atTrace' : AtTrace := by
  intro n lam hlam k
  ext i j
  rw [Matrix.trace, Matrix.sum_apply]
  simp only [Matrix.diag_apply, At_pow, matB]
  have e : ∑ a, Cxc.extL lam i ((Et lam ^ k) a a ((wb lam j : Formalism.BasicNotions.nablaSq ℂ n (dw lam)) : MvPolynomial (Fin n × Fin n) ℂ)) =
      Cxc.extL lam i ((Et lam ^ k).trace ((wb lam j : Formalism.BasicNotions.nablaSq ℂ n (dw lam)) : MvPolynomial (Fin n × Fin n) ℂ)) := by
    rw [Matrix.trace, LinearMap.sum_apply, map_sum]
    rfl
  rw [e, trace_on_model lam hlam k (wb lam j).2, map_smul, extL_wb, gelfC_eq, Matrix.smul_apply]

theorem glRel_At (lam : Fin n → ℤ) (a b c d : Fin n) :
    At lam a b * At lam c d - At lam c d * At lam a b =
      (if b = c then At lam a d else 0) - (if a = d then At lam c b else 0) := by
  have h := glRel_Et lam a b c d
  have hm : ∀ x y, ∀ g ∈ Formalism.BasicNotions.nablaSq ℂ n (dw lam), Et lam x y g ∈ Formalism.BasicNotions.nablaSq ℂ n (dw lam) :=
    fun x y g hg => Et_mem lam x y hg
  have := congrArg (matB lam) h
  rw [matB_sub, matB_mul lam _ _ (hm c d), matB_mul lam _ _ (hm a b), matB_sub] at this
  rw [At_eq, At_eq, At_eq, At_eq, this]
  congr 1
  · split_ifs <;> simp [At_eq, matB_zero]
  · by_cases h1 : a = d
    · subst h1; simp [At_eq]
    · have h2 : ¬ d = a := fun e => h1 e.symm
      simp [h1, h2, matB_zero]

theorem epw_eq_pow {A : Type} [Ring A] (e : Fin n → Fin n → A) (m : ℕ) (a b : Fin n) :
    GlobalTheory.CompanionTheory.WaveMult.Epw e m a b = ((Matrix.of e) ^ m) a b := by
  induction m generalizing a b with
  | zero => rw [GlobalTheory.CompanionTheory.WaveMult.GlTranspose.epw_zero, pow_zero, Matrix.one_apply]
  | succ m ih =>
    rw [GlobalTheory.CompanionTheory.WaveMult.GlTranspose.epw_succ, pow_succ', Matrix.mul_apply]
    exact Finset.sum_congr rfl fun c _ => by rw [ih, Matrix.of_apply]

theorem trE_eq {A : Type} [Ring A] (e : Fin n → Fin n → A) (m : ℕ) :
    GlobalTheory.CompanionTheory.WaveMult.trE e m = ((Matrix.of e) ^ m).trace := by
  simp only [GlobalTheory.CompanionTheory.WaveMult.trE, Matrix.trace, Matrix.diag_apply, epw_eq_pow]

theorem pow_neg_of {A : Type} [Ring A] [Algebra ℂ A] (e : Fin n → Fin n → A) (m : ℕ) :
    (Matrix.of fun a b => -(e a b)) ^ m = ((-1 : ℂ) ^ m) • (Matrix.of e) ^ m := by
  have : (Matrix.of fun a b => -(e a b)) = (-1 : ℂ) • Matrix.of e := by ext a b; simp
  rw [this, smul_pow]

theorem atTraceT' : AtTraceT := by
  intro n lam hlam k
  set A := Matrix (Jd n lam) (Jd n lam) ℂ
  set e : Fin n → Fin n → A := fun a b => At lam a b
  have he : ∀ a b c d, e a b * e c d - e c d * e a b = (if b = c then e a d else 0) - (if a = d then e c b else 0) :=
    fun a b c d => glRel_At lam a b c d
  have hT := GlobalTheory.CompanionTheory.WaveMult.GlTranspose.trE_transpose_eq_phiSeq n e he k
  have htr : GlobalTheory.CompanionTheory.WaveMult.trE e = fun m => algebraMap ℂ A (GlobalTheory.Dec.gelfVal (infOf lam true) m) := by
    funext m
    rw [trE_eq, Algebra.algebraMap_eq_smul_one]
    exact atTrace' n lam hlam m
  have hφ := GlobalTheory.CompanionTheory.WaveMult.GenTr.map_phiSeq (algebraMap ℂ A) (n : ℂ) (GlobalTheory.Dec.gelfVal (infOf lam true)) k
  rw [map_natCast] at hφ
  have hneg := GlobalTheory.CompanionTheory.WaveMult.ValPhi.gelfVal_neg_eq_phiSeq n (infOf lam true) k
  have hinf : (fun a => -(infOf lam true a)) = infOf lam false := by
    funext a; simp [infOf]
  rw [hinf] at hneg
  have h1 : (Matrix.of fun a b => -(At lam b a)) ^ k = ((-1 : ℂ) ^ k) • (Matrix.of fun a b => e b a) ^ k :=
    pow_neg_of (fun a b => e b a) k
  have h2 : GlobalTheory.CompanionTheory.WaveMult.phiSeq (n : A) (fun m => algebraMap ℂ A (GlobalTheory.Dec.gelfVal (infOf lam true) m)) k =
      algebraMap ℂ A (GlobalTheory.CompanionTheory.WaveMult.phiSeq (n : ℂ) (GlobalTheory.Dec.gelfVal (infOf lam true)) k) := by
    rw [hφ]; rfl
  rw [h1, Matrix.trace_smul, ← trE_eq, hT, htr, h2, ← hneg, Algebra.algebraMap_eq_smul_one, smul_smul, ← mul_assoc,
    ← mul_pow]
  norm_num

end PositivityTheory.RgBcC.Cxd2.Alg
