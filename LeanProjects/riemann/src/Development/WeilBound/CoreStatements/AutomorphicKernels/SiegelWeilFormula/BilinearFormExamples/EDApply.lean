import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SDarb
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.BilinearFormExamples.EQSymmApply

noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ldexa
open PositivityTheory.SiegelWeilFormula.Ald

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable {m n : ℕ}

def Pm (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (bs : Module.Basis (Fin 2) F E) :
    Matrix (Fin m × Fin n × Fin 2) (Fin m × Fin n × Fin 2) (AF F) :=
  ((Gm (n := n) σ J bs).map (algebraMap F (AF F)))ᵀ

theorem Pm_unit [FiniteDimensional F E] (σ : E →ₐ[F] E) (hσ : ∀ a, σ (σ a) = a) (J : Matrix (Fin m) (Fin m) E)
    (hJ : J.det ≠ 0) (bs : Module.Basis (Fin 2) F E) : IsUnit (Pm (n := n) σ J bs).det := by
  rw [Pm, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (Ne.isUnit (Gm_det σ hσ J hJ bs)).map _

def eD (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (bs : Module.Basis (Fin 2) F E) (b : GL (Fin n ⊕ Fin n) E)
    (hP : IsUnit (Pm (n := n) σ J bs).det) :
    Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E) ≃ₗ[AF F] (Fin m × Fin n × Fin 2 → AF F) × (Fin m × Fin n × Fin 2 → AF F) :=
  (eQ b).trans ((LinearEquiv.prodComm (AF F) _ _).trans (by
    first
    | exact (bM bs).equivFun.prodCongr ((bM bs).equivFun.trans
        (@Matrix.toLinearEquiv' _ _ _ _ _ (Pm σ J bs) (Matrix.invertibleOfIsUnitDet _ hP)))
    | exact (bM bs).equivFun.prod ((bM bs).equivFun.trans
        (@Matrix.toLinearEquiv' _ _ _ _ _ (Pm σ J bs) (Matrix.invertibleOfIsUnitDet _ hP)))))

theorem eD_apply (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (bs : Module.Basis (Fin 2) F E) (b : GL (Fin n ⊕ Fin n) E)
    (hP : IsUnit (Pm (n := n) σ J bs).det) (w : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) :
    eD σ J bs b hP w = ((bM bs).equivFun (eQ b w).2, Pm σ J bs *ᵥ (bM bs).equivFun (eQ b w).1) := rfl

theorem eD_frame [FiniteDimensional F E] (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (bs : Module.Basis (Fin 2) F E)
    (b : GL (Fin n ⊕ Fin n) E) (hP : IsUnit (Pm (n := n) σ J bs).det) (Z X : Mx F E m n) :
    eD σ J bs b hP (Z * (incM F b.1.toCols₁)ᵀ + X * (incM F b.1.toCols₂)ᵀ) = (crdB bs X, fun k => Bf σ J Z (Ek bs k)) := by
  rw [eD_apply, eQ_frame]
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · exact bM_repr bs X k
  · show (Pm σ J bs *ᵥ (bM bs).equivFun Z) k = Bf σ J Z (Ek bs k)
    rw [Bf_eq_sum_left σ J bs Z (Ek bs k)]
    simp only [Matrix.mulVec, dotProduct, Module.Basis.equivFun_apply, bM_repr, Pm, Matrix.transpose_apply,
      Matrix.map_apply]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [Bf_Ek_Ek, mul_comm]

theorem eD_form [FiniteDimensional F E] (σ : E →ₐ[F] E) (J : Matrix (Fin m) (Fin m) E) (bs : Module.Basis (Fin 2) F E)
    (YJ : Matrix (Fin n) (Fin n) E) (b : GL (Fin n ⊕ Fin n) E) (ε : ℤˣ) (hb : b.1ᵀ * dbl YJ * b.1.map σ = jeps n ε)
    (u : ℤ) (hsym : ∀ X Z : Mx F E m n, Bf σ J X Z = (u : AF F) * Bf σ J Z X) (hεu : (ε : ℤ) * u = -1)
    (hP : IsUnit (Pm (n := n) σ J bs).det) (w w' : Matrix (Fin m) (Fin n ⊕ Fin n) (AE F E)) :
    symp (R := AF F) (cA σ) (-1) (incM F J) (dbl (incM F YJ)) w w' =
      (eD σ J bs b hP w).1 ⬝ᵥ (eD σ J bs b hP w').2 - (eD σ J bs b hP w').1 ⬝ᵥ (eD σ J bs b hP w).2 := by
  obtain ⟨⟨Z, X⟩, rfl⟩ := (eQ (m := m) b).symm.surjective w
  obtain ⟨⟨Z', X'⟩, rfl⟩ := (eQ (m := m) b).symm.surjective w'
  rw [eQ_symm_apply, eQ_symm_apply, symp_frame σ J YJ b ε hb, eD_frame, eD_frame]
  simp only [dotProduct]
  rw [← Bf_eq_sum_right σ J bs Z' X, ← Bf_eq_sum_right σ J bs Z X', hsym X Z']
  have h1 : ((ε : ℤ) : AF F) * (u : AF F) = -1 := by rw [← Int.cast_mul, hεu]; norm_num
  linear_combination (-(Bf σ J Z' X)) * h1

theorem sDarb : SDarb := by
  intro F E _ _ _ _ _ σ B bs m n A Y b ε r s hB hm hn hsg hb hε
  haveI : FiniteDimensional F E := Module.Finite.of_basis bs
  have hσ : ∀ a, σ (σ a) = a := by
    obtain ⟨-, -, -, h⟩ := hB.cm
    intro a
    let τ : E →+* ℂ := Classical.arbitrary _
    apply τ.injective
    rw [h, h, star_star]
  obtain ⟨u, hsym, hεu, hJ⟩ : ∃ u : ℤ, (∀ i j, σ (A.J j i) = (u : E) * A.J i j) ∧ (ε : ℤ) * u = -1 ∧ A.J.det ≠ 0 := by
    rcases hsg with ⟨hA, hY⟩ | ⟨hA, hY⟩
    · refine ⟨1, fun i j => by simp [hA.herm], ?_, GlobalTheory.ThetaRatPair.det_ne_of_sig B A.J hA.sig⟩
      rw [eps_eq hσ Y.J (-1) (fun i j => by simp [hY]) b ε hε hn]
      norm_num
    · refine ⟨-1, fun i j => by simp [hA.skew], ?_, GlobalTheory.ThetaRatPair.det_ne_of_sig' B A.J hA.sig⟩
      rw [eps_eq hσ Y.J 1 (fun i j => by simp [hY]) b ε hε hn]
      norm_num
  have hP := Pm_unit (n := n) σ hσ A.J hJ bs
  let dd : Darboux (symp (R := AF F) (cA σ) (-1) (incM F A.J) (dbl (incM F Y.J))) (Fin m × Fin n × Fin 2) :=
    ⟨eD σ A.J bs b hP, eD_form σ A.J bs Y.J b ε hε u (fun X Z => Bf_symm hσ A.J u hsym X Z) hεu hP⟩
  have hd : IsAdapted bs A Y b dd := fun Z X => eD_frame σ A.J bs b hP Z X
  refine ⟨dd, hd, fun x => ?_⟩
  obtain ⟨c, hc⟩ := e_rat bs A Y b dd hd x
  exact ⟨_, c, hc⟩

end PositivityTheory.SiegelWeilFormula.Ldexa
