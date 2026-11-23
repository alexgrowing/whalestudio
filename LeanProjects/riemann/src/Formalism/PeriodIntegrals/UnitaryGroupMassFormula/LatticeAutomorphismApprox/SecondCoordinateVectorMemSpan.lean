import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.LocDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.ValNatCastLtOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeAutomorphismApprox.GlueHoldsVar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.LocSplitChiOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FiniteAdelicComparison.AdelicLatticeToLocalLattices

noncomputable section

namespace PI.UnitaryGroupMassFormula.ScXuExists.BrA

open NumberField IsDedekindDomain Matrix PI.UnitaryGroupMassFormula.AdIndexEq PI.UnitaryGroupMassFormula.ScXuExists
open scoped TensorProduct
open Formalism.MainNotions.S PI.ScRefExists

theorem gp_int (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (ε : RV I v) (p1 : RV I v →+* KV I v)
    (hp : IsAdaptedFirstProjection I v ε p1) : ∀ x ∈ Formalism.UG.intOE I.E, p1 (inclV I v x) ∈ OV I v := by
  first
  | exact hp.2.2.2.1
  | exact hp.2.2.2

theorem gp_lin (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (ε : RV I v) (p1 : RV I v →+* KV I v)
    (hp : IsAdaptedFirstProjection I v ε p1) : ∀ c : KV I v, p1 (algebraMap (KV I v) (RV I v) c) = c := hp.1

def hl (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (X Y : Fin I.n → RV I v) : RV I v :=
  Formalism.UG.hform (sigV I v) (I.J.map (inclV I v)) X Y

theorem sig2 (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (r : RV I v) :
    sigV I v (sigV I v r) = r := by
  induction r using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [sigV, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply]
    rw [spl_sig_sig]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

theorem alg_eq (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (c : KV I v) :
    algebraMap (KV I v) (RV I v) c = c ⊗ₜ[I.F] (1 : I.E) := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

theorem sig_alg (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (c : KV I v) :
    sigV I v (algebraMap (KV I v) (RV I v) c) = algebraMap (KV I v) (RV I v) c := by
  rw [alg_eq]
  simp [sigV]

theorem hl_sub_left (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (X Y Z : Fin I.n → RV I v) :
    hl I v (X - Y) Z = hl I v X Z - hl I v Y Z := by
  simp only [hl, Formalism.UG.hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem hl_smul_left (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (c : RV I v) (X Z : Fin I.n → RV I v) :
    hl I v (c • X) Z = sigV I v c * hl I v X Z := by
  simp only [hl, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hl_swap (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (X Y : Fin I.n → RV I v) :
    hl I v Y X = sigV I v (hl I v X Y) := by
  have hJ := spl_herm_v I v
  have hJij : ∀ i j, sigV I v ((I.J.map (inclV I v)) j i) = (I.J.map (inclV I v)) i j := by
    intro i j
    have := congrFun (congrFun hJ i) j
    simpa [Formalism.UG.cT] using this
  simp only [hl, Formalism.UG.hform, map_sum, map_mul, sig2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJij j i]
  ring

theorem pr_vec (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (p1 : RV I v →+* KV I v)
    (X Y : Fin I.n → RV I v) :
    pr (Pm I v p1) (vec2 p1 X) (vec1 p1 Y) = p1 (hl I v X Y) := by
  simp only [pr, Pm, vec1, vec2, hl, Formalism.UG.hform, dotProduct, mulVec, map_sum, map_mul,
    Matrix.map_apply, RingHom.comp_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hl_ratV (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (l l' : Fin I.n → I.E) :
    hl I v (Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) l)
      (Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) l') =
      inclV I v (Formalism.UG.hform (starRingEnd I.E) I.J l l') := by
  have h1 : Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) l = fun i => inclV I v (l i) := rfl
  have h2 : Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) l' = fun i => inclV I v (l' i) := rfl
  rw [h1, h2]
  simp only [hl, Formalism.UG.hform, spl_sigV_inclV, Matrix.map_apply, map_sum, map_mul]

theorem psiV_hA (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (x y : VA I) :
    PI.FinKW.psiV I v (hA I x y) = hl I v (PI.FinKW.vecV I v x) (PI.FinKW.vecV I v y) := by
  simp only [hA, hl, Formalism.UG.hform, map_sum, map_mul, Matrix.map_apply, psiV_sigR, psiV_inclE,
    PI.FinKW.vecV]

theorem vecV_incl' (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (l : Fin I.n → I.E) :
    PI.FinKW.vecV I v (incl I l) = Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) l := by
  funext i
  simp only [PI.FinKW.vecV, incl, PI.FinKW.LocTo.psiV_inclE]
  rfl

theorem pr_rat (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (p1 : RV I v →+* KV I v) (x y : Fin I.n → I.E) :
    pr (Pm I v p1) (vec2 p1 (PI.FinKW.vecV I v (incl I x))) (vec1 p1 (PI.FinKW.vecV I v (incl I y))) =
      p1 (inclV I v (Formalism.UG.hform (starRingEnd I.E) I.J x y)) := by
  rw [pr_vec, vecV_incl', vecV_incl', hl_ratV]

theorem hformE_swap (I : AutInst) (x y : Fin I.n → I.E) :
    Formalism.UG.hform (starRingEnd I.E) I.J y x = starRingEnd I.E (Formalism.UG.hform (starRingEnd I.E) I.J x y) := by
  have hJij : ∀ i j, starRingEnd I.E (I.J j i) = I.J i j := by
    intro i j
    have := congrFun (congrFun I.J_herm i) j
    simpa [Formalism.UG.cT] using this
  simp only [Formalism.UG.hform, map_sum, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJij j i]
  ring

theorem first_coordinate_vector_smul (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (p1 : RV I v →+* KV I v)
    (hp : ∀ c : KV I v, p1 (algebraMap (KV I v) (RV I v) c) = c) (c : OV I v) (X : Fin I.n → RV I v) :
    vec1 p1 (c • X) = c • vec1 p1 X := by
  rw [PI.FinKW.LocTo.ov_smul_vec]
  funext i
  simp only [vec1, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [← alg_eq, hp]
  rfl

theorem second_coordinate_vector_smul (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (p1 : RV I v →+* KV I v)
    (hp : ∀ c : KV I v, p1 (algebraMap (KV I v) (RV I v) c) = c) (c : OV I v) (X : Fin I.n → RV I v) :
    vec2 p1 (c • X) = c • vec2 p1 X := by
  rw [PI.FinKW.LocTo.ov_smul_vec]
  funext i
  simp only [vec2, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [← alg_eq, sig_alg, hp]
  rfl

theorem first_coordinate_vector_add {I : AutInst} {v : HeightOneSpectrum (𝓞 I.F)} (p1 : RV I v →+* KV I v) (X Y : Fin I.n → RV I v) :
    vec1 p1 (X + Y) = vec1 p1 X + vec1 p1 Y := by
  funext i; simp [vec1]

theorem vec2_add {I : AutInst} {v : HeightOneSpectrum (𝓞 I.F)} (p1 : RV I v →+* KV I v) (X Y : Fin I.n → RV I v) :
    vec2 p1 (X + Y) = vec2 p1 X + vec2 p1 Y := by
  funext i; simp [vec2]

theorem first_coordinate_vector_zero {I : AutInst} {v : HeightOneSpectrum (𝓞 I.F)} (p1 : RV I v →+* KV I v) :
    vec1 p1 (0 : Fin I.n → RV I v) = 0 := by
  funext i; simp [vec1]

theorem second_coordinate_vector_zero {I : AutInst} {v : HeightOneSpectrum (𝓞 I.F)} (p1 : RV I v →+* KV I v) :
    vec2 p1 (0 : Fin I.n → RV I v) = 0 := by
  funext i; simp [vec2]

section PrSpan

variable {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ} (P : Matrix (Fin n) (Fin n) K)

theorem prA_add_left (β β' x : Fin n → K) : pr P (β + β') x = pr P β x + pr P β' x := by
  simp [pr, add_dotProduct]

theorem prA_smul_left (c : K) (β x : Fin n → K) : pr P (c • β) x = c * pr P β x := by
  simp [pr, smul_dotProduct]

theorem prA_add_right (β x y : Fin n → K) : pr P β (x + y) = pr P β x + pr P β y := by
  simp [pr, mulVec_add, dotProduct_add]

theorem prA_smul_right (c : K) (β x : Fin n → K) : pr P β (c • x) = c * pr P β x := by
  simp [pr, mulVec_smul, dotProduct_smul]

theorem pr_span_left {S : Set (Fin n → K)} {x : Fin n → K} (h : ∀ β ∈ S, pr P β x ∈ O) :
    ∀ β ∈ Submodule.span O S, pr P β x ∈ O := by
  intro β hβ
  induction hβ using Submodule.span_induction with
  | mem y hy => exact h y hy
  | zero => simp [pr]
  | add a b _ _ ha hb => rw [prA_add_left]; exact add_mem ha hb
  | smul c a _ ha =>
    have : c • a = (c : K) • a := rfl
    rw [this, prA_smul_left]
    exact mul_mem c.2 ha

theorem pr_span_right {S : Set (Fin n → K)} {β : Fin n → K} (h : ∀ x ∈ S, pr P β x ∈ O) :
    ∀ x ∈ Submodule.span O S, pr P β x ∈ O := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact h y hy
  | zero => simp [pr]
  | add a b _ _ ha hb => rw [prA_add_right]; exact add_mem ha hb
  | smul c a _ ha =>
    have : c • a = (c : K) • a := rfl
    rw [this, prA_smul_right]
    exact mul_mem c.2 ha

end PrSpan

theorem first_coordinate_vector_mem_span (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (p1 : RV I v →+* KV I v)
    (hp : ∀ c : KV I v, p1 (algebraMap (KV I v) (RV I v) c) = c) (X : Fin I.n → RV I v)
    (hX : X ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))) :
    vec1 p1 X ∈ Submodule.span (OV I v)
      ((fun l => vec1 p1 (Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) l)) '' (I.L : Set _)) := by
  induction hX using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact Submodule.subset_span ⟨l, hl, rfl⟩
  | zero => rw [first_coordinate_vector_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [first_coordinate_vector_add]; exact add_mem ha hb
  | smul c a _ ha => rw [first_coordinate_vector_smul I v p1 hp]; exact Submodule.smul_mem _ c ha

theorem second_coordinate_vector_mem_span (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (p1 : RV I v →+* KV I v)
    (hp : ∀ c : KV I v, p1 (algebraMap (KV I v) (RV I v) c) = c) (X : Fin I.n → RV I v)
    (hX : X ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))) :
    vec2 p1 X ∈ Submodule.span (OV I v)
      ((fun l => vec2 p1 (Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) l)) '' (I.L : Set _)) := by
  induction hX using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, rfl⟩ := hy
    exact Submodule.subset_span ⟨l, hl, rfl⟩
  | zero => rw [second_coordinate_vector_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [vec2_add]; exact add_mem ha hb
  | smul c a _ ha => rw [second_coordinate_vector_smul I v p1 hp]; exact Submodule.smul_mem _ c ha

theorem pr_int (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (ε : RV I v) (p1 : RV I v →+* KV I v)
    (hp : IsAdaptedFirstProjection I v ε p1) : ∀ β ∈ Lam2 I v p1, ∀ x ∈ Lam1 I v p1, pr (Pm I v p1) β x ∈ OV I v := by

  have h0 : ∀ l ∈ (I.L : Set (Fin I.n → I.E)), ∀ l' ∈ (I.L : Set (Fin I.n → I.E)),
      pr (Pm I v p1) (vec2 p1 (Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) l))
        (vec1 p1 (Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) l')) ∈ OV I v := by
    intro l hl l' hl'
    rw [pr_vec, hl_ratV]
    exact gp_int I v ε p1 hp _ ((I.L_dual l').1 hl' l hl)
  have h1 : ∀ β ∈ Submodule.span (OV I v)
      ((fun l => vec2 p1 (Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) l)) '' (I.L : Set _)),
      ∀ x ∈ Submodule.span (OV I v)
      ((fun l => vec1 p1 (Formalism.L2.SG.Sub.ratV (F := I.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v) l)) '' (I.L : Set _)),
      pr (Pm I v p1) β x ∈ OV I v := by
    intro β hβ x hx
    refine pr_span_left (OV I v) (Pm I v p1) (fun β' hβ' => ?_) β hβ
    obtain ⟨l, hl, rfl⟩ := hβ'
    refine pr_span_right (OV I v) (Pm I v p1) (fun x' hx' => ?_) x hx
    obtain ⟨l', hl', rfl⟩ := hx'
    exact h0 l hl l' hl'
  intro β hβ x hx
  refine pr_span_left (OV I v) (Pm I v p1) (fun β' hβ' => ?_) β hβ
  obtain ⟨X, hX, rfl⟩ := hβ'
  refine pr_span_right (OV I v) (Pm I v p1) (fun x' hx' => ?_) x hx
  obtain ⟨Y, hY, rfl⟩ := hx'
  exact h1 _ (second_coordinate_vector_mem_span I v p1 hp.1 X hX) _ (first_coordinate_vector_mem_span I v p1 hp.1 Y hY)

theorem hl_int (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (ε : RV I v) (p1 : RV I v →+* KV I v)
    (hp : IsAdaptedFirstProjection I v ε p1) (X Y : Fin I.n → RV I v)
    (hX : X ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E)))
    (hY : Y ∈ Formalism.L2.SG.Sub.latLoc v (I.L : Set (Fin I.n → I.E))) : p1 (hl I v X Y) ∈ OV I v := by
  rw [← pr_vec]
  exact pr_int I v ε p1 hp _ (Submodule.subset_span ⟨X, hX, rfl⟩) _ (Submodule.subset_span ⟨Y, hY, rfl⟩)

theorem conj_intOE (I : AutInst) (x : I.E) (hx : x ∈ Formalism.UG.intOE I.E) :
    starRingEnd I.E x ∈ Formalism.UG.intOE I.E := by
  obtain ⟨o, rfl⟩ := hx
  have h : IsIntegral ℤ (starRingEnd I.E (algebraMap (𝓞 I.E) I.E o)) :=
    (RingOfIntegers.isIntegral_coe o).map (starRingEnd I.E).toIntAlgHom
  exact ⟨⟨_, h⟩, rfl⟩

theorem adaptedProjection_psiV_mem_integers_of_mem_intAf (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (ε : RV I v) (p1 : RV I v →+* KV I v)
    (hp : IsAdaptedFirstProjection I v ε p1) (t : I.E ⊗[I.F] Af I.F) (ht : t ∈ IntAf I.F I.E) :
    p1 (PI.FinKW.psiV I v t) ∈ OV I v ∧ p1 (sigV I v (PI.FinKW.psiV I v t)) ∈ OV I v := by
  induction ht using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨y, rfl⟩ | ⟨y, rfl⟩
    · have e1 : PI.FinKW.psiV I v ((y : I.E) ⊗ₜ[I.F] (1 : Af I.F)) = inclV I v (y : I.E) :=
        psiV_inclE I v (y : I.E)
      rw [e1, spl_sigV_inclV]
      exact ⟨gp_int I v ε p1 hp _ y.2, gp_int I v ε p1 hp _ (conj_intOE I _ y.2)⟩
    · have e1 : PI.FinKW.psiV I v ((1 : I.E) ⊗ₜ[I.F] (y : Af I.F)) =
          algebraMap (KV I v) (RV I v) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v (y : Af I.F)) := by
        rw [PI.FinKW.LocTo.psiV_tmul, alg_eq]
      have hy : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV I.F v (y : Af I.F) ∈ OV I v := y.2 v
      rw [e1, sig_alg, hp.1]
      exact ⟨hy, hy⟩
  | zero => simp
  | one => simp
  | add a b _ _ ha hb => simp only [map_add]; exact ⟨add_mem ha.1 hb.1, add_mem ha.2 hb.2⟩
  | neg a _ ha => simp only [map_neg]; exact ⟨neg_mem ha.1, neg_mem ha.2⟩
  | mul a b _ _ ha hb => simp only [map_mul]; exact ⟨mul_mem ha.1 hb.1, mul_mem ha.2 hb.2⟩

end PI.UnitaryGroupMassFormula.ScXuExists.BrA

end
