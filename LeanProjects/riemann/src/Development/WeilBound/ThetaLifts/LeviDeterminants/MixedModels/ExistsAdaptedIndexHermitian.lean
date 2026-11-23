import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.PlaneC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxCoordinatesTensorHermitian

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace PositivityTheory.Mix

open Adapt

set_option maxHeartbeats 1000000 in
theorem exists_adapted_index_hermitian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₁ : Model σ X₁ W) (r₁ s₁ : ℕ), X₁.IsHerm σ B r₁ s₁ →
      H.IsAdapted σ B X X₁ j₀ j₁ → M₁.IsGood B.ψ →
      ∃ (j : Fin n₁ × Fin d → Fin n × Fin d) (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d)),
        Function.Injective j ∧
        (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
          co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) ∧
        (∀ z, co.e (incM F H.ι * z) = (Function.extend j (M₁.co.e z).1 0, Function.extend j (M₁.co.e z).2 0)) ∧
        (∀ z, (co.e (Matrix.vecMulVec (incV F H.x) z)).1 = 0 ∧ ∀ k, (co.e (Matrix.vecMulVec (incV F H.x) z)).2 (j k) = 0) ∧
        (∀ z, (co.e (Matrix.vecMulVec (incV F H.y) z)).2 = 0 ∧ ∀ k, (co.e (Matrix.vecMulVec (incV F H.y) z)).1 (j k) = 0)
:= by
  intro F E _ _ _ _ _ σ B n d X W r s r' s' hB hX hW n₁ X₁ H j₀ j₁ M₁ r₁ s₁ _ hH hM₁
  classical
  obtain ⟨c₀, -⟩ := GlobalTheory.RatDarboux.exists_rational_darboux_of_isGood B hB X W r s r' s' hX hW
  obtain ⟨Q, hPQ, hQP, -⟩ := exists_frame_inv hH hX.lat
  have hA : incM F Q * incM F (frame H) = 1 := by rw [← incM_mul, hQP, incM_one]
  have hA' : incM F (frame H) * incM F Q = 1 := by rw [← incM_mul, hPQ, incM_one]
  let b : Matrix (Fin n) (Fin d) (AE F E) → Fin d → AE F E := fun z => (incM F Q * z) (.inr 1)
  let D : Matrix (Fin n) (Fin d) (AE F E) → Fin d → AE F E := fun z k => ∑ l, incM F W.J k l * cA σ ((incM F Q * z) (.inr 0) l)
  let π : Matrix (Fin n) (Fin d) (AE F E) → Matrix (Fin n₁) (Fin d) (AE F E) := fun z => (incM F Q * z).submatrix .inl id
  have hG : (incM F (frame H))ᵀ * incM F X.J * (incM F (frame H)).map (cA σ) =
      Matrix.fromBlocks (incM F X₁.J) 0 0 !![0, 1; 1, 0] := by
    have h := congrArg (incM F) (frame_gram hB hH (η := 1) (one_mul 1) fun i j => by rw [one_mul]; exact hX.herm i j)
    rw [incM_mul, incM_mul] at h
    refine Eq.trans ?_ (h.trans ?_)
    · rfl
    · ext (i | i) (j | j)
      · rfl
      · simp [incM]
      · simp [incM]
      · fin_cases i <;> fin_cases j <;> simp [incM]
  have hH' : ∀ z z', hTens (cA σ) (incM F X.J) (incM F W.J) z z' =
      b z ⬝ᵥ D z' - cA σ (b z' ⬝ᵥ D z) + hTens (cA σ) (incM F X₁.J) (incM F W.J) (π z) (π z') := fun z z' => by
    have e : ∀ z : Matrix (Fin n) (Fin d) (AE F E), z = incM F (frame H) * (incM F Q * z) * (1 : Matrix (Fin d) (Fin d) (AE F E))ᵀ :=
      fun z => by rw [Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc, hA', Matrix.one_mul]
    conv_lhs => rw [e z, e z']
    rw [hTens_mul, hG, Matrix.transpose_one, Matrix.one_mul, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
      hTens_plane_left]
    have hc := conj_pair (cA σ) (cA_cA hB) (J := incM F W.J) (η := -1) (fun i j => by
      show cA σ (inclR (F := F) (AF F) _) = -1 * inclR (F := F) (AF F) _
      rw [GlobalTheory.VacIndic.cA_inclR, hW.skew, map_neg, neg_one_mul]) (b z') ((incM F Q * z) (.inr 0))
    have e1 : ∀ z z', b z ⬝ᵥ D z' = ∑ i, ∑ k, b z i * incM F W.J i k * cA σ ((incM F Q * z') (.inr 0) k) := fun z z' => by
      simp only [dotProduct, D, Finset.mul_sum, mul_assoc]
    rw [e1, e1, hc]
    simp only [b, π]
    ring
  let ε : Fin n × Fin d ≃ (Fin d × Fin 2) ⊕ Fin n₁ × Fin d := Fintype.equivOfCardEq (by simp [hH.rank]; ring)
  let β := Module.finBasisOfFinrankEq F E hB.cm.2.2.1
  let βA := Algebra.TensorProduct.basis (AF F) β
  let Tr := Algebra.trace (AF F) (AE F E)
  let p : Matrix (Fin n) (Fin d) (AE F E) → Fin d × Fin 2 → AF F := fun z k => βA.repr (b z k.1) k.2
  let q : Matrix (Fin n) (Fin d) (AE F E) → Fin d × Fin 2 → AF F := fun z k => -Tr (βA k.2 * D z k.1)
  have hpq : ∀ z z', p z ⬝ᵥ q z' = -Tr (b z ⬝ᵥ D z') := fun z z' => by
    simp only [dotProduct, Fintype.sum_prod_type, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    conv_rhs => rw [← βA.sum_repr (b z k), Finset.sum_mul, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, map_smul, smul_eq_mul, ← mul_neg]
  have hTr : ∀ z, Tr (cA σ z) = Tr z := GlobalTheory.VacCocycle.trace_conj (cA σ) (cA_cA hB)
  have hb : IsLinearMap (AF F) b := ⟨fun z z' => by simp only [b, Matrix.mul_add]; rfl, fun c z => by
    simp only [b, Matrix.mul_smul]; rfl⟩
  have hD : IsLinearMap (AF F) D := ⟨fun z z' => funext fun k => by
    simp [D, Matrix.mul_add, mul_add, Finset.sum_add_distrib], fun c z => funext fun k => by
    simp [D, Matrix.mul_smul, Finset.smul_sum]⟩
  have hπ : IsLinearMap (AF F) π := ⟨fun z z' => by simp only [π, Matrix.mul_add]; rfl, fun c z => by
    simp only [π, Matrix.mul_smul]; rfl⟩
  let Φ : Matrix (Fin n) (Fin d) (AE F E) →ₗ[AF F] (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
    { toFun := fun z => (glue ε (p z) (M₁.co.e (π z)).1, glue ε (q z) (M₁.co.e (π z)).2)
      map_add' := fun z z' => by
        rw [Prod.mk_add_mk, glue_add, glue_add, hπ.map_add, map_add]
        congr 2 <;> funext k <;> simp [p, q, hb.map_add, hD.map_add, mul_add, add_comm]
      map_smul' := fun c z => by
        rw [Prod.smul_mk, glue_smul, glue_smul, hπ.map_smul, map_smul]
        congr 2 <;> funext k <;> simp [p, q, hb.map_smul, hD.map_smul] }
  have hΦ : ∀ z z', symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) z z' =
      (Φ z).1 ⬝ᵥ (Φ z').2 - (Φ z').1 ⬝ᵥ (Φ z).2 := fun z z' => by
    have h1 := M₁.co.form (π z) (π z')
    show Tr _ = glue ε _ _ ⬝ᵥ glue ε _ _ - glue ε _ _ ⬝ᵥ glue ε _ _
    change Tr _ = _ at h1
    rw [glue_dot, glue_dot, hpq, hpq, hH', mul_add, map_add, h1, neg_one_mul, map_neg, map_sub, hTr]
    ring
  have hbij : Function.Bijective Φ := by
    have := (bijective_of_symp (Φ ∘ₗ c₀.e.symm.toLinearMap) fun u w => by
      have h1 := c₀.form (c₀.e.symm u) (c₀.e.symm w)
      rw [hΦ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
      exact h1).comp c₀.e.bijective
    convert this using 1
    funext z
    simp
  let co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d) :=
    ⟨LinearEquiv.ofBijective Φ hbij, hΦ⟩
  have hco : ∀ z, co.e z = (glue ε (p z) (M₁.co.e (π z)).1, glue ε (q z) (M₁.co.e (π z)).2) := fun z => rfl
  refine ⟨fun k => ε.symm (.inr k), co, ε.symm.injective.comp Sum.inr_injective, fun x => ?_, fun z => ?_, fun z => ?_, fun z => ?_⟩
  · obtain ⟨u, w, huw⟩ := hM₁.rat ((Q * x).submatrix .inl id)
    have hx₁ : π (incM F x) = incM F ((Q * x).submatrix .inl id) := by simp only [π, ← incM_mul]; rfl
    have hy : b (incM F x) = fun k => inclR (F := F) (AF F) ((Q * x) (.inr 1) k) := by simp only [b, ← incM_mul]; rfl
    have hy' : D (incM F x) = fun k => inclR (F := F) (AF F) (∑ l, W.J k l * σ ((Q * x) (.inr 0) l)) := by
      funext k
      simp only [D, ← incM_mul, map_sum, map_mul]
      rfl
    refine ⟨glue ε (fun k => β.repr ((Q * x) (.inr 1) k.1) k.2) u,
      glue ε (fun k => -Algebra.trace F E (β k.2 * ∑ l, W.J k.1 l * σ ((Q * x) (.inr 0) l))) w, ?_⟩
    rw [hco, hx₁, huw, glue_map ε (algebraMap F (AF F)), glue_map ε (algebraMap F (AF F))]
    congr 2 <;> funext k
    · simp only [p, hy]
      show βA.repr ((1 : AF F) ⊗ₜ[F] (Q * x) (.inr 1) k.1) k.2 = _
      simp [βA, Algebra.TensorProduct.basis_repr_tmul]
    · simp only [q, hy']
      rw [map_neg, ← GlobalTheory.VacIndic.trace_inclR, map_mul (inclR (F := F) (AF F)), Algebra.TensorProduct.basis_apply]
      rfl
  · have e := mul_iota hA z
    have h1 : p (incM F H.ι * z) = 0 := funext fun k => by simp [p, b, e]
    have h2 : q (incM F H.ι * z) = 0 := funext fun k => by simp [q, D, e]
    have h3 : π (incM F H.ι * z) = z := by simp only [π, e, rows_sub]
    rw [hco, h1, h2, h3, Adapt.extend_eq, Adapt.extend_eq]
  · have e := adapted_frame_mul_vecMulVec hA z
    have h1 : p (Matrix.vecMulVec (incV F H.x) z) = 0 := funext fun k => by simp [p, b, e]
    have h3 : π (Matrix.vecMulVec (incV F H.x) z) = 0 := by simp only [π, e, rows_sub]
    rw [hco, h1, h3, map_zero]
    exact ⟨glue_zero ε, fun k => glue_inr ε _ _ k⟩
  · have e := mul_y hA z
    have h1 : q (Matrix.vecMulVec (incV F H.y) z) = 0 := funext fun k => by simp [q, D, e]
    have h3 : π (Matrix.vecMulVec (incV F H.y) z) = 0 := by simp only [π, e, rows_sub]
    rw [hco, h1, h3, map_zero]
    exact ⟨glue_zero ε, fun k => glue_inr ε _ _ k⟩

end PositivityTheory.Mix
