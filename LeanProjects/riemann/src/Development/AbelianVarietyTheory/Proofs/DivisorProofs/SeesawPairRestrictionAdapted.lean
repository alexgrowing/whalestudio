import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.MixedCoord

open GlobalTheory.ThK.Adapt

def swapD {R S : Type} [CommRing R] [CommRing S] [Algebra R S] [Invertible (2 : R)] (c : S →ₐ[R] S) {α β : Type}
    [Fintype α] [Fintype β] {ξ : S} {JA : Matrix α α S} {JB : Matrix β β S} {κ : Type} [Fintype κ]
    (d : Darboux (symp c ξ JA JB) κ) : Darboux (symp c ξ JB JA) κ where
  e := (Matrix.transposeLinearEquiv β α R S).trans d.e
  form w w' := by
    have h := d.form wᵀ w'ᵀ
    refine Eq.trans ?_ h
    unfold symp hTens
    congr 2
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [Matrix.transpose_apply]
    ring

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem frame_mul {d d₁ : ℕ} {β : Type} (H : Plane E d d₁) (z : Matrix (Fin d₁) β (AE F E)) (u v : β → AE F E) :
    incM F (frame H) * Matrix.of (Sum.elim z ![u, v]) =
      incM F H.ι * z + Matrix.vecMulVec (incV F H.x) u + Matrix.vecMulVec (incV F H.y) v := by
  ext i j
  simp [frame, incM, incV, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.vecMulVec_apply, add_assoc]
  rfl

theorem incM_one {α : Type} [DecidableEq α] : incM F (1 : Matrix α α E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

set_option maxHeartbeats 800000 in

theorem exists_coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ (dd₁ : Darboux (symp (cA σ) (-1) (incM F W₁.J) (dbl (incM F X.J))) ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁))),
        (∀ x : Matrix (Fin d₁) (Fin n ⊕ Fin n) E, ∃ u v : (Fin n × Fin d₁) ⊕ (Fin n × Fin d₁) → F,
          dd₁.e (incM F x) = (fun i => algebraMap F (AF F) (u i), fun i => algebraMap F (AF F) (v i))) →
      ∃ (κa : Type) (_ : Fintype κa) (ε : (Fin n × Fin d) ⊕ (Fin n × Fin d) ≃ κa ⊕ ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁)))
        (C : Matrix κa (Fin n) E)
        (dN : Darboux (symp (cA σ) (-1) (incM F W.J) (dbl (incM F X.J))) ((Fin n × Fin d) ⊕ (Fin n × Fin d))),
        (∀ x : Matrix (Fin d) (Fin n ⊕ Fin n) E, ∃ u v : (Fin n × Fin d) ⊕ (Fin n × Fin d) → F,
          dN.e (incM F x) = (fun i => algebraMap F (AF F) (u i), fun i => algebraMap F (AF F) (v i))) ∧
        (∀ z : Fin n → E, (∀ k, ∑ j, Algebra.trace F E (C k j * z j) = 0) → z = 0) ∧
        (∀ z : Matrix (Fin d₁) (Fin n ⊕ Fin n) (AE F E),
          dN.e (incM F H'.ι * z) = (GlobalTheory.ThK.Adapt.glue ε 0 (dd₁.e z).1, GlobalTheory.ThK.Adapt.glue ε 0 (dd₁.e z).2)) ∧
        (∀ y : Fin n ⊕ Fin n → AE F E, ∃ q : κa → AF F,
          dN.e (Matrix.vecMulVec (incV F H'.x) y) = (0, GlobalTheory.ThK.Adapt.glue ε q 0)) ∧
        (∀ y : Fin n → AE F E, dN.e (Matrix.vecMulVec (incV F H'.y) (Sum.elim y y)) =
          (GlobalTheory.ThK.Adapt.glue ε (fun k => ∑ j, Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) (C k j) * y j)) 0, 0)) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H i₀ i₁ M₁ om₁ r₁ s₁ hH _ dd₁ hdd₁
  have hB := hP.base
  let ε : (Fin n × Fin d) ⊕ (Fin n × Fin d) ≃ ((Fin n ⊕ Fin n) × Fin 2) ⊕ ((Fin n × Fin d₁) ⊕ (Fin n × Fin d₁)) :=
    Fintype.equivOfCardEq (by simp [hH.rank]; ring)
  let β := Module.finBasisOfFinrankEq F E hB.cm.2.2.1
  let βA := Algebra.TensorProduct.basis (AF F) β
  have hβA : ∀ i, βA i = inclR (F := F) (AF F) (β i) := fun i => Algebra.TensorProduct.basis_apply _ _
  let Tr := Algebra.trace (AF F) (AE F E)
  obtain ⟨Q, hPQ, hQP, -⟩ := exists_frame_inv hH hP.skew.lat
  have hG := frame_gram (η := -1) hB hH (by ring) (fun i j => by rw [hP.skew.skew]; ring)
  let J' := dbl (incM F X.J)
  let J₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E := dbl X.J
  have hJ₀ : J' = incM F J₀ := by
    ext (i | i) (j | j) <;> simp [J', J₀, dbl, incM]
  have hJ' : ∀ i j, cA σ (J' j i) = 1 * J' i j := by
    rintro (i | i) (j | j) <;> simp [J', dbl, incM, GlobalTheory.VacIndic.cA_inclR, hP.herm.herm]
  let b : Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) → Fin n ⊕ Fin n → AE F E := fun z => (incM F Q * z) (.inr 1)
  let D : Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) → Fin n ⊕ Fin n → AE F E :=
    fun z j => -∑ l, J' j l * cA σ ((incM F Q * z) (.inr 0) l)
  let π : Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) → Matrix (Fin d₁) (Fin n ⊕ Fin n) (AE F E) :=
    fun z => (incM F Q * z).submatrix .inl id
  have hGA : (incM F (frame H))ᵀ * incM F W.J * (incM F (frame H)).map (cA σ) =
      Matrix.fromBlocks (incM F W₁.J) 0 0 !![0, 1; -1, 0] := by
    have h1 : (incM F (frame H)).map (cA σ) = incM F ((frame H).map σ) := by
      ext i j; simp [incM, GlobalTheory.VacIndic.cA_inclR]
    rw [h1, show (incM F (frame H))ᵀ = incM F (frame H)ᵀ from rfl, ← incM_mul, ← incM_mul, hG]
    ext (i | i) (j | j)
    · rfl
    · simp [incM]
    · simp [incM]
    · fin_cases i <;> fin_cases j <;> simp [incM]
  have hbD : ∀ z z', b z ⬝ᵥ D z' =
      -∑ j, ∑ l, (incM F Q * z) (.inr 1) j * J' j l * cA σ ((incM F Q * z') (.inr 0) l) := fun z z' => by
    simp only [b, D, dotProduct, mul_neg, Finset.sum_neg_distrib, Finset.mul_sum, mul_assoc]
  have hHt : ∀ z z', hTens (cA σ) (incM F W.J) J' z z' =
      b z ⬝ᵥ D z' - cA σ (b z' ⬝ᵥ D z) + hTens (cA σ) (incM F W₁.J) J' (π z) (π z') := fun z z' => by
    have h0 : ∀ z : Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E), incM F (frame H) * (incM F Q * z) *
        (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E))ᵀ = z := fun z => by
      rw [← Matrix.mul_assoc, ← incM_mul, hPQ, incM_one, Matrix.transpose_one, Matrix.mul_one, Matrix.one_mul]
    have h1 := hTens_mul (cA σ) (incM F W.J) J' (incM F (frame H)) 1 (incM F Q * z) (incM F Q * z')
    rw [h0, h0, hGA, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one,
      hTens_plane_left] at h1
    rw [h1, hbD, hbD, map_neg, conj_pair (cA σ) (cA_cA hB) hJ']
    ring
  let p : Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) → (Fin n ⊕ Fin n) × Fin 2 → AF F := fun z k => Tr (βA k.2 * b z k.1)
  let q : Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) → (Fin n ⊕ Fin n) × Fin 2 → AF F := fun z k => -βA.repr (D z k.1) k.2
  have hpq : ∀ z z', p z ⬝ᵥ q z' = -Tr (b z ⬝ᵥ D z') := fun z z' => by
    simp only [dotProduct, Fintype.sum_prod_type, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    conv_rhs => rw [← βA.sum_repr (D z' k), Finset.mul_sum, map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm (b z k)]
    simp only [p, q]
    ring
  have hTr : ∀ z, Tr (cA σ z) = Tr z := GlobalTheory.VacCocycle.trace_conj (cA σ) (cA_cA hB)
  have hb1 : ∀ z z', b (z + z') = b z + b z' := fun z z' => by funext j; simp [b, Matrix.mul_add]
  have hb2 : ∀ (c : AF F) z, b (c • z) = c • b z := fun c z => by funext j; simp [b, Matrix.mul_smul]
  have hD1 : ∀ z z', D (z + z') = D z + D z' := fun z z' => by
    funext j
    simp only [D, Matrix.mul_add, Matrix.add_apply, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, neg_add]
  have hD2 : ∀ (c : AF F) z, D (c • z) = c • D z := fun c z => by
    funext j; simp [D, Matrix.mul_smul, Finset.smul_sum]
  have hπ1 : ∀ z z', π (z + z') = π z + π z' := fun z z' => by ext i j; simp [π, Matrix.mul_add]
  have hπ2 : ∀ (c : AF F) z, π (c • z) = c • π z := fun c z => by ext i j; simp [π, Matrix.mul_smul]
  let Φ : Matrix (Fin d) (Fin n ⊕ Fin n) (AE F E) →ₗ[AF F]
      ((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) × ((Fin n × Fin d) ⊕ (Fin n × Fin d) → AF F) :=
    { toFun := fun z => (glue ε (p z) (dd₁.e (π z)).1, glue ε (q z) (dd₁.e (π z)).2)
      map_add' := fun z z' => by
        rw [Prod.mk_add_mk, glue_add, glue_add, hπ1, map_add]
        congr 2 <;> funext k <;>
          simp only [p, q, hb1, hD1, mul_add, Pi.add_apply, map_add, Finsupp.add_apply, neg_add]
      map_smul' := fun c z => by
        rw [Prod.smul_mk, glue_smul, glue_smul, hπ2, map_smul]
        congr 2 <;> funext k <;> simp [p, q, hb2, hD2] }
  have hΦ : ∀ z z', symp (R := AF F) (cA σ) (-1) (incM F W.J) J' z z' =
      (Φ z).1 ⬝ᵥ (Φ z').2 - (Φ z').1 ⬝ᵥ (Φ z).2 := fun z z' => by
    have h1 := dd₁.form (π z) (π z')
    show Tr _ = glue ε _ _ ⬝ᵥ glue ε _ _ - glue ε _ _ ⬝ᵥ glue ε _ _
    change Tr _ = _ at h1
    rw [glue_dot, glue_dot, hpq, hpq, hHt, mul_add, map_add, h1, neg_one_mul, map_neg, map_sub, hTr]
    ring
  let co₀ := GlobalTheory.DblSchr.dblD (cA σ) (swapD (cA σ) M.co)
  have hbij : Function.Bijective Φ := by
    have := (bijective_of_symp (Φ ∘ₗ co₀.e.symm.toLinearMap) fun u w => by
      have h1 := co₀.form (co₀.e.symm u) (co₀.e.symm w)
      rw [hΦ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h1
      exact h1).comp co₀.e.bijective
    convert this using 1
    funext z
    simp
  let co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F W.J) J') ((Fin n × Fin d) ⊕ (Fin n × Fin d)) :=
    ⟨LinearEquiv.ofBijective Φ hbij, hΦ⟩
  have hco : ∀ z, co.e z = (glue ε (p z) (dd₁.e (π z)).1, glue ε (q z) (dd₁.e (π z)).2) := fun z => rfl
  have hdec : ∀ (z : Matrix (Fin d₁) (Fin n ⊕ Fin n) (AE F E)) (u v : Fin n ⊕ Fin n → AE F E),
      incM F Q * (incM F H.ι * z + Matrix.vecMulVec (incV F H.x) u + Matrix.vecMulVec (incV F H.y) v) =
        Matrix.of (Sum.elim z ![u, v]) := fun z u v => by
    rw [← frame_mul, ← Matrix.mul_assoc, ← incM_mul, hQP, incM_one, Matrix.one_mul]
  have hval : ∀ (z : Matrix (Fin d₁) (Fin n ⊕ Fin n) (AE F E)) (u v : Fin n ⊕ Fin n → AE F E),
      co.e (incM F H.ι * z + Matrix.vecMulVec (incV F H.x) u + Matrix.vecMulVec (incV F H.y) v) =
        (glue ε (fun k => Tr (βA k.2 * v k.1)) (dd₁.e z).1,
          glue ε (fun k => -βA.repr (-∑ l, J' k.1 l * cA σ (u l)) k.2) (dd₁.e z).2) := fun z u v => by
    rw [hco]
    simp only [p, q, b, D, π, hdec]
    rfl
  have hv0 : ∀ u : Fin d → AE F E, Matrix.vecMulVec u (0 : Fin n ⊕ Fin n → AE F E) = 0 := fun u => by
    ext i j; simp [Matrix.vecMulVec_apply]
  refine ⟨(Fin n ⊕ Fin n) × Fin 2, inferInstance, ε, fun k j => if Sum.elim id id k.1 = j then β k.2 else 0, co,
    fun x => ?_, fun z hz => ?_, fun z => ?_, fun y => ?_, fun y => ?_⟩
  · obtain ⟨u, w, huw⟩ := hdd₁ ((Q * x).submatrix .inl id)
    have hx₁ : π (incM F x) = incM F ((Q * x).submatrix .inl id) := by
      simp only [π, ← incM_mul]; rfl
    refine ⟨glue ε (fun k => Algebra.trace F E (β k.2 * (Q * x) (.inr 1) k.1)) u,
      glue ε (fun k => -β.repr (-∑ l, J₀ k.1 l * σ ((Q * x) (.inr 0) l)) k.2) w, ?_⟩
    rw [hco, hx₁, huw, glue_map ε (algebraMap F (AF F)), glue_map ε (algebraMap F (AF F))]
    congr 2 <;> funext k
    · simp only [p, b, ← incM_mul]
      rw [← GlobalTheory.VacIndic.trace_inclR, map_mul (inclR (F := F) (AF F)), hβA]
      rfl
    · have h1 : D (incM F x) k.1 = inclR (F := F) (AF F) (-∑ l, J₀ k.1 l * σ ((Q * x) (.inr 0) l)) := by
        simp only [D, ← incM_mul, hJ₀]
        simp [incM, GlobalTheory.VacIndic.cA_inclR]
      simp only [q, h1]
      rw [map_neg (algebraMap F (AF F))]
      generalize (-∑ l, J₀ k.1 l * σ ((Q * x) (.inr 0) l)) = t
      show -βA.repr ((1 : AF F) ⊗ₜ[F] t) k.2 = _
      simp [βA, Algebra.TensorProduct.basis_repr_tmul]
  · funext j
    have h1 : ∀ i, Algebra.trace F E (β i * z j) = 0 := fun i => by
      have h2 := hz (.inl j, i)
      rw [Finset.sum_eq_single j (fun j' _ hj => by simp [Ne.symm hj]) (by simp)] at h2
      simpa using h2
    refine (traceForm_nondegenerate F E).1 (z j) fun t => ?_
    rw [← β.sum_repr t, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, Algebra.traceForm_apply, mul_comm, h1, smul_zero]
  · have := hval z 0 0
    rw [hv0, hv0] at this
    simp only [add_zero, Pi.zero_apply, mul_zero, map_zero, Finset.sum_const_zero, neg_zero,
      Finsupp.coe_zero] at this
    exact this
  · have := hval 0 y 0
    rw [hv0] at this
    simp only [add_zero, zero_add, Matrix.mul_zero, Pi.zero_apply, mul_zero, map_zero,
      Prod.fst_zero, Prod.snd_zero] at this
    exact ⟨_, this.trans (congrArg₂ Prod.mk (glue_zero ε) rfl)⟩
  · have := hval 0 0 (Sum.elim y y)
    rw [hv0] at this
    simp only [add_zero, zero_add, Matrix.mul_zero, Pi.zero_apply, mul_zero, map_zero,
      Prod.fst_zero, Prod.snd_zero, Finset.sum_const_zero, neg_zero, Finsupp.coe_zero] at this
    refine this.trans (congrArg₂ Prod.mk ?_ (glue_zero ε))
    show glue ε _ _ = glue ε _ _
    congr 1
    funext k
    rw [Finset.sum_eq_single (Sum.elim id id k.1) (fun j _ hj => by simp [Ne.symm hj]) (by simp), hβA]
    beta_reduce
    rw [if_pos rfl]
    rcases k with ⟨k | k, i⟩ <;> rfl

end GlobalTheory.MixedCoord

end
