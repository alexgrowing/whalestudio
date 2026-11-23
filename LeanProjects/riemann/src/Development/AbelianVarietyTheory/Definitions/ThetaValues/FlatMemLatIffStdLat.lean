import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ActEMemSpanOmega
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TiledBoundaries.ETSymmApply
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.InhabSt

namespace GlobalTheory.TensorLat

open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.GeometryOfNumbersTheory (stdLat)

noncomputable section

section Flat

variable {ι : Type} [Fintype ι] {n : ℕ}

def flat : (Fin n → EuclideanSpace ℂ ι) ≃L[ℂ] EuclideanSpace ℂ (Fin n × ι) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun v => WithLp.toLp 2 fun p => v p.1 p.2
      invFun := fun w k => WithLp.toLp 2 fun i => w (k, i)
      map_add' := fun v w => by ext p; simp
      map_smul' := fun c v => by ext p; simp
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

@[simp] theorem flat_apply (v : Fin n → EuclideanSpace ℂ ι) (p : Fin n × ι) :
    flat v p = v p.1 p.2 := rfl

@[simp] theorem flat_symm_apply (w : EuclideanSpace ℂ (Fin n × ι)) (k : Fin n) (i : ι) :
    (flat (n := n) (ι := ι)).symm w k i = w (k, i) := rfl

theorem Hf_flat (v w : Fin n → EuclideanSpace ℂ ι) : Hf (flat v) (flat w) = HC v w := by
  unfold Hf HC
  rw [Fintype.sum_prod_type]
  rfl

theorem HC_flat_symm (v w : EuclideanSpace ℂ (Fin n × ι)) :
    HC ((flat (n := n) (ι := ι)).symm v) (flat.symm w) = Hf v w := by
  rw [← Hf_flat, ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply]

theorem norm_sq_flat (v : Fin n → EuclideanSpace ℂ ι) : ‖flat v‖ ^ 2 = ∑ k, ‖v k‖ ^ 2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, flat_apply]

theorem HC_self_re (v : Fin n → EuclideanSpace ℂ ι) : (HC v v).re = ‖flat v‖ ^ 2 := by
  rw [← Hf_flat, ← real_inner_eq_Hf, real_inner_self_eq_norm_sq]

theorem flat_single [DecidableEq ι] (k : Fin n) (i : ι) (c : ℂ) :
    flat (Pi.single k (EuclideanSpace.single i c) : Fin n → EuclideanSpace ℂ ι) =
      EuclideanSpace.single (k, i) c := by
  ext ⟨k', i'⟩
  by_cases hk : k' = k
  · subst hk
    by_cases hi : i' = i
    · subst hi; simp
    · simp [hi]
  · simp [hk]

theorem HC_conj (v w : Fin n → EuclideanSpace ℂ ι) : HC w v = (starRingEnd ℂ) (HC v w) := by
  rw [← Hf_flat, ← Hf_flat, Hf_conj]

theorem Hf_sum_left {κ : Type*} (s : Finset κ) (v : κ → EuclideanSpace ℂ ι)
    (w : EuclideanSpace ℂ ι) : Hf (∑ j ∈ s, v j) w = ∑ j ∈ s, Hf (v j) w := by
  simp only [Hf, WithLp.ofLp_sum, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem Hf_sum_right {κ : Type*} (s : Finset κ) (v : EuclideanSpace ℂ ι)
    (w : κ → EuclideanSpace ℂ ι) : Hf v (∑ j ∈ s, w j) = ∑ j ∈ s, Hf v (w j) := by
  simp only [Hf, WithLp.ofLp_sum, Finset.sum_apply, map_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem HC_add_left (v v' w : Fin n → EuclideanSpace ℂ ι) :
    HC (v + v') w = HC v w + HC v' w := by
  simp [HC, Hf, add_mul, Finset.sum_add_distrib]

theorem HC_add_right (v w w' : Fin n → EuclideanSpace ℂ ι) :
    HC v (w + w') = HC v w + HC v w' := by
  simp [HC, Hf, mul_add, Finset.sum_add_distrib]

theorem HC_sum_left {κ : Type*} (s : Finset κ) (v : κ → Fin n → EuclideanSpace ℂ ι)
    (w : Fin n → EuclideanSpace ℂ ι) : HC (∑ j ∈ s, v j) w = ∑ j ∈ s, HC (v j) w := by
  simp only [← Hf_flat, map_sum, Hf_sum_left]

theorem HC_sum_right {κ : Type*} (s : Finset κ) (v : Fin n → EuclideanSpace ℂ ι)
    (w : κ → Fin n → EuclideanSpace ℂ ι) : HC v (∑ j ∈ s, w j) = ∑ j ∈ s, HC v (w j) := by
  simp only [← Hf_flat, map_sum, Hf_sum_right]

end Flat

variable {E : Type} [Field E] [NumberField E] {dim : (E →+* ℂ) → ℕ} {n : ℕ}

open Classical in

theorem flat_dir (l : Letter n dim) : flat (dir l) = EuclideanSpace.single l 1 := by
  have := flat_single (n := n) l.1 l.2 (1 : ℂ)
  unfold dir
  convert this

theorem flat_eq_eT (X : PT E) (v : Fin n → Vsp X.dim) : flat v = TiledBoundaries.eT X n v := rfl

theorem flat_symm_eq_eT_symm (X : PT E) (w : EuclideanSpace ℂ (Fin n × Idx X.dim)) :
    (flat (n := n) (ι := Idx X.dim)).symm w = (TiledBoundaries.eT X n).symm w := rfl

def actL : E →+* (Vsp dim →L[ℂ] Vsp dim) where
  toFun α := LinearMap.toContinuousLinearMap
    { toFun := actE α
      map_add' := actE_add_right α
      map_smul' := actE_smul_right α }
  map_one' := ContinuousLinearMap.ext actE_one
  map_mul' α β := ContinuousLinearMap.ext (actE_mul α β)
  map_zero' := ContinuousLinearMap.ext actE_zero_left
  map_add' α β := ContinuousLinearMap.ext (actE_add_left α β)

@[simp] theorem actL_apply (α : E) (v : Vsp dim) : actL α v = actE α v := rfl

theorem actE_coe (α : 𝓞 E) (v : Vsp dim) : actE (α : E) v = act α v := rfl

theorem actE_sum_left {κ : Type*} (s : Finset κ) (α : κ → E) (v : Vsp dim) :
    actE (∑ j ∈ s, α j) v = ∑ j ∈ s, actE (α j) v := by
  simp only [← actL_apply, map_sum, ContinuousLinearMap.sum_apply]

theorem actE_sum_right {κ : Type*} (s : Finset κ) (α : E) (v : κ → Vsp dim) :
    actE α (∑ j ∈ s, v j) = ∑ j ∈ s, actE α (v j) := by
  simp only [← actL_apply, map_sum]

theorem actE_neg_left (α : E) (v : Vsp dim) : actE (-α) v = -actE α v := by
  ext i; simp

theorem actE_neg_right (α : E) (v : Vsp dim) : actE α (-v) = -actE α v := by
  ext i; simp

theorem actE_comm (α β : E) (v : Vsp dim) : actE α (actE β v) = actE β (actE α v) := by
  rw [← actE_mul, ← actE_mul, mul_comm]

theorem actE_intCast (m : ℤ) (v : Vsp dim) : actE (m : E) v = m • v := by
  ext i; simp

theorem actE_natCast (m : ℕ) (v : Vsp dim) : actE (m : E) v = m • v := by
  ext i; simp

theorem actE_mem_of_isIntegral (X : PT E) {α : E} (hα : IsIntegral ℤ α) {x : Vsp X.dim}
    (hx : x ∈ X.L) : actE α x ∈ X.L :=
  X.stable ⟨α, hα⟩ x hx

def tens (x : Vsp dim) (v : Fin n → E) : Fin n → Vsp dim := fun k => actE (v k) x

@[simp] theorem tens_apply (x : Vsp dim) (v : Fin n → E) (k : Fin n) :
    tens x v k = actE (v k) x := rfl

theorem tens_add_left (x y : Vsp dim) (v : Fin n → E) : tens (x + y) v = tens x v + tens y v :=
  funext fun k => actE_add_right (v k) x y

theorem tens_add_right (x : Vsp dim) (v w : Fin n → E) : tens x (v + w) = tens x v + tens x w :=
  funext fun k => actE_add_left (v k) (w k) x

@[simp] theorem tens_zero_left (v : Fin n → E) : tens (0 : Vsp dim) v = 0 :=
  funext fun k => actE_zero_right (v k)

@[simp] theorem tens_zero_right (x : Vsp dim) : tens x (0 : Fin n → E) = 0 :=
  funext fun _ => actE_zero_left x

theorem tens_smul_left (c : ℂ) (x : Vsp dim) (v : Fin n → E) : tens (c • x) v = c • tens x v :=
  funext fun k => actE_smul_right (v k) c x

theorem tens_smul_right (α : E) (x : Vsp dim) (v : Fin n → E) :
    tens x (α • v) = tens (actE α x) v :=
  funext fun k => by simp only [tens_apply, Pi.smul_apply, smul_eq_mul, ← actE_mul, mul_comm]

theorem actE_tens (α : E) (x : Vsp dim) (v : Fin n → E) :
    (fun k => actE α (tens x v k)) = tens (actE α x) v :=
  funext fun k => actE_comm α (v k) x

theorem tens_sum_left {κ : Type*} (s : Finset κ) (x : κ → Vsp dim) (v : Fin n → E) :
    tens (∑ j ∈ s, x j) v = ∑ j ∈ s, tens (x j) v :=
  funext fun k => by simp only [tens_apply, Finset.sum_apply, actE_sum_right]

theorem tens_sum_right {κ : Type*} (s : Finset κ) (x : Vsp dim) (v : κ → Fin n → E) :
    tens x (∑ j ∈ s, v j) = ∑ j ∈ s, tens x (v j) :=
  funext fun k => by simp only [tens_apply, Finset.sum_apply, actE_sum_left]

theorem tens_single (x : Vsp dim) (k : Fin n) :
    tens x (Pi.single k (1 : E)) = Pi.single k x := by
  funext j
  by_cases h : j = k
  · subst h; simp [actE_one]
  · simp [h, actE_zero_left]

theorem sum_tens_single (γ : Fin n → Vsp dim) : ∑ k, tens (γ k) (Pi.single k (1 : E)) = γ := by
  simp only [tens_single, Finset.univ_sum_single]

def tensorEps (w₀ : 𝓞 E) (γ : Fin n → Vsp dim) : ℂ :=
  cexp (Real.pi * I * ((HC γ fun k => act w₀ (γ k)).im : ℂ))

theorem norm_tensorEps (w₀ : 𝓞 E) (γ : Fin n → Vsp dim) : ‖tensorEps w₀ γ‖ = 1 := by
  rw [tensorEps, Complex.norm_exp]
  simp

@[simp] theorem tensorEps_zero (w₀ : 𝓞 E) : tensorEps w₀ (0 : Fin n → Vsp dim) = 1 := by
  simp [tensorEps, HC, Hf]

theorem tensorEps_neg (w₀ : 𝓞 E) (γ : Fin n → Vsp dim) : tensorEps w₀ (-γ) = tensorEps w₀ γ := by
  simp [tensorEps, HC, Hf, act]

theorem tensorEps_of_int (w₀ : 𝓞 E) (γ : Fin n → Vsp dim) (m : ℤ)
    (h : (HC γ fun k => act w₀ (γ k)).im = m) : tensorEps w₀ γ = (-1) ^ m := by
  rw [tensorEps, h, mul_comm, Complex.ofReal_intCast, Complex.exp_int_mul, Complex.exp_pi_mul_I]

theorem tensorEps_eq_prod (w₀ : 𝓞 E) (γ : Fin n → Vsp dim) :
    tensorEps w₀ γ = ∏ k, cexp (Real.pi * I * ((Hf (γ k) (act w₀ (γ k))).im : ℂ)) := by
  rw [tensorEps, HC, Complex.im_sum, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]

theorem tensorEps_eq_prod_eps (X : PT E) (w₀ : 𝓞 E)
    (heps : ∀ x ∈ X.L, (X.eps x : ℝ) = Real.cos (Real.pi * (Hf x (act w₀ x)).im))
    {γ : Fin n → Vsp X.dim} (hγ : ∀ k, γ k ∈ X.L) :
    tensorEps w₀ γ = ∏ k, (X.eps (γ k) : ℂ) := by
  rw [tensorEps_eq_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  obtain ⟨m, hm⟩ := X.integral _ _ (hγ k) (X.stable w₀ _ (hγ k))
  have h1 := heps _ (hγ k)
  rw [hm, mul_comm, Real.cos_int_mul_pi] at h1
  have h2 : (X.eps (γ k) : ℂ) = (-1) ^ m := by simpa using congrArg (fun t : ℝ => (t : ℂ)) h1
  rw [hm, h2, mul_comm, Complex.ofReal_intCast, Complex.exp_int_mul, Complex.exp_pi_mul_I]

variable [IsCMField E]

theorem Hf_actE_cc (α : E) (v w : Vsp dim) : Hf (actE α v) w = Hf v (actE (cc α) w) :=
  Hf_actE α v w

theorem Hf_actE_cc' (α : E) (v w : Vsp dim) : Hf v (actE α w) = Hf (actE (cc α) v) w :=
  Hf_actE' α v w

theorem HC_actE (α : E) (γ γ' : Fin n → Vsp dim) :
    HC (fun k => actE α (γ k)) γ' = HC γ fun k => actE (cc α) (γ' k) :=
  Finset.sum_congr rfl fun k _ => Hf_actE_cc α (γ k) (γ' k)

def contr (γ : Fin n → Vsp dim) (w : Fin n → E) : Vsp dim := ∑ k, actE (cc (w k)) (γ k)

theorem contr_apply (γ : Fin n → Vsp dim) (w : Fin n → E) (i : Idx dim) :
    contr γ w i = ∑ k, (starRingEnd ℂ) (i.1 (w k)) * γ k i := by
  simp [contr, cc, IsCMField.complexEmbedding_complexConj]

theorem contr_add_left (γ γ' : Fin n → Vsp dim) (w : Fin n → E) :
    contr (γ + γ') w = contr γ w + contr γ' w := by
  simp only [contr, Pi.add_apply, actE_add_right, Finset.sum_add_distrib]

theorem contr_add_right (γ : Fin n → Vsp dim) (w w' : Fin n → E) :
    contr γ (w + w') = contr γ w + contr γ w' := by
  simp only [contr, cc, Pi.add_apply, map_add, actE_add_left, Finset.sum_add_distrib]

@[simp] theorem contr_zero_left (w : Fin n → E) : contr (0 : Fin n → Vsp dim) w = 0 := by
  simp [contr, actE_zero_right]

@[simp] theorem contr_zero_right (γ : Fin n → Vsp dim) : contr γ (0 : Fin n → E) = 0 := by
  simp [contr, cc, actE_zero_left]

theorem contr_smul_left (c : ℂ) (γ : Fin n → Vsp dim) (w : Fin n → E) :
    contr (c • γ) w = c • contr γ w := by
  simp only [contr, Pi.smul_apply, actE_smul_right, Finset.smul_sum]

theorem contr_zsmul_left (m : ℤ) (γ : Fin n → Vsp dim) (w : Fin n → E) :
    contr (m • γ) w = m • contr γ w := by
  simp only [contr, Pi.smul_apply, ← actL_apply, map_zsmul, Finset.smul_sum]

theorem contr_actE_left (α : E) (γ : Fin n → Vsp dim) (w : Fin n → E) :
    contr (fun k => actE α (γ k)) w = actE α (contr γ w) := by
  simp only [contr, actE_sum_right, actE_comm α]

theorem contr_smul_right (α : E) (γ : Fin n → Vsp dim) (w : Fin n → E) :
    contr γ (α • w) = actE (cc α) (contr γ w) := by
  simp only [contr, cc, Pi.smul_apply, smul_eq_mul, map_mul, actE_mul, actE_sum_right]

theorem contr_sum_left {κ : Type*} (s : Finset κ) (γ : κ → Fin n → Vsp dim) (w : Fin n → E) :
    contr (∑ j ∈ s, γ j) w = ∑ j ∈ s, contr (γ j) w := by
  simp only [contr, Finset.sum_apply, actE_sum_right]
  exact Finset.sum_comm

theorem contr_sum_right {κ : Type*} (s : Finset κ) (γ : Fin n → Vsp dim) (w : κ → Fin n → E) :
    contr γ (∑ j ∈ s, w j) = ∑ j ∈ s, contr γ (w j) := by
  simp only [contr, cc, Finset.sum_apply, map_sum, actE_sum_left]
  exact Finset.sum_comm

theorem contr_single' (γ : Fin n → Vsp dim) (k : Fin n) (α : E) :
    contr γ (Pi.single k α) = actE (cc α) (γ k) := by
  rw [contr, Finset.sum_eq_single k]
  · simp
  · intro j _ h
    simp [h, cc, actE_zero_left]
  · simp

@[simp] theorem contr_single (γ : Fin n → Vsp dim) (k : Fin n) :
    contr γ (Pi.single k (1 : E)) = γ k := by
  simp [contr_single', cc, actE_one]

theorem contr_tens (x : Vsp dim) (v w : Fin n → E) :
    contr (tens x v) w = actE (herm 1 v w) x := by
  have : herm 1 v w = ∑ k, cc (w k) * v k := by simp [herm, Matrix.one_apply, mul_comm]
  simp only [this, contr, tens_apply, actE_sum_left, actE_mul]

theorem HC_tens_right (γ : Fin n → Vsp dim) (x : Vsp dim) (w : Fin n → E) :
    HC γ (tens x w) = Hf (contr γ w) x := by
  simp only [HC, contr, tens_apply, Hf_sum_left, Hf_actE_cc']

theorem HC_tens_left (γ : Fin n → Vsp dim) (x : Vsp dim) (w : Fin n → E) :
    HC (tens x w) γ = Hf x (contr γ w) := by
  rw [HC_conj, HC_tens_right, ← Hf_conj]

theorem HC_tens_tens (x y : Vsp dim) (v w : Fin n → E) :
    HC (tens x v) (tens y w) = Hf (actE (herm 1 v w) x) y := by
  rw [HC_tens_right, contr_tens]

theorem eq_zero_of_contr_span {S : Set (Fin n → E)} (hS : Submodule.span E S = ⊤)
    {γ : Fin n → Vsp dim} (h : ∀ w ∈ S, contr γ w = 0) : γ = 0 := by
  have key : ∀ w ∈ Submodule.span E S, contr γ w = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw => exact h w hw
    | zero => simp
    | add a b _ _ ha hb => rw [contr_add_right, ha, hb, add_zero]
    | smul α a _ ha => rw [contr_smul_right, ha, actE_zero_right]
  funext k
  rw [← contr_single γ k]
  exact key _ (hS ▸ Submodule.mem_top)

def tensorLat (X : PT E) (Λ' : Submodule (𝓞 E) (Fin n → E)) : Submodule ℤ (Fin n → Vsp X.dim) where
  carrier := {γ | ∀ w ∈ Λ', contr γ w ∈ X.L}
  add_mem' := fun ha hb w hw => by
    rw [contr_add_left]; exact X.L.add_mem (ha w hw) (hb w hw)
  zero_mem' := fun w _ => by simp
  smul_mem' := fun m γ h w hw => by
    rw [contr_zsmul_left]; exact X.L.smul_mem m (h w hw)

variable {X : PT E} {Λ' : Submodule (𝓞 E) (Fin n → E)}

theorem mem_tensorLat {γ : Fin n → Vsp X.dim} :
    γ ∈ tensorLat X Λ' ↔ ∀ w ∈ Λ', contr γ w ∈ X.L := Iff.rfl

theorem tensorLat_anti {Λ₁ Λ₂ : Submodule (𝓞 E) (Fin n → E)} (h : Λ₁ ≤ Λ₂) :
    tensorLat X Λ₂ ≤ tensorLat X Λ₁ := fun _ hγ w hw => hγ w (h hw)

theorem act_mem_tensorLat (α : 𝓞 E) {γ : Fin n → Vsp X.dim} (hγ : γ ∈ tensorLat X Λ') :
    (fun k => act α (γ k)) ∈ tensorLat X Λ' := fun w hw => by
  have := X.stable α _ (hγ w hw)
  rwa [act_eq_actE, ← contr_actE_left] at this

theorem tens_mem_tensorLat {x : Vsp X.dim} (hx : x ∈ X.L) {v : Fin n → E}
    (hv : ∀ w ∈ Λ', IsIntegral ℤ (herm 1 v w)) : tens x v ∈ tensorLat X Λ' := fun w hw => by
  rw [contr_tens]
  exact actE_mem_of_isIntegral X (hv w hw) hx

theorem im_HC_tens_int {γ : Fin n → Vsp X.dim} (hγ : γ ∈ tensorLat X Λ') {x : Vsp X.dim}
    (hx : x ∈ X.L) {w : Fin n → E} (hw : w ∈ Λ') : ∃ m : ℤ, (HC γ (tens x w)).im = m := by
  rw [HC_tens_right]
  exact X.integral _ _ (hγ w hw) hx

theorem mem_tensorLat_span {S : Set (Fin n → E)} {γ : Fin n → Vsp X.dim} :
    γ ∈ tensorLat X (Submodule.span (𝓞 E) S) ↔ ∀ w ∈ S, contr γ w ∈ X.L := by
  refine ⟨fun h w hw => h w (Submodule.subset_span hw), fun h w hw => ?_⟩
  induction hw using Submodule.span_induction with
  | mem w hw => exact h w hw
  | zero => simp
  | add a b _ _ ha hb => rw [contr_add_right]; exact X.L.add_mem ha hb
  | smul α a _ ha =>
    have : α • a = (α : E) • a := rfl
    rw [this, contr_smul_right]
    exact actE_mem_of_isIntegral X
      (α.isIntegral_coe.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom) ha

omit [IsCMField E] in

theorem mem_stdLat {v : Fin n → E} : v ∈ stdLat E n ↔ ∀ k, IsIntegral ℤ (v k) := by
  rw [stdLat, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩ k
    have : (∑ j, c j • (Pi.single j 1 : Fin n → E)) k = (c k : E) := by
      simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def]
    rw [this]
    exact (c k).isIntegral_coe
  · intro h
    have hc : ∀ k, ∃ c : 𝓞 E, algebraMap (𝓞 E) E c = v k := fun k => ⟨⟨v k, h k⟩, rfl⟩
    choose c hc using hc
    refine ⟨c, ?_⟩
    funext k
    simp [Finset.sum_apply, Pi.single_apply, Algebra.smul_def, hc]

omit [IsCMField E] in

theorem stdLat_fg : (stdLat E n).FG := Submodule.fg_span (Set.finite_range _)

theorem mem_stdLat_iff_herm {v : Fin n → E} :
    v ∈ stdLat E n ↔ ∀ w ∈ stdLat E n, IsIntegral ℤ (herm 1 v w) := by
  have hh : ∀ w, herm 1 v w = ∑ k, v k * cc (w k) := fun w => by simp [herm, Matrix.one_apply]
  constructor
  · intro hv w hw
    rw [hh]
    exact IsIntegral.sum _ fun k _ => (mem_stdLat.1 hv k).mul
      ((mem_stdLat.1 hw k).map (IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom)
  · intro h
    refine mem_stdLat.2 fun k => ?_
    have := h (Pi.single k 1) (Submodule.subset_span ⟨k, rfl⟩)
    rw [hh, Finset.sum_eq_single k] at this
    · simpa [cc] using this
    · intro j _ hj
      simp [hj, cc]
    · simp

theorem mem_tensorLat_stdLat {γ : Fin n → Vsp X.dim} :
    γ ∈ tensorLat X (stdLat E n) ↔ ∀ k, γ k ∈ X.L := by
  simp [stdLat, mem_tensorLat_span]

omit [IsCMField E] in

theorem stdLat_eq_pi : stdLat E n = Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E) := by
  ext v
  simp only [mem_stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
  exact forall_congr' fun k =>
    ⟨fun h => ⟨⟨v k, h⟩, rfl⟩, fun ⟨c, hc⟩ => hc ▸ c.isIntegral_coe⟩

theorem mem_tensorLat_pi {γ : Fin n → Vsp X.dim} :
    γ ∈ tensorLat X (Submodule.pi Set.univ fun _ => (1 : Submodule (𝓞 E) E)) ↔
      ∀ k, γ k ∈ X.L := by
  rw [← stdLat_eq_pi, mem_tensorLat_stdLat]

theorem flat_mem_lat_iff_stdLat {γ : Fin n → Vsp X.dim} :
    flat γ ∈ lat (TiledBoundaries.bT X n) ↔ γ ∈ tensorLat X (stdLat E n) := by
  rw [mem_tensorLat_stdLat, flat_eq_eT, TiledBoundaries.mem_latT, LinearEquiv.symm_apply_apply]

example (α : E) (γ : Fin 1 → Vsp X.dim) :
    γ ∈ tensorLat X (Submodule.span (𝓞 E) {Pi.single 0 α}) ↔ actE (cc α) (γ 0) ∈ X.L := by
  simp [mem_tensorLat_span, contr_single']

example (α : E) (hα : cc α * α = 1) (x : Vsp X.dim) :
    tens x (Pi.single (0 : Fin 1) α) ∈ tensorLat X (Submodule.span (𝓞 E) {Pi.single 0 α}) ↔
      x ∈ X.L := by
  simp [mem_tensorLat_span, contr_single', ← actE_mul, hα, actE_one]

example (κ : E) (hκ : cc κ = -κ) (x : Vsp dim) :
    contr (tens x (Pi.single (0 : Fin 2) 1)) (Pi.single 0 κ) = -actE κ x := by
  simp [contr_single', hκ, actE_neg_left, actE_one]

omit [IsCMField E] in

example (w₀ : 𝓞 E) (l : Letter n dim) :
    tensorEps w₀ (dir l) = cexp (-(Real.pi * I * ((l.2.1 (w₀ : E)).im : ℂ))) := by
  classical
  rw [tensorEps, ← Hf_flat, flat_dir, Hf, Finset.sum_eq_single l]
  · simp [act, dir]
  · intro p _ hp
    simp [hp]
  · simp

end

end GlobalTheory.TensorLat
