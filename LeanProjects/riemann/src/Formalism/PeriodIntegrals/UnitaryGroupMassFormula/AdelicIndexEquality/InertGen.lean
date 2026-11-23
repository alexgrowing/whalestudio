import Formalism.SatakeDualWeyl.Statement

noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq.QRG

open Matrix Formalism.UG

variable {K : Type} [Field K] {n : ℕ}

def H (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) : K :=
  (σ ∘ x) ⬝ᵥ (J *ᵥ y)

section Form

variable (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K)

theorem H_add_right (x y z : Fin n → K) : H σ J x (y + z) = H σ J x y + H σ J x z := by
  simp [H, Matrix.mulVec_add, dotProduct_add]

theorem H_smul_right (x y : Fin n → K) (c : K) : H σ J x (c • y) = c * H σ J x y := by
  simp [H, Matrix.mulVec_smul, dotProduct_smul]

theorem H_neg_right (x y : Fin n → K) : H σ J x (-y) = - H σ J x y := by
  simp [H, Matrix.mulVec_neg, dotProduct_neg]

theorem H_sub_right (x y z : Fin n → K) : H σ J x (y - z) = H σ J x y - H σ J x z := by
  simp [H, Matrix.mulVec_sub, dotProduct_sub]

theorem comp_add' (x y : Fin n → K) : σ ∘ (x + y) = σ ∘ x + σ ∘ y := by
  funext i
  simp

theorem comp_smul' (c : K) (x : Fin n → K) : σ ∘ (c • x) = σ c • (σ ∘ x) := by
  funext i
  simp

theorem comp_neg' (x : Fin n → K) : σ ∘ (-x) = -(σ ∘ x) := by
  funext i
  simp

theorem H_add_left (x y z : Fin n → K) : H σ J (x + y) z = H σ J x z + H σ J y z := by
  unfold H
  rw [comp_add' σ, add_dotProduct]

theorem H_smul_left (x y : Fin n → K) (c : K) : H σ J (c • x) y = σ c * H σ J x y := by
  unfold H
  rw [comp_smul' σ, smul_dotProduct, smul_eq_mul]

theorem H_neg_left (x y : Fin n → K) : H σ J (-x) y = - H σ J x y := by
  unfold H
  rw [comp_neg' σ, neg_dotProduct]

theorem H_sub_left (x y z : Fin n → K) : H σ J (x - y) z = H σ J x z - H σ J y z := by
  rw [sub_eq_add_neg, H_add_left, H_neg_left, ← sub_eq_add_neg]

theorem H_zero_right (x : Fin n → K) : H σ J x 0 = 0 := by
  simp [H]

theorem H_sum_right {ι : Type} (s : Finset ι) (x : Fin n → K) (v : ι → Fin n → K) :
    H σ J x (∑ i ∈ s, v i) = ∑ i ∈ s, H σ J x (v i) := by
  simp [H, Matrix.mulVec_sum, dotProduct_sum]

theorem H_symm (hσ : ∀ a, σ (σ a) = a) (hJ : cT σ J = J) (x y : Fin n → K) :
    H σ J y x = σ (H σ J x y) := by
  have hJ' : ∀ i j, σ (J i j) = J j i := by
    intro i j
    have h := congrFun (congrFun hJ j) i
    simpa [cT] using h
  unfold H
  simp only [dotProduct, Matrix.mulVec, Function.comp_apply, map_sum, map_mul, hσ, hJ',
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

theorem H_mulVec (M : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    H σ J (M *ᵥ x) (M *ᵥ y) = H σ (cT σ M * J * M) x y := by
  have e1 : σ ∘ (M *ᵥ x) = (M.map σ) *ᵥ (σ ∘ x) := by
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum]
  unfold H
  rw [e1]
  conv_rhs => rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  simp only [cT, Matrix.vecMul_transpose]

theorem H_single (A : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    H σ A (Pi.single i 1) (Pi.single j 1) = A i j := by
  simp [H, dotProduct, Matrix.mulVec, Pi.single_apply, apply_ite σ]

theorem mem_UJ_of (g : GL (Fin n) K)
    (h : ∀ x y, H σ J ((g : Matrix (Fin n) (Fin n) K) *ᵥ x) ((g : Matrix (Fin n) (Fin n) K) *ᵥ y) =
      H σ J x y) : g ∈ UJ σ J := by
  show cT σ (g : Matrix (Fin n) (Fin n) K) * J * (g : Matrix (Fin n) (Fin n) K) = J
  ext i j
  have h1 := h (Pi.single i 1) (Pi.single j 1)
  rw [H_mulVec, H_single, H_single] at h1
  exact h1

theorem H_of_mem (g : GL (Fin n) K) (hg : g ∈ UJ σ J) (x y : Fin n → K) :
    H σ J ((g : Matrix (Fin n) (Fin n) K) *ᵥ x) ((g : Matrix (Fin n) (Fin n) K) *ᵥ y) = H σ J x y := by
  have hg' : cT σ (g : Matrix (Fin n) (Fin n) K) * J * (g : Matrix (Fin n) (Fin n) K) = J := hg
  rw [H_mulVec, hg']

theorem eq_zero_of_H (hdet : J.det ≠ 0) (w : Fin n → K) (h : ∀ z, H σ J w z = 0) : w = 0 := by
  have h1 : (σ ∘ w) ᵥ* J = 0 := by
    funext k
    have h2 := h (Pi.single k 1)
    rw [H, Matrix.dotProduct_mulVec, dotProduct_single, mul_one] at h2
    exact h2
  have h2 := Matrix.eq_zero_of_vecMul_eq_zero hdet h1
  funext i
  have h3 := congrFun h2 i
  simpa using h3

end Form

section Refl

variable (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K)

def Pm (a : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  (H σ J a a)⁻¹ • vecMulVec a ((σ ∘ a) ᵥ* J)

theorem Pm_mulVec (a z : Fin n → K) : Pm σ J a *ᵥ z = ((H σ J a a)⁻¹ * H σ J a z) • a := by
  have hb : ((σ ∘ a) ᵥ* J) ⬝ᵥ z = H σ J a z := by
    unfold H
    rw [Matrix.dotProduct_mulVec]
  funext k
  rw [← hb]
  simp only [Pm, Matrix.mulVec, dotProduct, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul,
    Pi.smul_apply, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun j _ => by ring)

theorem Pm_idem (a : Fin n → K) (ha : H σ J a a ≠ 0) : Pm σ J a * Pm σ J a = Pm σ J a := by
  have key : ∀ v, (Pm σ J a * Pm σ J a) *ᵥ v = Pm σ J a *ᵥ v := by
    intro v
    rw [← Matrix.mulVec_mulVec, Pm_mulVec σ J a v, Matrix.mulVec_smul, Pm_mulVec σ J a a,
      inv_mul_cancel₀ ha, one_smul]
  ext i j
  have h1 := congrFun (key (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using h1

def Rm (a : Fin n → K) (α : K) : Matrix (Fin n) (Fin n) K := 1 + (α - 1) • Pm σ J a

theorem Rm_mulVec (a z : Fin n → K) (α : K) :
    Rm σ J a α *ᵥ z = z + ((α - 1) * ((H σ J a a)⁻¹ * H σ J a z)) • a := by
  have e : ((α - 1) • Pm σ J a) *ᵥ z = (α - 1) • (Pm σ J a *ᵥ z) := by
    funext k
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [Rm, Matrix.add_mulVec, Matrix.one_mulVec, e, Pm_mulVec, smul_smul]

theorem one_add_smul_mul (P : Matrix (Fin n) (Fin n) K) (hP : P * P = P) (u w : K) :
    (1 + u • P) * (1 + w • P) = 1 + (u + w + u * w) • P := by
  simp only [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, hP, add_smul, mul_comm w u]
  abel

def Rgl (a : Fin n → K) (α : K) (hα : σ α * α = 1) (ha : H σ J a a ≠ 0) : GL (Fin n) K where
  val := Rm σ J a α
  inv := Rm σ J a (σ α)
  val_inv := by
    rw [Rm, Rm, one_add_smul_mul _ (Pm_idem σ J a ha)]
    have : α - 1 + (σ α - 1) + (α - 1) * (σ α - 1) = 0 := by linear_combination hα
    rw [this, zero_smul, add_zero]
  inv_val := by
    rw [Rm, Rm, one_add_smul_mul _ (Pm_idem σ J a ha)]
    have : σ α - 1 + (α - 1) + (σ α - 1) * (α - 1) = 0 := by linear_combination hα
    rw [this, zero_smul, add_zero]

theorem Rm_H (hσ : ∀ a, σ (σ a) = a) (hJ : cT σ J = J) (a : Fin n → K) (α : K) (hα : σ α * α = 1)
    (x y : Fin n → K) : H σ J (Rm σ J a α *ᵥ x) (Rm σ J a α *ᵥ y) = H σ J x y := by
  rw [Rm_mulVec, Rm_mulVec]
  by_cases hc : H σ J a a = 0
  · simp [hc]
  have hxa : H σ J x a = σ (H σ J a x) := H_symm σ J hσ hJ a x
  have hcs : σ (H σ J a a) = H σ J a a := (H_symm σ J hσ hJ a a).symm
  have hcc : (H σ J a a)⁻¹ * H σ J a a = 1 := inv_mul_cancel₀ hc
  rw [H_add_left, H_add_right, H_add_right, H_smul_left, H_smul_right, H_smul_right, H_smul_left, hxa]
  simp only [map_mul, map_sub, map_one, map_inv₀, hcs]
  linear_combination (σ (H σ J a x) * H σ J a y * (H σ J a a)⁻¹) * hα +
    ((σ α - 1) * (α - 1) * σ (H σ J a x) * H σ J a y * (H σ J a a)⁻¹) * hcc

theorem move (hσ : ∀ a, σ (σ a) = a) (hJ : cT σ J = J) (u y : Fin n → K)
    (huy : H σ J u u = H σ J y y) (ha : H σ J (u - y) (u - y) ≠ 0) :
    ∃ α : K, σ α * α = 1 ∧ Rm σ J (u - y) α *ᵥ u = y ∧
      ∀ z, H σ J (u - y) z = 0 → Rm σ J (u - y) α *ᵥ z = z := by
  have hD : H σ J (u - y) u = H σ J u u - H σ J y u := H_sub_left σ J u y u
  have hsD : σ (H σ J (u - y) u) = H σ J u u - H σ J u y := by
    rw [hD, map_sub, ← H_symm σ J hσ hJ u u, ← H_symm σ J hσ hJ y u]
  have hc : H σ J (u - y) (u - y) = H σ J (u - y) u + σ (H σ J (u - y) u) := by
    rw [hsD, hD, H_sub_right, H_sub_left, H_sub_left, huy]
    ring
  have hD0 : H σ J (u - y) u ≠ 0 := by
    intro h0
    apply ha
    rw [hc, h0, map_zero, add_zero]
  have hsD0 : σ (H σ J (u - y) u) ≠ 0 := (map_ne_zero σ).mpr hD0
  refine ⟨-(σ (H σ J (u - y) u)) / H σ J (u - y) u, ?_, ?_, ?_⟩
  · rw [map_div₀, map_neg, hσ]
    field_simp
  · rw [Rm_mulVec]
    have hcoef : (-(σ (H σ J (u - y) u)) / H σ J (u - y) u - 1) *
        ((H σ J (u - y) (u - y))⁻¹ * H σ J (u - y) u) = -1 := by
      rw [hc]
      have hsum : H σ J (u - y) u + σ (H σ J (u - y) u) ≠ 0 := by rw [← hc]; exact ha
      field_simp
      ring
    rw [hcoef, neg_one_smul]
    abel
  · intro z hz
    rw [Rm_mulVec, hz, mul_zero, mul_zero, zero_smul, add_zero]

end Refl

section Gen

variable (σ : K →+* K) (J : Matrix (Fin n) (Fin n) K)

def S : Subgroup (UJ σ J) :=
  Subgroup.closure {s : UJ σ J | ∃ (P : Matrix (Fin n) (Fin n) K) (α : K), P * P = P ∧ σ α * α = 1 ∧
    ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 + (α - 1) • P}

def gm (g : UJ σ J) : Matrix (Fin n) (Fin n) K := ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)

theorem gm_mul (g g' : UJ σ J) : gm σ J (g * g') = gm σ J g * gm σ J g' := rfl

theorem H_gm (g : UJ σ J) (x y : Fin n → K) : H σ J (gm σ J g *ᵥ x) (gm σ J g *ᵥ y) = H σ J x y := by exact H_of_mem σ J g.1 g.2 x y

def Rel (hσ : ∀ a, σ (σ a) = a) (hJ : cT σ J = J) (a : Fin n → K) (α : K) (hα : σ α * α = 1)
    (ha : H σ J a a ≠ 0) : UJ σ J :=
  ⟨Rgl σ J a α hα ha, mem_UJ_of σ J _ (fun x y => Rm_H σ J hσ hJ a α hα x y)⟩

theorem gm_Rel (hσ : ∀ a, σ (σ a) = a) (hJ : cT σ J = J) (a : Fin n → K) (α : K) (hα : σ α * α = 1)
    (ha : H σ J a a ≠ 0) : gm σ J (Rel σ J hσ hJ a α hα ha) = Rm σ J a α := rfl

theorem Rel_mem (hσ : ∀ a, σ (σ a) = a) (hJ : cT σ J = J) (a : Fin n → K) (α : K) (hα : σ α * α = 1)
    (ha : H σ J a a ≠ 0) : Rel σ J hσ hJ a α hα ha ∈ S σ J := by exact Subgroup.subset_closure ⟨Pm σ J a, α, Pm_idem σ J a ha, hα, rfl⟩

theorem card_le {m : ℕ} (f : Fin m → Fin n → K)
    (hf : ∀ i, H σ J (f i) (f i) ≠ 0) (ho : ∀ i j, i ≠ j → H σ J (f i) (f j) = 0) : m ≤ n := by
  have hli : LinearIndependent K f := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h1 := congrArg (H σ J (f j)) hg
    rw [H_sum_right, H_zero_right] at h1
    simp_rw [H_smul_right] at h1
    rw [Finset.sum_eq_single j (fun i _ hij => by rw [ho j i (Ne.symm hij), mul_zero]) (by simp)] at h1
    exact (mul_eq_zero.mp h1).resolve_right (hf j)
  have h2 := hli.fintype_card_le_finrank
  simpa using h2

theorem main (hσ : ∀ a, σ (σ a) = a) (hJ : cT σ J = J) (hdet : J.det ≠ 0) (h2 : (2 : K) ≠ 0)
    (d : ℕ) : ∀ (k : ℕ) (e : Fin k → Fin n → K), n - k = d → (∀ i, H σ J (e i) (e i) ≠ 0) →
      (∀ i j, i ≠ j → H σ J (e i) (e j) = 0) →
      ∀ g : UJ σ J, (∀ i, gm σ J g *ᵥ e i = e i) → g ∈ S σ J := by
  classical
  have hHsymm := H_symm σ J hσ hJ
  have horth_rev : ∀ x v, H σ J x v = 0 → H σ J v x = 0 := by
    intro x v h
    rw [hHsymm x v, h, map_zero]
  have hlin : ∀ {m : ℕ} (f : Fin m → Fin n → K), (∀ i, H σ J (f i) (f i) ≠ 0) →
      (∀ i j, i ≠ j → H σ J (f i) (f j) = 0) → LinearIndependent K f := by
    intro m f hf ho
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h1 := congrArg (H σ J (f j)) hc
    rw [H_sum_right, H_zero_right] at h1
    simp_rw [H_smul_right] at h1
    rw [Finset.sum_eq_single j (fun i _ hij => by rw [ho j i (Ne.symm hij), mul_zero]) (by simp)] at h1
    exact (mul_eq_zero.mp h1).resolve_right (hf j)
  have fixS : ∀ g : UJ σ J, gm σ J g = 1 → g ∈ S σ J := by
    intro g hg
    have h1 : g = 1 := Subtype.ext (Units.ext hg)
    rw [h1]
    exact (S σ J).one_mem
  have gm_eq_one : ∀ g : UJ σ J, (∀ v, gm σ J g *ᵥ v = v) → gm σ J g = 1 := by
    intro g hv
    ext i j
    have h1 := congrFun (hv (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one] at h1
    simpa [Matrix.one_apply, Pi.single_apply] using h1
  have proj : ∀ {k : ℕ} (e : Fin k → Fin n → K), (∀ i, H σ J (e i) (e i) ≠ 0) →
      (∀ i j, i ≠ j → H σ J (e i) (e j) = 0) →
      ∀ z, ∃ v, (∀ i, H σ J (e i) v = 0) ∧ z - v ∈ Submodule.span K (Set.range e) := by
    intro k e he ho z
    refine ⟨z - ∑ i, ((H σ J (e i) (e i))⁻¹ * H σ J (e i) z) • e i, ?_, ?_⟩
    · intro j
      rw [H_sub_right, H_sum_right]
      simp_rw [H_smul_right]
      rw [Finset.sum_eq_single j (fun i _ hij => by rw [ho j i (Ne.symm hij), mul_zero]) (by simp)]
      rw [mul_comm ((H σ J (e j) (e j))⁻¹), mul_assoc, inv_mul_cancel₀ (he j), mul_one, sub_self]
    · rw [sub_sub_cancel]
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
  have aniso : ∀ {k : ℕ} (e : Fin k → Fin n → K), k < n → (∀ i, H σ J (e i) (e i) ≠ 0) →
      (∀ i j, i ≠ j → H σ J (e i) (e j) = 0) →
      ∃ w, (∀ i, H σ J (e i) w = 0) ∧ H σ J w w ≠ 0 := by
    intro k e hk he ho
    have hspan : Submodule.span K (Set.range e) ≠ ⊤ := by
      intro htop
      have h1 := finrank_range_le_card (R := K) e
      unfold Set.finrank at h1
      rw [htop, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at h1
      omega
    obtain ⟨z, hz⟩ : ∃ z, z ∉ Submodule.span K (Set.range e) := by
      by_contra hall
      push_neg at hall
      exact hspan (eq_top_iff.mpr (fun z _ => hall z))
    obtain ⟨v, hvW, hzv⟩ := proj e he ho z
    have hv0 : v ≠ 0 := by
      rintro rfl
      rw [sub_zero] at hzv
      exact hz hzv
    obtain ⟨z2, hz2⟩ : ∃ z2, H σ J v z2 ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hv0 (eq_zero_of_H σ J hdet v hall)
    obtain ⟨v2, hv2W, hzv2⟩ := proj e he ho z2
    have hvspan : ∀ x ∈ Submodule.span K (Set.range e), H σ J v x = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact horth_rev _ _ (hvW i)
      | zero => exact H_zero_right σ J v
      | add x y _ _ hx hy => rw [H_add_right, hx, hy, add_zero]
      | smul c x _ hx => rw [H_smul_right, hx, mul_zero]
    have hvv2 : H σ J v v2 ≠ 0 := by
      intro h0
      apply hz2
      have e1 : z2 = v2 + (z2 - v2) := by abel
      rw [e1, H_add_right, h0, hvspan _ hzv2, add_zero]
    by_cases h1 : H σ J v v = 0
    · by_cases h2' : H σ J v2 v2 = 0
      · refine ⟨v + σ (H σ J v v2) • v2, ?_, ?_⟩
        · intro i
          rw [H_add_right, H_smul_right, hvW i, hv2W i, mul_zero, add_zero]
        · have hsb : σ (H σ J v v2) ≠ 0 := (map_ne_zero σ).mpr hvv2
          intro h0
          rw [H_add_left, H_add_right, H_add_right, H_smul_left, H_smul_right, H_smul_right,
            H_smul_left, h1, h2', hσ, hHsymm v v2] at h0
          exact mul_ne_zero h2 (mul_ne_zero hvv2 hsb) (by linear_combination h0)
      · exact ⟨v2, hv2W, h2'⟩
    · exact ⟨v, hvW, h1⟩
  induction d with
  | zero =>
    intro k e hnk he ho g hg
    have hkn : k ≤ n := card_le σ J e he ho
    have hk : k = n := by omega
    apply fixS
    apply gm_eq_one
    have hli := hlin e he ho
    have h3 : Module.finrank K (Submodule.span K (Set.range e)) = n := by
      have h4 := linearIndependent_iff_card_eq_finrank_span.mp hli
      unfold Set.finrank at h4
      rw [Fintype.card_fin] at h4
      exact h4.symm.trans hk
    have hspan : Submodule.span K (Set.range e) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [h3, Module.finrank_fin_fun])
    intro v
    have hv : v ∈ Submodule.span K (Set.range e) := by rw [hspan]; exact Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hg i
    | zero => exact Matrix.mulVec_zero _
    | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy]
    | smul c x _ hx => rw [Matrix.mulVec_smul, hx]
  | succ d ih =>
    intro k e hnk he ho g hg
    obtain ⟨w, hwe, hww⟩ := aniso e (by omega) he ho
    have he'a : ∀ i, H σ J ((Fin.snoc e w : Fin (k + 1) → Fin n → K) i)
        ((Fin.snoc e w : Fin (k + 1) → Fin n → K) i) ≠ 0 := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hww
      · simpa using he j
    have he'o : ∀ i j, i ≠ j → H σ J ((Fin.snoc e w : Fin (k + 1) → Fin n → K) i)
        ((Fin.snoc e w : Fin (k + 1) → Fin n → K) j) = 0 := by
      intro i j
      refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j
      · intro hij
        exact absurd rfl hij
      · intro _
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        exact horth_rev _ _ (hwe j')
      · intro _
        simp only [Fin.snoc_last, Fin.snoc_castSucc]
        exact hwe i'
      · intro hij
        simp only [Fin.snoc_castSucc]
        exact ho i' j' (fun h => hij (by rw [h]))
    have hnk' : n - (k + 1) = d := by omega
    have key : ∀ g' : UJ σ J, (∀ i, gm σ J g' *ᵥ e i = e i) → gm σ J g' *ᵥ w = w → g' ∈ S σ J := by
      intro g' hg'e hg'w
      apply ih (k + 1) (Fin.snoc e w) hnk' he'a he'o g'
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hg'w
      · simpa using hg'e j
    have huu : H σ J (gm σ J g *ᵥ w) (gm σ J g *ᵥ w) = H σ J w w := H_gm σ J g w w
    have hue : ∀ i, H σ J (gm σ J g *ᵥ w) (e i) = 0 := by
      intro i
      calc H σ J (gm σ J g *ᵥ w) (e i) = H σ J (gm σ J g *ᵥ w) (gm σ J g *ᵥ e i) := by rw [hg i]
        _ = H σ J w (e i) := H_gm σ J g w (e i)
        _ = 0 := horth_rev _ _ (hwe i)
    by_cases hA : H σ J (gm σ J g *ᵥ w - w) (gm σ J g *ᵥ w - w) = 0
    · have hpw : H σ J (gm σ J g *ᵥ w - -w) (gm σ J g *ᵥ w - -w) ≠ 0 := by
        rw [sub_neg_eq_add]
        intro h0
        apply mul_ne_zero (mul_ne_zero h2 h2) hww
        have e1 : H σ J (gm σ J g *ᵥ w + w) (gm σ J g *ᵥ w + w) +
            H σ J (gm σ J g *ᵥ w - w) (gm σ J g *ᵥ w - w) =
            2 * H σ J (gm σ J g *ᵥ w) (gm σ J g *ᵥ w) + 2 * H σ J w w := by
          rw [H_add_left, H_add_right, H_add_right, H_sub_left, H_sub_right, H_sub_right]
          ring
        rw [huu, h0, hA] at e1
        linear_combination -e1
      obtain ⟨α, hα, hαu, hαfix⟩ := move σ J hσ hJ (gm σ J g *ᵥ w) (-w)
        (by rw [H_neg_left, H_neg_right, neg_neg, huu]) hpw
      have hR1 := Rel_mem σ J hσ hJ _ α hα hpw
      have hm1 : σ (-1) * (-1 : K) = 1 := by simp
      have hR2 := Rel_mem σ J hσ hJ w (-1) hm1 hww
      have hR2w : Rm σ J w (-1) *ᵥ (-w) = w := by
        rw [Rm_mulVec, H_neg_right, mul_neg, inv_mul_cancel₀ hww,
          show ((-1 : K) - 1) * -1 = 2 by ring, two_smul]
        abel
      have hR2e : ∀ i, Rm σ J w (-1) *ᵥ e i = e i := by
        intro i
        rw [Rm_mulVec, horth_rev _ _ (hwe i), mul_zero, mul_zero, zero_smul, add_zero]
      have hR1e : ∀ i, Rm σ J (gm σ J g *ᵥ w - -w) α *ᵥ e i = e i := fun i =>
        hαfix (e i) (by rw [H_sub_left, H_neg_left, hue i, horth_rev _ _ (hwe i), neg_zero, sub_zero])
      have hTS : (Rel σ J hσ hJ w (-1) hm1 hww * Rel σ J hσ hJ _ α hα hpw) * g ∈ S σ J := by
        apply key
        · intro i
          rw [gm_mul, gm_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg i, gm_Rel, gm_Rel,
            hR1e, hR2e]
        · rw [gm_mul, gm_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, gm_Rel, gm_Rel, hαu, hR2w]
      have e2 : g = (Rel σ J hσ hJ w (-1) hm1 hww * Rel σ J hσ hJ _ α hα hpw)⁻¹ *
          ((Rel σ J hσ hJ w (-1) hm1 hww * Rel σ J hσ hJ _ α hα hpw) * g) := by group
      rw [e2]
      exact (S σ J).mul_mem ((S σ J).inv_mem ((S σ J).mul_mem hR2 hR1)) hTS
    · obtain ⟨α, hα, hαu, hαfix⟩ := move σ J hσ hJ (gm σ J g *ᵥ w) w huu hA
      have hR := Rel_mem σ J hσ hJ _ α hα hA
      have hR1e : ∀ i, Rm σ J (gm σ J g *ᵥ w - w) α *ᵥ e i = e i := fun i =>
        hαfix (e i) (by rw [H_sub_left, hue i, horth_rev _ _ (hwe i), sub_zero])
      have hTS : Rel σ J hσ hJ _ α hα hA * g ∈ S σ J := by
        apply key
        · intro i
          rw [gm_mul, ← Matrix.mulVec_mulVec, hg i, gm_Rel, hR1e]
        · rw [gm_mul, ← Matrix.mulVec_mulVec, gm_Rel, hαu]
      have e2 : g = (Rel σ J hσ hJ _ α hα hA)⁻¹ * (Rel σ J hσ hJ _ α hα hA * g) := by group
      rw [e2]
      exact (S σ J).mul_mem ((S σ J).inv_mem hR) hTS

theorem mem_S (hσ : ∀ a, σ (σ a) = a) (hJ : cT σ J = J) (hdet : J.det ≠ 0) (h2 : (2 : K) ≠ 0)
    (g : UJ σ J) : g ∈ S σ J := by exact main σ J hσ hJ hdet h2 n 0 Fin.elim0 (by simp) (fun i => i.elim0) (fun i => i.elim0) g (fun i => i.elim0)

end Gen

end PI.UnitaryGroupMassFormula.AdIndexEq.QRG

end
