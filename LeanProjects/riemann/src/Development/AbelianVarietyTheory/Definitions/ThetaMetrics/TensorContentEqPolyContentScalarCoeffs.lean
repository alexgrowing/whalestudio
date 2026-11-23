import Mathlib

namespace GlobalTheory

noncomputable section

open scoped NNReal TensorProduct

section CoeffSup

variable {ι M Γ₀ : Type*} [Zero M] [LinearOrderedCommMonoidWithZero Γ₀]

def coeffSup (N : M → Γ₀) (c : ι →₀ M) : Γ₀ := c.support.sup fun i => N (c i)

variable {N : M → Γ₀}

@[simp] theorem coeffSup_zero : coeffSup N (0 : ι →₀ M) = 0 := by
  simp [coeffSup, bot_eq_zero]

theorem coeffSup_le_iff (h0 : N 0 = 0) {c : ι →₀ M} {γ : Γ₀} :
    coeffSup N c ≤ γ ↔ ∀ i, N (c i) ≤ γ := by
  rw [coeffSup, Finset.sup_le_iff]
  refine ⟨fun h i => ?_, fun h i _ => h i⟩
  by_cases hi : i ∈ c.support
  · exact h i hi
  · rw [Finsupp.notMem_support_iff.mp hi, h0]; exact zero_le

theorem coeffSup_lt_iff (h0 : N 0 = 0) {c : ι →₀ M} {γ : Γ₀} (hγ : γ ≠ 0) :
    coeffSup N c < γ ↔ ∀ i, N (c i) < γ := by
  have hγ' : (⊥ : Γ₀) < γ := by rw [bot_eq_zero]; exact zero_lt_iff.mpr hγ
  rw [coeffSup, Finset.sup_lt_iff hγ']
  refine ⟨fun h i => ?_, fun h i _ => h i⟩
  by_cases hi : i ∈ c.support
  · exact h i hi
  · rw [Finsupp.notMem_support_iff.mp hi, h0]; exact zero_lt_iff.mpr hγ

theorem le_coeffSup (h0 : N 0 = 0) (c : ι →₀ M) (i : ι) : N (c i) ≤ coeffSup N c :=
  (coeffSup_le_iff h0).mp le_rfl i

theorem exists_mem_support_coeffSup_eq {c : ι →₀ M} (hc : c ≠ 0) :
    ∃ i ∈ c.support, coeffSup N c = N (c i) :=
  Finset.exists_mem_eq_sup _ (Finsupp.support_nonempty_iff.mpr hc) _

theorem exists_coeffSup_eq [Nonempty ι] (h0 : N 0 = 0) (c : ι →₀ M) :
    ∃ i, coeffSup N c = N (c i) := by
  by_cases hc : c = 0
  · exact ⟨Classical.arbitrary ι, by simp [hc, h0]⟩
  · obtain ⟨i, -, hi⟩ := exists_mem_support_coeffSup_eq (N := N) hc
    exact ⟨i, hi⟩

theorem coeffSup_eq_zero_iff (h0 : N 0 = 0) {c : ι →₀ M} :
    coeffSup N c = 0 ↔ ∀ i, N (c i) = 0 := by
  simp only [← le_zero_iff, coeffSup_le_iff h0]

theorem coeffSup_single (h0 : N 0 = 0) (i : ι) (a : M) :
    coeffSup N (Finsupp.single i a) = N a := by
  classical
  refine le_antisymm ((coeffSup_le_iff h0).mpr fun j => ?_) ?_
  · rw [Finsupp.single_apply]; split_ifs
    · exact le_rfl
    · rw [h0]; exact zero_le
  · simpa using le_coeffSup h0 (Finsupp.single i a) i

theorem coeffSup_eq_sup_univ [Fintype ι] (h0 : N 0 = 0) (c : ι →₀ M) :
    coeffSup N c = Finset.univ.sup fun i => N (c i) :=
  eq_of_forall_ge_iff fun γ => by simp [coeffSup_le_iff h0]

theorem coeffSup_eq_mul_of_forall (h0 : N 0 = 0) {M' : Type*} [Zero M'] {N' : M' → Γ₀}
    (h0' : N' 0 = 0) {c : ι →₀ M} {c' : ι →₀ M'} {γ : Γ₀} (h : ∀ i, N' (c' i) = γ * N (c i)) :
    coeffSup N' c' = γ * coeffSup N c := by
  refine le_antisymm ((coeffSup_le_iff h0').mpr fun i => ?_) ?_
  · rw [h i]; exact mul_le_mul_right (le_coeffSup h0 c i) γ
  · by_cases hc : c = 0
    · simp [hc]
    · obtain ⟨i, -, hi⟩ := exists_mem_support_coeffSup_eq (N := N) hc
      rw [hi, ← h i]; exact le_coeffSup h0' c' i

end CoeffSup

section MonoidAlgebra

variable {R G Γ₀ : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)

theorem coeffSup_coeff_mul_le [Add G] (f g : AddMonoidAlgebra R G) :
    coeffSup v (f * g).coeff ≤ coeffSup v f.coeff * coeffSup v g.coeff := by
  classical
  refine (coeffSup_le_iff v.map_zero).mpr fun m => ?_
  rw [AddMonoidAlgebra.coeff_mul]
  refine v.map_sum_le fun a _ => v.map_sum_le fun b _ => ?_
  dsimp only
  split_ifs
  · rw [v.map_mul]
    exact mul_le_mul' (le_coeffSup v.map_zero _ _) (le_coeffSup v.map_zero _ _)
  · rw [v.map_zero]; exact zero_le

theorem coeffSup_coeff_mul [Add G] [UniqueSums G] (f g : AddMonoidAlgebra R G) :
    coeffSup v (f * g).coeff = coeffSup v f.coeff * coeffSup v g.coeff := by
  classical
  refine le_antisymm (coeffSup_coeff_mul_le v f g) ?_
  by_cases hf : coeffSup v f.coeff = 0
  · simp [hf]
  by_cases hg : coeffSup v g.coeff = 0
  · simp [hg]
  have hf' : f.coeff ≠ 0 := fun h => hf (by simp [h])
  have hg' : g.coeff ≠ 0 := fun h => hg (by simp [h])
  obtain ⟨a, ha, ha'⟩ := exists_mem_support_coeffSup_eq (N := v) hf'
  obtain ⟨b, hb, hb'⟩ := exists_mem_support_coeffSup_eq (N := v) hg'
  obtain ⟨a₀, ha₀, b₀, hb₀, hu⟩ := UniqueSums.uniqueAdd_of_nonempty
    (A := f.coeff.support.filter fun x => v (f.coeff x) = coeffSup v f.coeff)
    (B := g.coeff.support.filter fun x => v (g.coeff x) = coeffSup v g.coeff)
    ⟨a, Finset.mem_filter.mpr ⟨ha, ha'.symm⟩⟩ ⟨b, Finset.mem_filter.mpr ⟨hb, hb'.symm⟩⟩
  obtain ⟨ha₁, ha₂⟩ := Finset.mem_filter.mp ha₀
  obtain ⟨hb₁, hb₂⟩ := Finset.mem_filter.mp hb₀
  refine le_trans (le_of_eq ?_) (le_coeffSup v.map_zero _ (a₀ + b₀))
  have hpos : 0 < coeffSup v f.coeff * coeffSup v g.coeff := zero_lt_iff.mpr (mul_ne_zero hf hg)
  rw [AddMonoidAlgebra.coeff_mul]
  simp_rw [Finsupp.sum]
  rw [← Finset.sum_product', v.map_sum_eq_of_lt (j := (a₀, b₀))
    (Finset.mem_product.mpr ⟨ha₁, hb₁⟩)]
  · simp [ha₂, hb₂]
  · intro p hp
    obtain ⟨hp, hne⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
    rw [Finset.mem_singleton] at hne
    simp only [if_true, map_mul, ha₂, hb₂]
    split_ifs with he
    · rw [map_mul]
      have h₁ := le_coeffSup v.map_zero f.coeff p.1
      have h₂ := le_coeffSup v.map_zero g.coeff p.2
      rcases h₁.eq_or_lt with h₁ | h₁
      · rcases h₂.eq_or_lt with h₂ | h₂
        · have := hu (Finset.mem_filter.mpr ⟨hp₁, h₁⟩) (Finset.mem_filter.mpr ⟨hp₂, h₂⟩) he
          exact absurd (Prod.ext this.1 this.2) hne
        · rw [h₁]; exact mul_lt_mul_of_pos_left h₂ (zero_lt_iff.mpr hf)
      · exact lt_of_le_of_lt (mul_le_mul_right h₂ _)
          (mul_lt_mul_of_pos_right h₁ (zero_lt_iff.mpr hg))
    · rw [map_zero]; exact hpos

variable [AddMonoid G] [UniqueSums G]

def gaussValAlg : Valuation (AddMonoidAlgebra R G) Γ₀ where
  toFun f := coeffSup v f.coeff
  map_zero' := by simp
  map_one' := by
    rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single, coeffSup_single v.map_zero,
      v.map_one]
  map_mul' := coeffSup_coeff_mul v
  map_add_le_max' f g := (coeffSup_le_iff v.map_zero).mpr fun m => by
    rw [AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
    exact (v.map_add _ _).trans
      (max_le_max (le_coeffSup v.map_zero _ _) (le_coeffSup v.map_zero _ _))

theorem gaussValAlg_apply (f : AddMonoidAlgebra R G) :
    gaussValAlg v f = f.coeff.support.sup fun m => v (f.coeff m) := rfl

theorem gaussValAlg_le_iff {f : AddMonoidAlgebra R G} {γ : Γ₀} :
    gaussValAlg v f ≤ γ ↔ ∀ m, v (f.coeff m) ≤ γ := coeffSup_le_iff v.map_zero

@[simp] theorem gaussValAlg_single (m : G) (a : R) :
    gaussValAlg v (AddMonoidAlgebra.single m a) = v a :=
  coeffSup_single v.map_zero m a

theorem exists_gaussValAlg_eq (f : AddMonoidAlgebra R G) :
    ∃ m, gaussValAlg v f = v (f.coeff m) :=
  haveI : Nonempty G := ⟨0⟩
  exists_coeffSup_eq v.map_zero f.coeff

theorem gaussValAlg_eq_zero_iff {f : AddMonoidAlgebra R G} :
    gaussValAlg v f = 0 ↔ ∀ m, v (f.coeff m) = 0 := coeffSup_eq_zero_iff v.map_zero

end MonoidAlgebra

section Poly

open MvPolynomial

variable {R S Γ₀ σ τ : Type*} [CommRing R] [CommRing S] [LinearOrderedCommMonoidWithZero Γ₀]
  (v : Valuation R Γ₀)

def gaussVal : Valuation (MvPolynomial σ R) Γ₀ := gaussValAlg v

theorem gaussVal_apply (f : MvPolynomial σ R) :
    gaussVal v f = f.support.sup fun m => v (coeff m f) := rfl

theorem gaussVal_mul (f g : MvPolynomial σ R) :
    gaussVal v (f * g) = gaussVal v f * gaussVal v g := map_mul _ f g

theorem gaussVal_le_iff {f : MvPolynomial σ R} {γ : Γ₀} :
    gaussVal v f ≤ γ ↔ ∀ m, v (coeff m f) ≤ γ := gaussValAlg_le_iff v

theorem gaussVal_lt_iff {f : MvPolynomial σ R} {γ : Γ₀} (hγ : γ ≠ 0) :
    gaussVal v f < γ ↔ ∀ m, v (coeff m f) < γ := coeffSup_lt_iff v.map_zero hγ

theorem le_gaussVal (f : MvPolynomial σ R) (m : σ →₀ ℕ) : v (coeff m f) ≤ gaussVal v f :=
  (gaussVal_le_iff v).mp le_rfl m

theorem exists_gaussVal_eq (f : MvPolynomial σ R) : ∃ m, gaussVal v f = v (coeff m f) :=
  exists_gaussValAlg_eq v f

theorem gaussVal_eq_zero_iff_forall {f : MvPolynomial σ R} :
    gaussVal v f = 0 ↔ ∀ m, v (coeff m f) = 0 := gaussValAlg_eq_zero_iff v

@[simp] theorem gaussVal_monomial (m : σ →₀ ℕ) (a : R) :
    gaussVal v (monomial m a) = v a := gaussValAlg_single v m a

@[simp] theorem gaussVal_C (a : R) : gaussVal v (C a : MvPolynomial σ R) = v a :=
  gaussVal_monomial v 0 a

@[simp] theorem gaussVal_X (i : σ) : gaussVal v (X i : MvPolynomial σ R) = 1 :=
  (gaussVal_monomial v _ 1).trans v.map_one

@[simp] theorem gaussVal_comap_C :
    (gaussVal v).comap (C : R →+* MvPolynomial σ R) = v := by
  ext a; simp

theorem gaussVal_smul (a : R) (f : MvPolynomial σ R) :
    gaussVal v (a • f) = v a * gaussVal v f := by
  rw [smul_eq_C_mul, map_mul, gaussVal_C]

theorem gaussVal_supp :
    (gaussVal v).supp = v.supp.map (C : R →+* MvPolynomial σ R) := by
  ext f
  rw [Valuation.mem_supp_iff, gaussVal_eq_zero_iff_forall, mem_map_C_iff]
  simp only [Valuation.mem_supp_iff]

theorem gaussVal_supp_eq_bot_of_supp (hv : v.supp = ⊥) :
    (gaussVal (σ := σ) v).supp = ⊥ := by
  rw [gaussVal_supp, hv, Ideal.map_bot]

theorem gaussVal_eq_zero_iff_of_supp (hv : v.supp = ⊥) {f : MvPolynomial σ R} :
    gaussVal v f = 0 ↔ f = 0 := by
  rw [← Valuation.mem_supp_iff, gaussVal_supp_eq_bot_of_supp v hv, Ideal.mem_bot]

theorem gaussVal_sum_C_mul_X (s : Finset σ) (a : σ → R) :
    gaussVal v (∑ i ∈ s, C (a i) * X i : MvPolynomial σ R) = s.sup fun i => v (a i) := by
  classical
  refine le_antisymm (Valuation.map_sum_le _ fun i hi => ?_) (Finset.sup_le fun i hi => ?_)
  · rw [map_mul, gaussVal_C, gaussVal_X, mul_one]
    exact Finset.le_sup (f := fun i => v (a i)) hi
  · refine le_trans (le_of_eq ?_) (le_gaussVal v _ (Finsupp.single i 1))
    rw [coeff_sum, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [coeff_C_mul, coeff_X, if_neg, mul_zero]
      exact fun h => hj (Finsupp.single_left_injective one_ne_zero h)
    · exact fun h => absurd hi h

theorem gaussVal_map (w : Valuation S Γ₀) (φ : R →+* S) (f : MvPolynomial σ R) :
    gaussVal w (map φ f) = gaussVal (w.comap φ) f :=
  eq_of_forall_ge_iff fun γ => by simp [gaussVal_le_iff, coeff_map]

theorem gaussVal_map_of_eq (w : Valuation S Γ₀) (φ : R →+* S) (h : ∀ a, w (φ a) = v a)
    (f : MvPolynomial σ R) : gaussVal w (map φ f) = gaussVal v f := by
  rw [gaussVal_map, show w.comap φ = v from Valuation.ext h]

theorem valuation_eval₂_le_gaussVal (w : Valuation S Γ₀) (φ : R →+* S)
    (h : ∀ a, w (φ a) ≤ v a) (x : σ → S) (hx : ∀ i, w (x i) ≤ 1) (f : MvPolynomial σ R) :
    w (eval₂ φ x f) ≤ gaussVal v f := by
  rw [eval₂_eq]
  refine w.map_sum_le fun m _ => ?_
  rw [map_mul, map_prod]
  refine le_trans (mul_le_mul' (h _) (Finset.prod_le_one' fun i _ => ?_)) ?_
  · rw [map_pow]; exact pow_le_one' (hx i) _
  · rw [mul_one]; exact le_gaussVal v f m

theorem valuation_eval_le_gaussVal (x : σ → R) (hx : ∀ i, v (x i) ≤ 1) (f : MvPolynomial σ R) :
    v (eval x f) ≤ gaussVal v f :=
  valuation_eval₂_le_gaussVal v v (RingHom.id R) (fun _ => le_rfl) x hx f

theorem valuation_aeval_le_gaussVal [Algebra R S] (w : Valuation S Γ₀)
    (h : ∀ a, w (algebraMap R S a) ≤ v a) (x : σ → S) (hx : ∀ i, w (x i) ≤ 1)
    (f : MvPolynomial σ R) : w (aeval x f) ≤ gaussVal v f :=
  valuation_eval₂_le_gaussVal v w _ h x hx f

theorem gaussVal_aeval_le (g : σ → MvPolynomial τ R) (hg : ∀ i, gaussVal v (g i) ≤ 1)
    (f : MvPolynomial σ R) : gaussVal v (aeval g f) ≤ gaussVal v f :=
  valuation_aeval_le_gaussVal v (gaussVal v) (fun a => by simp) g hg f

theorem gaussVal_algHom_le (e : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (h : ∀ i, gaussVal v (e (X i)) ≤ 1) (f : MvPolynomial σ R) :
    gaussVal v (e f) ≤ gaussVal v f := by
  rw [aeval_unique e]
  exact gaussVal_aeval_le v _ h f

theorem gaussVal_algEquiv (e : MvPolynomial σ R ≃ₐ[R] MvPolynomial τ R)
    (h : ∀ i, gaussVal v (e (X i)) ≤ 1) (h' : ∀ j, gaussVal v (e.symm (X j)) ≤ 1)
    (f : MvPolynomial σ R) : gaussVal v (e f) = gaussVal v f := by
  refine le_antisymm (gaussVal_algHom_le v e.toAlgHom h f) ?_
  simpa using gaussVal_algHom_le v e.symm.toAlgHom h' (e f)

theorem gaussVal_rename_le (e : σ → τ) (f : MvPolynomial σ R) :
    gaussVal v (rename e f) ≤ gaussVal v f := by
  rw [rename_eq_aeval]
  exact gaussVal_aeval_le v _ (fun i => by simp) f

theorem gaussVal_rename {e : σ → τ} (he : Function.Injective e) (f : MvPolynomial σ R) :
    gaussVal v (rename e f) = gaussVal v f := by
  refine le_antisymm (gaussVal_rename_le v e f) ((gaussVal_le_iff v).mpr fun m => ?_)
  rw [← coeff_rename_mapDomain e he f m]
  exact le_gaussVal v _ _

@[simp] theorem gaussVal_renameEquiv (e : σ ≃ τ) (f : MvPolynomial σ R) :
    gaussVal v (renameEquiv R e f) = gaussVal v f :=
  gaussVal_rename v e.injective f

@[simp] theorem gaussVal_sumAlgEquiv (f : MvPolynomial (σ ⊕ τ) R) :
    gaussVal (gaussVal v) (sumAlgEquiv R σ τ f) = gaussVal v f := by
  refine le_antisymm ?_ ?_
  · have := valuation_aeval_le_gaussVal v (gaussVal (σ := σ) (gaussVal (σ := τ) v))
      (fun a => by simp) (fun i => sumAlgEquiv R σ τ (X i))
      (fun i => by cases i <;> simp) f
    convert this using 2
    exact DFunLike.congr_fun (aeval_unique (sumAlgEquiv R σ τ).toAlgHom) f
  · obtain ⟨g, rfl⟩ := (sumAlgEquiv R σ τ).symm.surjective f
    rw [AlgEquiv.apply_symm_apply]
    have := valuation_eval₂_le_gaussVal (gaussVal (σ := τ) v) (gaussVal (σ := σ ⊕ τ) v)
      (rename Sum.inr).toRingHom (fun a => gaussVal_rename_le v _ a) (fun i => X (Sum.inl i))
      (fun i => by simp) g
    convert this using 2
    have : ((sumAlgEquiv R σ τ).symm : MvPolynomial σ (MvPolynomial τ R) →+* _) =
        eval₂Hom (rename Sum.inr).toRingHom (fun i => X (Sum.inl i)) := by
      ext <;> simp
    exact DFunLike.congr_fun this g

@[simp] theorem gaussVal_sumAlgEquiv_symm (g : MvPolynomial σ (MvPolynomial τ R)) :
    gaussVal v ((sumAlgEquiv R σ τ).symm g) = gaussVal (gaussVal v) g := by
  rw [← gaussVal_sumAlgEquiv, AlgEquiv.apply_symm_apply]

end Poly

section Field

open MvPolynomial

variable {K Γ₀ σ τ : Type*} [Field K]

section Monoid

variable [LinearOrderedCommMonoidWithZero Γ₀] [Nontrivial Γ₀] (v : Valuation K Γ₀)

theorem valuation_supp_eq_bot : v.supp = ⊥ :=
  (Ideal.eq_bot_or_top v.supp).resolve_right (Ideal.IsPrime.ne_top inferInstance)

theorem gaussVal_supp_eq_bot : (gaussVal (σ := σ) v).supp = ⊥ :=
  gaussVal_supp_eq_bot_of_supp v (valuation_supp_eq_bot v)

@[simp] theorem gaussVal_eq_zero_iff {f : MvPolynomial σ K} : gaussVal v f = 0 ↔ f = 0 :=
  gaussVal_eq_zero_iff_of_supp v (valuation_supp_eq_bot v)

theorem exists_eq_C_mul_gaussVal_eq_one {f : MvPolynomial σ K} (hf : f ≠ 0) :
    ∃ (c : K) (g : MvPolynomial σ K), c ≠ 0 ∧ v c = gaussVal v f ∧ gaussVal v g = 1 ∧
      f = C c * g := by
  obtain ⟨m, hm⟩ := exists_gaussVal_eq v f
  have hc : coeff m f ≠ 0 := fun h => hf ((gaussVal_eq_zero_iff v).mp (by rw [hm, h, map_zero]))
  refine ⟨coeff m f, C (coeff m f)⁻¹ * f, hc, hm.symm, ?_, ?_⟩
  · rw [map_mul, gaussVal_C, hm, ← map_mul, inv_mul_cancel₀ hc, map_one]
  · rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hc, C_1, one_mul]

end Monoid

variable [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

theorem gaussVal_le_one_iff {O : Type*} [CommRing O] [Algebra O K] (hO : v.Integers O)
    {f : MvPolynomial σ K} :
    gaussVal v f ≤ 1 ↔ ∃ g : MvPolynomial σ O, map (algebraMap O K) g = f := by
  refine ⟨fun h => ?_, ?_⟩
  · refine (mem_range_map_iff_coeffs_subset.mpr ?_ :
      f ∈ Set.range (map (algebraMap O K)))
    intro c hc
    obtain ⟨m, -, rfl⟩ := mem_coeffs_iff.mp hc
    exact hO.exists_of_le_one ((le_gaussVal v f m).trans h)
  · rintro ⟨g, rfl⟩
    exact (gaussVal_le_iff v).mpr fun m => by rw [coeff_map]; exact hO.map_le_one _

theorem gaussVal_lt_one_iff_map_residue {O : Type*} [CommRing O] [IsLocalRing O] [Algebra O K]
    (hO : v.Integers O) (g : MvPolynomial σ O) :
    gaussVal v (map (algebraMap O K) g) < 1 ↔ map (IsLocalRing.residue O) g = 0 := by
  rw [gaussVal_lt_iff v one_ne_zero, MvPolynomial.ext_iff]
  refine forall_congr' fun m => ?_
  rw [coeff_map, coeff_map, coeff_zero, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hO.isUnit_iff_valuation_eq_one]
  exact (hO.map_le_one _).lt_iff_ne

theorem exists_valuation_eval_eq_gaussVal {O : Type*} [CommRing O] [IsLocalRing O] [Algebra O K]
    (hO : v.Integers O) [Infinite (IsLocalRing.ResidueField O)] (f d : MvPolynomial σ K)
    (hd : gaussVal v d = 1) :
    ∃ x : σ → K, (∀ i, v (x i) ≤ 1) ∧ v (eval x d) = 1 ∧ v (eval x f) = gaussVal v f := by
  have key : ∀ g : MvPolynomial σ K, gaussVal v g = 1 →
      ∃ x : σ → K, (∀ i, v (x i) ≤ 1) ∧ v (eval x g) = 1 := by
    intro g hg
    obtain ⟨g, rfl⟩ := (gaussVal_le_one_iff v hO).mp hg.le
    have h₁ : map (IsLocalRing.residue O) g ≠ 0 := fun h =>
      ((gaussVal_lt_one_iff_map_residue v hO g).mpr h).ne hg
    obtain ⟨y, hy⟩ : ∃ y, eval y (map (IsLocalRing.residue O) g) ≠ 0 := by
      by_contra! h
      exact h₁ (MvPolynomial.funext fun y => by simpa using h y)
    choose z hz using fun i => IsLocalRing.residue_surjective (y i)
    refine ⟨fun i => algebraMap O K (z i), fun i => hO.map_le_one _, ?_⟩
    have e₁ : eval (fun i => algebraMap O K (z i)) (map (algebraMap O K) g) =
        algebraMap O K (eval z g) := by
      rw [eval_map, ← coe_eval₂Hom, ← MvPolynomial.eval₂_id, ← coe_eval₂Hom, map_eval₂Hom]
      simp
    have e₂ : eval y (map (IsLocalRing.residue O) g) = IsLocalRing.residue O (eval z g) := by
      rw [eval_map, ← coe_eval₂Hom, ← MvPolynomial.eval₂_id, ← coe_eval₂Hom, map_eval₂Hom]
      simp [hz]
    rw [e₂, IsLocalRing.residue_ne_zero_iff_isUnit] at hy
    rw [e₁]
    exact hO.isUnit_iff_valuation_eq_one.mp hy
  by_cases hf : f = 0
  · obtain ⟨x, hx, hx'⟩ := key d hd
    exact ⟨x, hx, hx', by simp [hf]⟩
  obtain ⟨c, g, -, hc, hg, rfl⟩ := exists_eq_C_mul_gaussVal_eq_one v hf
  obtain ⟨x, hx, hx'⟩ := key (g * d) (by rw [map_mul, hg, hd, mul_one])
  rw [map_mul, map_mul] at hx'
  have h₁ : v (eval x g) ≤ 1 := hg ▸ valuation_eval_le_gaussVal v x hx g
  have h₂ : v (eval x d) ≤ 1 := hd ▸ valuation_eval_le_gaussVal v x hx d
  have h₃ : v (eval x g) = 1 :=
    le_antisymm h₁ (hx' ▸ (mul_le_mul_right h₂ _).trans_eq (mul_one _))
  refine ⟨x, hx, by simpa [h₃] using hx', ?_⟩
  rw [← hc]
  simp [h₃]

def gaussValFrac (σ F : Type*) [Field F] [Algebra (MvPolynomial σ K) F]
    [IsFractionRing (MvPolynomial σ K) F] : Valuation F Γ₀ :=
  (gaussVal (σ := σ) v).extendToLocalization (S := nonZeroDivisors (MvPolynomial σ K))
    (fun _ hf h => nonZeroDivisors.ne_zero hf ((gaussVal_eq_zero_iff v).mp h)) F

variable {F : Type*} [Field F] [Algebra (MvPolynomial σ K) F]
  [IsFractionRing (MvPolynomial σ K) F]

@[simp] theorem gaussValFrac_algebraMap (f : MvPolynomial σ K) :
    gaussValFrac v σ F (algebraMap _ F f) = gaussVal v f :=
  Valuation.extendToLocalization_apply_map_apply _ _ _ f

theorem gaussValFrac_div (f g : MvPolynomial σ K) :
    gaussValFrac v σ F (algebraMap _ F f / algebraMap _ F g) = gaussVal v f / gaussVal v g := by
  simp

@[simp] theorem gaussValFrac_comap :
    (gaussValFrac v σ F).comap (algebraMap (MvPolynomial σ K) F) = gaussVal v := by
  ext f; simp

@[simp] theorem gaussValFrac_algebraMap_const [Algebra K F]
    [IsScalarTower K (MvPolynomial σ K) F] (a : K) :
    gaussValFrac v σ F (algebraMap K F a) = v a := by
  rw [IsScalarTower.algebraMap_apply K (MvPolynomial σ K) F, gaussValFrac_algebraMap]
  simp

theorem eq_gaussValFrac {w : Valuation F Γ₀}
    (h : ∀ f : MvPolynomial σ K, w (algebraMap _ F f) = gaussVal v f) :
    w = gaussValFrac v σ F := by
  ext x
  obtain ⟨f, g, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial σ K) x
  simp [h]

theorem exists_gaussValFrac_eq (x : F) : ∃ c : K, gaussValFrac v σ F x = v c := by
  obtain ⟨f, g, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial σ K) x
  obtain ⟨m, hm⟩ := exists_gaussVal_eq v f
  obtain ⟨n, hn⟩ := exists_gaussVal_eq v g
  exact ⟨coeff m f / coeff n g, by simp [hm, hn]⟩

theorem gaussValFrac_le_one_iff {x : F} :
    gaussValFrac v σ F x ≤ 1 ↔ ∃ f g : MvPolynomial σ K, gaussVal v f ≤ 1 ∧ gaussVal v g = 1 ∧
      x = algebraMap _ F f / algebraMap _ F g := by
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨f, g, hg, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial σ K) x
    obtain ⟨c, g', hc, -, hg', rfl⟩ :=
      exists_eq_C_mul_gaussVal_eq_one v (nonZeroDivisors.ne_zero hg)
    have e : algebraMap _ F f / algebraMap _ F (C c * g') =
        algebraMap _ F (C c⁻¹ * f) / algebraMap _ F g' := by
      have : algebraMap (MvPolynomial σ K) F (C c⁻¹) = (algebraMap _ F (C c : MvPolynomial σ K))⁻¹ :=
        map_inv₀ ((algebraMap (MvPolynomial σ K) F).comp C) c
      rw [map_mul, map_mul, this]
      ring
    refine ⟨C c⁻¹ * f, g', ?_, hg', e⟩
    rwa [e, gaussValFrac_div, hg', div_one] at h
  · rintro ⟨f, g, hf, hg, rfl⟩
    rwa [gaussValFrac_div, hg, div_one]

theorem gaussVal_gaussValFrac_sumAlgEquiv (f : MvPolynomial (τ ⊕ σ) K) :
    gaussVal (gaussValFrac v σ F) (map (algebraMap _ F) (sumAlgEquiv K τ σ f)) =
      gaussVal v f := by
  rw [gaussVal_map, gaussValFrac_comap, gaussVal_sumAlgEquiv]

end Field

section Additive

open MvPolynomial

variable {R Γ σ τ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
  (v : AddValuation R Γ)

def gaussAddVal : AddValuation (MvPolynomial σ R) Γ :=
  AddValuation.ofValuation (gaussVal (AddValuation.toValuation v))

theorem le_gaussAddVal_iff {f : MvPolynomial σ R} {γ : Γ} :
    γ ≤ gaussAddVal v f ↔ ∀ m, γ ≤ v (coeff m f) :=
  gaussVal_le_iff (AddValuation.toValuation v) (γ := Multiplicative.ofAdd (OrderDual.toDual γ))

theorem gaussAddVal_apply (f : MvPolynomial σ R) :
    gaussAddVal v f = f.support.inf fun m => v (coeff m f) := by
  refine eq_of_forall_le_iff fun γ => ?_
  rw [le_gaussAddVal_iff, Finset.le_inf_iff]
  refine ⟨fun h m _ => h m, fun h m => ?_⟩
  by_cases hm : m ∈ f.support
  · exact h m hm
  · rw [notMem_support_iff.mp hm, v.map_zero]; exact le_top

theorem gaussAddVal_le (f : MvPolynomial σ R) (m : σ →₀ ℕ) : gaussAddVal v f ≤ v (coeff m f) :=
  (le_gaussAddVal_iff v).mp le_rfl m

theorem exists_gaussAddVal_eq (f : MvPolynomial σ R) : ∃ m, gaussAddVal v f = v (coeff m f) :=
  exists_gaussVal_eq (AddValuation.toValuation v) f

theorem gaussAddVal_mul (f g : MvPolynomial σ R) :
    gaussAddVal v (f * g) = gaussAddVal v f + gaussAddVal v g := AddValuation.map_mul _ f g

@[simp] theorem gaussAddVal_C (a : R) : gaussAddVal v (C a : MvPolynomial σ R) = v a :=
  gaussVal_C (AddValuation.toValuation v) a

@[simp] theorem gaussAddVal_X (i : σ) : gaussAddVal v (X i : MvPolynomial σ R) = 0 :=
  gaussVal_X (AddValuation.toValuation v) i

theorem gaussAddVal_rename {e : σ → τ} (he : Function.Injective e) (f : MvPolynomial σ R) :
    gaussAddVal v (rename e f) = gaussAddVal v f :=
  gaussVal_rename (AddValuation.toValuation v) he f

@[simp] theorem gaussAddVal_sumAlgEquiv (f : MvPolynomial (σ ⊕ τ) R) :
    gaussAddVal (gaussAddVal v) (sumAlgEquiv R σ τ f) = gaussAddVal v f :=
  gaussVal_sumAlgEquiv (AddValuation.toValuation v) f

end Additive

section Abs

open MvPolynomial

variable {R σ τ : Type*} [CommRing R]

def absValuation [Nontrivial R] (a : AbsoluteValue R ℝ) (ha : IsNonarchimedean a) :
    Valuation R ℝ≥0 where
  toFun x := NNReal.mk (a x) (a.nonneg x)
  map_zero' := NNReal.eq a.map_zero
  map_one' := NNReal.eq a.map_one
  map_mul' x y := NNReal.eq (a.map_mul x y)
  map_add_le_max' x y := by
    refine NNReal.coe_le_coe.mp ?_
    rw [NNReal.coe_max]
    exact ha x y

@[simp] theorem coe_absValuation [Nontrivial R] (a : AbsoluteValue R ℝ) (ha : IsNonarchimedean a)
    (x : R) : (absValuation a ha x : ℝ) = a x := rfl

theorem absValuation_supp [Nontrivial R] (a : AbsoluteValue R ℝ) (ha : IsNonarchimedean a) :
    (absValuation a ha).supp = ⊥ := by
  ext x
  rw [Valuation.mem_supp_iff, ← NNReal.coe_eq_zero, coe_absValuation, a.eq_zero, Ideal.mem_bot]

def valuationAbs (v : Valuation R ℝ≥0) (hv : v.supp = ⊥) : AbsoluteValue R ℝ where
  toFun x := v x
  map_mul' x y := by simp
  nonneg' x := NNReal.coe_nonneg _
  eq_zero' x := by
    rw [NNReal.coe_eq_zero, ← Valuation.mem_supp_iff, hv, Ideal.mem_bot]
  add_le' x y := by
    have h : (v (x + y) : ℝ) ≤ max (v x : ℝ) (v y) := by exact_mod_cast v.map_add x y
    exact h.trans (max_le_add_of_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _))

@[simp] theorem valuationAbs_apply (v : Valuation R ℝ≥0) (hv : v.supp = ⊥) (x : R) :
    valuationAbs v hv x = v x := rfl

theorem isNonarchimedean_valuationAbs (v : Valuation R ℝ≥0) (hv : v.supp = ⊥) :
    IsNonarchimedean (valuationAbs v hv) := fun x y => by
  simp only [valuationAbs_apply]
  exact_mod_cast v.map_add x y

variable [Nontrivial R] (a : AbsoluteValue R ℝ) (ha : IsNonarchimedean a)

def gaussAbs : AbsoluteValue (MvPolynomial σ R) ℝ :=
  valuationAbs (gaussVal (absValuation a ha))
    (gaussVal_supp_eq_bot_of_supp _ (absValuation_supp a ha))

theorem gaussAbs_apply (f : MvPolynomial σ R) :
    gaussAbs a ha f = gaussVal (absValuation a ha) f := rfl

theorem isNonarchimedean_gaussAbs : IsNonarchimedean (gaussAbs (σ := σ) a ha) :=
  isNonarchimedean_valuationAbs _ _

theorem le_gaussAbs (f : MvPolynomial σ R) (m : σ →₀ ℕ) : a (coeff m f) ≤ gaussAbs a ha f :=
  NNReal.coe_le_coe.mpr (le_gaussVal (absValuation a ha) f m)

theorem exists_gaussAbs_eq (f : MvPolynomial σ R) : ∃ m, gaussAbs a ha f = a (coeff m f) :=
  (exists_gaussVal_eq (absValuation a ha) f).imp fun _ h => by
    rw [gaussAbs_apply, h, coe_absValuation]

theorem gaussAbs_le_iff {f : MvPolynomial σ R} {r : ℝ} :
    gaussAbs a ha f ≤ r ↔ ∀ m, a (coeff m f) ≤ r := by
  refine ⟨fun h m => (le_gaussAbs a ha f m).trans h, fun h => ?_⟩
  obtain ⟨m, hm⟩ := exists_gaussAbs_eq a ha f
  exact hm ▸ h m

@[simp] theorem gaussAbs_C (x : R) : gaussAbs a ha (C x : MvPolynomial σ R) = a x := by
  simp [gaussAbs_apply]

@[simp] theorem gaussAbs_X (i : σ) : gaussAbs a ha (X i : MvPolynomial σ R) = 1 := by
  simp [gaussAbs_apply]

theorem gaussAbs_rename {e : σ → τ} (he : Function.Injective e) (f : MvPolynomial σ R) :
    gaussAbs a ha (rename e f) = gaussAbs a ha f := by
  rw [gaussAbs_apply, gaussVal_rename _ he, gaussAbs_apply]

theorem gaussAbs_sumAlgEquiv (f : MvPolynomial (σ ⊕ τ) R) :
    gaussAbs (gaussAbs a ha) (isNonarchimedean_gaussAbs a ha) (sumAlgEquiv R σ τ f) =
      gaussAbs a ha f :=
  congrArg NNReal.toReal (gaussVal_sumAlgEquiv (absValuation a ha) f)

theorem gaussAbs_eq_gaussNorm (f : MvPolynomial σ R) :
    gaussAbs a ha f = MvPowerSeries.gaussNorm a (fun _ => 1) (f : MvPowerSeries σ R) := by
  obtain ⟨m, hm⟩ := exists_gaussAbs_eq a ha f
  have hb : ∀ t : σ →₀ ℕ, a (MvPowerSeries.coeff t (f : MvPowerSeries σ R)) *
      t.prod ((fun _ : σ => (1 : ℝ)) · ^ ·) = a (coeff t f) := fun t => by
    simp [Finsupp.prod]
  rw [MvPowerSeries.gaussNorm]
  simp_rw [hb]
  refine le_antisymm (hm.le.trans (le_ciSup (f := fun t => a (coeff t f)) ⟨gaussAbs a ha f, ?_⟩ m))
    (ciSup_le fun t => le_gaussAbs a ha f t)
  rintro _ ⟨t, rfl⟩
  exact le_gaussAbs a ha f t

variable {K : Type*} [Field K] (a : AbsoluteValue K ℝ) (ha : IsNonarchimedean a)

def gaussAbsFrac (σ F : Type*) [Field F] [Algebra (MvPolynomial σ K) F]
    [IsFractionRing (MvPolynomial σ K) F] : AbsoluteValue F ℝ :=
  valuationAbs (gaussValFrac (absValuation a ha) σ F) (valuation_supp_eq_bot _)

variable {F : Type*} [Field F] [Algebra (MvPolynomial σ K) F]
  [IsFractionRing (MvPolynomial σ K) F]

@[simp] theorem gaussAbsFrac_algebraMap (f : MvPolynomial σ K) :
    gaussAbsFrac a ha σ F (algebraMap _ F f) = gaussAbs a ha f :=
  congrArg NNReal.toReal (gaussValFrac_algebraMap (absValuation a ha) f)

theorem isNonarchimedean_gaussAbsFrac : IsNonarchimedean (gaussAbsFrac a ha σ F) :=
  isNonarchimedean_valuationAbs _ _

end Abs

section Content

open MvPolynomial Module

variable {R Γ₀ ι κ σ : Type*} [CommRing R] [LinearOrderedCommMonoidWithZero Γ₀]
  (v : Valuation R Γ₀) {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

def basisVal (b : Basis ι R M) (x : M) : Γ₀ := coeffSup v (b.repr x)

variable (b : Basis ι R M)

theorem basisVal_le_iff {x : M} {γ : Γ₀} : basisVal v b x ≤ γ ↔ ∀ i, v (b.repr x i) ≤ γ :=
  coeffSup_le_iff v.map_zero

theorem le_basisVal (x : M) (i : ι) : v (b.repr x i) ≤ basisVal v b x :=
  le_coeffSup v.map_zero _ i

theorem basisVal_eq_sup_univ [Fintype ι] (x : M) :
    basisVal v b x = Finset.univ.sup fun i => v (b.repr x i) :=
  coeffSup_eq_sup_univ v.map_zero _

theorem exists_basisVal_eq {x : M} (hx : x ≠ 0) : ∃ i, basisVal v b x = v (b.repr x i) := by
  obtain ⟨i, -, hi⟩ := exists_mem_support_coeffSup_eq (N := v) (c := b.repr x) (by simpa using hx)
  exact ⟨i, hi⟩

@[simp] theorem basisVal_zero : basisVal v b 0 = 0 := by simp [basisVal]

@[simp] theorem basisVal_basis (i : ι) : basisVal v b (b i) = 1 := by
  rw [basisVal, b.repr_self, coeffSup_single v.map_zero, v.map_one]

theorem basisVal_smul (a : R) (x : M) : basisVal v b (a • x) = v a * basisVal v b x :=
  coeffSup_eq_mul_of_forall v.map_zero v.map_zero fun i => by simp

@[simp] theorem basisVal_neg (x : M) : basisVal v b (-x) = basisVal v b x := by
  rw [← neg_one_smul R x, basisVal_smul]; simp

theorem basisVal_add_le (x y : M) :
    basisVal v b (x + y) ≤ max (basisVal v b x) (basisVal v b y) :=
  (basisVal_le_iff v b).mpr fun i => by
    rw [map_add, Finsupp.add_apply]
    exact (v.map_add _ _).trans (max_le_max (le_basisVal v b x i) (le_basisVal v b y i))

theorem basisVal_sum_le {α : Type*} {s : Finset α} {x : α → M} {γ : Γ₀}
    (h : ∀ a ∈ s, basisVal v b (x a) ≤ γ) : basisVal v b (∑ a ∈ s, x a) ≤ γ :=
  (basisVal_le_iff v b).mpr fun i => by
    rw [map_sum, Finsupp.finset_sum_apply]
    exact v.map_sum_le fun a ha => (le_basisVal v b _ i).trans (h a ha)

theorem basisVal_eq_zero_iff (hv : v.supp = ⊥) {x : M} : basisVal v b x = 0 ↔ x = 0 := by
  rw [basisVal, coeffSup_eq_zero_iff v.map_zero, ← b.repr.map_eq_zero_iff, Finsupp.ext_iff]
  simp only [← Valuation.mem_supp_iff, hv, Ideal.mem_bot, Finsupp.zero_apply]

theorem basisVal_map_le (c : Basis κ R N) (φ : M →ₗ[R] N) (h : ∀ i, basisVal v c (φ (b i)) ≤ 1)
    (x : M) : basisVal v c (φ x) ≤ basisVal v b x := by
  conv_lhs => rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum]
  refine basisVal_sum_le v c fun i _ => ?_
  rw [map_smul, basisVal_smul]
  exact (mul_le_mul' (le_basisVal v b x i) (h i)).trans_eq (mul_one _)

theorem valuation_linearMap_le_basisVal (φ : M →ₗ[R] R) (h : ∀ i, v (φ (b i)) ≤ 1) (x : M) :
    v (φ x) ≤ basisVal v b x := by
  conv_lhs => rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum,
    map_sum]
  refine v.map_sum_le fun i _ => ?_
  rw [map_smul, smul_eq_mul, map_mul]
  exact (mul_le_mul' (le_basisVal v b x i) (h i)).trans_eq (mul_one _)

theorem isGreatest_basisVal (x : M) :
    IsGreatest {γ | ∃ φ : M →ₗ[R] R, (∀ y, basisVal v b y ≤ 1 → v (φ y) ≤ 1) ∧ v (φ x) = γ}
      (basisVal v b x) := by
  constructor
  · by_cases hx : x = 0
    · exact ⟨0, by simp, by simp [hx]⟩
    · obtain ⟨i, hi⟩ := exists_basisVal_eq v b hx
      exact ⟨b.coord i, fun y hy => (le_basisVal v b y i).trans hy, hi.symm⟩
  · rintro _ ⟨φ, hφ, rfl⟩
    exact valuation_linearMap_le_basisVal v b φ (fun i => hφ _ (by simp)) x

theorem basisVal_eq_of_le_one (c : Basis κ R M) (h : ∀ i, basisVal v c (b i) ≤ 1)
    (h' : ∀ j, basisVal v b (c j) ≤ 1) (x : M) : basisVal v b x = basisVal v c x :=
  le_antisymm (basisVal_map_le v c b LinearMap.id h' x) (basisVal_map_le v b c LinearMap.id h x)

theorem basisVal_eq_of_forall_le_one (hv : ∀ a, v a ≤ 1) (c : Basis κ R M) (x : M) :
    basisVal v b x = basisVal v c x :=
  basisVal_eq_of_le_one v b c (fun _ => (basisVal_le_iff v c).mpr fun _ => hv _)
    (fun _ => (basisVal_le_iff v b).mpr fun _ => hv _) x

theorem basisVal_basisMonomials (f : MvPolynomial σ R) :
    basisVal v (basisMonomials σ R) f = gaussVal v f := rfl

def polyContent (c : (σ →₀ ℕ) →₀ M) : Γ₀ := coeffSup (basisVal v b) c

theorem polyContent_le_iff {c : (σ →₀ ℕ) →₀ M} {γ : Γ₀} :
    polyContent v b c ≤ γ ↔ ∀ m, basisVal v b (c m) ≤ γ :=
  coeffSup_le_iff (basisVal_zero v b)

theorem polyContent_le_iff_coord {c : (σ →₀ ℕ) →₀ M} {γ : Γ₀} :
    polyContent v b c ≤ γ ↔ ∀ m i, v (b.repr (c m) i) ≤ γ := by
  simp only [polyContent_le_iff, basisVal_le_iff]

theorem le_polyContent (c : (σ →₀ ℕ) →₀ M) (m : σ →₀ ℕ) :
    basisVal v b (c m) ≤ polyContent v b c := le_coeffSup (basisVal_zero v b) c m

theorem exists_polyContent_eq (c : (σ →₀ ℕ) →₀ M) :
    ∃ m, polyContent v b c = basisVal v b (c m) := exists_coeffSup_eq (basisVal_zero v b) c

theorem polyContent_smul (a : R) (c : (σ →₀ ℕ) →₀ M) :
    polyContent v b (a • c) = v a * polyContent v b c :=
  coeffSup_eq_mul_of_forall (basisVal_zero v b) (basisVal_zero v b) fun m => by
    rw [Finsupp.smul_apply, basisVal_smul]

theorem polyContent_eq_zero_iff (hv : v.supp = ⊥) {c : (σ →₀ ℕ) →₀ M} :
    polyContent v b c = 0 ↔ c = 0 := by
  rw [polyContent, coeffSup_eq_zero_iff (basisVal_zero v b), Finsupp.ext_iff]
  simp only [basisVal_eq_zero_iff v b hv, Finsupp.zero_apply]

theorem polyContent_eq_of_le_one (b' : Basis κ R M) (h : ∀ i, basisVal v b' (b i) ≤ 1)
    (h' : ∀ j, basisVal v b (b' j) ≤ 1) (c : (σ →₀ ℕ) →₀ M) :
    polyContent v b c = polyContent v b' c := by
  rw [polyContent, polyContent, funext (basisVal_eq_of_le_one v b b' h h')]

end Content

section Lattice

open Module

variable {R Γ₀ ι κ : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation R Γ₀) {M : Type*} [AddCommGroup M] [Module R M] (b : Basis ι R M)
  {O : Type*} [CommRing O] [Algebra O R] [Module O M] [IsScalarTower O R M]

theorem basisVal_le_one_iff (hO : v.Integers O) {x : M} :
    basisVal v b x ≤ 1 ↔ x ∈ Submodule.span O (Set.range b) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← b.linearCombination_repr x, Finsupp.linearCombination_apply]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨a, ha⟩ := hO.exists_of_le_one ((le_basisVal v b x i).trans h)
    simp_rw [← ha, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · induction h using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; simp
    | zero => simp
    | add y z _ _ hy hz => exact (basisVal_add_le v b y z).trans (max_le hy hz)
    | smul a y _ hy =>
      rw [← algebraMap_smul R a y, basisVal_smul]
      exact mul_le_one' (hO.map_le_one a) hy

theorem basisVal_eq_of_span_eq (hO : v.Integers O) (c : Basis κ R M)
    (h : Submodule.span O (Set.range b) = Submodule.span O (Set.range c)) (x : M) :
    basisVal v b x = basisVal v c x :=
  basisVal_eq_of_le_one v b c
    (fun i => (basisVal_le_one_iff v c hO).mpr (h ▸ Submodule.subset_span ⟨i, rfl⟩))
    (fun j => (basisVal_le_one_iff v b hO).mpr (h.symm ▸ Submodule.subset_span ⟨j, rfl⟩)) x

end Lattice

section Tensor

open MvPolynomial Module

variable {O R S Γ₀ ι κ σ : Type*} [CommRing O] [CommRing R] [Algebra O R] [CommRing S]
  [Algebra O S] [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)
  {M : Type*} [AddCommGroup M] [Module O M] (b : Basis ι O M)

theorem basisVal_baseChange_eq (hv : ∀ a : O, v (algebraMap O R a) ≤ 1) (c : Basis κ O M)
    (x : R ⊗[O] M) : basisVal v (b.baseChange R) x = basisVal v (c.baseChange R) x :=
  basisVal_eq_of_le_one v _ _
    (fun _ => (basisVal_le_iff v _).mpr fun _ => by simpa [Algebra.smul_def] using hv _)
    (fun _ => (basisVal_le_iff v _).mpr fun _ => by simpa [Algebra.smul_def] using hv _) x

theorem basisVal_baseChange_one_tmul (y : M) :
    basisVal v (b.baseChange R) (1 ⊗ₜ y) = basisVal (v.comap (algebraMap O R)) b y :=
  eq_of_forall_ge_iff fun γ => by simp [basisVal_le_iff, Algebra.smul_def]

theorem basisVal_baseChange_rTensor (w : Valuation S Γ₀) (φ : R →ₐ[O] S)
    (h : ∀ a, w (φ a) = v a) (x : R ⊗[O] M) :
    basisVal w (b.baseChange S) (φ.toLinearMap.rTensor M x) = basisVal v (b.baseChange R) x := by
  have key : ∀ i, (b.baseChange S).repr (φ.toLinearMap.rTensor M x) i =
      φ ((b.baseChange R).repr x i) := fun i => by
    induction x with
    | zero => simp
    | tmul a y => simp
    | add y z hy hz => simp only [map_add, Finsupp.add_apply, hy, hz]
  exact eq_of_forall_ge_iff fun γ => by simp only [basisVal_le_iff, key, h]

def tensorContent (x : MvPolynomial σ R ⊗[O] M) : Γ₀ :=
  basisVal (gaussVal v) (b.baseChange (MvPolynomial σ R)) x

def tensorCoeffs : MvPolynomial σ R ⊗[O] M ≃ₗ[R] (σ →₀ ℕ) →₀ R ⊗[O] M :=
  open Classical in
  TensorProduct.AlgebraTensorModule.congr (AddMonoidAlgebra.coeffLinearEquiv R)
    (LinearEquiv.refl O M) ≪≫ₗ TensorProduct.finsuppLeft O R R M (σ →₀ ℕ)

@[simp] theorem tensorCoeffs_tmul (f : MvPolynomial σ R) (y : M) (m : σ →₀ ℕ) :
    tensorCoeffs (f ⊗ₜ[O] y) m = coeff m f ⊗ₜ[O] y := by
  simp [tensorCoeffs, coeff]

theorem repr_tensorCoeffs (x : MvPolynomial σ R ⊗[O] M) (m : σ →₀ ℕ) (i : ι) :
    (b.baseChange R).repr (tensorCoeffs x m) i =
      coeff m ((b.baseChange (MvPolynomial σ R)).repr x i) := by
  induction x with
  | zero => simp
  | tmul f y => simp
  | add y z hy hz => simp only [map_add, Finsupp.add_apply, hy, hz, coeff_add]

theorem tensorContent_eq_polyContent (x : MvPolynomial σ R ⊗[O] M) :
    tensorContent v b x = polyContent v (b.baseChange R) (tensorCoeffs x) :=
  eq_of_forall_ge_iff fun γ => by
    simp only [tensorContent, basisVal_le_iff, gaussVal_le_iff, polyContent_le_iff_coord,
      repr_tensorCoeffs]
    exact forall_comm

theorem tensorContent_le_iff {x : MvPolynomial σ R ⊗[O] M} {γ : Γ₀} :
    tensorContent v b x ≤ γ ↔ ∀ m, basisVal v (b.baseChange R) (tensorCoeffs x m) ≤ γ := by
  rw [tensorContent_eq_polyContent, polyContent_le_iff]

theorem tensorContent_smul (f : MvPolynomial σ R) (x : MvPolynomial σ R ⊗[O] M) :
    tensorContent v b (f • x) = gaussVal v f * tensorContent v b x :=
  basisVal_smul _ _ f x

theorem tensorContent_add_le (x y : MvPolynomial σ R ⊗[O] M) :
    tensorContent v b (x + y) ≤ max (tensorContent v b x) (tensorContent v b y) :=
  basisVal_add_le _ _ x y

theorem tensorContent_tmul (f : MvPolynomial σ R) (y : M) :
    tensorContent v b (f ⊗ₜ y) = gaussVal v f * basisVal (v.comap (algebraMap O R)) b y := by
  have : (gaussVal (σ := σ) v).comap (algebraMap O (MvPolynomial σ R)) =
      v.comap (algebraMap O R) := by
    ext a; simp
  rw [← this, ← basisVal_baseChange_one_tmul, ← basisVal_smul, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one, tensorContent]

theorem tensorContent_eq_zero_iff (hv : v.supp = ⊥) {x : MvPolynomial σ R ⊗[O] M} :
    tensorContent v b x = 0 ↔ x = 0 :=
  basisVal_eq_zero_iff _ _ (gaussVal_supp_eq_bot_of_supp v hv)

theorem tensorContent_eq_of_basis (hv : ∀ a : O, v (algebraMap O R a) ≤ 1) (c : Basis κ O M)
    (x : MvPolynomial σ R ⊗[O] M) : tensorContent v b x = tensorContent v c x :=
  basisVal_baseChange_eq _ b (fun a => by simpa using hv a) c x

def scalarCoeffs {N : Type*} [AddCommGroup N] [Module R N] :
    MvPolynomial σ R ⊗[R] N ≃ₗ[R] (σ →₀ ℕ) →₀ N :=
  tensorCoeffs ≪≫ₗ Finsupp.mapRange.linearEquiv (TensorProduct.lid R N)

@[simp] theorem scalarCoeffs_tmul {N : Type*} [AddCommGroup N] [Module R N]
    (f : MvPolynomial σ R) (y : N) (m : σ →₀ ℕ) :
    scalarCoeffs (f ⊗ₜ[R] y) m = coeff m f • y := by
  simp [scalarCoeffs]

theorem tensorContent_eq_polyContent_scalarCoeffs {N : Type*} [AddCommGroup N] [Module R N]
    (c : Basis ι R N) (x : MvPolynomial σ R ⊗[R] N) :
    tensorContent v c x = polyContent v c (scalarCoeffs x) := by
  have key : ∀ m i, c.repr (scalarCoeffs x m) i =
      coeff m ((c.baseChange (MvPolynomial σ R)).repr x i) := fun m i => by
    induction x with
    | zero => simp
    | tmul f y => simp [mul_comm]
    | add y z hy hz => simp only [map_add, Finsupp.add_apply, hy, hz, coeff_add]
  refine eq_of_forall_ge_iff fun γ => ?_
  simp only [tensorContent, basisVal_le_iff, gaussVal_le_iff, polyContent_le_iff_coord, key]
  exact forall_comm

end Tensor

section AdditiveContent

open MvPolynomial Module

variable {R Γ ι κ σ : Type*} [CommRing R] [LinearOrderedAddCommMonoidWithTop Γ]
  (v : AddValuation R Γ)

section

variable {M : Type*} [AddCommGroup M] [Module R M] (b : Basis ι R M)

def basisAddVal (x : M) : Γ :=
  OrderDual.ofDual (Multiplicative.toAdd (basisVal (AddValuation.toValuation v) b x))

theorem le_basisAddVal_iff {x : M} {γ : Γ} :
    γ ≤ basisAddVal v b x ↔ ∀ i, γ ≤ v (b.repr x i) :=
  basisVal_le_iff (AddValuation.toValuation v) b (γ := Multiplicative.ofAdd (OrderDual.toDual γ))

theorem basisAddVal_eq_inf_univ [Fintype ι] (x : M) :
    basisAddVal v b x = Finset.univ.inf fun i => v (b.repr x i) :=
  eq_of_forall_le_iff fun γ => by simp [le_basisAddVal_iff]

theorem basisAddVal_smul (a : R) (x : M) :
    basisAddVal v b (a • x) = v a + basisAddVal v b x :=
  basisVal_smul (AddValuation.toValuation v) b a x

theorem basisAddVal_eq_of_forall_nonneg (hv : ∀ a, 0 ≤ v a) (c : Basis κ R M) (x : M) :
    basisAddVal v b x = basisAddVal v c x :=
  basisVal_eq_of_forall_le_one (AddValuation.toValuation v) b hv c x

def polyAddContent (c : (σ →₀ ℕ) →₀ M) : Γ :=
  OrderDual.ofDual (Multiplicative.toAdd (polyContent (AddValuation.toValuation v) b c))

theorem le_polyAddContent_iff {c : (σ →₀ ℕ) →₀ M} {γ : Γ} :
    γ ≤ polyAddContent v b c ↔ ∀ m, γ ≤ basisAddVal v b (c m) :=
  polyContent_le_iff (AddValuation.toValuation v) b
    (γ := Multiplicative.ofAdd (OrderDual.toDual γ))

end

variable {O M : Type*} [CommRing O] [Algebra O R] [AddCommGroup M] [Module O M] (b : Basis ι O M)

def tensorAddContent (x : MvPolynomial σ R ⊗[O] M) : Γ :=
  basisAddVal (gaussAddVal v) (b.baseChange (MvPolynomial σ R)) x

theorem tensorAddContent_eq_polyAddContent (x : MvPolynomial σ R ⊗[O] M) :
    tensorAddContent v b x = polyAddContent v (b.baseChange R) (tensorCoeffs x) :=
  tensorContent_eq_polyContent (AddValuation.toValuation v) b x

theorem tensorAddContent_smul (f : MvPolynomial σ R) (x : MvPolynomial σ R ⊗[O] M) :
    tensorAddContent v b (f • x) = gaussAddVal v f + tensorAddContent v b x :=
  basisAddVal_smul _ _ f x

theorem tensorAddContent_eq_of_basis (hv : ∀ a : O, 0 ≤ v (algebraMap O R a)) (c : Basis κ O M)
    (x : MvPolynomial σ R ⊗[O] M) : tensorAddContent v b x = tensorAddContent v c x :=
  tensorContent_eq_of_basis (AddValuation.toValuation v) b hv c x

end AdditiveContent

section More

open MvPolynomial Module IsDedekindDomain

theorem basisVal_gaussValFrac {O K Γ₀ ι σ F M : Type*} [CommRing O] [Field K] [Algebra O K]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) [Field F]
    [Algebra (MvPolynomial σ K) F] [IsFractionRing (MvPolynomial σ K) F] [Algebra O F]
    [IsScalarTower O (MvPolynomial σ K) F] [AddCommGroup M] [Module O M] (b : Basis ι O M)
    (x : MvPolynomial σ K ⊗[O] M) :
    basisVal (gaussValFrac v σ F) (b.baseChange F)
      ((IsScalarTower.toAlgHom O (MvPolynomial σ K) F).toLinearMap.rTensor M x) =
      tensorContent v b x :=
  basisVal_baseChange_rTensor _ b _ _ (fun a => gaussValFrac_algebraMap v a) x

def gaussAddValFrac {K Γ : Type*} [Field K] [LinearOrderedAddCommGroupWithTop Γ]
    (v : AddValuation K Γ) (σ F : Type*) [Field F] [Algebra (MvPolynomial σ K) F]
    [IsFractionRing (MvPolynomial σ K) F] : AddValuation F Γ :=
  AddValuation.ofValuation (gaussValFrac (AddValuation.toValuation v) σ F)

@[simp] theorem gaussAddValFrac_algebraMap {K Γ σ F : Type*} [Field K]
    [LinearOrderedAddCommGroupWithTop Γ] (v : AddValuation K Γ) [Field F]
    [Algebra (MvPolynomial σ K) F] [IsFractionRing (MvPolynomial σ K) F]
    (f : MvPolynomial σ K) : gaussAddValFrac v σ F (algebraMap _ F f) = gaussAddVal v f :=
  gaussValFrac_algebraMap (AddValuation.toValuation v) f

theorem finite_gaussVal_ne_one {O K σ : Type*} [CommRing O] [IsDedekindDomain O] [Field K]
    [Algebra O K] [IsFractionRing O K] {f : MvPolynomial σ K} (hf : f ≠ 0) :
    {p : HeightOneSpectrum O | gaussVal (p.valuation K) f ≠ 1}.Finite := by
  obtain ⟨m₀, hm₀⟩ := ne_zero_iff.mp hf
  refine ((f.support.finite_toSet.biUnion fun m _ =>
    HeightOneSpectrum.Support.finite O (coeff m f)).union
      (HeightOneSpectrum.Support.finite O (coeff m₀ f)⁻¹)).subset fun p hp => ?_
  by_contra h
  simp only [Set.mem_union, Set.mem_iUnion, HeightOneSpectrum.Support, Set.mem_setOf_eq, not_or,
    not_exists, not_lt, map_inv₀] at h
  refine hp (le_antisymm ?_ ?_)
  · rw [gaussVal_apply]
    exact Finset.sup_le fun m hm => h.1 m hm
  · refine le_trans ?_ (le_gaussVal _ f m₀)
    exact (inv_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hm₀))).mp h.2

end More

section Examples

open MvPolynomial

example (p : ℕ) [Fact p.Prime] :
    ((gaussVal (NormedField.valuation (K := ℚ_[p]))
      (C (p : ℚ_[p]) * X 0 + C ((p : ℚ_[p]) ^ 2) * X 1 : MvPolynomial (Fin 2) ℚ_[p]) : ℝ≥0) : ℝ) =
      (p : ℝ)⁻¹ := by
  have h := gaussVal_sum_C_mul_X (NormedField.valuation (K := ℚ_[p])) Finset.univ
    (![(p : ℚ_[p]), (p : ℚ_[p]) ^ 2] : Fin 2 → ℚ_[p])
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  rw [h, Finset.univ_fin2, Finset.sup_insert, Finset.sup_singleton, NNReal.coe_max]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, NormedField.valuation_apply, coe_nnnorm,
    norm_pow, Padic.norm_p]
  refine max_eq_left ?_
  rw [sq]
  exact mul_le_of_le_one_left (by positivity) (inv_le_one_of_one_le₀ hp)

example {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) :
    gaussVal v (X 0 - X 1 : MvPolynomial (Fin 2) K) = 1 ∧
      gaussVal v (rename (fun _ => ()) (X 0 - X 1 : MvPolynomial (Fin 2) K)) = 0 := by
  refine ⟨?_, by simp⟩
  have h := gaussVal_sum_C_mul_X v Finset.univ (![1, -1] : Fin 2 → K)
  simpa [Fin.sum_univ_two, Finset.univ_fin2, ← sub_eq_add_neg] using h

example {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (h : Irreducible ϖ) :
    gaussAddVal (IsDiscreteValuationRing.addVal O) (C ϖ * X () : MvPolynomial Unit O) = 1 := by
  rw [gaussAddVal_mul, gaussAddVal_C, gaussAddVal_X, add_zero,
    IsDiscreteValuationRing.addVal_uniformizer h]

example {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (h : Irreducible ϖ) :
    basisAddVal (IsDiscreteValuationRing.addVal O) (Pi.basisFun O (Fin 2)) ![ϖ, ϖ ^ 2] = 1 := by
  rw [basisAddVal_eq_inf_univ, Finset.univ_fin2, Finset.inf_insert, Finset.inf_singleton]
  simp [IsDiscreteValuationRing.addVal_uniformizer h]

end Examples

end

end GlobalTheory
