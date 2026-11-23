import Mathlib

noncomputable section

open UpperHalfPlane Filter
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

def IsMF (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ℍ → ℂ) : Prop :=
  (∀ γ ∈ Γ, f ∣[k] γ = f) ∧ MDiff f ∧ ∀ x : SL(2, ℤ), IsBoundedAtImInfty (f ∣[k] x)

def IsCF (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ℍ → ℂ) : Prop :=
  (∀ γ ∈ Γ, f ∣[k] γ = f) ∧ MDiff f ∧ ∀ x : SL(2, ℤ), IsZeroAtImInfty (f ∣[k] x)

def IsReps (Γ : Subgroup SL(2, ℤ)) {r : ℕ} (s : Fin r → SL(2, ℤ)) : Prop :=
  (∀ x : SL(2, ℤ), ∃ i, ∃ γ ∈ Γ, x = γ * s i ∨ x = -(γ * s i)) ∧
    ∀ i j, ∀ γ ∈ Γ, (s i = γ * s j ∨ s i = -(γ * s j)) → i = j

def evM {r : ℕ} (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ) (τ : ℍ) :
    Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i j => (F j ∣[w j] s i) τ

def co (M : ℕ) (k : ℤ) (f : ℍ → ℂ) (x : SL(2, ℤ)) (n : ℕ) : ℂ :=
  (qExpansion (M : ℝ) (f ∣[k] x)).coeff n

def leadM (M : ℕ) {r : ℕ} (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ) :
    Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i j => ∑ n ∈ Finset.range M, co M (w j) (F j) (s i) n

def Reduces (Γ : Subgroup SL(2, ℤ)) {r : ℕ} (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ) : Prop :=
  ∃ (j₀ : Fin r) (w' : ℤ) (G E : ℍ → ℂ) (e : Fin r → ℍ → ℂ), w' < w j₀ ∧ Odd w' ∧ IsMF Γ w' G ∧
    (∀ j, MDiff (e j)) ∧ e j₀ ≠ 0 ∧
    ∀ (x : SL(2, ℤ)) (τ : ℍ), E τ * (G ∣[w'] x) τ = ∑ j, e j τ * (F j ∣[w j] x) τ

theorem mdiff_slash {f : ℍ → ℂ} (hf : MDiff f) (k : ℤ) (x : SL(2, ℤ)) : MDiff (f ∣[k] x) := by
  rw [ModularForm.SL_slash]
  exact hf.slash k _

theorem slash_neg (k : ℤ) (f : ℍ → ℂ) (x : SL(2, ℤ)) : f ∣[k] (-x) = ((-1 : ℂ) ^ k) • f ∣[k] x := by
  ext τ
  simp only [Pi.smul_apply, ModularForm.SL_slash_apply, smul_eq_mul, ModularGroup.SL_neg_smul]
  have hd : denom ((-x : SL(2, ℤ)) : GL (Fin 2) ℝ) τ = -denom (x : GL (Fin 2) ℝ) τ := by
    simp [denom]
    ring
  rw [hd]
  rcases Int.even_or_odd k with hk | hk
  · rw [hk.neg_one_zpow, hk.neg.neg_zpow]; ring
  · rw [hk.neg_one_zpow, hk.neg.neg_zpow]; ring

theorem slash_neg_of_odd {k : ℤ} (hk : Odd k) (f : ℍ → ℂ) (x : SL(2, ℤ)) : f ∣[k] (-x) = -(f ∣[k] x) := by
  rw [slash_neg, hk.neg_one_zpow, neg_one_smul]

theorem slash_neg_of_even {k : ℤ} (hk : Even k) (f : ℍ → ℂ) (x : SL(2, ℤ)) : f ∣[k] (-x) = f ∣[k] x := by
  rw [slash_neg, hk.neg_one_zpow, one_smul]

theorem slash_mul_apply (k : ℤ) (f : ℍ → ℂ) (x y : SL(2, ℤ)) (τ : ℍ) :
    (f ∣[k] (x * y)) τ = (f ∣[k] x) (y • τ) * denom (y : GL (Fin 2) ℝ) τ ^ (-k) := by
  rw [SlashAction.slash_mul, ModularForm.SL_slash_apply]

theorem IsCF.isMF {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {f : ℍ → ℂ} (h : IsCF Γ k f) : IsMF Γ k f := ⟨h.1, h.2.1, fun x => (h.2.2 x).boundedAtFilter⟩

theorem IsMF.slash_mul {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {f : ℍ → ℂ} (h : IsMF Γ k f) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Γ) (x : SL(2, ℤ)) : f ∣[k] (γ * x) = f ∣[k] x := by
  rw [SlashAction.slash_mul, h.1 γ hγ]

theorem IsMF.slash_top {k : ℤ} {f : ℍ → ℂ} (h : IsMF ⊤ k f) (x : SL(2, ℤ)) : f ∣[k] x = f := h.1 x (Subgroup.mem_top x)

theorem IsMF.mono {Γ Γ' : Subgroup SL(2, ℤ)} {k : ℤ} {f : ℍ → ℂ} (h : IsMF Γ k f) (hle : Γ' ≤ Γ) :
    IsMF Γ' k f := ⟨fun γ hγ => h.1 γ (hle hγ), h.2.1, h.2.2⟩

theorem IsMF.zero (Γ : Subgroup SL(2, ℤ)) (k : ℤ) : IsMF Γ k 0 := by
  refine ⟨fun γ _ => SlashAction.zero_slash _ _, mdifferentiable_const, fun x => ?_⟩
  rw [SlashAction.zero_slash]
  exact zero_form_isBoundedAtImInfty

theorem IsMF.add {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {f g : ℍ → ℂ} (hf : IsMF Γ k f) (hg : IsMF Γ k g) :
    IsMF Γ k (f + g) := by
  refine ⟨fun γ hγ => ?_, hf.2.1.add hg.2.1, fun x => ?_⟩
  · rw [SlashAction.add_slash, hf.1 γ hγ, hg.1 γ hγ]
  · rw [SlashAction.add_slash]
    exact (hf.2.2 x).add (hg.2.2 x)

theorem IsMF.smul {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {f : ℍ → ℂ} (hf : IsMF Γ k f) (c : ℂ) :
    IsMF Γ k (c • f) := by
  refine ⟨fun γ hγ => ?_, hf.2.1.const_smul c, fun x => ?_⟩
  · rw [ModularForm.SL_smul_slash, hf.1 γ hγ]
  · rw [ModularForm.SL_smul_slash]
    exact (hf.2.2 x).smul c

theorem IsMF.neg {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {f : ℍ → ℂ} (hf : IsMF Γ k f) : IsMF Γ k (-f) := by
  have h := hf.smul (-1)
  rwa [neg_one_smul] at h

theorem IsMF.sub {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {f g : ℍ → ℂ} (hf : IsMF Γ k f) (hg : IsMF Γ k g) :
    IsMF Γ k (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

theorem IsMF.sum {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {ι : Type*} (t : Finset ι) {f : ι → ℍ → ℂ}
    (hf : ∀ i ∈ t, IsMF Γ k (f i)) : IsMF Γ k (∑ i ∈ t, f i) := Finset.sum_induction _ (IsMF Γ k) (fun _ _ ha hb => ha.add hb) (IsMF.zero Γ k) hf

theorem IsMF.mul {Γ : Subgroup SL(2, ℤ)} {k l m : ℤ} {f g : ℍ → ℂ} (hf : IsMF Γ k f) (hg : IsMF Γ l g)
    (hm : m = k + l) : IsMF Γ m (f * g) := by
  subst hm
  refine ⟨fun γ hγ => ?_, hf.2.1.mul hg.2.1, fun x => ?_⟩
  · rw [ModularForm.mul_slash_SL2, hf.1 γ hγ, hg.1 γ hγ]
  · rw [ModularForm.mul_slash_SL2]
    exact (hf.2.2 x).mul (hg.2.2 x)

theorem IsMF.mul_isCF {Γ : Subgroup SL(2, ℤ)} {k l m : ℤ} {f g : ℍ → ℂ} (hf : IsMF Γ k f) (hg : IsCF Γ l g)
    (hm : m = k + l) : IsCF Γ m (f * g) := by
  subst hm
  refine ⟨fun γ hγ => ?_, hf.2.1.mul hg.2.1, fun x => ?_⟩
  · rw [ModularForm.mul_slash_SL2, hf.1 γ hγ, hg.1 γ hγ]
  · rw [ModularForm.mul_slash_SL2]
    exact (hf.2.2 x).mul_zeroAtFilter (hg.2.2 x)

theorem IsMF.one (Γ : Subgroup SL(2, ℤ)) : IsMF Γ 0 1 := by
  refine ⟨fun γ _ => ModularForm.is_invariant_one γ, mdifferentiable_const, fun x => ?_⟩
  rw [ModularForm.is_invariant_one]
  exact Filter.const_boundedAtFilter _ (1 : ℂ)

theorem IsMF.pow {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {f : ℍ → ℂ} (hf : IsMF Γ k f) (n : ℕ) :
    IsMF Γ (n * k) (f ^ n) := by
  induction n with
  | zero => simpa using IsMF.one Γ
  | succ n ih =>
    rw [pow_succ]
    exact ih.mul hf (by push_cast; ring)

theorem isMF_coe {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} (f : ModularForm Γ k) : IsMF Γ k f := ⟨fun γ hγ => SlashInvariantFormClass.slash_action_eq f _ ⟨γ, hγ, rfl⟩, ModularFormClass.holo f,
    fun x => ModularFormClass.bdd_at_infty_slash f x⟩

theorem isMF_coe_top {k : ℤ} (f : ModularForm 𝒮ℒ k) : IsMF ⊤ k f := ⟨fun γ _ => SlashInvariantFormClass.slash_action_eq f _ ⟨γ, rfl⟩, ModularFormClass.holo f,
    fun x => ModularFormClass.bdd_at_infty_slash f x⟩

theorem isCF_coe_top {k : ℤ} (f : CuspForm 𝒮ℒ k) : IsCF ⊤ k f := ⟨fun γ _ => SlashInvariantFormClass.slash_action_eq f _ ⟨γ, rfl⟩, ModularFormClass.holo f,
    fun x => CuspFormClass.zero_at_infty_slash f x⟩

def IsMF.toMF {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {f : ℍ → ℂ} (h : IsMF Γ k f) :
    ModularForm Γ k where
  toFun := f
  slash_action_eq' := by rintro _ ⟨γ, hγ, rfl⟩; exact h.1 γ hγ
  holo' := h.2.1
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    exact fun γ _ => h.2.2 γ

@[simp] theorem IsMF.coe_toMF {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {f : ℍ → ℂ} (h : IsMF Γ k f) :
    ⇑h.toMF = f := rfl

def IsCF.toCF {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {f : ℍ → ℂ} (h : IsCF Γ k f) :
    CuspForm Γ k where
  toFun := f
  slash_action_eq' := by rintro _ ⟨γ, hγ, rfl⟩; exact h.1 γ hγ
  holo' := h.2.1
  zero_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    exact fun γ _ => h.2.2 γ

@[simp] theorem IsCF.coe_toCF {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {f : ℍ → ℂ} (h : IsCF Γ k f) :
    ⇑h.toCF = f := rfl

def IsMF.toLevelOne {k : ℤ} {f : ℍ → ℂ} (h : IsMF ⊤ k f) : ModularForm 𝒮ℒ k where
  toFun := f
  slash_action_eq' := by rintro _ ⟨γ, rfl⟩; exact h.slash_top γ
  holo' := h.2.1
  bdd_at_cusps' {c} hc := by
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    exact fun γ _ => h.2.2 γ

@[simp] theorem IsMF.coe_toLevelOne {k : ℤ} {f : ℍ → ℂ} (h : IsMF ⊤ k f) : ⇑h.toLevelOne = f := rfl

theorem finiteIndex_of_Gamma_le {M : ℕ} {Γ : Subgroup SL(2, ℤ)} (hM : 0 < M)
    (h : CongruenceSubgroup.Gamma M ≤ Γ) : Γ.FiniteIndex := by
  have : NeZero M := ⟨hM.ne'⟩
  exact Subgroup.finiteIndex_of_le h

theorem IsMF.eq_zero_of_neg {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {f : ℍ → ℂ} (h : IsMF Γ k f)
    (hk : k < 0) : f = 0 := by
  have h0 := ModularForm.isZero_of_neg_weight hk h.toMF
  rw [← h.coe_toMF, h0]
  rfl

private theorem exists_finite_residue_reps_mod_natCast {Γ : Subgroup SL(2, ℤ)} {x z y : SL(2, ℤ)}
    (h : ∃ γ ∈ Γ, x = γ * z ∨ x = -(γ * z)) : ∃ γ ∈ Γ, x * y = γ * (z * y) ∨ x * y = -(γ * (z * y)) := by
  obtain ⟨γ, hγ, h | h⟩ := h
  · exact ⟨γ, hγ, Or.inl (by rw [h, mul_assoc])⟩
  · exact ⟨γ, hγ, Or.inr (by rw [h, neg_mul, mul_assoc])⟩

private theorem exists_mem_mul_or_neg_mul_symm {Γ : Subgroup SL(2, ℤ)} {x z : SL(2, ℤ)}
    (h : ∃ γ ∈ Γ, x = γ * z ∨ x = -(γ * z)) : ∃ γ ∈ Γ, z = γ * x ∨ z = -(γ * x) := by
  obtain ⟨γ, hγ, h | h⟩ := h
  · exact ⟨γ⁻¹, Γ.inv_mem hγ, Or.inl (by rw [h, ← mul_assoc, inv_mul_cancel, one_mul])⟩
  · exact ⟨γ⁻¹, Γ.inv_mem hγ, Or.inr (by rw [h, mul_neg, ← mul_assoc, inv_mul_cancel, one_mul, neg_neg])⟩

private theorem exists_mem_mul_or_neg_mul_trans {Γ : Subgroup SL(2, ℤ)} {x z u : SL(2, ℤ)}
    (h₁ : ∃ γ ∈ Γ, x = γ * z ∨ x = -(γ * z)) (h₂ : ∃ γ ∈ Γ, z = γ * u ∨ z = -(γ * u)) :
    ∃ γ ∈ Γ, x = γ * u ∨ x = -(γ * u) := by
  obtain ⟨γ, hγ, h | h⟩ := h₁ <;> obtain ⟨δ, hδ, h' | h'⟩ := h₂
  · exact ⟨γ * δ, Γ.mul_mem hγ hδ, Or.inl (by rw [h, h', mul_assoc])⟩
  · exact ⟨γ * δ, Γ.mul_mem hγ hδ, Or.inr (by rw [h, h', mul_neg, mul_assoc])⟩
  · exact ⟨γ * δ, Γ.mul_mem hγ hδ, Or.inr (by rw [h, h', mul_assoc])⟩
  · exact ⟨γ * δ, Γ.mul_mem hγ hδ, Or.inl (by rw [h, h', mul_neg, neg_neg, mul_assoc])⟩

theorem IsReps.exists_perm {Γ : Subgroup SL(2, ℤ)} {r : ℕ} {s : Fin r → SL(2, ℤ)} (hs : IsReps Γ s)
    (y : SL(2, ℤ)) : ∃ π : Equiv.Perm (Fin r), ∀ i, ∃ γ ∈ Γ, s i * y = γ * s (π i) ∨ s i * y = -(γ * s (π i)) := by
  choose π γ hγ hπ using fun i => hs.1 (s i * y)
  have hinj : Function.Injective π := by
    intro i i' he
    have h1 : ∃ g ∈ Γ, s i * y = g * s (π i) ∨ s i * y = -(g * s (π i)) := ⟨γ i, hγ i, hπ i⟩
    have h2 : ∃ g ∈ Γ, s i' * y = g * s (π i) ∨ s i' * y = -(g * s (π i)) := by
      rw [he]; exact ⟨γ i', hγ i', hπ i'⟩
    obtain ⟨g, hg, h⟩ := exists_finite_residue_reps_mod_natCast (y := y⁻¹) (exists_mem_mul_or_neg_mul_trans h1 (exists_mem_mul_or_neg_mul_symm h2))
    simp only [mul_inv_cancel_right] at h
    exact hs.2 i i' g hg h
  exact ⟨Equiv.ofBijective π (Finite.injective_iff_bijective.mp hinj), fun i => ⟨γ i, hγ i, hπ i⟩⟩

theorem IsReps.sum_eq_zero {Γ : Subgroup SL(2, ℤ)} {r : ℕ} {s : Fin r → SL(2, ℤ)} (hs : IsReps Γ s)
    {ι : Type*} [Fintype ι] {w : ι → ℤ} {F : ι → ℍ → ℂ} (hF : ∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j))
    (c : ι → ℂ) (τ : ℍ) (h : ∀ i, ∑ j, c j * (F j ∣[w j] s i) τ = 0) (x : SL(2, ℤ)) :
    ∑ j, c j * (F j ∣[w j] x) τ = 0 := by
  obtain ⟨i, γ, hγ, hx | hx⟩ := hs.1 x
  · have e : ∀ j, (F j ∣[w j] x) τ = (F j ∣[w j] s i) τ := fun j => by
      rw [hx, (hF j).2.slash_mul hγ]
    simp only [e]
    exact h i
  · have e : ∀ j, (F j ∣[w j] x) τ = -(F j ∣[w j] s i) τ := fun j => by
      rw [hx, slash_neg_of_odd (hF j).1, (hF j).2.slash_mul hγ]
      rfl
    simp only [e, mul_neg, Finset.sum_neg_distrib, h i, neg_zero]

theorem mdiff_det_evM {r : ℕ} (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) {F : Fin r → ℍ → ℂ}
    (hF : ∀ j, MDiff (F j)) : MDiff (fun τ => (evM s w F τ).det) := by
  have he : ∀ i j, MDiff (fun τ => evM s w F τ i j) := fun i j => mdiff_slash (hF j) (w j) (s i)
  have e1 : (fun τ => (evM s w F τ).det) = ∑ σ : Equiv.Perm (Fin r), fun τ =>
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, evM s w F τ (σ i) i := by
    funext τ
    rw [Matrix.det_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
  rw [e1]
  refine MDifferentiable.sum fun σ _ => ?_
  refine mdifferentiable_const.mul ?_
  have e2 : (fun τ => ∏ i, evM s w F τ (σ i) i) = ∏ i, fun τ => evM s w F τ (σ i) i := by
    funext τ
    rw [Finset.prod_apply]
  rw [e2]
  exact MDifferentiable.prod fun i _ => he (σ i) i

end GlobalTheory.OddFrame
