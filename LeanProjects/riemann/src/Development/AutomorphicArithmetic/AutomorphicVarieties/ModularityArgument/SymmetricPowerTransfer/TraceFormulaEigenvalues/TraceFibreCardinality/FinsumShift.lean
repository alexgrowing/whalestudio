import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.RepIndep

noncomputable section

namespace UpperTheory.V.Z.Sym.Tf

private lemma out_smul_eq {G M : Type} [Group G] (U : Subgroup G) (F : G → M)
    (hF : ∀ g (u : U), F (g * u) = F g) (a : G) (x : G ⧸ U) : F (a • x).out = F (a * x.out) := by
  have h : (a • x : G ⧸ U) = QuotientGroup.mk (a * x.out) := by
    conv_lhs => rw [← QuotientGroup.out_eq' x]
    rfl
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U (a * x.out)
  rw [h, hu, hF]

private lemma finsum_shift {G M : Type} [Group G] [AddCommMonoid M] (U : Subgroup G) (F : G → M)
    (hF : ∀ g (u : U), F (g * u) = F g) (a : G) :
    ∑ᶠ x : G ⧸ U, F (a * x.out) = ∑ᶠ x : G ⧸ U, F x.out := by
  rw [← finsum_comp_equiv (MulAction.toPerm a : Equiv.Perm (G ⧸ U)) (f := fun x : G ⧸ U => F x.out)]
  exact finsum_congr fun x => (out_smul_eq U F hF a x).symm

variable {Γ G V : Type} [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] {B : Base Γ G V}

private lemma fin_shift (s : B.Tw) {f : G → ℂ} (h : s.IsTest f) (a : G) :
    {z : G ⧸ B.U | f (s.θ (a * z.out)) ≠ 0}.Finite := by
  refine (h.fin.preimage (f := fun z : G ⧸ B.U => a • z) (MulAction.injective a).injOn).subset ?_
  intro z hz
  have := out_smul_eq B.U (fun g => f (s.θ g) ≠ 0) (fun g u => by
    simp only [map_mul, h.right]; simp) a z
  simp only [Set.mem_preimage, Set.mem_setOf_eq] at hz ⊢
  rw [this]; exact hz

private lemma conv_eq (s₁ : B.Tw) {f₁ : G → ℂ} (f₂ : G → ℂ) (h₁ : s₁.IsTest f₁) (y : G) :
    s₁.conv f₁ f₂ y = ∑ x ∈ h₁.fin.toFinset, f₁ (s₁.θ x.out) * f₂ (x.out⁻¹ * s₁.θ.symm y) := by
  refine finsum_eq_sum_of_support_subset _ ?_
  intro x hx
  simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
  exact left_ne_zero_of_mul hx

private lemma conv_test (s₁ s₂ : B.Tw) {f₁ f₂ : G → ℂ} (h₁ : s₁.IsTest f₁) (h₂ : s₂.IsTest f₂) :
    (s₁.mul s₂).IsTest (s₁.conv f₁ f₂) := by
  refine ⟨fun u y => ?_, fun u y => ?_, ?_⟩
  · have key := finsum_shift B.U (fun g => f₁ (s₁.θ g) * f₂ (g⁻¹ * s₁.θ.symm (u * y))) (fun g w => by
      have e := h₂.left w⁻¹ (g⁻¹ * s₁.θ.symm (u * y))
      simp only [map_mul s₁.θ, h₁.right, mul_inv_rev, mul_assoc]
      rw [Subgroup.coe_inv] at e
      rw [e, map_inv, inv_inv, mul_left_comm (f₁ _), ← mul_assoc, ← Units.val_mul, inv_mul_cancel]
      simp) (s₁.θ.symm u)
    have hc := conv_eq s₁ f₂ h₁ y
    unfold Base.Tw.conv
    rw [← key]
    unfold Base.Tw.conv at hc
    rw [hc, Finset.mul_sum, finsum_eq_sum_of_support_subset (s := h₁.fin.toFinset)]
    · refine Finset.sum_congr rfl fun x _ => ?_
      simp only [map_mul, MulEquiv.apply_symm_apply, h₁.left, mul_inv_rev, mul_assoc, inv_mul_cancel_left]
    · intro x hx
      simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
      have := left_ne_zero_of_mul hx
      simp only [map_mul, MulEquiv.apply_symm_apply, h₁.left] at this
      exact right_ne_zero_of_mul this
  · rw [conv_eq s₁ f₂ h₁, conv_eq s₁ f₂ h₁, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    have : (s₁.mul s₂).θ u = s₁.θ (s₂.θ u) := rfl
    rw [this, map_mul, MulEquiv.symm_apply_apply, ← mul_assoc, h₂.right]
    ring
  · refine (h₁.fin.biUnion fun x _ => fin_shift s₂ h₂ (s₂.θ.symm x.out⁻¹)).subset ?_
    intro z hz
    simp only [Set.mem_setOf_eq] at hz
    rw [conv_eq s₁ f₂ h₁] at hz
    obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    refine ⟨x, left_ne_zero_of_mul hne, ?_⟩
    have e : (s₁.mul s₂).θ z.out = s₁.θ (s₂.θ z.out) := rfl
    have := right_ne_zero_of_mul hne
    rw [e, MulEquiv.symm_apply_apply] at this
    rwa [map_mul, MulEquiv.apply_symm_apply]

private lemma opF_comp (s₁ s₂ : B.Tw) {f₁ f₂ : G → ℂ} (h₁ : s₁.IsTest f₁) (h₂ : s₂.IsTest f₂)
    (φ : B.Forms) (g : G) :
    s₁.opF f₁ (s₂.opF f₂ φ.1) g = (s₁.mul s₂).opF (s₁.conv f₁ f₂) φ.1 g := by
  have eθ : ∀ z, s₁.θ.symm ((s₁.mul s₂).θ z) = s₂.θ z := fun z => s₁.θ.symm_apply_apply _
  have eθ' : (s₁.mul s₂).θ.symm g = s₂.θ.symm (s₁.θ.symm g) := rfl
  have eΘ : ∀ v, (s₁.mul s₂).Θ v = s₁.Θ (s₂.Θ v) := fun _ => rfl
  have inner : ∀ x : G, s₂.opF f₂ φ.1 (s₁.θ.symm g * x) =
      ∑ᶠ z : G ⧸ B.U, f₂ (x⁻¹ * s₂.θ z.out) • s₂.Θ (φ.1 (s₂.θ.symm (s₁.θ.symm g) * z.out)) := by
    intro x
    have key := finsum_shift B.U
      (fun z => f₂ (x⁻¹ * s₂.θ z) • s₂.Θ (φ.1 (s₂.θ.symm (s₁.θ.symm g) * z))) (fun z w => by
        rw [map_mul, ← mul_assoc, ← mul_assoc, h₂.right, φ.2.2, map_smul, smul_smul]
        congr 1
        rw [mul_right_comm, ← Units.val_mul, inv_mul_cancel]
        simp) (s₂.θ.symm x)
    rw [← key]
    unfold Base.Tw.opF
    refine finsum_congr fun z => ?_
    simp only [map_mul, MulEquiv.apply_symm_apply, mul_assoc, inv_mul_cancel_left]
  have hfin : ∀ x : G, {z : G ⧸ B.U | f₂ (x⁻¹ * s₂.θ z.out) ≠ 0}.Finite := fun x => by
    simpa only [map_mul, MulEquiv.apply_symm_apply] using fin_shift s₂ h₂ (s₂.θ.symm x⁻¹)
  conv_rhs => unfold Base.Tw.opF
  simp only [conv_eq s₁ f₂ h₁, eθ, eθ', eΘ, Finset.sum_smul]
  rw [finsum_sum_comm]
  · conv_lhs => unfold Base.Tw.opF
    rw [finsum_eq_sum_of_support_subset (s := h₁.fin.toFinset)]
    · refine Finset.sum_congr rfl fun x _ => ?_
      have := inner x.out
      unfold Base.Tw.opF at this
      rw [this, finsum_eq_sum_of_support_subset (s := (hfin x.out).toFinset),
        finsum_eq_sum_of_support_subset (s := (hfin x.out).toFinset), map_sum, Finset.smul_sum]
      · refine Finset.sum_congr rfl fun z _ => ?_
        rw [map_smul, smul_smul]
      · intro z hz
        simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
        exact right_ne_zero_of_mul (left_ne_zero_of_smul hz)
      · intro z hz
        simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
        exact left_ne_zero_of_smul hz
    · intro x hx
      simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
      exact left_ne_zero_of_smul hx
  · intro x _
    refine (hfin x.out).subset fun z hz => ?_
    exact right_ne_zero_of_mul (left_ne_zero_of_smul hz)

end UpperTheory.V.Z.Sym.Tf

theorem UpperTheory.V.Z.Sym.Tf.rMul :
    UpperTheory.V.Z.Sym.Tf.RMul := by
  intro Γ G V _ _ _ _ B s₁ s₂ f₁ f₂ h₁ h₂
  have ht := UpperTheory.V.Z.Sym.Tf.conv_test s₁ s₂ h₁ h₂
  refine ⟨ht, LinearMap.ext fun φ => Subtype.ext ?_⟩
  rw [Module.End.mul_apply, UpperTheory.V.Z.Sym.Tf.rSpec _ _ _ B s₁ f₁ h₁, UpperTheory.V.Z.Sym.Tf.rSpec _ _ _ B s₂ f₂ h₂,
    UpperTheory.V.Z.Sym.Tf.rSpec _ _ _ B _ _ ht]
  funext g
  exact UpperTheory.V.Z.Sym.Tf.opF_comp s₁ s₂ h₁ h₂ φ g
