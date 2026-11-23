import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

noncomputable section

open Matrix
open scoped NNReal Kronecker

namespace GlobalTheory.WeilM

variable {R : Type} [CommRing R]

theorem schr_schr [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ] (w w' : (κ → R) × (κ → R))
    (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc x w.1 w'.1]
  congr 2
  simp only [add_dotProduct, dotProduct_add]
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * (mul_invOf_self (2 : R))

variable (R) in

def swapA : R × R →ₐ[R] R × R := { (RingEquiv.prodComm : R × R ≃+* R × R).toRingHom with commutes' := fun _ => rfl }

@[simp] theorem swapA_apply (x : R × R) : swapA R x = (x.2, x.1) := rfl

theorem norm_pair (x : R × R) : Algebra.norm R x = x.1 * x.2 := by
  rw [Algebra.norm_eq_matrix_det (Module.Basis.finTwoProd R), Matrix.det_fin_two]
  simp [Algebra.leftMulMatrix_eq_repr_mul]

theorem isQuad_split [Invertible (2 : R)] : IsQuad (swapA R) ((1, -1) : R × R) where
  unit := IsUnit.of_mul_eq_one ((1, -1) : R × R) (by ext <;> simp)
  anti := by ext <;> simp [swapA_apply]
  basis := by
    have hli : LinearIndependent R ![(1 : R × R), (1, -1)] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h1 := congrArg Prod.fst hst
      have h2 := congrArg Prod.snd hst
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_one, Prod.snd_one,
        smul_eq_mul, mul_one, mul_neg, Prod.fst_zero, Prod.snd_zero] at h1 h2
      have hs : s = 0 := by
        have h3 : (2 : R) * s = 0 := by linear_combination h1 + h2
        simpa using congrArg (⅟(2 : R) * ·) h3
      exact ⟨hs, by rw [hs] at h1; simpa using h1⟩
    have hsp : ⊤ ≤ Submodule.span R (Set.range ![(1 : R × R), (1, -1)]) := by
      intro z _
      rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Submodule.mem_span_pair]
      refine ⟨⅟(2 : R) * (z.1 + z.2), ⅟(2 : R) * (z.1 - z.2), ?_⟩
      ext
      · simp only [Prod.fst_add, Prod.smul_fst, Prod.fst_one, smul_eq_mul, mul_one]
        linear_combination z.1 * (invOf_mul_self (2 : R))
      · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_one, smul_eq_mul, mul_one, mul_neg]
        linear_combination z.2 * (invOf_mul_self (2 : R))
    exact ⟨Module.Basis.mk hli hsp, by rw [Module.Basis.mk_apply]; rfl, by rw [Module.Basis.mk_apply]; rfl⟩

def complexDarboux : Darboux (R := ℝ) (symp (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) Complex.I (1 : Matrix Unit Unit ℂ)
    (1 : Matrix Unit Unit ℂ)) Unit where
  e :=
    { toFun := fun x => (fun _ => 2 * (x () ()).re, fun _ => (x () ()).im)
      invFun := fun v => of fun _ _ => ⟨v.1 () / 2, v.2 ()⟩
      map_add' := fun x y => by ext <;> simp [mul_add]
      map_smul' := fun a x => by ext <;> simp [mul_left_comm]
      left_inv := fun x => by ext; apply Complex.ext <;> simp
      right_inv := fun v => by ext <;> simp [mul_div_cancel₀] }
  form w w' := by
    show _ = (fun _ : Unit => 2 * (w () ()).re) ⬝ᵥ (fun _ => (w' () ()).im) -
      (fun _ : Unit => 2 * (w' () ()).re) ⬝ᵥ (fun _ => (w () ()).im)
    simp [symp, hTens, Algebra.trace_complex_apply, dotProduct]
    ring

variable {α β κ : Type}

def flat (σ : κ ≃ α × β) : Matrix α β R ≃ₗ[R] (κ → R) where
  toFun X k := X (σ k).1 (σ k).2
  invFun u := of fun i j => u (σ.symm (i, j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv X := by ext i j; simp
  right_inv u := by ext k; simp

theorem flat_apply (σ : κ ≃ α × β) (X : Matrix α β R) (k : κ) : flat σ X k = X (σ k).1 (σ k).2 := rfl

theorem flat_symm_apply (σ : κ ≃ α × β) (u : κ → R) (i : α) (j : β) : (flat σ).symm u i j = u (σ.symm (i, j)) := rfl

abbrev cmp₁ {m n : Type} (X : Matrix m n (R × R)) : Matrix m n R := X.map (RingHom.fst R R)

abbrev cmp₂ {m n : Type} (X : Matrix m n (R × R)) : Matrix m n R := X.map (RingHom.snd R R)

variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]

omit [DecidableEq α] [DecidableEq β] in
theorem flat_dot (σ : κ ≃ α × β) (X Y : Matrix α β R) : flat σ X ⬝ᵥ flat σ Y = trace (X * Yᵀ) := by
  simp only [dotProduct, flat_apply, trace, diag_apply, mul_apply, transpose_apply]
  rw [← Fintype.sum_prod_type']
  exact Equiv.sum_comp σ (fun p => X p.1 p.2 * Y p.1 p.2)

theorem IsHerm.isUnit_cmp₁ {J : Matrix α α (R × R)} (h : IsHerm (swapA R) J) : IsUnit (cmp₁ J).det := by
  have hu := h.2.map (RingHom.fst R R)
  rwa [RingHom.map_det] at hu

theorem IsHerm.snd_eq {J : Matrix α α (R × R)} (h : IsHerm (swapA R) J) (i j : α) : (J i j).2 = (J j i).1 := by
  have hc := congrArg Prod.snd (h.1 i j)
  rw [swapA_apply] at hc
  exact hc.symm

def splitDarboux {JA : Matrix α α (R × R)} {JB : Matrix β β (R × R)} (hA : IsHerm (swapA R) JA)
    (hB : IsHerm (swapA R) JB) (σ : κ ≃ α × β) : Darboux (R := R) (symp (swapA R) (1, -1) JA JB) κ where
  e :=
    { toFun := fun x => (flat σ (cmp₁ x), flat σ (cmp₁ JA * cmp₂ x * (cmp₁ JB)ᵀ))
      invFun := fun v => of fun i j =>
        ((flat σ).symm v.1 i j, ((cmp₁ JA)⁻¹ * (flat σ).symm v.2 * ((cmp₁ JB)⁻¹)ᵀ : Matrix α β R) i j)
      map_add' := fun x y => by
        rw [Prod.mk_add_mk, ← map_add, ← map_add, ← Matrix.add_mul, ← Matrix.mul_add]; rfl
      map_smul' := fun a x => by
        rw [RingHom.id_apply, Prod.smul_mk, ← map_smul, ← map_smul, ← Matrix.smul_mul, ← Matrix.mul_smul]; rfl
      left_inv := fun x => by
        simp only [LinearEquiv.symm_apply_apply, Matrix.mul_assoc, ← transpose_mul,
          nonsing_inv_mul _ hB.isUnit_cmp₁, transpose_one, Matrix.mul_one,
          nonsing_inv_mul_cancel_left _ _ hA.isUnit_cmp₁]
        rfl
      right_inv := fun v => by
        show (flat σ ((flat σ).symm v.1), flat σ (cmp₁ JA * ((cmp₁ JA)⁻¹ * (flat σ).symm v.2 * ((cmp₁ JB)⁻¹)ᵀ) *
          (cmp₁ JB)ᵀ)) = v
        simp only [Matrix.mul_assoc, ← transpose_mul,
          mul_nonsing_inv _ hB.isUnit_cmp₁, transpose_one, Matrix.mul_one,
          mul_nonsing_inv_cancel_left _ _ hA.isUnit_cmp₁, LinearEquiv.apply_symm_apply] }
  form w w' := by
    show _ = flat σ (cmp₁ w) ⬝ᵥ flat σ (cmp₁ JA * cmp₂ w' * (cmp₁ JB)ᵀ) -
      flat σ (cmp₁ w') ⬝ᵥ flat σ (cmp₁ JA * cmp₂ w * (cmp₁ JB)ᵀ)
    have key : ∀ (X Y : Matrix α β R), trace (X * (cmp₁ JA * Y * (cmp₁ JB)ᵀ)ᵀ) =
        ∑ i, ∑ j, ∑ k, ∑ l, X i j * (JA i k).1 * (JB j l).1 * Y k l := by
      intro X Y
      simp only [trace, diag_apply, mul_apply, transpose_apply, Finset.mul_sum, Finset.sum_mul, map_apply,
        RingHom.coe_fst]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm.trans ?_
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    rw [flat_dot, flat_dot, key, key]
    simp only [symp, hTens, Algebra.trace_prod_apply, Algebra.trace_self_apply, Prod.fst_mul, Prod.snd_mul,
      Prod.fst_sum, Prod.snd_sum, swapA_apply, one_mul, neg_mul, map_apply, RingHom.coe_fst, RingHom.coe_snd,
      hA.snd_eq, hB.snd_eq, sub_eq_add_neg]
    congr 2
    have s4 : ∀ f : α → β → α → β → R, ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := fun f => by
      have := Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun p q : α × β => f p.1 p.2 q.1 q.2)
      simpa only [Fintype.sum_prod_type] using this
    rw [s4]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem splitDarboux_e {JA : Matrix α α (R × R)} {JB : Matrix β β (R × R)} (hA : IsHerm (swapA R) JA)
    (hB : IsHerm (swapA R) JB) (σ : κ ≃ α × β) (x : Matrix α β (R × R)) :
    (splitDarboux hA hB σ).e x = (flat σ (cmp₁ x), flat σ (cmp₁ JA * cmp₂ x * (cmp₁ JB)ᵀ)) := rfl

def ugFst (J : Matrix β β (R × R)) : UG (swapA R) J →* GL β R :=
  (GeneralLinearGroup.map (RingHom.fst R R)).comp (UG (swapA R) J).subtype

theorem ugFst_val {J : Matrix β β (R × R)} (h : UG (swapA R) J) :
    (ugFst J h).val = cmp₁ ((h : GL β (R × R)) : Matrix β β (R × R)) := rfl

theorem ug_rel {J : Matrix β β (R × R)} (h : UG (swapA R) J) :
    (ugFst J h).valᵀ * cmp₁ J * cmp₂ ((h : GL β (R × R)) : Matrix β β (R × R)) = cmp₁ J := by
  have hh : ((h : GL β (R × R)) : Matrix β β (R × R))ᵀ * J *
      ((h : GL β (R × R)) : Matrix β β (R × R)).map (swapA R) = J := h.2
  have hm := congrArg (fun M => M.map (RingHom.fst R R)) hh
  simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map] at hm
  rw [ugFst_val]
  convert hm using 3
  ext x
  simp [swapA_apply]

def substB (σ : κ ≃ α × β) : GL β R →* Module.End ℂ ((κ → R) → ℂ) where
  toFun h := LinearMap.funLeft ℂ ℂ fun u => flat σ ((flat σ).symm u * (h⁻¹).valᵀ)
  map_one' := by ext φ u; simp
  map_mul' h h' := by ext φ u; simp [Matrix.mul_assoc]

def splitChar (m : Rˣ →* ℝ≥0) (χ : (R × R)ˣ →* Circle) (a : ℕ) : Rˣ →* ℂ where
  toFun t := (χ (Units.map (MonoidHom.inl R R) t) : ℂ) * (((m t : ℝ) ^ (-(a : ℝ) / 2) : ℝ) : ℂ)
  map_one' := by simp
  map_mul' s t := by
    simp only [map_mul, Circle.coe_mul, NNReal.coe_mul, Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _),
      Complex.ofReal_mul]
    ring

def splitOm (m : Rˣ →* ℝ≥0) (χ : (R × R)ˣ →* Circle) (J : Matrix β β (R × R)) (σ : κ ≃ α × β) :
    UG (swapA R) J →* Module.End ℂ ((κ → R) → ℂ) where
  toFun h := splitChar m χ (Fintype.card α) (GeneralLinearGroup.det (ugFst J h)) • substB σ (ugFst J h)
  map_one' := by simp
  map_mul' h h' := by simp only [map_mul, smul_mul_smul_comm]

omit [DecidableEq α] [Fintype κ] in
theorem splitOm_apply (m : Rˣ →* ℝ≥0) (χ : (R × R)ˣ →* Circle) (J : Matrix β β (R × R)) (σ : κ ≃ α × β)
    (h : UG (swapA R) J) (φ : (κ → R) → ℂ) (u : κ → R) :
    splitOm m χ J σ h φ u = splitChar m χ (Fintype.card α) (GeneralLinearGroup.det (ugFst J h)) *
      φ (flat σ ((flat σ).symm u * ((ugFst J h)⁻¹).valᵀ)) := rfl

theorem splitOm_rho [Invertible (2 : R)] (m : Rˣ →* ℝ≥0) (χ : (R × R)ˣ →* Circle) {JA : Matrix α α (R × R)}
    {JB : Matrix β β (R × R)} (hA : IsHerm (swapA R) JA) (hB : IsHerm (swapA R) JB) (σ : κ ≃ α × β) (ψ : AddChar R ℂ)
    (h : UG (swapA R) JB) (w : Matrix α β (R × R)) (φ : (κ → R) → ℂ) :
    splitOm m χ JB σ h ((splitDarboux hA hB σ).rho ψ w φ) =
      (splitDarboux hA hB σ).rho ψ (actB (swapA R) h w) (splitOm m χ JB σ h φ) := by
  funext u
  have rel := ug_rel h
  have hv := ugFst_val h
  have hmul : (ugFst JB h).val * ((ugFst JB h)⁻¹).val = 1 := by simp
  have hinv : ((ugFst JB h)⁻¹).val * (ugFst JB h).val = 1 := by simp
  have c1 : cmp₁ (actB (swapA R) h w) = cmp₁ w * (ugFst JB h).valᵀ := by
    rw [hv]; simp [actB, Matrix.map_mul, Matrix.transpose_map]; rfl
  have c2 : cmp₂ (actB (swapA R) h w) = cmp₂ w * (cmp₂ ((h : GL β (R × R)) : Matrix β β (R × R)))ᵀ := by
    simp [actB, Matrix.map_mul, Matrix.transpose_map]; rfl
  simp only [splitOm_apply, Darboux.rho, schr, splitDarboux_e, c1, c2]

  have key1 : cmp₁ JB * cmp₂ ((h : GL β (R × R)) : Matrix β β (R × R)) = ((ugFst JB h)⁻¹).valᵀ * cmp₁ JB := by
    calc cmp₁ JB * cmp₂ ((h : GL β (R × R)) : Matrix β β (R × R))
        = ((ugFst JB h).val * ((ugFst JB h)⁻¹).val)ᵀ * cmp₁ JB * cmp₂ ((h : GL β (R × R)) : Matrix β β (R × R)) := by
          rw [hmul, Matrix.transpose_one, Matrix.one_mul]
      _ = ((ugFst JB h)⁻¹).valᵀ * ((ugFst JB h).valᵀ * cmp₁ JB * cmp₂ ((h : GL β (R × R)) : Matrix β β (R × R))) := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [rel]
  have rel' : ∀ X : Matrix β α R, (ugFst JB h).valᵀ * (cmp₁ JB * (cmp₂ ((h : GL β (R × R)) : Matrix β β (R × R)) * X)) = cmp₁ JB * X := by
    intro X; rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, rel]
  have m1 : (flat σ).symm u * (cmp₁ JA * (cmp₂ w * (cmp₂ ((h : GL β (R × R)) : Matrix β β (R × R)))ᵀ) * (cmp₁ JB)ᵀ)ᵀ =
      (flat σ).symm u * ((ugFst JB h)⁻¹).valᵀ * (cmp₁ JA * cmp₂ w * (cmp₁ JB)ᵀ)ᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (cmp₁ JB) (cmp₂ ((h : GL β (R × R)) : Matrix β β (R × R))), key1, Matrix.mul_assoc]
  have m2 : cmp₁ w * (ugFst JB h).valᵀ * (cmp₁ JA * (cmp₂ w * (cmp₂ ((h : GL β (R × R)) : Matrix β β (R × R)))ᵀ) * (cmp₁ JB)ᵀ)ᵀ =
      cmp₁ w * (cmp₁ JA * cmp₂ w * (cmp₁ JB)ᵀ)ᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [rel']
  have eX : flat σ ((flat σ).symm (u + flat σ (cmp₁ w * (ugFst JB h).valᵀ)) * ((ugFst JB h)⁻¹).valᵀ) =
      flat σ ((flat σ).symm u * ((ugFst JB h)⁻¹).valᵀ) + flat σ (cmp₁ w) := by
    rw [map_add, LinearEquiv.symm_apply_apply, Matrix.add_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, hinv,
      Matrix.transpose_one, Matrix.mul_one, map_add]
  have eP : u ⬝ᵥ flat σ (cmp₁ JA * (cmp₂ w * (cmp₂ ((h : GL β (R × R)) : Matrix β β (R × R)))ᵀ) * (cmp₁ JB)ᵀ) +
        ⅟2 * flat σ (cmp₁ w * (ugFst JB h).valᵀ) ⬝ᵥ flat σ (cmp₁ JA * (cmp₂ w * (cmp₂ ((h : GL β (R × R)) : Matrix β β (R × R)))ᵀ) * (cmp₁ JB)ᵀ) =
      flat σ ((flat σ).symm u * ((ugFst JB h)⁻¹).valᵀ) ⬝ᵥ flat σ (cmp₁ JA * cmp₂ w * (cmp₁ JB)ᵀ) +
        ⅟2 * flat σ (cmp₁ w) ⬝ᵥ flat σ (cmp₁ JA * cmp₂ w * (cmp₁ JB)ᵀ) := by
    conv_lhs => rw [← LinearEquiv.apply_symm_apply (flat σ) u]
    rw [flat_dot, flat_dot, flat_dot, flat_dot, m1, m2]
  rw [eX, eP]
  ring

omit [DecidableEq α] [Fintype κ] in
theorem splitOm_mem_SB [TopologicalSpace R] [IsTopologicalRing R] (m : Rˣ →* ℝ≥0) (χ : (R × R)ˣ →* Circle)
    (J : Matrix β β (R × R)) (σ : κ ≃ α × β) (h : UG (swapA R) J) {φ : (κ → R) → ℂ} (hφ : φ ∈ SB (κ → R)) :
    splitOm m χ J σ h φ ∈ SB (κ → R) := by
  have hc : ∀ M : Matrix β β R, Continuous fun u : κ → R => flat σ ((flat σ).symm u * M) := by
    intro M
    refine continuous_pi fun k => ?_
    simp only [flat_apply, Matrix.mul_apply, flat_symm_apply]
    exact continuous_finsetSum _ fun l _ => (continuous_apply _).mul continuous_const
  let e : (κ → R) ≃ₜ (κ → R) :=
    { toFun := fun u => flat σ ((flat σ).symm u * ((ugFst J h)⁻¹).valᵀ)
      invFun := fun u => flat σ ((flat σ).symm u * (ugFst J h).valᵀ)
      left_inv := fun u => by simp [Matrix.mul_assoc, ← Matrix.transpose_mul]
      right_inv := fun u => by simp [Matrix.mul_assoc, ← Matrix.transpose_mul]
      continuous_toFun := hc _
      continuous_invFun := hc _ }
  have hφ' : IsLocallyConstant φ ∧ HasCompactSupport φ := hφ
  have hφe : (φ ∘ e) ∈ SB (κ → R) := ⟨hφ'.1.comp_continuous e.continuous, hφ'.2.comp_homeomorph e⟩
  have hs : splitOm m χ J σ h φ =
      splitChar m χ (Fintype.card α) (GeneralLinearGroup.det (ugFst J h)) • (φ ∘ e) := by
    funext u
    rw [splitOm_apply]
    rfl
  rw [hs]
  exact (SB (κ → R)).smul_mem _ hφe

theorem isSplitting_splitOm [Invertible (2 : R)] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
    (m : Rˣ →* ℝ≥0) (χ : (R × R)ˣ →* Circle) {JA : Matrix α α (R × R)}
    {JB : Matrix β β (R × R)} (hA : IsHerm (swapA R) JA) (hB : IsHerm (swapA R) JB) (σ : κ ≃ α × β) (ψ : AddChar R ℂ) :
    IsSplitting (sbClass R) ψ (splitDarboux hA hB σ) (actB (swapA R)) (splitOm m χ JB σ) where
  pres g _ hφ := splitOm_mem_SB m χ JB σ g hφ
  impl g w φ _ := splitOm_rho m χ hA hB σ ψ g w φ
  adm _ _ _ := Set.mem_univ _

theorem IsHerm.dbl {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E} {J : Matrix β β E} (h : IsHerm c J) :
    IsHerm c (dbl J) := by
  refine ⟨fun i j => ?_, ?_⟩
  · change c (Matrix.fromBlocks J 0 0 (-J) j i) = Matrix.fromBlocks J 0 0 (-J) i j
    rcases i with i | i <;> rcases j with j | j <;> simp [h.1]
  · change IsUnit (Matrix.fromBlocks J 0 0 (-J)).det
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
    exact h.2.mul ((isUnit_neg_one.pow _).mul h.2)

def dblNum (σ : κ ≃ α × β) : κ ⊕ κ ≃ α × (β ⊕ β) := (σ.sumCongr σ).trans (Equiv.prodSumDistrib α β β).symm

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] in
theorem flat_fromCols (σ : κ ≃ α × β) (X Y : Matrix α β R) :
    flat (dblNum σ) (fromCols X Y) = Sum.elim (flat σ X) (flat σ Y) := by
  funext k
  cases k <;> rfl

theorem isDblCoord_split {JA : Matrix α α (R × R)} {JB : Matrix β β (R × R)} (hA : IsHerm (swapA R) JA)
    (hB : IsHerm (swapA R) JB) (σ : κ ≃ α × β) :
    IsDblCoord (swapA R) (1, -1) JA JB (splitDarboux hA hB σ) (splitDarboux hA hB.dbl (dblNum σ)) := by
  intro w₁ w₂
  have hd : (cmp₁ (dbl JB))ᵀ = fromBlocks (cmp₁ JB)ᵀ 0 0 (-(cmp₁ JB)ᵀ) := by
    ext (i | i) (j | j) <;> simp [dbl]
  simp only [splitDarboux_e]
  rw [hd]
  simp only [Matrix.fromCols_map, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks, flat_fromCols,
    Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg, map_neg]
  try rfl

theorem det_siegel {JB : Matrix β β (R × R)} (hB : IsHerm (swapA R) JB) (p : UG (swapA R) (dbl JB))
    (t : Matrix β β (R × R))
    (h : ((p : GL (β ⊕ β) (R × R)) : Matrix (β ⊕ β) (β ⊕ β) (R × R)) * (diagCols β : Matrix (β ⊕ β) β (R × R)) =
      (diagCols β : Matrix (β ⊕ β) β (R × R)) * t) :
    (ugFst _ p).val * (diagCols β : Matrix (β ⊕ β) β R) = (diagCols β : Matrix (β ⊕ β) β R) * cmp₁ t ∧
      (ugFst _ p).val.det * (cmp₂ t).det = (cmp₁ t).det := by
  have hD1 : (diagCols β : Matrix (β ⊕ β) β (R × R)).map (RingHom.fst R R) = diagCols β := by
    rw [diagCols, diagCols, Matrix.fromRows_map, Matrix.map_one _ (map_zero _) (map_one _)]
  have hD2 : (diagCols β : Matrix (β ⊕ β) β (R × R)).map (RingHom.snd R R) = diagCols β := by
    rw [diagCols, diagCols, Matrix.fromRows_map, Matrix.map_one _ (map_zero _) (map_one _)]
  have h1 := congrArg (fun M => M.map (RingHom.fst R R)) h
  have h2 := congrArg (fun M => M.map (RingHom.snd R R)) h
  simp only [Matrix.map_mul] at h1 h2
  rw [hD1] at h1
  rw [hD2] at h2
  have e1 : (ugFst _ p).val * diagCols β = diagCols β * cmp₁ t := by rw [ugFst_val]; exact h1
  have e2 : cmp₂ ((p : GL (β ⊕ β) (R × R)) : Matrix (β ⊕ β) (β ⊕ β) (R × R)) * diagCols β = diagCols β * cmp₂ t := h2
  refine ⟨e1, ?_⟩
  obtain ⟨a, b, c, d, hP⟩ : ∃ a b c d, (ugFst (dbl JB) p).val = fromBlocks a b c d :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks _).symm⟩

  have hdc : (diagCols β : Matrix (β ⊕ β) β R) = Matrix.fromRows 1 1 := rfl
  have e1' : fromBlocks a b c d * (Matrix.fromRows 1 1 : Matrix (β ⊕ β) β R) = Matrix.fromRows 1 1 * cmp₁ t := by
    rw [← hP, ← hdc]; exact e1
  rw [Matrix.fromBlocks_mul_fromRows] at e1'
  obtain ⟨ha, hc⟩ := Matrix.fromRows_inj (e1'.trans (Matrix.fromRows_mul (1 : Matrix β β R) 1 (cmp₁ t)))
  simp only [Matrix.mul_one, Matrix.one_mul] at ha hc

  have hS : fromBlocks a b c d * fromBlocks (1 : Matrix β β R) 0 1 1 =
      fromBlocks (1 : Matrix β β R) 0 1 1 * fromBlocks (cmp₁ t) b 0 (d - b) := by
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.one_mul, Matrix.zero_mul, zero_add]
    rw [ha, hc, add_sub_cancel]
  have hdetP : (ugFst (dbl JB) p).val.det = (cmp₁ t).det * (d - b).det := by
    have hd := congrArg Matrix.det hS
    simp only [Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one, one_mul,
      Matrix.det_fromBlocks_zero₂₁] at hd
    rw [hP, hd]

  have rel := ug_rel p
  have hK : (ugFst (dbl JB) p).valᵀ * (cmp₁ (dbl JB) * (diagCols β : Matrix (β ⊕ β) β R)) * cmp₂ t = cmp₁ (dbl JB) * (diagCols β : Matrix (β ⊕ β) β R) := by
    calc (ugFst (dbl JB) p).valᵀ * (cmp₁ (dbl JB) * (diagCols β : Matrix (β ⊕ β) β R)) * cmp₂ t
        = (ugFst (dbl JB) p).valᵀ * cmp₁ (dbl JB) * ((diagCols β : Matrix (β ⊕ β) β R) * cmp₂ t) := by simp only [Matrix.mul_assoc]
      _ = (ugFst (dbl JB) p).valᵀ * cmp₁ (dbl JB) * (cmp₂ ((p : GL (β ⊕ β) (R × R)) : Matrix (β ⊕ β) (β ⊕ β) (R × R)) * (diagCols β : Matrix (β ⊕ β) β R)) := congrArg (_ * ·) e2.symm
      _ = ((ugFst (dbl JB) p).valᵀ * cmp₁ (dbl JB) * cmp₂ ((p : GL (β ⊕ β) (R × R)) : Matrix (β ⊕ β) (β ⊕ β) (R × R))) * (diagCols β : Matrix (β ⊕ β) β R) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [rel]
  have hDB : cmp₁ (dbl JB) * (diagCols β : Matrix (β ⊕ β) β R) = fromRows (cmp₁ JB) (-cmp₁ JB) := by
    have hb : cmp₁ (dbl JB) = fromBlocks (cmp₁ JB) 0 0 (-cmp₁ JB) := by
      ext (i | i) (j | j) <;> simp [dbl]
    rw [hb, hdc, Matrix.fromBlocks_mul_fromRows]
    simp
  rw [hDB, hP, Matrix.fromBlocks_transpose, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul] at hK
  obtain ⟨-, hK2⟩ := Matrix.fromRows_inj hK
  have hY : (d - b)ᵀ * cmp₁ JB * cmp₂ t = cmp₁ JB := by
    calc (d - b)ᵀ * cmp₁ JB * cmp₂ t = -((bᵀ * cmp₁ JB + dᵀ * -cmp₁ JB) * cmp₂ t) := by
          rw [Matrix.transpose_sub]; noncomm_ring
      _ = cmp₁ JB := by rw [hK2, neg_neg]
  have hdetY : (d - b).det * (cmp₂ t).det = 1 := by
    have hd := congrArg Matrix.det hY
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose] at hd
    refine hB.isUnit_cmp₁.mul_left_cancel ?_
    rw [mul_one]
    calc (cmp₁ JB).det * ((d - b).det * (cmp₂ t).det) = (d - b).det * (cmp₁ JB).det * (cmp₂ t).det := by ring
      _ = _ := hd
  rw [hdetP, mul_assoc, hdetY, mul_one]

end GlobalTheory.WeilM

end
