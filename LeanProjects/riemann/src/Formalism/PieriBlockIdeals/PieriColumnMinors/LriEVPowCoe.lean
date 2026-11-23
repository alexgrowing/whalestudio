import Formalism.PieriBlockIdeals.PieriColumnMinors.XiOfDepth2

open MvPolynomial

noncomputable section

namespace Formalism.CohomologicalDescent.LR

open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

theorem lri_LevZ_le (p q w : ℕ) (lam2 : Fin q → ℕ) :
    LevZ p q w lam2 ≤ (weyl ℤ (p + q) (p + q) le_rfl (LD.blockWt p q w lam2)).map (intQ (p + q) (p + q)) := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨ω, rfl⟩
  refine ⟨applyWord ℤ (liftWord p ω) (hw ℤ le_rfl (LD.blockWt p q w lam2)), Submodule.subset_span ⟨liftWord p ω, rfl⟩, ?_⟩
  rw [lrc_intQ_apply, ← lclosedeq_applyWord_map, lclosedeq_hw_map]

theorem MW_le_MV (p q w : ℕ) (lam2 : Fin q → ℕ) (u : (rationalBlockModuleSetting p q w lam2).W) (hu : u ∈ MW p q w lam2) :
    (u : VQ p q w lam2) ∈ MV p q w lam2 :=
  lri_LevZ_le p q w lam2 hu

theorem lri_EV_pow_coe (p q w : ℕ) (lam2 : Fin q → ℕ) (a b : Fin p ⊕ Fin q) (k : ℕ) (x : VQ p q w lam2) :
    ((((EV p q w lam2 a b) ^ k) x : VQ p q w lam2) : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) =
      ((der (p + q) (p + q) (idx p q a) (idx p q b) : Module.End ℚ _) ^ k) (x : MvPolynomial _ ℚ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, EV_coe, ih, pow_succ', Module.End.mul_apply]
    rfl

theorem lri_hL (p q w : ℕ) (lam2 : Fin q → ℕ) (v : Fin q × Fin p) (k : ℕ) (x : VQ p q w lam2)
    (hx : x ∈ MV p q w lam2) :
    ((k.factorial : ℚ)⁻¹) • (((rationalBlockModuleSetting p q w lam2).f v) ^ k) x ∈ MV p q w lam2 := by
  rw [mem_MV] at hx ⊢
  obtain ⟨y, hy, hyx⟩ := hx
  have hne : Fin.natAdd p v.1 ≠ Fin.castAdd q v.2 := by
    intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_natAdd, Fin.val_castAdd] at h'
    have := v.2.isLt
    omega
  have e : (((((k.factorial : ℚ)⁻¹) • (((rationalBlockModuleSetting p q w lam2).f v) ^ k) x : VQ p q w lam2)) :
      MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) =
      rowDiv ℚ (Fin.natAdd p v.1) (Fin.castAdd q v.2) k (x : MvPolynomial _ ℚ) := by
    rw [der_pow _ _ hne, Submodule.coe_smul]
    congr 1
    exact lri_EV_pow_coe p q w lam2 (Sum.inr v.1) (Sum.inl v.2) k x
  rw [e, ← hyx, lrc_intQ_apply, lclosedeq_rowDiv_map]
  exact ⟨_, weylRowDivStable ℤ _ _ le_rfl _ _ _ k y hy, rfl⟩

theorem lri_coe_zsmul (p q w : ℕ) (lam2 : Fin q → ℕ) (m : ℤ) (u : (rationalBlockModuleSetting p q w lam2).W) :
    ((m • u : (rationalBlockModuleSetting p q w lam2).W) : VQ p q w lam2) = m • (u : VQ p q w lam2) := by
  simp

theorem deltaAll_le (l : ℕ) (hl : l.Prime) (p q w : ℕ) (lam2 : Fin q → ℕ) :
    DeltaAll (rationalBlockModuleSetting p q w lam2) (DelLR l hl p q w lam2) ≤ locSpan l hl (MV p q w lam2) := by
  refine iSup_le fun n => Submodule.span_le.mpr ?_
  rintro x ⟨m, u, hu, rfl⟩
  obtain ⟨m₀, hm₀, hmu⟩ := (mem_locSpan l hl _ u).1 hu
  have h1 := MW_le_MV p q w lam2 _ hmu
  rw [lri_coe_zsmul] at h1
  have h2 := Fs_div_mem (rationalBlockModuleSetting p q w lam2) (MV p q w lam2) (lri_hL p q w lam2) m _ h1
  refine ⟨m₀, hm₀, ?_⟩
  have e : ((Symmetrization.mfact m : ℚ)⁻¹) • (rationalBlockModuleSetting p q w lam2).Fs m (m₀ • (u : VQ p q w lam2)) =
      m₀ • (((Symmetrization.mfact m : ℚ)⁻¹) • (rationalBlockModuleSetting p q w lam2).Fs m (u : VQ p q w lam2)) := by
    rw [map_zsmul, smul_comm]
  rw [← e]
  exact h2

theorem lri_intQ_zsmul (r : ℕ) (z : ℤ) (x : MvPolynomial (Fin r × Fin r) ℤ) :
    intQ r r (z • x) = (z : ℚ) • intQ r r x := by
  rw [map_zsmul, Int.cast_smul_eq_zsmul]

theorem lri_intQ_inj (r : ℕ) : Function.Injective (intQ r r) := by
  intro x y h
  rw [lrc_intQ_apply, lrc_intQ_apply] at h
  exact MvPolynomial.map_injective _ (RingHom.injective_int (Int.castRingHom ℚ)) h

theorem mem_dual (l : ℕ) (hl : l.Prime) (p q w : ℕ) (lam2 : Fin q → ℕ) (ha : Antitone lam2) (hb : ∀ b, lam2 b ≤ w)
    (x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℤ) (hx : x ∈ dualWeyl ℤ (p + q) (p + q) (LD.blockWt p q w lam2))
    (hx' : intQ _ _ x ∈ dualWeyl ℚ (p + q) (p + q) (LD.blockWt p q w lam2)) :
    (⟨intQ _ _ x, hx'⟩ : VQ p q w lam2) ∈
      (formB p q w lam2).dualSubmodule (DeltaAll (rationalBlockModuleSetting p q w lam2) (DelLR l hl p q w lam2)) := by
  have hanti := LD.ld_blockWt_anti p q w lam2 ha hb
  rw [LinearMap.BilinForm.mem_dualSubmodule]
  intro y hy
  obtain ⟨m, hm, hmy⟩ := (mem_locSpan l hl _ y).1 (deltaAll_le l hl p q w lam2 hy)
  rw [mem_MV] at hmy
  obtain ⟨y', hy', hy'e⟩ := hmy
  obtain ⟨z, hz⟩ := fock_int (p + q) _ hanti x hx y' hy'
  rw [mem_one_iff, zl_mem_iff hl]
  refine ⟨m, hm, z, ?_⟩
  have hc := (hw_norm_pos (LD.blockWt p q w lam2)).ne'
  have e1 : (m : ℚ) * formB p q w lam2 ⟨intQ _ _ x, hx'⟩ y = formB p q w lam2 ⟨intQ _ _ x, hx'⟩ (m • y) := by
    rw [map_zsmul, zsmul_eq_mul]
  rw [e1, formB_apply]
  have e2 : (((m • y : VQ p q w lam2)) : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) = intQ _ _ y' := by
    rw [hy'e]
  rw [e2]
  change fockQ (intQ (p + q) (p + q) x) (intQ (p + q) (p + q) y') / _ = _
  rw [hz, mul_div_assoc, div_self hc, mul_one]

theorem concl (l : ℕ) (hl : l.Prime) (p q w : ℕ) (lam2 : Fin q → ℕ)
    (x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℤ)
    (hx' : intQ _ _ x ∈ dualWeyl ℚ (p + q) (p + q) (LD.blockWt p q w lam2)) (E : ℕ)
    (h : ((l : Zl l) ^ E) • (⟨intQ _ _ x, hx'⟩ : VQ p q w lam2) ∈
      DeltaAll (rationalBlockModuleSetting p q w lam2) (DelLR l hl p q w lam2)) :
    ∃ m : ℤ, ¬ (l : ℤ) ∣ m ∧ (m * (l : ℤ) ^ E) • x ∈ weyl ℤ (p + q) (p + q) le_rfl (LD.blockWt p q w lam2) := by
  obtain ⟨m, hm, hmv⟩ := (mem_locSpan l hl _ _).1 (deltaAll_le l hl p q w lam2 h)
  rw [mem_MV] at hmv
  obtain ⟨y, hy, hye⟩ := hmv
  refine ⟨m, hm, ?_⟩
  have e : intQ _ _ ((m * (l : ℤ) ^ E) • x) = intQ _ _ y := by
    rw [hye, lri_intQ_zsmul]
    simp only [Submodule.coe_smul_of_tower, lrc_smul_def]
    rw [← Int.cast_smul_eq_zsmul ℚ m, smul_smul]
    congr 1
    push_cast
    rfl
  rw [lri_intQ_inj _ e]
  exact hy

theorem wt_of_hom (p q w : ℕ) (lam2 : Fin q → ℕ) (x : MvPolynomial (Fin (p + q) × Fin (p + q)) ℤ)
    (hx' : intQ _ _ x ∈ dualWeyl ℚ (p + q) (p + q) (LD.blockWt p q w lam2)) (μ : Fin (p + q) → ℕ)
    (hμ : IsWeightedHomogeneous (rowW (p + q) (p + q)) x μ) :
    (⟨intQ _ _ x, hx'⟩ : VQ p q w lam2) ∈ (rationalBlockModuleSetting p q w lam2).wt fun a => (μ (idx p q a) : ℤ) := by
  refine (real_weight p q w lam2 _ μ).1 ?_
  intro d hd
  apply hμ
  intro h0
  apply hd
  change coeff d (intQ _ _ x) = 0
  rw [lrc_intQ_apply, coeff_map, h0, map_zero]

theorem dominant_xi {p q : ℕ} (ξ : Fin (p + q) → ℤ) (hξ : Antitone ξ) (α : Fin p) (b : Fin q) :
    0 ≤ xiOf ξ (Pi.single (Sum.inl α) 1 - Pi.single (Sum.inr b) 1) := by
  show 0 ≤ ∑ a, ξ (idx p q a) * ((Pi.single (Sum.inl α) 1 - Pi.single (Sum.inr b) 1 : Fin p ⊕ Fin q → ℤ) a)
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  refine sub_nonneg.mpr (hξ ?_)
  show Fin.castAdd q α ≤ Fin.natAdd p b
  rw [Fin.le_def]
  simp only [Fin.val_castAdd, Fin.val_natAdd]
  omega

end Formalism.CohomologicalDescent.LR
