import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocHomAlgebraMap
open IsLocalRing

namespace GlobalTheory.AbhyankarLocal

set_option maxHeartbeats 1000000 in
theorem exists_frac_closure : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D] (ψ : D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π : Polynomial S)), Irreducible π → 0 < e → ∀ [IsDomain D] [IsDiscreteValuationRing D] (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal] (w : Localization.AtPrime Q), ∃ x z : Localization.AtPrime Q, x ∈ Subring.closure (Set.range (GlobalTheory.AbhyankarLocal.locHom Q) ∪ {algebraMap D (Localization.AtPrime Q) (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)))}) ∧ z ∈ Subring.closure (Set.range (GlobalTheory.AbhyankarLocal.locHom Q) ∪ {algebraMap D (Localization.AtPrime Q) (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)))}) ∧ z ∈ nonZeroDivisors (Localization.AtPrime Q) ∧ z * w = x := by
  intro S K L _ _ _ _ _ _ _ _ _ _ _ _ π e D _ _ ψ _ _ _ _ Q _ w

  have hS : ∀ r : S, algebraMap D (Localization.AtPrime Q) (algebraMap S D r) =
      locHom Q (algebraMap _ _ (algebraMap S (integralClosure S L) r)) := by
    intro r
    rw [locHom_algebraMap, IsScalarTower.algebraMap_apply D (integralClosure D (TensorProduct S D L))
      (Localization.AtPrime Q)]
    congr 1
    apply Subtype.ext
    simp only [toNorm_coe, Subalgebra.coe_algebraMap, Algebra.TensorProduct.algebraMap_apply]
    rw [Algebra.algebraMap_eq_smul_one r, Algebra.algebraMap_eq_smul_one r]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    rw [TensorProduct.smul_tmul]
  have hD : ∀ d : D, algebraMap D (Localization.AtPrime Q) d ∈ Subring.closure (Set.range (GlobalTheory.AbhyankarLocal.locHom Q) ∪ {algebraMap D (Localization.AtPrime Q) (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)))}) := by
    intro d
    rw [← ψ.symm_apply_apply d]
    generalize ψ d = a
    have hd : a ∈ Algebra.adjoin S ({AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)} : Set _) := by
      rw [AdjoinRoot.adjoinRoot_eq_top]; trivial
    induction hd using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact Subring.subset_closure (Or.inr rfl)
    | algebraMap r =>
      rw [AlgEquiv.commutes, hS]
      exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
    | add x y _ _ hx hy => rw [map_add, map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul, map_mul]; exact mul_mem hx hy

  have hT : ∀ u : TensorProduct S D (integralClosure S L), ∃ b : integralClosure D (TensorProduct S D L),
      (b : TensorProduct S D L) = Algebra.TensorProduct.map (AlgHom.id S D) (integralClosure S L).val u ∧
      algebraMap _ (Localization.AtPrime Q) b ∈ Subring.closure (Set.range (GlobalTheory.AbhyankarLocal.locHom Q) ∪ {algebraMap D (Localization.AtPrime Q) (ψ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π : Polynomial S)))}) := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp, by simp⟩
    | tmul d o =>
      refine ⟨algebraMap D _ d * toNorm S L D o, ?_, ?_⟩
      · simp [toNorm_coe, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
      · rw [map_mul, ← IsScalarTower.algebraMap_apply, ← locHom_algebraMap]
        exact mul_mem (hD d) (Subring.subset_closure (Or.inl ⟨_, rfl⟩))
    | add u v hu hv =>
      obtain ⟨b1, h1, m1⟩ := hu
      obtain ⟨b2, h2, m2⟩ := hv
      exact ⟨b1 + b2, by simp [h1, h2], by rw [map_add]; exact add_mem m1 m2⟩
  have hI : ∀ y : TensorProduct S D L, ∃ σ : S, σ ≠ 0 ∧ ∃ u : TensorProduct S D (integralClosure S L),
      Algebra.TensorProduct.map (AlgHom.id S D) (integralClosure S L).val u = σ • y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
    | tmul d l =>
      have hl : IsAlgebraic S l := (IsFractionRing.isAlgebraic_iff S K L).2 (Algebra.IsAlgebraic.isAlgebraic l)
      obtain ⟨σ, hσ, hint⟩ := hl.exists_integral_multiple
      exact ⟨σ, hσ, d ⊗ₜ ⟨σ • l, hint⟩, by simp [TensorProduct.tmul_smul]⟩
    | add y1 y2 h1 h2 =>
      obtain ⟨σ1, n1, u1, e1⟩ := h1
      obtain ⟨σ2, n2, u2, e2⟩ := h2
      refine ⟨σ1 * σ2, mul_ne_zero n1 n2, σ2 • u1 + σ1 • u2, ?_⟩
      rw [map_add, map_smul, map_smul, e1, e2, smul_add, smul_smul, smul_smul, mul_comm σ1 σ2]
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl w
  obtain ⟨σ1, n1, u1, e1⟩ := hI (b : TensorProduct S D L)
  obtain ⟨σ2, n2, u2, e2⟩ := hI ((s : integralClosure D (TensorProduct S D L)) : TensorProduct S D L)
  obtain ⟨bb, hbb, mb⟩ := hT (σ2 • u1)
  obtain ⟨ss, hss, ms⟩ := hT (σ1 • u2)
  set a : integralClosure D (TensorProduct S D L) := algebraMap D _ (algebraMap S D (σ1 * σ2)) with ha
  have hcoe : ∀ y : integralClosure D (TensorProduct S D L), ((a * y : integralClosure D (TensorProduct S D L)) : TensorProduct S D L) = (σ1 * σ2) • (y : TensorProduct S D L) := by
    intro y
    rw [ha, Subalgebra.coe_mul, Subalgebra.coe_algebraMap, ← IsScalarTower.algebraMap_apply, Algebra.smul_def]
  have hbb' : bb = a * b := by
    apply Subtype.ext
    rw [hcoe, hbb, map_smul, e1, smul_smul, mul_comm σ2 σ1]
  have hss' : ss = a * s := by
    apply Subtype.ext
    rw [hcoe, hss, map_smul, e2, smul_smul]
  have hL : algebraMap S L (σ1 * σ2) ≠ 0 := by
    intro h
    rw [IsScalarTower.algebraMap_apply S K L, map_eq_zero, IsFractionRing.to_map_eq_zero_iff] at h
    exact mul_ne_zero n1 n2 h
  have hU : IsUnit (algebraMap S (TensorProduct S D L) (σ1 * σ2)) := by
    rw [← (Algebra.TensorProduct.includeRight (R := S) (A := D) (B := L)).commutes]
    exact (IsUnit.mk0 _ hL).map _
  have haN : a ∈ nonZeroDivisors (integralClosure D (TensorProduct S D L)) := by
    rw [mem_nonZeroDivisors_iff_right]
    intro y hy
    have := congrArg Subtype.val hy
    rw [mul_comm, hcoe, Algebra.smul_def, ZeroMemClass.coe_zero] at this
    exact Subtype.ext (by simpa using (hU.mul_right_eq_zero).1 this)
  refine ⟨algebraMap _ _ bb, algebraMap _ _ ss, mb, ms, ?_, ?_⟩
  · rw [hss', map_mul]
    have h1 : algebraMap _ (Localization.AtPrime Q) a ∈ nonZeroDivisors (Localization.AtPrime Q) :=
      IsLocalization.map_nonZeroDivisors_le Q.primeCompl (Localization.AtPrime Q)
        (Submonoid.mem_map_of_mem (algebraMap _ (Localization.AtPrime Q)) haN)
    exact mul_mem h1 (IsLocalization.map_units (Localization.AtPrime Q) s).mem_nonZeroDivisors
  · rw [hss', hbb', map_mul, map_mul, mul_assoc, IsLocalization.mk'_spec']

end GlobalTheory.AbhyankarLocal
