import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalC

open MvPolynomial Formalism.GradedWeylDivisibility TensorProduct

noncomputable section
namespace GlobalTheory.LeviCut

theorem mem_range_map_of_flat {M1 M2 : Type} [AddCommGroup M1] [AddCommGroup M2]
    (N1 : Submodule ℤ M1) (N2 : Submodule ℤ M2) [Module.Flat ℤ (M2 ⧸ N2)] (z : M1 ⊗[ℤ] M2)
    (h1 : z ∈ LinearMap.range (LinearMap.lTensor M1 N2.subtype))
    (h2 : z ∈ LinearMap.range (LinearMap.rTensor M2 N1.subtype)) :
    z ∈ LinearMap.range (TensorProduct.map N1.subtype N2.subtype) := by
  obtain ⟨u, hu⟩ := h1
  obtain ⟨w, rfl⟩ := h2
  have hw : LinearMap.lTensor N1 N2.mkQ w = 0 := by
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := M2 ⧸ N2) N1.subtype N1.injective_subtype
    rw [map_zero, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
      LinearMap.comp_apply, ← hu, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
    have : N2.mkQ ∘ₗ N2.subtype = 0 := by ext x; simp
    rw [this, LinearMap.lTensor_zero, LinearMap.zero_apply]
  obtain ⟨w', hw'⟩ := (lTensor_exact N1 (LinearMap.exact_subtype_mkQ N2) N2.mkQ_surjective w).1 hw
  refine ⟨w', ?_⟩
  rw [← hw', ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor]

theorem flat_quot_dualWeyl (q : ℕ) (ν : Fin q → ℕ) :
    Module.Flat ℤ (MvPolynomial (Fin q × Fin q) ℤ ⧸ dualWeyl ℤ q q ν) := by
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨⟨c, hc⟩, hcx⟩ := (Submodule.mem_torsion_iff x).1 hx
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective _ x
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have : c • f ∈ dualWeyl ℤ q q ν := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]; simpa using hcx
  rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact dualWeylSat ℤ q q ν c f hc0 this

theorem bidet_map' {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {r n K : ℕ} (sz : Fin K → ℕ)
    (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r) :
    map φ (bideterminant R sz hsz I) = bideterminant S sz hsz I := by
  unfold bideterminant initMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp

def psiR (p q : ℕ) (v : Fin (p + q) × Fin (p + q)) :
    MvPolynomial (Fin q × Fin q) (MvPolynomial (Fin p × Fin p) ℤ) :=
  Fin.addCases (motive := fun _ => MvPolynomial (Fin q × Fin q) (MvPolynomial (Fin p × Fin p) ℤ))
    (fun a => Fin.addCases (motive := fun _ => MvPolynomial (Fin q × Fin q) (MvPolynomial (Fin p × Fin p) ℤ))
      (fun s => C (X (a, s))) (fun _ => 0) v.2)
    (fun b => Fin.addCases (motive := fun _ => MvPolynomial (Fin q × Fin q) (MvPolynomial (Fin p × Fin p) ℤ))
      (fun _ => 0) (fun t => X (b, t)) v.2) v.1

def psiL (p q : ℕ) (v : Fin (p + q) × Fin (p + q)) :
    MvPolynomial (Fin p × Fin p) (MvPolynomial (Fin q × Fin q) ℤ) :=
  Fin.addCases (motive := fun _ => MvPolynomial (Fin p × Fin p) (MvPolynomial (Fin q × Fin q) ℤ))
    (fun a => Fin.addCases (motive := fun _ => MvPolynomial (Fin p × Fin p) (MvPolynomial (Fin q × Fin q) ℤ))
      (fun s => X (a, s)) (fun _ => 0) v.2)
    (fun b => Fin.addCases (motive := fun _ => MvPolynomial (Fin p × Fin p) (MvPolynomial (Fin q × Fin q) ℤ))
      (fun _ => 0) (fun t => C (X (b, t))) v.2) v.1

def phiR (p q : ℕ) : MvPolynomial (Fin q × Fin q) (MvPolynomial (Fin p × Fin p) ℤ) →+*
    MvPolynomial (Fin p × Fin p) ℤ ⊗[ℤ] MvPolynomial (Fin q × Fin q) ℤ :=
  eval₂Hom Algebra.TensorProduct.includeLeftRingHom (fun v => 1 ⊗ₜ X v)

def phiL (p q : ℕ) : MvPolynomial (Fin p × Fin p) (MvPolynomial (Fin q × Fin q) ℤ) →+*
    MvPolynomial (Fin p × Fin p) ℤ ⊗[ℤ] MvPolynomial (Fin q × Fin q) ℤ :=
  eval₂Hom (Algebra.TensorProduct.includeRight : MvPolynomial (Fin q × Fin q) ℤ →ₐ[ℤ] _).toRingHom
    (fun v => X v ⊗ₜ 1)

theorem phiR_psiR (p q : ℕ) (f : MvPolynomial (Fin (p + q) × Fin (p + q)) ℤ) :
    phiR p q (aeval (psiR p q) (map (C : ℤ →+* MvPolynomial (Fin p × Fin p) ℤ) f)) = resT ℤ p q f := by
  have : (phiR p q).comp ((aeval (psiR p q)).toRingHom.comp (map (C : ℤ →+* MvPolynomial (Fin p × Fin p) ℤ))) = (resT ℤ p q).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact RingHom.congr_fun (RingHom.ext_int (((phiR p q).comp ((aeval (psiR p q)).toRingHom.comp (map (C : ℤ →+* MvPolynomial (Fin p × Fin p) ℤ)))).comp C) ((resT ℤ p q).toRingHom.comp C)) r
    rintro ⟨i, j⟩
    induction i using Fin.addCases <;> induction j using Fin.addCases <;>
        (simp [phiR, psiR, resT, resVarT])
  exact DFunLike.congr_fun this f

theorem phiL_psiL (p q : ℕ) (f : MvPolynomial (Fin (p + q) × Fin (p + q)) ℤ) :
    phiL p q (aeval (psiL p q) (map (C : ℤ →+* MvPolynomial (Fin q × Fin q) ℤ) f)) = resT ℤ p q f := by
  have : (phiL p q).comp ((aeval (psiL p q)).toRingHom.comp (map (C : ℤ →+* MvPolynomial (Fin q × Fin q) ℤ))) = (resT ℤ p q).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact RingHom.congr_fun (RingHom.ext_int (((phiL p q).comp ((aeval (psiL p q)).toRingHom.comp (map (C : ℤ →+* MvPolynomial (Fin q × Fin q) ℤ)))).comp C) ((resT ℤ p q).toRingHom.comp C)) r
    rintro ⟨i, j⟩
    induction i using Fin.addCases <;> induction j using Fin.addCases <;>
        (simp [phiL, psiL, resT, resVarT])
  exact DFunLike.congr_fun this f

theorem phiR_map (p q : ℕ) (h : MvPolynomial (Fin q × Fin q) ℤ) :
    phiR p q (map (C : ℤ →+* MvPolynomial (Fin p × Fin p) ℤ) h) = 1 ⊗ₜ h := by
  have : (phiR p q).comp (map (C : ℤ →+* MvPolynomial (Fin p × Fin p) ℤ)) =
      (Algebra.TensorProduct.includeRight : _ →ₐ[ℤ] MvPolynomial (Fin p × Fin p) ℤ ⊗[ℤ] _).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact RingHom.congr_fun (RingHom.ext_int (((phiR p q).comp (map (C : ℤ →+* MvPolynomial (Fin p × Fin p) ℤ))).comp C) (((Algebra.TensorProduct.includeRight : _ →ₐ[ℤ] MvPolynomial (Fin p × Fin p) ℤ ⊗[ℤ] _).toRingHom).comp C)) r
    intro v; (simp [phiR])
  exact DFunLike.congr_fun this h

theorem phiL_map (p q : ℕ) (h : MvPolynomial (Fin p × Fin p) ℤ) :
    phiL p q (map (C : ℤ →+* MvPolynomial (Fin q × Fin q) ℤ) h) = h ⊗ₜ 1 := by
  have : (phiL p q).comp (map (C : ℤ →+* MvPolynomial (Fin q × Fin q) ℤ)) =
      (Algebra.TensorProduct.includeLeft : _ →ₐ[ℤ] _ ⊗[ℤ] MvPolynomial (Fin q × Fin q) ℤ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact RingHom.congr_fun (RingHom.ext_int (((phiL p q).comp (map (C : ℤ →+* MvPolynomial (Fin q × Fin q) ℤ))).comp C) (((Algebra.TensorProduct.includeLeft : _ →ₐ[ℤ] _ ⊗[ℤ] MvPolynomial (Fin q × Fin q) ℤ).toRingHom).comp C)) r
    intro v; (simp [phiL])
  exact DFunLike.congr_fun this h

theorem mul_mem_range_lTensor {A B : Type} [CommRing A] [CommRing B] (N : Submodule ℤ B) (u : A)
    (x : A ⊗[ℤ] B) (hx : x ∈ LinearMap.range (LinearMap.lTensor A N.subtype)) :
    (u ⊗ₜ (1 : B)) * x ∈ LinearMap.range (LinearMap.lTensor A N.subtype) := by
  obtain ⟨w, rfl⟩ := hx
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a n => exact ⟨(u * a) ⊗ₜ n, by simp⟩
  | add x y hx hy => rw [map_add, mul_add]; exact add_mem hx hy

theorem mul_mem_range_rTensor {A B : Type} [CommRing A] [CommRing B] (N : Submodule ℤ A) (u : B)
    (x : A ⊗[ℤ] B) (hx : x ∈ LinearMap.range (LinearMap.rTensor B N.subtype)) :
    ((1 : A) ⊗ₜ u) * x ∈ LinearMap.range (LinearMap.rTensor B N.subtype) := by
  obtain ⟨w, rfl⟩ := hx
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul n b => exact ⟨n ⊗ₜ (u * b), by simp⟩
  | add x y hx hy => rw [map_add, mul_add]; exact add_mem hx hy

theorem resT_mem_lTensor (hS : SubstMem) (p q : ℕ) (ν : Fin (p + q) → ℕ)
    (f : MvPolynomial (Fin (p + q) × Fin (p + q)) ℤ) (hf : f ∈ dualWeyl ℤ (p + q) (p + q) ν) :
    resT ℤ p q f ∈ LinearMap.range (LinearMap.lTensor (MvPolynomial (Fin p × Fin p) ℤ)
      (dualWeyl ℤ q q (fun j => ν (Fin.natAdd p j))).subtype) := by
  have hg : aeval (psiR p q) (map (C : ℤ →+* MvPolynomial (Fin p × Fin p) ℤ) f) ∈
      dualWeyl (MvPolynomial (Fin p × Fin p) ℤ) q q (fun j => ν (Fin.natAdd p j)) := by
    refine hS (MvPolynomial (Fin p × Fin p) ℤ) q (p + q) (Fin.natAdd p) (Fin.strictMono_natAdd p) (psiR p q)
      ?_ ?_ ?_ ν _ (dualWeylMap ℤ _ C _ _ ν f hf)
    · intro a s; simp [psiR]
    · intro x s hx
      induction x using Fin.addCases with
      | left a => simp [psiR]
      | right b => exact absurd ⟨b, rfl⟩ hx
    · intro x y hy
      induction y using Fin.addCases with
      | right t => exact absurd ⟨t, rfl⟩ hy
      | left s =>
        induction x using Fin.addCases with
        | left a => exact ⟨X (a, s), by simp [psiR]⟩
        | right b => exact ⟨0, by simp [psiR]⟩
  rw [standardMonomialSpanDomain] at hg
  rw [← phiR_psiR]
  refine Submodule.span_induction (p := fun g _ => phiR p q g ∈ LinearMap.range
    (LinearMap.lTensor (MvPolynomial (Fin p × Fin p) ℤ) (dualWeyl ℤ q q (fun j => ν (Fin.natAdd p j))).subtype))
    ?_ ?_ ?_ ?_ hg
  · rintro g ⟨K, sz, hsz, I, hsh, rfl⟩
    rw [← bidet_map' (C : ℤ →+* MvPolynomial (Fin p × Fin p) ℤ), phiR_map]
    exact ⟨1 ⊗ₜ ⟨bideterminant ℤ sz hsz I, hsh ▸ bidetMem ℤ q q K sz hsz I⟩, rfl⟩
  · simp
  · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
  · intro u x _ hx
    rw [smul_eq_C_mul, map_mul]
    have : phiR p q (C u) = u ⊗ₜ 1 := by simp [phiR]
    rw [this]; exact mul_mem_range_lTensor _ u _ hx

theorem resT_mem_rTensor (hS : SubstMem) (p q : ℕ) (ν : Fin (p + q) → ℕ)
    (f : MvPolynomial (Fin (p + q) × Fin (p + q)) ℤ) (hf : f ∈ dualWeyl ℤ (p + q) (p + q) ν) :
    resT ℤ p q f ∈ LinearMap.range (LinearMap.rTensor (MvPolynomial (Fin q × Fin q) ℤ)
      (dualWeyl ℤ p p (fun i => ν (Fin.castAdd q i))).subtype) := by
  have hg : aeval (psiL p q) (map (C : ℤ →+* MvPolynomial (Fin q × Fin q) ℤ) f) ∈
      dualWeyl (MvPolynomial (Fin q × Fin q) ℤ) p p (fun i => ν (Fin.castAdd q i)) := by
    refine hS (MvPolynomial (Fin q × Fin q) ℤ) p (p + q) (Fin.castAdd q) (Fin.strictMono_castAdd q) (psiL p q)
      ?_ ?_ ?_ ν _ (dualWeylMap ℤ _ C _ _ ν f hf)
    · intro a s; simp [psiL]
    · intro x s hx
      induction x using Fin.addCases with
      | left a => exact absurd ⟨a, rfl⟩ hx
      | right b => simp [psiL]
    · intro x y hy
      induction y using Fin.addCases with
      | left s => exact absurd ⟨s, rfl⟩ hy
      | right t =>
        induction x using Fin.addCases with
        | left a => exact ⟨0, by simp [psiL]⟩
        | right b => exact ⟨X (b, t), by simp [psiL]⟩
  rw [standardMonomialSpanDomain] at hg
  rw [← phiL_psiL]
  refine Submodule.span_induction (p := fun g _ => phiL p q g ∈ LinearMap.range
    (LinearMap.rTensor (MvPolynomial (Fin q × Fin q) ℤ) (dualWeyl ℤ p p (fun i => ν (Fin.castAdd q i))).subtype))
    ?_ ?_ ?_ ?_ hg
  · rintro g ⟨K, sz, hsz, I, hsh, rfl⟩
    rw [← bidet_map' (C : ℤ →+* MvPolynomial (Fin q × Fin q) ℤ), phiL_map]
    exact ⟨⟨bideterminant ℤ sz hsz I, hsh ▸ bidetMem ℤ p p K sz hsz I⟩ ⊗ₜ 1, rfl⟩
  · simp
  · intro x y _ _ hx hy; rw [map_add]; exact add_mem hx hy
  · intro u x _ hx
    rw [smul_eq_C_mul, map_mul]
    have : phiL p q (C u) = 1 ⊗ₜ u := by simp [phiL]
    rw [this]; exact mul_mem_range_rTensor _ u _ hx

def toQ (p q : ℕ) : MvPolynomial (Fin p × Fin p) ℤ ⊗[ℤ] MvPolynomial (Fin q × Fin q) ℤ →+*
    MvPolynomial (Fin p × Fin p) ℚ ⊗[ℚ] MvPolynomial (Fin q × Fin q) ℚ :=
  (Algebra.TensorProduct.lift
    (RingHom.toIntAlgHom ((Algebra.TensorProduct.includeLeftRingHom).comp (map (Int.castRingHom ℚ))))
    (RingHom.toIntAlgHom ((Algebra.TensorProduct.includeRight :
      MvPolynomial (Fin q × Fin q) ℚ →ₐ[ℚ] MvPolynomial (Fin p × Fin p) ℚ ⊗[ℚ] _).toRingHom.comp
        (map (Int.castRingHom ℚ))))
    (fun _ _ => Commute.all _ _)).toRingHom

theorem toQ_tmul (p q : ℕ) (a : MvPolynomial (Fin p × Fin p) ℤ) (b : MvPolynomial (Fin q × Fin q) ℤ) :
    toQ p q (a ⊗ₜ b) = intQ p p a ⊗ₜ intQ q q b := by
  simp [toQ, intQ, RingHom.toIntAlgHom_apply]

theorem toQ_resT (p q : ℕ) (f : MvPolynomial (Fin (p + q) × Fin (p + q)) ℤ) :
    toQ p q (resT ℤ p q f) = resT ℚ p q (intQ (p + q) (p + q) f) := by
  have : (toQ p q).comp (resT ℤ p q).toRingHom = (resT ℚ p q).toRingHom.comp (map (Int.castRingHom ℚ)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      exact RingHom.congr_fun (RingHom.ext_int (((toQ p q).comp (resT ℤ p q).toRingHom).comp C)
        (((resT ℚ p q).toRingHom.comp (map (Int.castRingHom ℚ))).comp C)) r
    rintro ⟨i, j⟩
    induction i using Fin.addCases <;> induction j using Fin.addCases <;>
      simp [toQ, resT, resVarT, RingHom.toIntAlgHom_apply]
  exact RingHom.congr_fun this f

theorem resLat_of_substMem : SubstMem → ResLat := by
  intro hS p q ν f hf
  have := flat_quot_dualWeyl q (fun j => ν (Fin.natAdd p j))
  obtain ⟨w, hw⟩ := mem_range_map_of_flat (dualWeyl ℤ p p (fun i => ν (Fin.castAdd q i)))
    (dualWeyl ℤ q q (fun j => ν (Fin.natAdd p j))) (resT ℤ p q f)
    (resT_mem_lTensor hS p q ν f hf) (resT_mem_rTensor hS p q ν f hf)
  rw [← toQ_resT, ← hw]
  clear hw
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [TensorProduct.map_tmul, toQ_tmul]
    exact Submodule.subset_span ⟨a.1, a.2, b.1, b.2, rfl⟩
  | add x y hx hy => rw [map_add, map_add]; exact add_mem hx hy

end GlobalTheory.LeviCut
