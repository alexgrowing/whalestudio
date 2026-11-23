import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich

open Matrix QuadraticAlgebra

namespace UpperTheory.V.Z.Sym.Glob

open Loc

variable {K : Type} [Field K] {Δ τ : K}

private theorem sg_mul (x y : EL Δ τ) : sigL (x * y) = sigL x * sigL y := by
  ext <;> simp [sigL] <;> ring

private theorem sg_add (x y : EL Δ τ) : sigL (x + y) = sigL x + sigL y := by
  ext <;> simp [sigL] <;> ring

private theorem sg_sg (x : EL Δ τ) : sigL (sigL x) = x := by
  ext <;> simp [sigL]

private theorem sg_star (x : EL Δ τ) : sigL (star x) = star (sigL x) := by
  ext <;> simp [sigL]

private theorem sg_smul (a : Lsq K Δ) (x : EL Δ τ) : sigL (a • x) = star a • sigL x := by
  ext <;> simp [sigL] <;> ring

private theorem sg_tr (x : EL Δ τ) : QuadraticAlgebra.trace (sigL x) = star (QuadraticAlgebra.trace x) := by
  ext <;> simp [sigL, QuadraticAlgebra.trace_def, two_mul] <;> ring

private theorem sg_ofE (z : Etau K τ) : sigL (ofE Δ z) = ofE Δ z := by
  ext <;> simp [sigL, ofE]

private theorem ofE_mul (x y : Etau K τ) : ofE Δ (x * y) = ofE Δ x * ofE Δ y := by
  ext <;> simp [ofE]

private theorem ofE_star (x : Etau K τ) : ofE Δ (star x) = star (ofE Δ x) := by
  ext <;> simp [ofE]

private theorem ofE_one : ofE Δ (1 : Etau K τ) = 1 := by
  ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

private theorem st_alg (c : K) : star (algebraMap K (Lsq K Δ) c) = algebraMap K _ c := by
  ext <;> simp

private theorem herm_semi {c : K} {d m : EL Δ τ} (h : IsDat c d m) (x y : Sp Δ τ) :
    herm c m (semi d x) (semi d y) = star (herm c m x y) := by
  simp only [herm, semi, star_add, star_mul', star_star, st_alg, ← sg_tr, sg_mul, sg_sg, sg_star, h.m_sig]
  congr 2
  ring

private theorem herm_tor (c : K) (m : EL Δ τ) (z : (Etau K τ)ˣ) (x y : Sp Δ τ) :
    herm c m (tor Δ z x) (tor Δ z y) = herm c m x y := by
  have h1 : quo z * star (quo z) = 1 := by
    have e := z.mul_inv
    have e' := congrArg star e
    rw [star_mul', star_one] at e'
    simp only [quo, star_mul', star_star]
    linear_combination (star (z : Etau K τ) * star ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ)) * e + e'
  have h2 : ofE Δ (quo z) * star (ofE Δ (quo z)) = 1 := by rw [← ofE_star, ← ofE_mul, h1, ofE_one]
  simp only [herm, tor, sg_mul, sg_ofE, star_mul']
  congr 2
  linear_combination (m * x.2 * star (sigL y.2)) * h2

private theorem mem_unit (M : Matrix (Fin 3) (Fin 3) (Lsq K Δ))
    (h : ∀ u v, ∑ i, (M *ᵥ u) i * star ((M *ᵥ v) i) = ∑ i, u i * star (v i)) : M ∈ Matrix.unitaryGroup (Fin 3) (Lsq K Δ) := by
  rw [Matrix.mem_unitaryGroup_iff']
  refine Matrix.ext fun a b => ?_
  have := h (Pi.single b 1) (Pi.single a 1)
  simp only [Matrix.mulVec_single_one, Matrix.col_apply] at this
  rw [Matrix.mul_apply]
  simp only [Matrix.star_apply, mul_comm (star _)]
  rw [this, Matrix.one_apply, Finset.sum_eq_single a]
  · by_cases hab : a = b <;> simp [hab]
  · intro i _ hi
    simp [hi]
  · simp

theorem exG_models {c : K} {d m : EL Δ τ} (h : IsDat c d m) (P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ))
    (hP : ∀ x y, herm c m x y = ∑ i, P x i * star (P y i)) : ∃ δ ι, Models c d m δ ι P := by
  let f : (Fin 3 → Lsq K Δ) →ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ) :=
    { toFun := fun w => P (semi d (P.symm (star w)))
      map_add' := fun u v => by
        rw [← map_add, star_add, map_add]
        congr 1
        simp [semi, sg_add, mul_add]
      map_smul' := fun a u => by
        rw [RingHom.id_apply, ← map_smul, star_smul, map_smul]
        congr 1
        simp [semi, sg_smul] }
  let T : (Etau K τ)ˣ → Sp Δ τ →ₗ[Lsq K Δ] Sp Δ τ := fun z =>
    { toFun := tor Δ z
      map_add' := fun u v => by simp [tor, mul_add]
      map_smul' := fun a u => by simp [tor] }
  let g : (Etau K τ)ˣ → Matrix (Fin 3) (Fin 3) (Lsq K Δ) := fun z =>
    LinearMap.toMatrix' (P.toLinearMap ∘ₗ T z ∘ₗ P.symm.toLinearMap)
  have hg : ∀ z w, g z *ᵥ w = P (tor Δ z (P.symm w)) := fun z w => LinearMap.toMatrix'_mulVec _ _
  have hf : ∀ w, LinearMap.toMatrix' f *ᵥ w = P (semi d (P.symm (star w))) := fun w => LinearMap.toMatrix'_mulVec _ _
  have hgu : ∀ z, g z ∈ Matrix.unitaryGroup (Fin 3) (Lsq K Δ) := fun z => mem_unit _ fun u v => by
    simp only [hg]
    rw [← hP, herm_tor, hP]
    simp
  have hfu : LinearMap.toMatrix' f ∈ Matrix.unitaryGroup (Fin 3) (Lsq K Δ) := mem_unit _ fun u v => by
    simp only [hf]
    rw [← hP, herm_semi h, hP]
    simp [star_mul']
  refine ⟨⟨_, hfu⟩, MonoidHom.mk' (fun z => ⟨g z, hgu z⟩) fun a b => Subtype.ext ?_, hP, fun x => ?_, fun z x => ?_⟩
  · change g (a * b) = g a * g b
    refine Matrix.ext_of_mulVec_single fun i => ?_
    rw [← Matrix.mulVec_mulVec, hg, hg, hg, P.symm_apply_apply]
    congr 1
    have e : quo (a * b) = quo a * quo b := by
      simp only [quo, _root_.mul_inv_rev, Units.val_mul, star_mul]; ring
    simp [tor, e, ofE_mul, mul_assoc]
  · change _ = LinearMap.toMatrix' f *ᵥ _
    rw [hf, star_star, P.symm_apply_apply]
  · change _ = g z *ᵥ _
    rw [hg, P.symm_apply_apply]

theorem exG_norm [CharZero K] {c : K} {d m : EL Δ τ} (h : IsDat c d m) :
    ∃ y : Lsq K Δ, algebraMap K (Lsq K Δ) (2 + τ) * QuadraticAlgebra.norm m = y * star y := by
  have h1 : star m = sigL m := by
    conv_lhs => rw [← h.m_star, star_star]
  have ho : ofE Δ (ω : Etau K τ) = ω := by ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  have hd : d * sigL d = ω := h.d_norm.trans ho
  have hd' : star d * star (sigL d) = star ω := by rw [← star_mul', hd]
  have hn : (ω : EL Δ τ) * star ω = 1 := by rw [← algebraMap_norm_eq_mul_star]; simp [QuadraticAlgebra.norm_def]
  have ht : (ω : EL Δ τ) + star ω = algebraMap _ _ (algebraMap K (Lsq K Δ) τ) := by
    rw [← algebraMap_trace_eq_add_star, trace_omega]
  have hs : sigL (1 + star ω : EL Δ τ) = 1 + star ω := by
    ext <;> simp [sigL, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  set y : EL Δ τ := m * d * (1 + star ω) with hy
  have hys : star y = y := by
    rw [hy, star_mul', star_mul', h1, h.m_sig, star_add, star_one, star_star]
    linear_combination (m * d * (1 + ω)) * hd' + m * d * hn
  have him : y.im = 0 := by
    have e := congrArg QuadraticAlgebra.im hys
    rw [im_star] at e
    have e1 := congrArg QuadraticAlgebra.re e
    have e2 := congrArg QuadraticAlgebra.im e
    simp only [re_neg, im_neg] at e1 e2
    ext
    · exact self_eq_neg.1 e1.symm
    · exact self_eq_neg.1 e2.symm
  have hy1 : y = algebraMap _ _ y.re := by ext1 <;> simp [him]
  have hy2 : sigL y = algebraMap _ _ (star y.re) := by ext1 <;> simp [him, sigL]
  refine ⟨y.re, QuadraticAlgebra.algebraMap_injective (a := -1) (b := algebraMap K (Lsq K Δ) τ) ?_⟩
  rw [map_mul, map_mul, ← hy1, ← hy2, algebraMap_norm_eq_mul_star, hy, sg_mul, sg_mul, hs, ← h1, map_add, map_add, ← ht,
    map_ofNat, map_ofNat]
  linear_combination (-(m * star m * (1 + star ω) ^ 2)) * hd - (m * star m * (2 + star ω)) * hn

end UpperTheory.V.Z.Sym.Glob
