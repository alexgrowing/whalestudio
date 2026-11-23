import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin

noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open Loc Matrix QuadraticAlgebra

section Generic

variable {K : Type} [Field K] {Δ τ : K}

private lemma starL_alg (r : K) : star (algebraMap K (Lsq K Δ) r) = algebraMap K (Lsq K Δ) r := by
  ext <;> simp

private lemma sigL_add (x y : EL Δ τ) : sigL (x + y) = sigL x + sigL y := by
  ext <;> simp [sigL]

private lemma sigL_mul (x y : EL Δ τ) : sigL (x * y) = sigL x * sigL y := by
  ext <;> simp [sigL, starL_alg]

private lemma sigL_smul (a : Lsq K Δ) (x : EL Δ τ) : sigL (a • x) = star a • sigL x := by
  ext <;> simp [sigL]

private lemma star_smulE (a : Lsq K Δ) (x : EL Δ τ) : star (a • x) = a • star x := by
  ext <;> simp <;> ring

private lemma herm_add_left (c : K) (m : EL Δ τ) (x x' y : Sp Δ τ) :
    herm c m (x + x') y = herm c m x y + herm c m x' y := by
  simp only [herm, Prod.fst_add, Prod.snd_add, mul_add, add_mul, map_add]
  ring

private lemma herm_smul_left (c : K) (m : EL Δ τ) (a : Lsq K Δ) (x y : Sp Δ τ) :
    herm c m (a • x) y = a * herm c m x y := by
  have e : m * a • x.2 * star (sigL y.2) = a • (m * x.2 * star (sigL y.2)) := by
    simp only [mul_smul_comm, smul_mul_assoc]
  simp only [herm, Prod.smul_fst, Prod.smul_snd, e, map_smul, smul_eq_mul]
  ring

private lemma herm_add_right (c : K) (m : EL Δ τ) (x y y' : Sp Δ τ) :
    herm c m x (y + y') = herm c m x y + herm c m x y' := by
  simp only [herm, Prod.fst_add, Prod.snd_add, sigL_add, star_add, mul_add, add_mul, map_add]
  ring

private lemma herm_smul_right (c : K) (m : EL Δ τ) (a : Lsq K Δ) (x y : Sp Δ τ) :
    herm c m x (a • y) = star a * herm c m x y := by
  have e : m * x.2 * star (sigL (a • y.2)) = star a • (m * x.2 * star (sigL y.2)) := by
    rw [sigL_smul, star_smulE, mul_smul_comm]
  simp only [herm, Prod.smul_fst, Prod.smul_snd, e, map_smul, smul_eq_mul, star_smul, star_mul']
  ring

private lemma semi_add (d : EL Δ τ) (x y : Sp Δ τ) : semi d (x + y) = semi d x + semi d y := by
  simp [semi, sigL_add, mul_add]

private lemma semi_smul (d : EL Δ τ) (a : Lsq K Δ) (x : Sp Δ τ) : semi d (a • x) = star a • semi d x := by
  simp [semi, sigL_smul, mul_smul_comm]

end Generic

section Torus

variable {K : Type} [Field K] {Δ τ : K}

private lemma ofE_mul (x y : Etau K τ) : ofE Δ (x * y) = ofE Δ x * ofE Δ y := by
  ext <;> simp [ofE]

private lemma ofE_one : ofE Δ (1 : Etau K τ) = 1 := by
  ext <;> simp [ofE, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

private lemma sigL_ofE (x : Etau K τ) : sigL (ofE Δ x) = ofE Δ x := by
  ext <;> simp [sigL, ofE, starL_alg]

private lemma star_ofE (x : Etau K τ) : star (ofE Δ x) = ofE Δ (star x) := by
  ext <;> simp [ofE]

private lemma quo_mul (a b : (Etau K τ)ˣ) : quo (a * b) = quo a * quo b := by
  simp only [quo, _root_.mul_inv_rev, Units.val_mul, star_mul]; ring

private lemma quo_one : quo (1 : (Etau K τ)ˣ) = 1 := by simp [quo]

private lemma quo_star (z : (Etau K τ)ˣ) : quo z * star (quo z) = 1 := by
  have e : (z : Etau K τ) * ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) = 1 := by simp
  have e' : star (z : Etau K τ) * star ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) = 1 := by
    rw [← star_mul', e, star_one]
  simp only [quo, star_mul', star_star]
  calc _ = ((z : Etau K τ) * ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ)) *
        (star (z : Etau K τ) * star ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ)) := by ring
    _ = 1 := by rw [e, e', one_mul]

variable (Δ) in

private def torL (z : (Etau K τ)ˣ) : Sp Δ τ →ₗ[Lsq K Δ] Sp Δ τ where
  toFun := tor Δ z
  map_add' x y := by simp [tor, mul_add]
  map_smul' a x := by simp [tor, mul_smul_comm]

private lemma tor_mul (a b : (Etau K τ)ˣ) (x : Sp Δ τ) : tor Δ (a * b) x = tor Δ a (tor Δ b x) := by
  simp [tor, quo_mul, ofE_mul, mul_assoc]

private lemma tor_one (x : Sp Δ τ) : tor Δ (1 : (Etau K τ)ˣ) x = x := by
  simp [tor, quo_one, ofE_one]

private lemma herm_tor (c : K) (m : EL Δ τ) (z : (Etau K τ)ˣ) (x y : Sp Δ τ) :
    herm c m (tor Δ z x) (tor Δ z y) = herm c m x y := by
  have e : ofE Δ (quo z) * star (ofE Δ (quo z)) = 1 := by
    rw [star_ofE, ← ofE_mul, quo_star, ofE_one]
  have e2 : m * (ofE Δ (quo z) * x.2) * star (sigL (ofE Δ (quo z) * y.2)) = m * x.2 * star (sigL y.2) := by
    rw [sigL_mul, sigL_ofE, star_mul']
    calc _ = (ofE Δ (quo z) * star (ofE Δ (quo z))) * (m * x.2 * star (sigL y.2)) := by ring
      _ = _ := by rw [e, one_mul]
  simp only [herm, tor, e2]

private def mtor (P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)) (z : (Etau K τ)ˣ) :
    Matrix (Fin 3) (Fin 3) (Lsq K Δ) :=
  LinearMap.toMatrix' (P.toLinearMap ∘ₗ torL Δ z ∘ₗ P.symm.toLinearMap)

private lemma mtor_mulVec (P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)) (z : (Etau K τ)ˣ) (u : Fin 3 → Lsq K Δ) :
    mtor P z *ᵥ u = P (tor Δ z (P.symm u)) := by
  simp only [mtor, LinearMap.toMatrix'_mulVec]
  rfl

private lemma mtor_mul (P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)) (a b : (Etau K τ)ˣ) :
    mtor P (a * b) = mtor P a * mtor P b := by
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [← Matrix.mulVec_mulVec, mtor_mulVec, mtor_mulVec, mtor_mulVec, tor_mul, LinearEquiv.symm_apply_apply]

private lemma mtor_one (P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)) : mtor P (1 : (Etau K τ)ˣ) = 1 := by
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [mtor_mulVec, tor_one, LinearEquiv.apply_symm_apply, Matrix.one_mulVec]

private lemma mtor_mem {c : K} {m : EL Δ τ} (P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ))
    (hP : ∀ x y, herm c m x y = ∑ i, P x i * star (P y i)) (z : (Etau K τ)ˣ) :
    mtor P z ∈ unitaryGroup (Fin 3) (Lsq K Δ) := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext1 i j
  have h := herm_tor c m z (P.symm (Pi.single j 1)) (P.symm (Pi.single i 1))
  rw [hP, hP] at h
  simp only [LinearEquiv.apply_symm_apply] at h
  have col : ∀ j k, mtor P z k j = P (tor Δ z (P.symm (Pi.single j 1))) k := fun j k => by
    rw [← mtor_mulVec, Matrix.mulVec_single_one]
    rfl
  have r : ∑ k, (Pi.single j 1 : Fin 3 → Lsq K Δ) k * star ((Pi.single i 1 : Fin 3 → Lsq K Δ) k) = (1 : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) i j := by
    simp only [Pi.single_apply, Matrix.one_apply, eq_comm]
    split_ifs <;> simp_all
  rw [Matrix.mul_apply, ← r, ← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.star_apply, col, col, mul_comm]

end Torus

section Nat

variable {K K' : Type} [Field K] [Field K'] (f : K →+* K') {Δ τ : K}

private lemma lmap_alg (r : K) : lmap f Δ (algebraMap K (Lsq K Δ) r) = algebraMap K' (Lsq K' (f Δ)) (f r) := by
  ext <;> simp [lmap]

private lemma lmap_star (x : Lsq K Δ) : lmap f Δ (star x) = star (lmap f Δ x) := by
  ext <;> simp [lmap]

private lemma elmap_mul (x y : EL Δ τ) : elmap f (x * y) = elmap f x * elmap f y := by
  ext <;> simp [elmap, lmap_alg]

private lemma elmap_sigL (x : EL Δ τ) : elmap f (sigL x) = sigL (elmap f x) := by
  ext <;> simp [elmap, sigL, lmap_star]

private lemma elmap_star (x : EL Δ τ) : elmap f (star x) = star (elmap f x) := by
  ext <;> simp [elmap, lmap_alg]

private lemma elmap_ofE (x : Etau K τ) : elmap f (ofE Δ x) = ofE (f Δ) (emap f τ x) := by
  ext <;> simp [elmap, ofE, emap, lmap_alg]

private lemma elmap_one : elmap f (1 : EL Δ τ) = 1 := by
  ext <;> simp [elmap, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

private lemma lmap_trace (x : EL Δ τ) : lmap f Δ (trace x) = trace (elmap f x) := by
  have e : lmap f Δ 2 = 2 := map_ofNat _ 2
  simp [trace_def, elmap, lmap_alg, e]

private lemma emap_star (x : Etau K τ) : emap f τ (star x) = star (emap f τ x) := by
  ext <;> simp [emap]

private lemma emap_omega : emap f τ (ω : Etau K τ) = ω := by
  ext <;> simp [emap]

private def spm (x : Sp Δ τ) : Sp (f Δ) (f τ) := (lmap f Δ x.1, elmap f x.2)

private lemma herm_spm (c : K) (m : EL Δ τ) (x y : Sp Δ τ) :
    herm (f c) (elmap f m) (spm f x) (spm f y) = lmap f Δ (herm c m x y) := by
  simp only [herm, spm, map_add, map_mul, lmap_alg, lmap_star, lmap_trace, elmap_mul, elmap_star, elmap_sigL]

private lemma semi_spm (d : EL Δ τ) (x : Sp Δ τ) : semi (elmap f d) (spm f x) = spm f (semi d x) := by
  simp only [semi, spm, lmap_star, elmap_mul, elmap_sigL]

private lemma quo_emap (z : (Etau K τ)ˣ) (z' : (Etau K' (f τ))ˣ) (h : (z' : Etau K' (f τ)) = emap f τ z) :
    quo z' = emap f τ (quo z) := by
  have e : ((z'⁻¹ : (Etau K' (f τ))ˣ) : Etau K' (f τ)) = emap f τ ((z⁻¹ : (Etau K τ)ˣ) : Etau K τ) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [h, ← map_mul]
    simp
  simp only [quo, e, h, map_mul, emap_star]

private lemma tor_spm (z : (Etau K τ)ˣ) (z' : (Etau K' (f τ))ˣ) (h : (z' : Etau K' (f τ)) = emap f τ z) (x : Sp Δ τ) :
    tor (f Δ) z' (spm f x) = spm f (tor Δ z x) := by
  simp only [tor, spm, elmap_mul, elmap_ofE, quo_emap f z z' h]

private lemma sp_ind {p : Sp (f Δ) (f τ) → Prop} (hadd : ∀ x y, p x → p y → p (x + y))
    (hsmul : ∀ (a : Lsq K' (f Δ)) x, p x → p (a • x)) (h : ∀ x : Sp Δ τ, p (spm f x)) (x : Sp (f Δ) (f τ)) : p x := by
  have e : x = x.1 • spm f ((1, 0) : Sp Δ τ) + (x.2.re • spm f ((0, 1) : Sp Δ τ) + x.2.im • spm f ((0, ω) : Sp Δ τ)) := by
    refine Prod.ext ?_ (QuadraticAlgebra.ext ?_ ?_) <;>
      simp [spm, elmap, QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  rw [e]
  exact hadd _ _ (hsmul _ _ (h _)) (hadd _ _ (hsmul _ _ (h _)) (hsmul _ _ (h _)))

private lemma isDat_map {c : K} {d m : EL Δ τ} (h : IsDat c d m) : IsDat (f c) (elmap f d) (elmap f m) where
  reg := by
    rw [show f τ ^ 2 - 4 = f (τ ^ 2 - 4) by rw [map_sub, map_pow, map_ofNat]]
    exact (map_ne_zero f).2 h.reg
  c_ne := (map_ne_zero f).2 h.c_ne
  d_norm := by
    rw [← elmap_sigL, ← elmap_mul, h.d_norm, elmap_ofE, emap_omega]
  m_unit := by
    obtain ⟨u, hu⟩ := h.m_unit
    have e1 : (u : EL Δ τ) * ((u⁻¹ : (EL Δ τ)ˣ) : EL Δ τ) = 1 := by simp
    have e2 := congrArg (elmap f) e1
    rw [elmap_mul, elmap_one, hu] at e2
    exact IsUnit.of_mul_eq_one _ e2
  m_star := by
    rw [← elmap_sigL, ← elmap_star, h.m_star]
  m_sig := by
    rw [← elmap_sigL, h.m_sig, ← elmap_sigL, ← elmap_star, elmap_mul, elmap_mul]

end Nat

section Main

variable {K K' : Type} [Field K] [Field K'] (f : K →+* K') {Δ τ : K}

variable (Δ τ) in

private def cdE : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ) where
  toFun x := ![x.1, x.2.re, x.2.im]
  invFun u := (u 0, ⟨u 1, u 2⟩)
  map_add' x y := by
    funext i; fin_cases i <;> simp
  map_smul' a x := by
    funext i; fin_cases i <;> simp
  left_inv x := by simp
  right_inv u := by
    funext i; fin_cases i <;> simp

private lemma cdE_spm (x : Sp Δ τ) : cdE (f Δ) (f τ) (spm f x) = lmap f Δ ∘ cdE Δ τ x := by
  funext i; fin_cases i <;> simp [cdE, spm, elmap]

private def mA (P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)) : Matrix (Fin 3) (Fin 3) (Lsq K Δ) :=
  LinearMap.toMatrix' ((cdE Δ τ).symm.trans P).toLinearMap

private def mB (P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)) : Matrix (Fin 3) (Fin 3) (Lsq K Δ) :=
  LinearMap.toMatrix' ((cdE Δ τ).symm.trans P).symm.toLinearMap

private lemma mA_mB (P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)) : mA P * mB P = 1 := by
  rw [mA, mB, ← LinearMap.toMatrix'_comp, LinearEquiv.comp_symm, LinearMap.toMatrix'_id]

private lemma mB_mA (P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)) : mB P * mA P = 1 := by
  rw [mA, mB, ← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]

private lemma mA_mulVec (P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)) (x : Sp Δ τ) : mA P *ᵥ cdE Δ τ x = P x := by
  simp [mA, LinearMap.toMatrix'_mulVec]

private def mapP (P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)) :
    Sp (f Δ) (f τ) ≃ₗ[Lsq K' (f Δ)] (Fin 3 → Lsq K' (f Δ)) :=
  (cdE (f Δ) (f τ)).trans (Matrix.toLin'OfInv (M := (mB P).map (lmap f Δ)) (M' := (mA P).map (lmap f Δ))
    (by rw [← Matrix.map_mul, mB_mA, Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [← Matrix.map_mul, mA_mB, Matrix.map_one _ (map_zero _) (map_one _)]))

private lemma mapP_spm (P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ)) (x : Sp Δ τ) :
    mapP f P (spm f x) = lmap f Δ ∘ P x := by
  have e : mapP f P (spm f x) = (mA P).map (lmap f Δ) *ᵥ cdE (f Δ) (f τ) (spm f x) := rfl
  rw [e, cdE_spm, ← mA_mulVec P x]
  funext i
  exact (RingHom.map_mulVec (lmap f Δ) (mA P) _ i).symm

private lemma map_mulVec' (M : Matrix (Fin 3) (Fin 3) (Lsq K Δ)) (u : Fin 3 → Lsq K Δ) :
    lmap f Δ ∘ (M *ᵥ u) = M.map (lmap f Δ) *ᵥ (lmap f Δ ∘ u) := by
  funext i
  exact RingHom.map_mulVec (lmap f Δ) M u i

private lemma form_map {c : K} {m : EL Δ τ} (P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ))
    (hP : ∀ x y, herm c m x y = ∑ i, P x i * star (P y i)) (x y : Sp (f Δ) (f τ)) :
    herm (f c) (elmap f m) x y = ∑ i, mapP f P x i * star (mapP f P y i) := by
  revert y
  refine sp_ind f (p := fun x => ∀ y, herm (f c) (elmap f m) x y = ∑ i, mapP f P x i * star (mapP f P y i)) ?_ ?_ ?_ x
  · intro x x' hx hx' y
    simp only [herm_add_left, hx, hx', map_add, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  · intro a x hx y
    simp only [herm_smul_left, hx, map_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  · intro x y
    refine sp_ind f (p := fun y => herm (f c) (elmap f m) (spm f x) y = ∑ i, mapP f P (spm f x) i * star (mapP f P y i)) ?_ ?_ ?_ y
    · intro y y' hy hy'
      simp only [herm_add_right, hy, hy', map_add, Pi.add_apply, star_add, mul_add, Finset.sum_add_distrib]
    · intro a y hy
      rw [herm_smul_right, hy, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [map_smul, Pi.smul_apply, smul_eq_mul, star_mul']
      ring
    · intro y
      rw [herm_spm, hP, map_sum]
      simp only [map_mul, lmap_star, mapP_spm, Function.comp_apply]

private lemma semi_map {d : EL Δ τ} {δ : Matrix (Fin 3) (Fin 3) (Lsq K Δ)} (P : Sp Δ τ ≃ₗ[Lsq K Δ] (Fin 3 → Lsq K Δ))
    (hP : ∀ x, P (semi d x) = δ *ᵥ star (P x)) (x : Sp (f Δ) (f τ)) :
    mapP f P (semi (elmap f d) x) = δ.map (lmap f Δ) *ᵥ star (mapP f P x) := by
  refine sp_ind f (p := fun x => mapP f P (semi (elmap f d) x) = δ.map (lmap f Δ) *ᵥ star (mapP f P x)) ?_ ?_ ?_ x
  · intro x y hx hy
    rw [semi_add, map_add, hx, hy, map_add, star_add, Matrix.mulVec_add]
  · intro a x hx
    rw [semi_smul, map_smul, hx, map_smul, star_smul, Matrix.mulVec_smul]
  · intro x
    rw [semi_spm, mapP_spm, hP, map_mulVec', mapP_spm]
    congr 1
    funext i
    simp [lmap_star]

private def torHom {c : K'} {Δ' τ' : K'} {m : EL Δ' τ'} (P : Sp Δ' τ' ≃ₗ[Lsq K' Δ'] (Fin 3 → Lsq K' Δ'))
    (hP : ∀ x y, herm c m x y = ∑ i, P x i * star (P y i)) : (Etau K' τ')ˣ →* U3 Δ' where
  toFun z := ⟨mtor P z, mtor_mem P hP z⟩
  map_one' := Subtype.ext (mtor_one P)
  map_mul' a b := Subtype.ext (mtor_mul P a b)

end Main

private theorem model_map_exists : ModelMap := by
  intro K K' _ _ f Δ τ c d m hD
  refine ⟨isDat_map f hD, fun δ ι P hM δ' hδ => ?_⟩
  have hf := form_map f P hM.form
  refine ⟨torHom _ hf, mapP f P, ⟨hf, fun x => ?_, fun z x => ?_⟩, fun z z' h => ?_⟩
  · rw [hδ]
    exact semi_map f P hM.semi x
  · change _ = mtor (mapP f P) z *ᵥ _
    rw [mtor_mulVec, LinearEquiv.symm_apply_apply]
  · change mtor (mapP f P) z' = _
    apply Matrix.ext_of_mulVec_single
    intro j
    have hs : mapP f P (spm f (P.symm (Pi.single j 1))) = Pi.single j 1 := by
      rw [mapP_spm, LinearEquiv.apply_symm_apply]
      funext k
      simp [Pi.single_apply, apply_ite (lmap f Δ)]
    rw [← hs, mtor_mulVec, LinearEquiv.symm_apply_apply, tor_spm f z z' h, mapP_spm, hM.tor, map_mulVec', ← mapP_spm]

end UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Glob.modelMap :
    UpperTheory.V.Z.Sym.Glob.ModelMap := UpperTheory.V.Z.Sym.Glob.model_map_exists
