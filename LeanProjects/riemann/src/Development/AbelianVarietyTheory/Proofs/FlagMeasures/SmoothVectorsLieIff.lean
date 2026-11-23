import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LinMulti
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ISmulOneMemUnitaryLie

noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S GlobalTheory.Ell Filter
open scoped InnerProductSpace ContDiff Topology

namespace GlobalTheory.SmChart

variable {n : ℕ}

def oneProd {d : ℕ} (Y : Fin d → Matrix (Fin n) (Fin n) ℂ) (t : Fin d → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  (List.ofFn fun i => NormedSpace.exp (t i • Y i)).prod

theorem oneProd_succ {d : ℕ} (Y : Fin (d + 1) → Matrix (Fin n) (Fin n) ℂ) (t : Fin (d + 1) → ℝ) :
    oneProd Y t = NormedSpace.exp (t 0 • Y 0) * oneProd (fun i => Y i.succ) (fun i => t i.succ) := by
  simp [oneProd, List.ofFn_succ]

theorem oneProd_zero : ∀ {d : ℕ} (Y : Fin d → Matrix (Fin n) (Fin n) ℂ), oneProd Y 0 = 1 := by
  intro d
  induction d with
  | zero => intro Y; simp [oneProd]
  | succ d ih =>
    intro Y
    rw [oneProd_succ]
    have : (fun i : Fin d => (0 : Fin (d + 1) → ℝ) i.succ) = 0 := rfl
    rw [this, ih]
    simp [NormedSpace.exp_zero]

def lieSub (G : Matrix (Fin n) (Fin n) ℂ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) :=
  GlobalTheory.UnitaryLieAlgebra.unitaryLie G

theorem isUnit_of_mem_UH {G : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH G) : IsUnit g := by
  have h : gᴴ * G * g = G := hg
  exact isUnit_of_mul_isUnit_right (h.symm ▸ hG : IsUnit (gᴴ * G * g))

theorem mul_mem_UH {G a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ Formalism.QuantumDeterminants.UH G) (hb : b ∈ Formalism.QuantumDeterminants.UH G) :
    a * b ∈ Formalism.QuantumDeterminants.UH G := by
  have ha' : aᴴ * G * a = G := ha
  have hb' : bᴴ * G * b = G := hb
  show (a * b)ᴴ * G * (a * b) = G
  calc (a * b)ᴴ * G * (a * b) = bᴴ * (aᴴ * G * a) * b := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = G := by rw [ha', hb']

theorem inv_mem_UH {G : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Formalism.QuantumDeterminants.UH G) : g⁻¹ ∈ Formalism.QuantumDeterminants.UH G := by
  have h : gᴴ * G * g = G := hg
  have hd := (Matrix.isUnit_iff_isUnit_det g).1 (isUnit_of_mem_UH hG hg)
  show (g⁻¹)ᴴ * G * g⁻¹ = G
  calc (g⁻¹)ᴴ * G * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * G * g) * g⁻¹ := by rw [h]
    _ = (g * g⁻¹)ᴴ * G * (g * g⁻¹) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = G := by rw [mul_nonsing_inv _ hd]; simp

theorem exp_mem {G X : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G) (hX : X ∈ lieOf G) (t : ℝ) :
    NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH G := by
  have hX0 : Xᴴ * G + G * X = 0 := hX
  show (NormedSpace.exp (t • X))ᴴ * G * NormedSpace.exp (t • X) = G
  have hd : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).1 hG
  have h1 : (t • X)ᴴ = G * (-(t • X)) * G⁻¹ := by
    have h2 : Xᴴ = G * (-X) * G⁻¹ := by
      rw [Matrix.mul_neg, ← eq_neg_of_add_eq_zero_left hX0, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd,
        Matrix.mul_one]
    rw [conjTranspose_smul, h2]
    simp
  rw [← Matrix.exp_conjTranspose, h1, Matrix.exp_conj _ _ hG, Matrix.exp_neg]
  have hu : IsUnit (NormedSpace.exp (t • X)).det := (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _)
  rw [Matrix.mul_assoc (G * _), Matrix.nonsing_inv_mul _ hd, Matrix.mul_one, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

theorem oneProd_mem {G : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G) :
    ∀ {d : ℕ} (Y : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i, Y i ∈ lieOf G) → ∀ t : Fin d → ℝ,
      oneProd Y t ∈ Formalism.QuantumDeterminants.UH G := by
  intro d
  induction d with
  | zero =>
    intro Y _ t
    show (oneProd Y t)ᴴ * G * oneProd Y t = G
    simp [oneProd]
  | succ d ih =>
    intro Y hY t
    rw [oneProd_succ]
    exact mul_mem_UH (exp_mem hG (hY 0) _) (ih _ (fun i => hY _) _)

section Op

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

def cay (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (1 + 1) * Ring.inverse (g + 1) * (g - 1)

theorem isUnit_two : IsUnit (1 + 1 : Matrix (Fin n) (Fin n) ℂ) := by
  refine (Matrix.isUnit_iff_isUnit_det _).2 ?_
  rw [show (1 + 1 : Matrix (Fin n) (Fin n) ℂ) = (2 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) from
    (two_smul ℂ (1 : Matrix (Fin n) (Fin n) ℂ)).symm, Matrix.det_smul, Matrix.det_one, mul_one]
  exact (IsUnit.mk0 (2 : ℂ) two_ne_zero).pow _

theorem cay_one : cay (1 : Matrix (Fin n) (Fin n) ℂ) = 0 := by simp [cay]

theorem cay_eq (g : Matrix (Fin n) (Fin n) ℂ) (hg : IsUnit (g + 1)) :
    cay g = (1 + 1) - (1 + 1) * Ring.inverse (g + 1) * (1 + 1) := by
  unfold cay
  rw [show g - 1 = (g + 1) - (1 + 1) by abel, mul_sub, mul_assoc ((1 : Matrix (Fin n) (Fin n) ℂ) + 1) _ (g + 1),
    Ring.inverse_mul_cancel _ hg, mul_one]

theorem cay_inj {a b : Matrix (Fin n) (Fin n) ℂ} (ha : IsUnit (a + 1)) (hb : IsUnit (b + 1))
    (h : cay a = cay b) : a = b := by
  rw [cay_eq a ha, cay_eq b hb] at h
  have h1 := sub_right_injective h
  have h3 : Ring.inverse (a + 1) = Ring.inverse (b + 1) :=
    isUnit_two.mul_left_cancel (isUnit_two.mul_right_cancel h1)
  have e : a + 1 = b + 1 := calc
    a + 1 = (a + 1) * (Ring.inverse (b + 1) * (b + 1)) := by rw [Ring.inverse_mul_cancel _ hb, mul_one]
    _ = (a + 1) * Ring.inverse (a + 1) * (b + 1) := by rw [h3, mul_assoc]
    _ = b + 1 := by rw [Ring.mul_inverse_cancel _ ha, one_mul]
  exact add_right_cancel e

theorem cay_mem (G g : Matrix (Fin n) (Fin n) ℂ) (hg : g ∈ Formalism.QuantumDeterminants.UH G) (hu : IsUnit (g + 1)) :
    cay g ∈ lieOf G := by
  have hgG : gᴴ * G * g = G := hg
  have hu1 : (g + 1) * Ring.inverse (g + 1) = 1 := Ring.mul_inverse_cancel _ hu
  have hu1' : (Ring.inverse (g + 1))ᴴ * (g + 1)ᴴ = 1 := by
    rw [← conjTranspose_mul, hu1, conjTranspose_one]
  have key : G * (g + 1) + (g + 1)ᴴ * G = (g + 1)ᴴ * G * (g + 1) := by
    rw [conjTranspose_add, conjTranspose_one]
    simp only [mul_add, add_mul, mul_one, one_mul]
    rw [hgG]; abel
  set u := Ring.inverse (g + 1) with hudef
  have hS : uᴴ * G + G * u = G := calc
    uᴴ * G + G * u = uᴴ * G * ((g + 1) * u) + uᴴ * (g + 1)ᴴ * (G * u) := by
        rw [hu1, hu1', mul_one, one_mul]
    _ = uᴴ * (G * (g + 1) + (g + 1)ᴴ * G) * u := by noncomm_ring
    _ = uᴴ * ((g + 1)ᴴ * G * (g + 1)) * u := by rw [key]
    _ = uᴴ * (g + 1)ᴴ * G * ((g + 1) * u) := by noncomm_ring
    _ = G := by rw [hu1, hu1', one_mul, mul_one]
  show (cay g)ᴴ * G + G * cay g = 0
  rw [cay_eq g hu]
  simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_add, conjTranspose_one]
  calc _ = (G - (uᴴ * G + G * u)) * (1 + 1 + 1 + 1) := by noncomm_ring
    _ = 0 := by rw [hS, sub_self, zero_mul]

theorem hasStrictFDerivAt_cay :
    HasStrictFDerivAt (cay : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) 1 := by
  have h2 := (isUnit_two (n := n))
  obtain ⟨L, hL⟩ : ∃ L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ,
      HasStrictFDerivAt (Ring.inverse : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) L
      ((fun g : Matrix (Fin n) (Fin n) ℂ => g + 1) 1) :=
    ⟨_, hasStrictFDerivAt_ringInverse (𝕜 := ℝ) h2.unit⟩
  have hadd : HasStrictFDerivAt (fun g : Matrix (Fin n) (Fin n) ℂ => g + 1)
      (ContinuousLinearMap.id ℝ (Matrix (Fin n) (Fin n) ℂ)) 1 :=
    (hasStrictFDerivAt_id (1 : Matrix (Fin n) (Fin n) ℂ)).add_const 1
  have hu := (HasStrictFDerivAt.comp (f := fun g : Matrix (Fin n) (Fin n) ℂ => g + 1) (1 : Matrix (Fin n) (Fin n) ℂ)
    hL hadd).const_mul (1 + 1)
  have hv : HasStrictFDerivAt (fun g : Matrix (Fin n) (Fin n) ℂ => g - 1)
      (ContinuousLinearMap.id ℝ (Matrix (Fin n) (Fin n) ℂ)) 1 :=
    (hasStrictFDerivAt_id (1 : Matrix (Fin n) (Fin n) ℂ)).sub_const 1
  have hm := hu.fun_mul' hv
  have e : (cay : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) =
      fun g => (1 + 1) * (Ring.inverse ∘ fun g : Matrix (Fin n) (Fin n) ℂ => g + 1) g * (g - 1) := by
    funext g; rfl
  rw [e]
  refine hm.congr_fderiv ?_
  ext1 H
  change (1 + 1) * Ring.inverse ((1 : Matrix (Fin n) (Fin n) ℂ) + 1) * H + _ * ((1 : Matrix (Fin n) (Fin n) ℂ) - 1) = H
  rw [Ring.mul_inverse_cancel _ h2, one_mul, sub_self, mul_zero, add_zero]

theorem contDiffAt_cay {g : Matrix (Fin n) (Fin n) ℂ} (hu : IsUnit (g + 1)) : ContDiffAt ℝ ∞ cay g := by
  have h1 : ContDiffAt ℝ ∞ (Ring.inverse : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) (g + 1) := by
    simpa using contDiffAt_ringInverse ℝ (n := ∞) hu.unit
  have h2 : ContDiffAt ℝ ∞ (fun x : Matrix (Fin n) (Fin n) ℂ => Ring.inverse (x + 1)) g :=
    h1.comp g (contDiffAt_id.add contDiffAt_const)
  exact (contDiffAt_const.mul h2).mul (contDiffAt_id.sub contDiffAt_const)

def lin {d : ℕ} (Y : Fin d → Matrix (Fin n) (Fin n) ℂ) : (Fin d → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  ∑ i, (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (Y i)

theorem lin_apply {d : ℕ} (Y : Fin d → Matrix (Fin n) (Fin n) ℂ) (t : Fin d → ℝ) :
    lin Y t = ∑ i, t i • Y i := by
  simp [lin]

theorem hasStrictFDerivAt_oneProd : ∀ {d : ℕ} (Y : Fin d → Matrix (Fin n) (Fin n) ℂ),
    HasStrictFDerivAt (oneProd Y) (lin Y) 0 := by
  intro d
  induction d with
  | zero =>
    intro Y
    have e : oneProd Y = fun _ => 1 := by funext t; simp [oneProd]
    rw [e]
    have hl : lin Y = 0 := by ext1 t; simp [lin_apply]
    rw [hl]
    exact hasStrictFDerivAt_const _ _
  | succ d ih =>
    intro Y
    set L0 : (Fin (d + 1) → ℝ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
      (ContinuousLinearMap.proj 0 : (Fin (d + 1) → ℝ) →L[ℝ] ℝ).smulRight (Y 0) with hL0
    set P : (Fin (d + 1) → ℝ) →L[ℝ] (Fin d → ℝ) :=
      ContinuousLinearMap.pi fun i => (ContinuousLinearMap.proj i.succ : (Fin (d + 1) → ℝ) →L[ℝ] ℝ) with hP
    have e : oneProd Y = fun t => NormedSpace.exp (L0 t) * oneProd (fun i => Y i.succ) (P t) := by
      funext t
      rw [oneProd_succ]
      rfl
    have hE : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
        (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) (L0 0) := by
      rw [map_zero]; exact hasStrictFDerivAt_exp_zero
    have h1 := HasStrictFDerivAt.comp (f := fun t => L0 t) (0 : Fin (d + 1) → ℝ) hE L0.hasStrictFDerivAt
    have h2' := ih (fun i => Y i.succ)
    rw [← map_zero P] at h2'
    have h2 := HasStrictFDerivAt.comp (f := fun t => P t) (0 : Fin (d + 1) → ℝ) h2' P.hasStrictFDerivAt
    have hm := h1.fun_mul' h2
    rw [e]
    refine hm.congr_fderiv ?_
    ext1 v
    change NormedSpace.exp (L0 0) * lin (fun i => Y i.succ) (P v) +
      L0 v * oneProd (fun i => Y i.succ) (P 0) = lin Y v
    rw [map_zero, map_zero, NormedSpace.exp_zero, oneProd_zero, one_mul, mul_one, lin_apply, lin_apply,
      Fin.sum_univ_succ, add_comm]
    rfl

theorem contDiff_oneProd : ∀ {d : ℕ} (Y : Fin d → Matrix (Fin n) (Fin n) ℂ), ContDiff ℝ ∞ (oneProd Y) := by
  intro d
  induction d with
  | zero =>
    intro Y
    have e : oneProd Y = fun _ => 1 := by funext t; simp [oneProd]
    rw [e]
    exact contDiff_const
  | succ d ih =>
    intro Y
    have e : oneProd Y = fun t => NormedSpace.exp (t 0 • Y 0) * oneProd (fun i => Y i.succ) (fun i => t i.succ) := by
      funext t
      rw [oneProd_succ]
    rw [e]
    have hexp : ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) :=
      contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
    have h1 : ContDiff ℝ ∞ fun t : Fin (d + 1) → ℝ => NormedSpace.exp (t 0 • Y 0) :=
      hexp.comp ((contDiff_apply ℝ ℝ (0 : Fin (d + 1))).smul contDiff_const)
    have h2 : ContDiff ℝ ∞ fun t : Fin (d + 1) → ℝ => oneProd (fun i => Y i.succ) (fun i => t i.succ) :=
      (ih _).comp (contDiff_pi.2 fun i => contDiff_apply ℝ ℝ i.succ)
    exact h1.mul h2

theorem chart (G : Matrix (Fin n) (Fin n) ℂ) (hG : IsUnit G) :
    ∃ (d : ℕ) (Y : Fin d → Matrix (Fin n) (Fin n) ℂ), (∀ i, Y i ∈ lieOf G) ∧
      ∃ (U : Set (Matrix (Fin n) (Fin n) ℂ)) (φ : Matrix (Fin n) (Fin n) ℂ → (Fin d → ℝ)),
        IsOpen U ∧ (1 : Matrix (Fin n) (Fin n) ℂ) ∈ U ∧ ContDiffOn ℝ ∞ φ U ∧
        ∀ g ∈ U, g ∈ Formalism.QuantumDeterminants.UH G → oneProd Y (φ g) = g := by
  classical
  let L := lieSub G
  let d := Module.finrank ℝ L
  let b := Module.finBasis ℝ L
  let Y : Fin d → Matrix (Fin n) (Fin n) ℂ := fun i => (b i : Matrix (Fin n) (Fin n) ℂ)
  have hY : ∀ i, Y i ∈ lieOf G := fun i => (b i).2
  refine ⟨d, Y, hY, ?_⟩
  let ψ : (Fin d → ℝ) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ := L.subtype ∘ₗ b.equivFun.symm.toLinearMap
  have hψ : ∀ t, ψ t = lin Y t := by
    intro t
    simp [ψ, lin_apply, Y, Module.Basis.equivFun_symm_apply]
    try rfl
  have hinj : LinearMap.ker ψ = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact Subtype.val_injective.comp b.equivFun.symm.injective
  obtain ⟨Q0, hQ0⟩ := ψ.exists_leftInverse_of_injective hinj
  let Q : Matrix (Fin n) (Fin n) ℂ →L[ℝ] (Fin d → ℝ) := LinearMap.toContinuousLinearMap Q0
  have hQψ : ∀ t, Q (ψ t) = t := fun t => LinearMap.congr_fun hQ0 t
  have hback : ∀ X ∈ lieOf G, ψ (Q X) = X := by
    intro X hX
    have e : X = ψ (b.equivFun ⟨X, hX⟩) := by simp [ψ]
    rw [e, hQψ]
  let f : (Fin d → ℝ) → (Fin d → ℝ) := fun t => Q (cay (oneProd Y t))
  have hcay : HasStrictFDerivAt (cay : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ) (oneProd Y 0) := by
    rw [oneProd_zero]; exact hasStrictFDerivAt_cay
  have hΦ := hcay.comp (0 : Fin d → ℝ) (hasStrictFDerivAt_oneProd Y)
  have hf := Q.hasStrictFDerivAt.comp (0 : Fin d → ℝ) hΦ
  have hf' : HasStrictFDerivAt f
      ((ContinuousLinearEquiv.refl ℝ (Fin d → ℝ) : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ))) 0 := by
    refine hf.congr_fderiv ?_
    ext1 t
    change Q (lin Y t) = t
    rw [← hψ]
    exact hQψ t
  let W : Set (Fin d → ℝ) := {t | IsUnit (oneProd Y t + 1)}
  have hW : IsOpen W :=
    Continuous.isOpen_preimage ((contDiff_oneProd Y).continuous.add continuous_const) _ Units.isOpen
  have hfW : ContDiffOn ℝ ∞ f W := by
    intro t ht
    exact (Q.contDiff.contDiffAt.comp t ((contDiffAt_cay ht).comp t (contDiff_oneProd Y).contDiffAt)).contDiffWithinAt
  have hf0 : f 0 = 0 := by
    show Q (cay (oneProd Y 0)) = 0
    rw [oneProd_zero, cay_one, map_zero]
  have h0W : (0 : Fin d → ℝ) ∈ W := by
    show IsUnit (oneProd Y 0 + 1)
    rw [oneProd_zero]; exact isUnit_two
  have hfc : ContDiffAt ℝ ∞ f 0 := hfW.contDiffAt (hW.mem_nhds h0W)
  let e := hfc.toOpenPartialHomeomorph f hf'.hasFDerivAt (by simp)
  have hecoe : (e : (Fin d → ℝ) → (Fin d → ℝ)) = f := rfl
  let Gd : Set (Fin d → ℝ) := W ∩ fderiv ℝ f ⁻¹'
    Set.range (ContinuousLinearEquiv.toContinuousLinearMap : ((Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ)) → _)
  have hGd : IsOpen Gd :=
    (hfW.continuousOn_fderiv_of_isOpen hW (by simp)).isOpen_inter_preimage hW ContinuousLinearEquiv.isOpen
  have h0s : (0 : Fin d → ℝ) ∈ e.source := hfc.mem_toOpenPartialHomeomorph_source hf'.hasFDerivAt (by simp)
  have he0 : e.symm 0 = 0 := by
    have h2 := e.left_inv h0s
    have h3 : e 0 = 0 := hf0
    rw [h3] at h2
    exact h2
  let T : Set (Fin d → ℝ) := e.target ∩ e.symm ⁻¹' Gd
  have hT : IsOpen T := e.isOpen_inter_preimage_symm hGd
  have h0T : (0 : Fin d → ℝ) ∈ T := by
    refine ⟨?_, ?_⟩
    · have := hfc.image_mem_toOpenPartialHomeomorph_target hf'.hasFDerivAt (by simp)
      rwa [hf0] at this
    · show e.symm 0 ∈ Gd
      rw [he0]
      refine ⟨h0W, ?_⟩
      exact ⟨ContinuousLinearEquiv.refl ℝ (Fin d → ℝ), hf'.hasFDerivAt.fderiv.symm⟩
  have hsymm : ∀ a ∈ T, ContDiffAt ℝ ∞ e.symm a := by
    intro a ha
    obtain ⟨haT, haW, L', hL'⟩ := ha
    have hc : ContDiffAt ℝ ∞ f (e.symm a) := hfW.contDiffAt (hW.mem_nhds haW)
    have hd : DifferentiableAt ℝ f (e.symm a) := hc.differentiableAt (by simp)
    refine e.contDiffAt_symm haT (f₀' := L') ?_ hc
    rw [hecoe, hL']
    exact hd.hasFDerivAt
  let K : Matrix (Fin n) (Fin n) ℂ → (Fin d → ℝ) := fun g => Q (cay g)
  let V : Set (Matrix (Fin n) (Fin n) ℂ) := {g | IsUnit (g + 1)}
  have hV : IsOpen V := Continuous.isOpen_preimage (continuous_id.add continuous_const) _ Units.isOpen
  have hK : ∀ g ∈ V, ContDiffAt ℝ ∞ K g := fun g hg => Q.contDiff.contDiffAt.comp g (contDiffAt_cay hg)
  have hKc : ContinuousOn K V := fun g hg => (hK g hg).continuousAt.continuousWithinAt
  refine ⟨V ∩ K ⁻¹' T, fun g => e.symm (K g), hKc.isOpen_inter_preimage hV hT, ⟨isUnit_two, ?_⟩, ?_, ?_⟩
  · show Q (cay 1) ∈ T
    rw [cay_one, map_zero]
    exact h0T
  · intro g hg
    exact ((hsymm _ hg.2).comp g (hK g hg.1)).contDiffWithinAt
  · intro g hg hgG
    have haT : K g ∈ T := hg.2
    have h1 : e (e.symm (K g)) = K g := e.right_inv haT.1
    have h2 : e.symm (K g) ∈ Gd := haT.2
    have hu : IsUnit (oneProd Y (e.symm (K g)) + 1) := h2.1
    have h3 : Q (cay (oneProd Y (e.symm (K g)))) = Q (cay g) := h1
    have e1 : cay (oneProd Y (e.symm (K g))) = cay g := calc
      cay (oneProd Y (e.symm (K g))) = ψ (Q (cay (oneProd Y (e.symm (K g))))) :=
          (hback _ (cay_mem G _ (oneProd_mem hG Y hY _) hu)).symm
      _ = ψ (Q (cay g)) := congrArg ψ h3
      _ = cay g := hback _ (cay_mem G g hgG hg.1)
    exact cay_inj hu hg.1 e1

end Op

section Sup

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def idOp : @ContinuousLinearMap ℝ ℝ _ _ (RingHom.id ℝ) (Matrix (Fin n) (Fin n) ℂ) _ _
    (Matrix (Fin n) (Fin n) ℂ) (Matrix.linftyOpNormedAddCommGroup).toUniformSpace.toTopologicalSpace _ _
    (Matrix.linftyOpNormedSpace (R := ℝ)).toModule :=
  { toFun := id, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl, cont := continuous_id }

def idOp' : @ContinuousLinearMap ℝ ℝ _ _ (RingHom.id ℝ) (Matrix (Fin n) (Fin n) ℂ)
    (Matrix.linftyOpNormedAddCommGroup).toUniformSpace.toTopologicalSpace _
    (Matrix (Fin n) (Fin n) ℂ) _ _ (Matrix.linftyOpNormedSpace (R := ℝ)).toModule _ :=
  { toFun := id, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl, cont := continuous_id }

theorem contDiffOn_of_op {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Matrix (Fin n) (Fin n) ℂ → E}
    {U : Set (Matrix (Fin n) (Fin n) ℂ)}
    (h : @ContDiffOn ℝ _ (Matrix (Fin n) (Fin n) ℂ) Matrix.linftyOpNormedAddCommGroup
      (Matrix.linftyOpNormedSpace (R := ℝ)) E _ _ ∞ F U) : ContDiffOn ℝ ∞ F U :=
  @ContDiffOn.comp_continuousLinearMap ℝ (Matrix (Fin n) (Fin n) ℂ) E (Matrix (Fin n) (Fin n) ℂ) _
    Matrix.linftyOpNormedAddCommGroup (Matrix.linftyOpNormedSpace (R := ℝ)) _ _ _ _ U F ∞ h idOp

theorem contDiff_oneProd_sup {d : ℕ} (Y : Fin d → Matrix (Fin n) (Fin n) ℂ) : ContDiff ℝ ∞ (oneProd Y) :=
  @ContDiff.comp ℝ (Fin d → ℝ) (Matrix (Fin n) (Fin n) ℂ) (Matrix (Fin n) (Fin n) ℂ) _ _ _
    Matrix.linftyOpNormedAddCommGroup (Matrix.linftyOpNormedSpace (R := ℝ)) _ _ ∞ idOp' (oneProd Y)
    (@ContinuousLinearMap.contDiff ℝ (Matrix (Fin n) (Fin n) ℂ) (Matrix (Fin n) (Fin n) ℂ) _
      Matrix.linftyOpNormedAddCommGroup (Matrix.linftyOpNormedSpace (R := ℝ)) _ _ ∞ idOp')
    (contDiff_oneProd Y)

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem smV_iff_smoothOnH {G : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G)
    {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hρ : Formalism.QuantumDeterminants.IsCRepOn (Formalism.QuantumDeterminants.UH G) ρ) (x : H) :
    SmV (lieOf G) ρ x ↔ Formalism.QuantumDeterminants.SmoothOnH G (fun g => ρ g x) := by
  have hmul : ∀ a ∈ Formalism.QuantumDeterminants.UH G, ∀ b ∈ Formalism.QuantumDeterminants.UH G, ρ (a * b) x = ρ a (ρ b x) := by
    intro a ha b hb
    rw [hρ.2 a ha b hb]
    rfl
  constructor
  · intro hx g₀ hg₀
    obtain ⟨d, Y, hY, U, φ, hU, h1U, hφ, hφg⟩ := chart G hG
    have hΦ : ContDiff ℝ ∞ fun t : Fin d → ℝ => ρ (oneProd Y t) x := hx d Y hY
    have hφ' : ContDiffOn ℝ ∞ φ U := contDiffOn_of_op hφ
    have hg₀' : g₀ ∈ Formalism.QuantumDeterminants.UH G := hg₀
    have hd : IsUnit g₀.det := (Matrix.isUnit_iff_isUnit_det g₀).1 (isUnit_of_mem_UH hG hg₀')
    let Lm : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
      LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ g₀⁻¹)
    have hLm : ∀ g, Lm g = g₀⁻¹ * g := fun g => rfl
    refine ⟨Lm ⁻¹' U, fun g => ρ g₀ (ρ (oneProd Y (φ (Lm g))) x), hU.preimage Lm.continuous, ?_, ?_, ?_⟩
    · show Lm g₀ ∈ U
      rw [hLm, Matrix.nonsing_inv_mul _ hd]
      exact h1U
    · have h1 : ContDiffOn ℝ ∞ (φ ∘ Lm) (Lm ⁻¹' U) := hφ'.comp_continuousLinearMap Lm
      have h2 := hΦ.comp_contDiffOn h1
      exact ((ρ g₀).restrictScalars ℝ).contDiff.comp_contDiffOn h2
    · intro g hgU hgG
      have hgG' : g ∈ Formalism.QuantumDeterminants.UH G := hgG
      have hm : Lm g ∈ Formalism.QuantumDeterminants.UH G := by
        rw [hLm]; exact mul_mem_UH (inv_mem_UH hG hg₀') hgG'
      show ρ g x = ρ g₀ (ρ (oneProd Y (φ (Lm g))) x)
      rw [hφg _ hgU hm, ← hmul _ hg₀' _ hm, hLm, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
  · intro hx m Xs hXs
    have hP : ContDiff ℝ ∞ (oneProd Xs) := contDiff_oneProd_sup Xs
    show ContDiff ℝ ∞ fun t => ρ (oneProd Xs t) x
    rw [contDiff_iff_contDiffAt]
    intro t₀
    obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hx (oneProd Xs t₀) (oneProd_mem hG Xs hXs t₀)
    have hev : (fun t => ρ (oneProd Xs t) x) =ᶠ[𝓝 t₀] fun t => F (oneProd Xs t) := by
      filter_upwards [hP.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hgU)] with t ht
      exact hfF _ ht (oneProd_mem hG Xs hXs t)
    exact ((hF.contDiffAt (hU.mem_nhds hgU)).comp t₀ hP.contDiffAt).congr_of_eventuallyEq hev

end Sup

end GlobalTheory.SmChart
