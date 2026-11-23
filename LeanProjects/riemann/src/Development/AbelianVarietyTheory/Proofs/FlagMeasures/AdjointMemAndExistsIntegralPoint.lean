import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointRationalEquivariance

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov.RatElt

theorem hform_eq {E : Type} [CommRing E] [StarRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (x y : Fin n → E) : Formalism.UG.hform (starRingEnd E) J x y = star x ⬝ᵥ (J *ᵥ y) := by
  simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply,
    mul_assoc]

theorem cT_eq {E : Type} [CommRing E] [StarRing E] {n : ℕ} (M : Matrix (Fin n) (Fin n) E) :
    Formalism.UG.cT (starRingEnd E) M = Mᴴ := by
  ext i j
  simp [Formalism.UG.cT, conjTranspose_apply, starRingEnd_apply]

theorem unitary_map {A B : Type} [CommRing A] [CommRing B] {n : ℕ} (σ : A →+* A) (τ : B →+* B)
    (f : A →+* B) (hf : ∀ e, τ (f e) = f (σ e)) (J g : Matrix (Fin n) (Fin n) A)
    (h : Formalism.UG.cT σ g * J * g = J) : Formalism.UG.cT τ (g.map f) * J.map f * g.map f = J.map f := by
  have hc : Formalism.UG.cT τ (g.map f) = (Formalism.UG.cT σ g).map f := by
    ext i j
    simp [Formalism.UG.cT, hf]
  rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, h]

theorem exists_point (I : AutInst) (γ : GL (Fin I.n) I.E)
    (hγ : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J) : ∃ a : I.GA,
      (∀ v, uMat (a.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) ∧
      I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
  have hUJ : Formalism.UG.cT (starRingEnd I.E) (γ : Matrix (Fin I.n) (Fin I.n) I.E) * I.J * γ = I.J := hγ
  have hγH : (γ : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ * I.J * γ = I.J := by rwa [cT_eq] at hUJ
  let γA : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F)) :=
    Units.map (RingHom.mapMatrix (Formalism.UG.inclE (F := I.F) (Af I.F))).toMonoidHom γ
  have hγA : (γA : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) =
      (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) := rfl
  have hA : γA ∈ Formalism.UG.UPts I.cm.sig I.J (Af I.F) := by
    unfold Formalism.UG.UPts
    show Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (γA : Matrix (Fin I.n) (Fin I.n) _) *
        I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * γA = I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))
    rw [hγA]
    exact unitary_map (starRingEnd I.E) _ _ (fun e => Formalism.UG.P.csDual_sig_incl I.cm.sig e) _ _ hUJ

  let Mu : ∀ v, (Matrix (Fin I.n) (Fin I.n) ℂ)ˣ := fun v =>
    (I.P_unit v).unit⁻¹ * Units.map (RingHom.mapMatrix (I.φ v)).toMonoidHom γ * (I.P_unit v).unit
  have hMu : ∀ v, (Mu v : Matrix (Fin I.n) (Fin I.n) ℂ) =
      (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v := by
    intro v
    simp only [Mu, Units.val_mul, Matrix.coe_units_inv, IsUnit.unit_spec]
    rfl
  have hU : ∀ v, Mu v ∈ Formalism.REAL.UJ (I.ε v) := by
    intro v
    show Formalism.REAL.inUJ (I.ε v) (Mu v : Matrix (Fin I.n) (Fin I.n) ℂ)
    unfold Formalism.REAL.inUJ
    set Q := I.P v with hQdef
    set G := (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) with hGdef
    have hQ : Q * Q⁻¹ = 1 :=
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v))
    have hQH : Q⁻¹ᴴ * Qᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hQ, Matrix.conjTranspose_one]
    have hGH : Gᴴ = (γ : Matrix (Fin I.n) (Fin I.n) I.E)ᴴ.map (I.φ v) := by
      ext i j
      simp only [G, conjTranspose_apply, Matrix.map_apply]
      rw [I.cm.cmUnram.2.1 (I.φ v)]
      rfl
    have hGJG : Gᴴ * (I.J.map (I.φ v) * (G * Q)) = I.J.map (I.φ v) * Q := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hGH, hGdef, ← Matrix.map_mul, ← Matrix.map_mul, hγH]
    rw [hMu, ← I.P_spec v, ← hQdef, ← hGdef, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q⁻¹ᴴ Qᴴ, hQH, Matrix.one_mul, ← Matrix.mul_assoc Q Q⁻¹, hQ, Matrix.one_mul, hGJG]
  exact ⟨⟨fun v => ⟨Mu v, hU v⟩, ⟨γA, hA⟩⟩, fun v => hMu v, hγA⟩

theorem adj_mem (I : AutInst) (x : I.GA) (T : Matrix (Fin I.n) (Fin I.n) I.E)
    (hT : ∀ y ∈ lamX I x, T *ᵥ y ∈ lamX I x) : ∀ y ∈ lamX I x, (I.J⁻¹ * Tᴴ * I.J) *ᵥ y ∈ lamX I x := by
  intro y hy
  obtain ⟨-, -, -, hdual, -⟩ := GlobalTheory.PointLattice.lamX_selfDual I x
  rw [hdual]
  intro z hz
  have hJ : I.J * I.J⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr I.J_det)
  have key : Formalism.UG.hform (starRingEnd I.E) I.J z ((I.J⁻¹ * Tᴴ * I.J) *ᵥ y) =
      Formalism.UG.hform (starRingEnd I.E) I.J (T *ᵥ z) y := by
    have hM : I.J * (I.J⁻¹ * Tᴴ * I.J) = Tᴴ * I.J := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJ, Matrix.one_mul]
    rw [hform_eq, hform_eq, Matrix.mulVec_mulVec, hM, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.star_mulVec]
  rw [key]
  exact (hdual y).1 hy _ (hT z hz)

private lemma inv_mul_map_inclE_of_mem_lf (I : AutInst) (xf : I.Gf) (δ : Matrix (Fin I.n) (Fin I.n) I.E)
    (hδ : ∀ y ∈ lamX I (1, xf), δ *ᵥ y ∈ lamX I (1, xf))
    (x : Fin I.n → (TensorProduct I.F I.E (Af I.F))) (hx : x ∈ I.Lf) :
    ((((xf : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F)))⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) * δ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * ((xf : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F)))) *ᵥ x ∈ I.Lf := by
  set g : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F)) := (xf : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) with hg
  have hL : I.Lf = Formalism.UG.latS (F := I.F) (Af I.F) (IntAf I.F I.E) I.L := by
    unfold AutInst.Lf lamAf Formalism.UG.latS
    rw [Set.image_eq_range]
    rfl
  have hfin : Module.Finite (𝓞 I.E) I.L := Module.Finite.iff_fg.mpr I.L_fg
  have hrec := Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds I.F I.E (Fin I.n) I.L hfin I.L_span g
  have hglob : Formalism.UG.CS.globLat g I.L = lamX I (1, xf) := (GlobalTheory.PointLattice.lamX_eq_globLat I (1, xf)).symm
  rw [hglob] at hrec

  have hspan : ∀ w ∈ Submodule.span (IntAf I.F I.E) ((fun y : Fin I.n → I.E => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ''
        (lamX I (1, xf) : Set (Fin I.n → I.E))),
      δ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *ᵥ w ∈ Submodule.span (IntAf I.F I.E) ((fun y : Fin I.n → I.E => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ''
        (lamX I (1, xf) : Set (Fin I.n → I.E))) := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨y, hy, rfl⟩ := hw
      apply Submodule.subset_span
      refine ⟨δ *ᵥ y, hδ y hy, ?_⟩
      funext i
      exact RingHom.map_mulVec _ _ _ _
    | zero => simp
    | add w₁ w₂ _ _ h₁ h₂ =>
      rw [Matrix.mulVec_add]
      exact add_mem h₁ h₂
    | smul s w _ h =>
      rw [Matrix.mulVec_smul]
      exact Submodule.smul_mem _ s h
  have hu := (hrec ((g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) *ᵥ x)).2 (by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec, ← hL]
    exact hx)
  have h2 := (hrec _).1 (hspan _ hu)
  rw [← hL] at h2
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact h2

theorem adj_mem_and_exists_latGroup : ∀ (I : AutInst) (xf : I.Gf), (∀ T : Matrix (Fin I.n) (Fin I.n) I.E, (∀ y ∈ lamX I (1, xf), T *ᵥ y ∈ lamX I (1, xf)) → ∀ y ∈ lamX I (1, xf), (I.J⁻¹ * Tᴴ * I.J) *ᵥ y ∈ lamX I (1, xf)) ∧ ∀ γ : Matrix (Fin I.n) (Fin I.n) I.E, γᴴ * I.J * γ = I.J → (∀ y ∈ lamX I (1, xf), γ *ᵥ y ∈ lamX I (1, xf)) → ∃ g ∈ latGroup I xf, ∀ v, uMat (g v) = (I.P v)⁻¹ * γ.map (I.φ v) * I.P v := by
  intro I xf
  refine ⟨fun T hT => adj_mem I (1, xf) T hT, ?_⟩
  intro γ hγJ hγL
  have hdet : γ.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det hγJ
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h1
    exact I.J_det h1.symm
  let γu : GL (Fin I.n) I.E := Matrix.nonsingInvUnit γ (isUnit_iff_ne_zero.mpr hdet)
  have hγu : (γu : Matrix (Fin I.n) (Fin I.n) I.E) = γ := rfl
  have hmemUJ : γu ∈ Formalism.UG.UJ (starRingEnd I.E) I.J := by
    show Formalism.UG.cT (starRingEnd I.E) (γu : Matrix (Fin I.n) (Fin I.n) I.E) * I.J * γu = I.J
    rw [cT_eq, hγu]
    exact hγJ
  obtain ⟨a, ha1, ha2⟩ := exists_point I γu hmemUJ
  refine ⟨a.1, ⟨a, ⟨γu, hmemUJ, ha1, ha2⟩, rfl, ?_⟩, ha1⟩
  have hδγ : (I.J⁻¹ * γᴴ * I.J) * γ = 1 := by
    rw [show (I.J⁻¹ * γᴴ * I.J) * γ = I.J⁻¹ * (γᴴ * I.J * γ) by simp only [Matrix.mul_assoc], hγJ,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr I.J_det)]
  have hδγA : (I.J⁻¹ * γᴴ * I.J).map (Formalism.UG.inclE (F := I.F) (Af I.F)) * γ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) = 1 := by
    rw [← Matrix.map_mul, hδγ]
    simp
  have ha2' : ((a.2 : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) = γ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := by
    rw [← hγu]
    exact ha2
  set g : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F)) := (xf : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) with hg
  have hmat : (((xf⁻¹ * a.2 * xf : I.Gf) : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) =
      ((g⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) * γ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * (g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) := by
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, Units.val_mul]
    rw [ha2']
  have hprod : (((g⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) * (I.J⁻¹ * γᴴ * I.J).map (Formalism.UG.inclE (F := I.F) (Af I.F)) * (g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F)))) *
      (((g⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) * γ.map (Formalism.UG.inclE (F := I.F) (Af I.F)) * (g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F)))) = 1 := by
    calc _ = ((g⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) * ((I.J⁻¹ * γᴴ * I.J).map (Formalism.UG.inclE (F := I.F) (Af I.F)) *
            ((g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) * ((g⁻¹ : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F)))) * γ.map (Formalism.UG.inclE (F := I.F) (Af I.F))) * (g : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Units.mul_inv, Matrix.mul_one, hδγA, Matrix.mul_one, Units.inv_mul]
  show ((xf⁻¹ * a.2 * xf : I.Gf) : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) ∈ Formalism.UG.stabGL I.Lf
  unfold Formalism.UG.stabGL
  intro x
  show x ∈ I.Lf ↔ (((xf⁻¹ * a.2 * xf : I.Gf) : GL (Fin I.n) (TensorProduct I.F I.E (Af I.F))) : Matrix (Fin I.n) (Fin I.n) (TensorProduct I.F I.E (Af I.F))) *ᵥ x ∈ I.Lf
  rw [hmat]
  constructor
  · intro hx
    exact inv_mul_map_inclE_of_mem_lf I xf γ hγL x hx
  · intro hx
    have h1 := inv_mul_map_inclE_of_mem_lf I xf (I.J⁻¹ * γᴴ * I.J) (adj_mem I (1, xf) γ hγL) _ hx
    rwa [Matrix.mulVec_mulVec, hprod, Matrix.one_mulVec] at h1

end GlobalTheory.RadCov.RatElt
