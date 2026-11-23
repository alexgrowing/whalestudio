import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabNDenseCong

noncomputable section

open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped Classical TensorProduct

namespace Formalism.L2.SG.Pf.SlabNDensePf

open Formalism.L2.SG Formalism.L2.SG.PoincareInHH Formalism.L2.SG.Pf.Unip Formalism.L2.SG.Pf.UnipB

section KgPart

theorem cg_Lf_step (I : AutInst) {d₁ d₂ g : ℕ}
    (H₁ : ∀ y ∈ I.Lf, ∀ i, (d₁ : I.E ⊗[I.F] Af I.F) * y i ∈ IntAf I.F I.E)
    (H₂ : ∀ y : Fin I.n → I.E ⊗[I.F] Af I.F, (∀ i, y i ∈ IntAf I.F I.E) →
      (d₂ : I.E ⊗[I.F] Af I.F) • y ∈ I.Lf)
    {M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hM : cg_C (IntAf I.F I.E) (g * d₁ * d₂) M)
    (y : Fin I.n → I.E ⊗[I.F] Af I.F) (hy : y ∈ I.Lf) :
    ∃ z ∈ I.Lf, M *ᵥ y = (g : I.E ⊗[I.F] Af I.F) • z := by
  choose t ht e using hM
  refine ⟨(d₂ : I.E ⊗[I.F] Af I.F) • fun i => ∑ j, t i j * ((d₁ : I.E ⊗[I.F] Af I.F) * y j),
    H₂ _ fun i => sum_mem fun j _ => mul_mem (ht i j) (H₁ y hy j), ?_⟩
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [e i j]; push_cast; ring

theorem cg_Kg (I : AutInst) (k : I.Gf) (g : ℕ)
    (hk : ∀ y ∈ I.Lf, ∃ z ∈ I.Lf, (I.fmat k - 1) *ᵥ y = (g : I.E ⊗[I.F] Af I.F) • z) : k ∈ I.Kg g := by
  have fwd : ∀ v ∈ I.Lf, I.fmat k *ᵥ v ∈ I.Lf := by
    intro v hv
    obtain ⟨z, hz, e⟩ := hk v hv
    have e2 : I.fmat k *ᵥ v = v + (I.fmat k - 1) *ᵥ v := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [e2, e, Nat.cast_smul_eq_nsmul]
    exact add_mem hv (nsmul_mem hz g)
  have inv : ∀ w ∈ I.Lf, I.fmat k⁻¹ *ᵥ w ∈ I.Lf := by
    intro w hw
    refine PIW.AdelClassFin.dual_hat_lattice I _ fun y' hy' => ?_
    have e : PIW.AdelClassFin.hhat I y' (I.fmat k⁻¹ *ᵥ w) = PIW.AdelClassFin.hhat I (I.fmat k *ᵥ y') w := by
      rw [← PIW.AdelClassFin.dictTop_hhat_unit I k y' (I.fmat k⁻¹ *ᵥ w), Matrix.mulVec_mulVec,
        PIW.AdelClassFin.dictTop_mul_inv, Matrix.one_mulVec]
    rw [e]
    exact PIW.AdelClassFin.dual_hat_integral I _ (fwd y' hy') w hw
  refine ⟨?_, hk⟩
  show ∀ v, v ∈ I.Lf ↔ I.fmat k *ᵥ v ∈ I.Lf
  intro v
  refine ⟨fwd v, fun h => ?_⟩
  have h2 := inv _ h
  rwa [Matrix.mulVec_mulVec, PIW.AdelClassFin.dictTop_inv_mul, Matrix.one_mulVec] at h2

variable {D : D7} (X : HidaSetting D)

theorem cg_BB : Bf X * Bf' X = 1 := by
  unfold Bf Bf'
  rw [← Matrix.map_mul, Bm_mul_Bm']
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem cg_conj (y : X.B.I.Gf) : Bf X * Mf X y * Bf' X = X.B.I.fmat y := by
  simp only [Mf, ← Matrix.mul_assoc, cg_BB, Matrix.one_mul]
  rw [Matrix.mul_assoc, cg_BB, Matrix.mul_one]

theorem cg_fmat_eq (x y : X.B.I.Gf) :
    X.B.I.fmat (x⁻¹ * y) - 1 = X.B.I.fmat x⁻¹ * Bf X * (Mf X y - Mf X x) * Bf' X := by
  have key : Bf X * (Mf X y - Mf X x) * Bf' X = X.B.I.fmat y - X.B.I.fmat x := by
    rw [Matrix.mul_sub, Matrix.sub_mul, cg_conj, cg_conj]
  have h1 : X.B.I.fmat (x⁻¹ * y) = X.B.I.fmat x⁻¹ * X.B.I.fmat y := rfl
  have h2 : X.B.I.fmat x⁻¹ * X.B.I.fmat x = 1 := by
    rw [show X.B.I.fmat x⁻¹ * X.B.I.fmat x = X.B.I.fmat (x⁻¹ * x) from rfl, inv_mul_cancel]
    rfl
  rw [Matrix.mul_assoc (X.B.I.fmat x⁻¹) (Bf X), Matrix.mul_assoc (X.B.I.fmat x⁻¹), key, Matrix.mul_sub, h1, h2]

end KgPart

theorem level_of_close_element : KgOfClose := by
  intro D X x g hg
  obtain ⟨d₁, hd₁, H₁⟩ := Formalism.L2.SG.Pf.Tau.TraceIntegralityAlt.Lf_upper X.B.I
  obtain ⟨d₂, hd₂, H₂⟩ := Formalism.L2.SG.Pf.Tau.TraceIntegralityAlt.Lf_lower X.B.I
  obtain ⟨mP, hmP, hP⟩ := cg_D_exists (X.B.I.fmat x⁻¹ * Bf X)
  obtain ⟨mQ, hmQ, hQ⟩ := cg_D_exists (Bf' X)
  refine ⟨g * d₁ * d₂ * mQ * mP,
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hg hd₁) hd₂) hmQ) hmP, fun y hy => ?_⟩
  have hΔ : cg_C (IntAf X.B.I.F X.B.I.E) (g * d₁ * d₂) (X.B.I.fmat (x⁻¹ * y) - 1) := by
    rw [cg_fmat_eq X x y]
    exact cg_C_mul_right (cg_C_mul_left hP hy) hQ
  exact cg_Kg X.B.I _ g fun y' hy' => cg_Lf_step X.B.I H₁ H₂ hΔ y' hy'

section Approx

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cg_approx (k : ℕ) (hk : 1 ≤ k) (z : E ⊗[F] Af F) :
    ∃ a : E, ∃ t ∈ IntAf F E, Formalism.UG.inclE (F := F) (Af F) a - z = (k : E ⊗[F] Af F) * t := by
  obtain ⟨m, hm, hmz⟩ := PIW.AdelClassFin.dual_denominator F E z
  obtain ⟨a, r', hr', e⟩ := PIW.AdelClassFin.dual_dense F E (k * m) (Nat.mul_pos hk hm) _ hmz
  refine ⟨(a : E) / m, -r', neg_mem hr', ?_⟩
  have hm' : (m : E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have h2 : Formalism.UG.inclE (F := F) (Af F) ((1 : E) / m) * (m : E ⊗[F] Af F) = 1 := by
    rw [← map_natCast (Formalism.UG.inclE (F := F) (Af F)) m, ← map_mul, div_mul_cancel₀ _ hm', map_one]
  have hz : z = Formalism.UG.inclE (F := F) (Af F) ((1 : E) / m) * ((m : E ⊗[F] Af F) * z) := by
    rw [← mul_assoc, h2, one_mul]
  have ha : Formalism.UG.inclE (F := F) (Af F) ((a : E) / m) =
      Formalism.UG.inclE (F := F) (Af F) ((1 : E) / m) * Formalism.UG.inclE (F := F) (Af F) (a : E) := by
    rw [← map_mul]; congr 1; ring
  rw [ha]
  rw [hz]
  rw [e]
  push_cast
  linear_combination (-(k : E ⊗[F] Af F) * r') * h2

theorem cg_approx_mat {ι : Type} [Fintype ι] (lv : ι → ℕ) (Z : Matrix ι ι (E ⊗[F] Af F))
    (hZ : InPat lv 1 Z) (k : ℕ) (hk : 1 ≤ k) :
    ∃ W : Matrix ι ι E, InPat lv 1 W ∧ cg_C (IntAf F E) k (W.map (Formalism.UG.inclE (F := F) (Af F)) - Z) := by
  choose a t ht e using fun i j => cg_approx (F := F) k hk (Z i j)
  refine ⟨Matrix.of fun i j => if lv j < lv i + 1 then 0 else a i j, fun i j h => ?_, fun i j => ?_⟩
  · simp only [Matrix.of_apply, if_pos h]
  · by_cases h : lv j < lv i + 1
    · refine ⟨0, zero_mem _, ?_⟩
      simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.of_apply, if_pos h, map_zero, hZ i j h,
        sub_zero, mul_zero]
    · refine ⟨t i j, ht i j, ?_⟩
      simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.of_apply, if_neg h]
      exact e i j

end Approx

section Skew

variable {D : D7} (X : HidaSetting D)

theorem cg_C_cT (I : AutInst) {α β : Type} {c : ℕ} {A : Matrix α β (I.E ⊗[I.F] Af I.F)}
    (h : cg_C (IntAf I.F I.E) c A) :
    cg_C (IntAf I.F I.E) c (Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) A) := by
  have hle : IntAf I.F I.E ≤ (IntAf I.F I.E).comap (Formalism.UG.sigR I.cm.sig (Af I.F)) := by
    show Formalism.UG.tensInt (F := I.F) (Af I.F) (Formalism.UG.intOE I.E) (Formalism.UG.intAd I.F) ≤ _
    unfold Formalism.UG.tensInt
    rw [Subring.closure_le]
    rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · obtain ⟨z, rfl⟩ := hx
      rw [SetLike.mem_coe, Subring.mem_comap]
      apply Subring.subset_closure
      left
      exact ⟨⟨algebraMap (𝓞 I.E) I.E (NumberField.RingOfIntegers.mapRingHom (I.cm.sig : I.E →+* I.E) z),
        ⟨_, rfl⟩⟩, rfl⟩
    · rw [SetLike.mem_coe, Subring.mem_comap]
      apply Subring.subset_closure
      right
      exact ⟨⟨y, hy⟩, by simp [Formalism.UG.sigR]⟩
  intro i j
  obtain ⟨t, ht, hA⟩ := h j i
  refine ⟨Formalism.UG.sigR I.cm.sig (Af I.F) t, hle ht, ?_⟩
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, hA, map_mul, map_natCast]

theorem cg_cT_sub (I : AutInst) {α β : Type} (A B : Matrix α β (I.E ⊗[I.F] Af I.F)) :
    Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (A - B) =
      Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) A - Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) B := by
  ext i j
  simp [Formalism.UG.cT, map_sub]

theorem cg_map_cT {α β : Type} (M : Matrix α β X.B.I.E) :
    (Mᴴ).map (ic X) = Formalism.UG.cT (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)) (M.map (ic X)) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.conjTranspose_apply, Formalism.UG.cT, Matrix.transpose_apply]
  rfl

theorem cg_half : ic X (⅟2 : X.B.I.E) = (⅟2 : RA X) := by
  refine (invOf_eq_right_inv ?_).symm
  rw [← map_ofNat (ic X) 2, ← map_mul, mul_invOf_self, map_one]

theorem cg_JJ : (JB' X).map (ic X) * JBf X = 1 := by
  unfold JBf
  rw [← Matrix.map_mul, JB'_mul_JB]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem cg_proj_map (W : Matrix (Kap X) (Kap X) X.B.I.E) :
    (proj (JB X) (JB' X) W).map (ic X) = (⅟2 : RA X) • (W.map (ic X) - (JB' X).map (ic X) *
      Formalism.UG.cT (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)) (W.map (ic X)) * JBf X) := by
  have e1 : (JB' X * Wᴴ * JB X).map (ic X) =
      (JB' X).map (ic X) * Formalism.UG.cT (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)) (W.map (ic X)) * JBf X := by
    rw [Matrix.map_mul, Matrix.map_mul, cg_map_cT]
    unfold JBf
    rfl
  ext i j
  have e2 := congrFun (congrFun e1 i) j
  simp only [Matrix.map_apply] at e2
  simp only [proj, sharp, Matrix.map_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, map_mul,
    map_sub, cg_half, e2]

end Skew

theorem skew_hermitian_approximation : SkewApprox := by
  intro D X Z hZ hskew c hc
  obtain ⟨mJ, hmJ, hJ⟩ := cg_D_exists (JBf X)
  obtain ⟨mJ', hmJ', hJ'⟩ := cg_D_exists ((JB' X).map (ic X))
  obtain ⟨W, hW, hWZ⟩ := cg_approx_mat (lvk X) Z hZ (2 * c * mJ * mJ')
    (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos two_pos hc) hmJ) hmJ')
  refine ⟨proj (JB X) (JB' X) W, inPat_proj (JB_graded X) (JB'_graded X) hW,
    proj_skew (JB_herm X) (JB'_herm X) (JB'_mul_JB X) (JB_mul_JB' X) W, ?_⟩
  have hJZ : (JB' X).map (ic X) * Formalism.UG.cT (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)) Z * JBf X = -Z := by
    rw [Matrix.mul_assoc, hskew, Matrix.mul_neg, ← Matrix.mul_assoc, cg_JJ, Matrix.one_mul]
  have habel : ∀ P Q S : Matrix (Kap X) (Kap X) (RA X), P - S - (Q - -S) = (P - Q) - (S + S) := by
    intro P Q S; abel
  have hhalf : (⅟2 : RA X) • (Z + Z) = Z := by
    rw [← two_smul (RA X) Z, smul_smul, invOf_mul_self, one_smul]
  have e : (proj (JB X) (JB' X) W).map (ic X) - Z = (⅟2 : RA X) • ((W.map (ic X) - Z) -
      (JB' X).map (ic X) * Formalism.UG.cT (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)) (W.map (ic X) - Z) * JBf X) := by
    rw [cg_proj_map, cg_cT_sub, Matrix.mul_sub, Matrix.sub_mul, hJZ, habel, smul_sub _ _ (Z + Z), hhalf]
  show cg_C (IntAf X.B.I.F X.B.I.E) c _
  rw [e]
  refine cg_C_half (cg_C_sub (cg_C_dvd (k := mJ) (cg_C_dvd (k := mJ') hWZ)) ?_)
  exact cg_C_mul_right (cg_C_mul_left hJ' (cg_C_cT X.B.I hWZ)) hJ

end Formalism.L2.SG.Pf.SlabNDensePf
