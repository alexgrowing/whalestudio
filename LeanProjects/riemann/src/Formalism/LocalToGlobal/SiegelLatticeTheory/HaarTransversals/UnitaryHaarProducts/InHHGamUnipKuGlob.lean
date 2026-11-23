import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHGamUnipKuDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHLatOfLattice
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.Pf
open Matrix NumberField
open scoped TensorProduct

namespace Formalism.L2.SG.PoincareInHH.Cut.GU

open Formalism.L2.SG.Pf.Level

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem hA_zero_r (x : VA X.B.I) : hA X.B.I x 0 = 0 := by
  simp only [hA, Formalism.UG.hform, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

def YP (v : VA X.B.I) : Prop :=
  v ∈ X.B.I.Lf ∧ (∀ a, hA X.B.I (incl X.B.I (X.eR a)) v = 0) ∧ (∀ a, hA X.B.I (incl X.B.I (X.fR a)) v = 0) ∧
    hA X.B.I (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u)) v = 0

private theorem hA_add_right_unitary_haar_products (x y z : VA X.B.I) : hA X.B.I x (y + z) = hA X.B.I x y + hA X.B.I x z := by
  simp only [hA, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem yp_add {v w : VA X.B.I} (hv : YP X u v) (hw : YP X u w) : YP X u (v + w) := by
  unfold YP at hv hw ⊢
  obtain ⟨hv1, hv2, hv3, hv4⟩ := hv
  obtain ⟨hw1, hw2, hw3, hw4⟩ := hw
  refine ⟨add_mem hv1 hw1, fun a => ?_, fun a => ?_, ?_⟩
  · rw [hA_add_right_unitary_haar_products, hv2 a, hw2 a, add_zero]
  · rw [hA_add_right_unitary_haar_products, hv3 a, hw3 a, add_zero]
  · rw [hA_add_right_unitary_haar_products, hv4, hw4, add_zero]

theorem yp_zero : YP X u 0 := by
  unfold YP
  exact ⟨zero_mem _, fun a => hA_zero_r X _, fun a => hA_zero_r X _, hA_zero_r X _⟩

private theorem hA_smul_right_unitary_haar_products (c : IntAf X.B.I.F X.B.I.E) (x y : VA X.B.I) :
    hA X.B.I x (c • y) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I x y := by
  simp only [hA, Formalism.UG.hform, Pi.smul_apply, Subring.smul_def, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem yp_smul (c : IntAf X.B.I.F X.B.I.E) {v : VA X.B.I} (hv : YP X u v) : YP X u (c • v) := by
  unfold YP at hv ⊢
  obtain ⟨hv1, hv2, hv3, hv4⟩ := hv
  refine ⟨Submodule.smul_mem _ c hv1, fun a => ?_, fun a => ?_, ?_⟩
  · rw [hA_smul_right_unitary_haar_products, hv2 a, mul_zero]
  · rw [hA_smul_right_unitary_haar_products, hv3 a, mul_zero]
  · rw [hA_smul_right_unitary_haar_products, hv4, mul_zero]

def Yu : Submodule (IntAf X.B.I.F X.B.I.E) (VA X.B.I) where
  carrier := {v | YP X u v}
  add_mem' := fun hv hw => yp_add X u hv hw
  zero_mem' := yp_zero X u
  smul_mem' := fun c _ hv => yp_smul X u c hv

theorem zmod_cancel {t : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F} (ht : t ∈ IntAf X.B.I.F X.B.I.E) {c : ℕ}
    (hc : Nat.Coprime c X.B.g) (h : ZMod' X.B.I X.B.g ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t)) :
    ZMod' X.B.I X.B.g t := by
  unfold ZMod' at h ⊢
  obtain ⟨s, hs, hcs⟩ := h
  have hb := Nat.gcd_eq_gcd_ab c X.B.g
  rw [Nat.Coprime.gcd_eq_one hc] at hb
  have key : (1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) = (c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((Nat.gcdA c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) +
      (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((Nat.gcdB c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
    have h1 := congrArg (fun z : ℤ => (z : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) hb
    simpa using h1
  refine ⟨((Nat.gcdA c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s + ((Nat.gcdB c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t, ?_, ?_⟩
  · exact add_mem (mul_mem (intCast_mem _ _) hs) (mul_mem (intCast_mem _ _) ht)
  · calc t = 1 * t := (one_mul t).symm
      _ = ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((Nat.gcdA c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) +
          (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((Nat.gcdB c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) * t := by rw [← key]
      _ = ((Nat.gcdA c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t) +
          (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (((Nat.gcdB c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t) := by ring
      _ = (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (((Nat.gcdA c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * s + ((Nat.gcdB c X.B.g : ℤ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * t) := by
          rw [hcs]; ring

theorem hermitian_e0_congruent {v : VA X.B.I} (hv : YP X u v) (a : Fin D.R.rS) : ZMod' X.B.I X.B.g (hA X.B.I (X.e0 a) v) := by
  obtain ⟨hvL, he, -, -⟩ := hv
  obtain ⟨c, hc, hcm⟩ := (X.basisApprox a).1
  have h1 := Z_left X hcm hvL
  rw [hA_natsmul_left, hA_sub_left] at h1
  have h0 : hA X.B.I (incl X.B.I (crdOf X.B.I X.ιE X.bas (X.eX a))) v = 0 := he a
  rw [h0, sub_zero] at h1
  exact zmod_cancel X (unitaryCongruence.hA_int X.B.I (X.vectorsInLattice.1 a).1 hvL) hc h1

theorem hermitian_f0_congruent {v : VA X.B.I} (hv : YP X u v) (a : Fin D.R.rS) : ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) v) := by
  obtain ⟨hvL, -, hf, -⟩ := hv
  obtain ⟨c, hc, hcm⟩ := (X.basisApprox a).2
  have h1 := Z_left X hcm hvL
  rw [hA_natsmul_left, hA_sub_left] at h1
  have h0 : hA X.B.I (incl X.B.I (crdOf X.B.I X.ιE X.bas (X.fY a))) v = 0 := hf a
  rw [h0, sub_zero] at h1
  exact zmod_cancel X (unitaryCongruence.hA_int X.B.I (X.vectorsInLattice.1 a).2 hvL) hc h1

theorem hermitian_z0_congruent {v : VA X.B.I} (hv : YP X u v) : ZMod' X.B.I X.B.g (hA X.B.I X.z0 v) := by
  obtain ⟨hvL, -, -, hz⟩ := hv
  obtain ⟨c, hc, hcm⟩ := X.xu_z u
  have h1 := Z_left X hcm hvL
  rw [hA_natsmul_left, hA_sub_left] at h1
  have h0 : hA X.B.I (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (crdOf X.B.I X.ιE X.bas (X.zu u))) v = 0 := hz
  rw [h0, zero_sub] at h1
  have h2 : ZMod' X.B.I X.B.g ((c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * hA X.B.I X.z0 v) := by
    have := unitaryCongruence.Z_sub X.B.I X.B.g (unitaryCongruence.Z_zero X.B.I X.B.g) h1
    rwa [mul_neg, sub_neg_eq_add, zero_add] at this
  exact zmod_cancel X (unitaryCongruence.hA_int X.B.I X.vectorsInLattice.2.1 hvL) hc h2

theorem mL_exists {m : VA X.B.I} (hm : m ∈ mL X.B.I X.B.g) :
    ∃ x ∈ X.B.I.Lf, m = (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x := by
  unfold mL at hm
  induction hm using Submodule.span_induction with
  | mem y hy => exact hy
  | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
  | add y z _ _ hy hz =>
    obtain ⟨x1, h1, rfl⟩ := hy
    obtain ⟨x2, h2, rfl⟩ := hz
    exact ⟨x1 + x2, add_mem h1 h2, (smul_add _ _ _).symm⟩
  | smul a y _ hy =>
    obtain ⟨x1, h1, rfl⟩ := hy
    refine ⟨a • x1, Submodule.smul_mem _ a h1, ?_⟩
    funext i
    simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
    ring

theorem xu_inv_fix {w : VA X.B.I} (hw : X.B.I.fmat (X.xu u) *ᵥ w = w) : X.B.I.fmat (X.xu u)⁻¹ *ᵥ w = w := by
  conv_lhs => rw [← hw]
  rw [Matrix.mulVec_mulVec]
  have h1 : X.B.I.fmat (X.xu u)⁻¹ * X.B.I.fmat (X.xu u) = 1 := by
    simp only [Formalism.MainNotions.S.AutInst.fmat, Subgroup.coe_inv, Units.inv_mul]
  rw [h1, Matrix.one_mulVec]

theorem conj_fix (η : X.B.I.Gf) (hη : η ∈ Hfin X u) (p : VA X.B.I) (w : Fin X.B.I.n → X.B.I.E)
    (hw : w ∈ fixSet X u) (hp : X.B.I.fmat (X.xu u) *ᵥ p = incl X.B.I w) :
    X.B.I.fmat ((X.xu u)⁻¹ * η * X.xu u) *ᵥ p = X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I w := by
  have hη' : ∀ y ∈ fixSet X u, X.B.I.fmat η *ᵥ incl X.B.I y = incl X.B.I y := hη
  have e1 : X.B.I.fmat ((X.xu u)⁻¹ * η * X.xu u) =
      X.B.I.fmat (X.xu u)⁻¹ * X.B.I.fmat η * X.B.I.fmat (X.xu u) := by
    simp only [Formalism.MainNotions.S.AutInst.fmat, Subgroup.coe_mul, Units.val_mul]
  rw [e1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hp, hη' w hw]

theorem xu_e (a : Fin D.R.rS) : X.B.I.fmat (X.xu u) *ᵥ incl X.B.I (X.eR a) = incl X.B.I (X.eR a) :=
  (X.xu_fix u a).1

theorem xu_f (a : Fin D.R.rS) : X.B.I.fmat (X.xu u) *ᵥ incl X.B.I (X.fR a) = incl X.B.I (X.fR a) :=
  (X.xu_fix u a).2

theorem transport_fixes_z : X.B.I.fmat (X.xu u) *ᵥ (X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I (X.zR u)) = incl X.B.I (X.zR u) := by
  rw [Matrix.mulVec_mulVec]
  have h1 : X.B.I.fmat (X.xu u) * X.B.I.fmat (X.xu u)⁻¹ = 1 := by
    simp only [Formalism.MainNotions.S.AutInst.fmat, Subgroup.coe_inv, Units.mul_inv]
  rw [h1, Matrix.one_mulVec]

private theorem hA_eq_dotProduct_sigR (x y : VA X.B.I) :
    hA X.B.I x y = (fun i => Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F) (x i)) ⬝ᵥ ((X.B.I.J.map ⇑(Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F))) *ᵥ y) := by
  simp only [hA, Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

private theorem dotProduct_mulVec_eq_transpose (A : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Af X.B.I.F)) (a b : VA X.B.I) :
    (A *ᵥ a) ⬝ᵥ b = a ⬝ᵥ (Aᵀ *ᵥ b) := by
  simp only [dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem hA_fmat_mulVec (κ : X.B.I.Gf) (x y : VA X.B.I) :
    hA X.B.I (X.B.I.fmat κ *ᵥ x) (X.B.I.fmat κ *ᵥ y) = hA X.B.I x y := by
  have hκ : Formalism.UG.cT (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)) (X.B.I.fmat κ) * (X.B.I.J.map ⇑(Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F))) * X.B.I.fmat κ = X.B.I.J.map ⇑(Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) := κ.2
  rw [hA_eq_dotProduct_sigR, hA_eq_dotProduct_sigR]
  have e1 : (fun i => Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F) ((X.B.I.fmat κ *ᵥ x) i)) =
      ((X.B.I.fmat κ).map (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F))) *ᵥ (fun i => Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F) (x i)) := by
    funext i
    exact RingHom.map_mulVec _ _ _ i
  have e2 : ((X.B.I.fmat κ).map (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)))ᵀ = Formalism.UG.cT (Formalism.UG.sigR X.B.I.cm.sig (Af X.B.I.F)) (X.B.I.fmat κ) := rfl
  rw [e1, dotProduct_mulVec_eq_transpose, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, e2, hκ]

theorem yu_stable (η : X.B.I.Gf) (hη : η ∈ Hfin X u) (hK : (X.xu u)⁻¹ * η * X.xu u ∈ X.B.I.Kset)
    (v : VA X.B.I) (hv : v ∈ Yu X u) : X.B.I.fmat ((X.xu u)⁻¹ * η * X.xu u) *ᵥ v ∈ Yu X u := by
  set κ := (X.xu u)⁻¹ * η * X.xu u with hκdef
  have hv' : YP X u v := hv
  show YP X u _
  unfold YP at hv' ⊢
  obtain ⟨hv1, hv2, hv3, hv4⟩ := hv'
  have hKs : ∀ x : VA X.B.I, x ∈ X.B.I.Lf ↔ X.B.I.fmat κ *ᵥ x ∈ X.B.I.Lf := hK
  have hηi : η⁻¹ ∈ Hfin X u := inv_mem hη
  have hinv : ∀ w ∈ fixSet X u, ∀ p : VA X.B.I, X.B.I.fmat (X.xu u) *ᵥ p = incl X.B.I w →
      X.B.I.fmat κ⁻¹ *ᵥ p = X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I w := by
    intro w hw p hp
    have e : κ⁻¹ = (X.xu u)⁻¹ * η⁻¹ * X.xu u := by rw [hκdef]; group
    rw [e]
    exact conj_fix X u η⁻¹ hηi p w hw hp
  have hmove : ∀ a : VA X.B.I,
      hA X.B.I a (X.B.I.fmat κ *ᵥ v) = hA X.B.I (X.B.I.fmat κ⁻¹ *ᵥ a) v := by
    intro a
    have e : a = X.B.I.fmat κ *ᵥ (X.B.I.fmat κ⁻¹ *ᵥ a) := by
      rw [Matrix.mulVec_mulVec]
      simp only [Formalism.MainNotions.S.AutInst.fmat, Subgroup.coe_inv, Units.mul_inv, Matrix.one_mulVec]
    conv_lhs => rw [e]
    exact hA_fmat_mulVec X κ _ _
  refine ⟨(hKs v).1 hv1, fun a => ?_, fun a => ?_, ?_⟩
  · rw [hmove]
    have hw : X.eR a ∈ fixSet X u := by
      unfold fixSet
      exact Or.inl (Or.inl (Set.mem_range_self a))
    rw [hinv _ hw _ (xu_e X u a), xu_inv_fix X u (xu_e X u a)]
    exact hv2 a
  · rw [hmove]
    have hw : X.fR a ∈ fixSet X u := by
      unfold fixSet
      exact Or.inl (Or.inr (Set.mem_range_self a))
    rw [hinv _ hw _ (xu_f X u a), xu_inv_fix X u (xu_f X u a)]
    exact hv3 a
  · rw [hmove]
    have hw : X.zR u ∈ fixSet X u := by
      unfold fixSet
      exact Or.inr (Set.mem_singleton _)
    rw [hinv _ hw _ (transport_fixes_z X u)]
    exact hv4

theorem crd_sub (v w : (VS D).V) : X.crd (v - w) = X.crd v - X.crd w := by
  funext i
  simp only [HidaSetting.crd, crdOf, map_sub, Finsupp.coe_sub, Pi.sub_apply]

theorem crd_smul' (a : D.host.E) (v : (VS D).V) : X.crd (a • v) = X.ιE.symm a • X.crd v := by
  funext i
  simp only [HidaSetting.crd, crdOf, map_smul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul]

def hatv (h : Hfin X u) (y : (VS D).V) : VA X.B.I :=
  X.B.I.fmat ((h : X.B.I.Gf) * X.xu u)⁻¹ *ᵥ incl X.B.I (X.crd y)

theorem hatv_sub (h : Hfin X u) (a b : (VS D).V) : hatv X u h (a - b) = hatv X u h a - hatv X u h b := by
  unfold hatv
  rw [crd_sub]
  have e : incl X.B.I (X.crd a - X.crd b) = incl X.B.I (X.crd a) - incl X.B.I (X.crd b) := by
    funext i
    simp only [incl, Pi.sub_apply, map_sub]
  rw [e, Matrix.mulVec_sub]

theorem hatv_smul (h : Hfin X u) (c : D.host.E) (y : (VS D).V) :
    hatv X u h (c • y) = Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm c) • hatv X u h y := by
  unfold hatv
  rw [crd_smul']
  have e : incl X.B.I (X.ιE.symm c • X.crd y) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm c) • incl X.B.I (X.crd y) := by
    funext i
    simp only [incl, Pi.smul_apply, smul_eq_mul, map_mul]
  rw [e, Matrix.mulVec_smul]

theorem P_fix (h : Hfin X u) (w : Fin X.B.I.n → X.B.I.E) (hw : w ∈ fixSet X u) :
    X.B.I.fmat ((h : X.B.I.Gf) * X.xu u)⁻¹ *ᵥ incl X.B.I w = X.B.I.fmat (X.xu u)⁻¹ *ᵥ incl X.B.I w := by
  have hh : (h : X.B.I.Gf)⁻¹ ∈ Hfin X u := inv_mem h.2
  have hh' : ∀ y ∈ fixSet X u, X.B.I.fmat (h : X.B.I.Gf)⁻¹ *ᵥ incl X.B.I y = incl X.B.I y := hh
  have e1 : X.B.I.fmat ((h : X.B.I.Gf) * X.xu u)⁻¹ =
      X.B.I.fmat (X.xu u)⁻¹ * X.B.I.fmat (h : X.B.I.Gf)⁻¹ := by
    rw [_root_.mul_inv_rev]
    simp only [Formalism.MainNotions.S.AutInst.fmat, Subgroup.coe_mul, Units.val_mul]
  rw [e1, ← Matrix.mulVec_mulVec, hh' w hw]

theorem hatv_Y (h : Hfin X u) (y : (VS D).V) (hyL : hatv X u h y ∈ X.B.I.Lf)
    (hyW : y ∈ orth (VS D) (Submodule.span D.host.E (Set.range X.eX ∪ Set.range X.fY ∪ {X.zu u}))) :
    hatv X u h y ∈ Yu X u := by
  have horth := mem_orth_iff_bl.1 hyW
  have hiso : ∀ p, hA X.B.I (X.B.I.fmat ((h : X.B.I.Gf) * X.xu u)⁻¹ *ᵥ p) (hatv X u h y) =
      hA X.B.I p (incl X.B.I (X.crd y)) := fun p => hA_fmat X _ _ _
  refine ⟨hyL, fun a => ?_, fun a => ?_, ?_⟩
  · rw [← xu_inv_fix X u (xu_e X u a), ← P_fix X u h _ (eR_mem_fix X u a), hiso]
    show hA X.B.I (incl X.B.I (X.crd (X.eX a))) (incl X.B.I (X.crd y)) = 0
    rw [hA_crd, horth _ (Submodule.subset_span (Or.inl (Or.inl ⟨a, rfl⟩))), map_zero, map_zero]
  · rw [← xu_inv_fix X u (xu_f X u a), ← P_fix X u h _ (fR_mem_fix X u a), hiso]
    show hA X.B.I (incl X.B.I (X.crd (X.fY a))) (incl X.B.I (X.crd y)) = 0
    rw [hA_crd, horth _ (Submodule.subset_span (Or.inl (Or.inr ⟨a, rfl⟩))), map_zero, map_zero]
  · rw [← P_fix X u h _ (zR_mem_fix X u), hiso]
    show hA X.B.I (incl X.B.I (X.crd (X.zu u))) (incl X.B.I (X.crd y)) = 0
    rw [hA_crd, horth _ (Submodule.subset_span (Or.inr rfl)), map_zero, map_zero]

theorem inv_g_cancel : Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((X.B.g : D.host.E)⁻¹)) *
    (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) = 1 := by
  have hg : X.B.g ≠ 0 := by
    rw [X.g_eq]
    exact Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  have hgE : ((X.B.g : ℕ) : X.B.I.E) ≠ 0 := Nat.cast_ne_zero.mpr hg
  rw [map_inv₀, map_natCast, ← map_natCast (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) X.B.g, ← map_mul,
    inv_mul_cancel₀ hgE, map_one]

section QuotGen

variable {E V : Type} [Field E] [NumberField E] [StarRing E] [AddCommGroup V] [Module E V]
  [FiniteDimensional E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]

def dm1 {M : Type} [AddCommGroup M] [Module E M] (δ : M ≃ₗ[E] M) : Module.End E M :=
  ((δ : M →ₗ[E] M) : Module.End E M) - 1

theorem dm1_apply {M : Type} [AddCommGroup M] [Module E M] (δ : M ≃ₗ[E] M) (v : M) : dm1 δ v = δ v - v := by
  rfl

theorem q_aut (δ : V ≃ₗ[E] V) (W : Submodule E V) (hW : W.map (δ : V →ₗ[E] V) = W)
    (hX : (⊥ : Submodule E V).map (δ : V →ₗ[E] V) = ⊥) (Λ : Submodule (𝓞 E) V) (hδΛ : ∀ v, δ v ∈ Λ ↔ v ∈ Λ) :
    qEquiv δ W ⊥ hW hX ∈ Formalism.L2.Col.autLat (qLat Λ W ⊥) := by
  unfold qEquiv qLat
  show Formalism.HermitianLatticesTheory.gmap _ _ = _
  unfold Formalism.HermitianLatticesTheory.gmap
  apply le_antisymm
  · rintro _ ⟨q, hq, rfl⟩
    obtain ⟨w, hw, rfl⟩ := hq
    refine ⟨δ.ofSubmodules W W hW w, ?_, rfl⟩
    show δ (w : V) ∈ Λ
    exact (hδΛ (w : V)).2 hw
  · rintro _ ⟨w, hw, rfl⟩
    have e1 : δ (((δ.ofSubmodules W W hW).symm w : W) : V) = (w : V) :=
      congrArg Subtype.val ((δ.ofSubmodules W W hW).apply_symm_apply w)
    refine ⟨Submodule.Quotient.mk ((δ.ofSubmodules W W hW).symm w),
      ⟨(δ.ofSubmodules W W hW).symm w, ?_, rfl⟩, ?_⟩
    · show (((δ.ofSubmodules W W hW).symm w : W) : V) ∈ Λ
      rw [← hδΛ, e1]
      exact hw
    · show Submodule.Quotient.mk ((δ.ofSubmodules W W hW) ((δ.ofSubmodules W W hW).symm w)) =
        Submodule.Quotient.mk w
      rw [LinearEquiv.apply_symm_apply]

theorem q_powB (δ : V ≃ₗ[E] V) (W : Submodule E V) (hW : W.map (δ : V →ₗ[E] V) = W)
    (hX : (⊥ : Submodule E V).map (δ : V →ₗ[E] V) = ⊥) :
    ∀ j : ℕ, ∀ w w' : W, (w' : V) = ((dm1 δ) ^ j) (w : V) →
      ((dm1 (qEquiv δ W ⊥ hW hX)) ^ j) (Submodule.Quotient.mk w) = Submodule.Quotient.mk w' := by
  intro j
  induction j with
  | zero =>
    intro w w' h
    obtain rfl : w' = w := Subtype.ext (by simpa using h)
    rfl
  | succ j ih =>
    intro w w' h
    have hmem : δ (w : V) - (w : V) ∈ W :=
      W.sub_mem (δ.ofSubmodules W W hW w).2 w.2
    have h2 := ih ⟨δ (w : V) - (w : V), hmem⟩ w' (by rw [h, pow_succ, Module.End.mul_apply, dm1_apply])
    rw [pow_succ, Module.End.mul_apply, ← h2, dm1_apply]
    congr 1

theorem q_pow_one (δ : V ≃ₗ[E] V) (W : Submodule E V) (hW : W.map (δ : V →ₗ[E] V) = W)
    (hX : (⊥ : Submodule E V).map (δ : V →ₗ[E] V) = ⊥) (m : ℕ) (hδm : ∀ v, (δ ^ m) v = v) :
    qEquiv δ W ⊥ hW hX ^ m = 1 := by
  have key : ∀ k : ℕ, ∀ w : W, ∃ w' : W, (w' : V) = (δ ^ k) (w : V) ∧
      (qEquiv δ W ⊥ hW hX ^ k) (Submodule.Quotient.mk w) = Submodule.Quotient.mk w' := by
    intro k
    induction k with
    | zero => intro w; exact ⟨w, by rw [pow_zero]; rfl, by rw [pow_zero]; rfl⟩
    | succ k ih =>
      intro w
      obtain ⟨w', h1, h2⟩ := ih (δ.ofSubmodules W W hW w)
      refine ⟨w', ?_, ?_⟩
      · rw [h1, pow_succ]
        rfl
      · rw [pow_succ]
        change (qEquiv δ W ⊥ hW hX ^ k) (qEquiv δ W ⊥ hW hX (Submodule.Quotient.mk w)) = _
        rw [← h2]
        rfl
  ext q
  refine Submodule.Quotient.induction_on _ q fun w => ?_
  obtain ⟨w', h1, h2⟩ := key m w
  rw [h2]
  have e : w' = w := Subtype.ext (by rw [h1, hδm])
  rw [e]
  rfl

theorem q_fix (δ : V ≃ₗ[E] V) (W : Submodule E V) (hW : W.map (δ : V →ₗ[E] V) = W)
    (hX : (⊥ : Submodule E V).map (δ : V →ₗ[E] V) = ⊥) (hone : qEquiv δ W ⊥ hW hX = 1) : ∀ w ∈ W, δ w = w := by
  intro w hw
  have h1 := DFunLike.congr_fun hone (Submodule.Quotient.mk (⟨w, hw⟩ : W))
  unfold qEquiv Xc at h1
  change Submodule.Quotient.mk (δ.ofSubmodules W W hW ⟨w, hw⟩) = Submodule.Quotient.mk (⟨w, hw⟩ : W) at h1
  rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.mem_bot] at h1
  have h2 : δ w - w = 0 := h1
  exact sub_eq_zero.mp h2

end QuotGen

set_option maxHeartbeats 800000 in

theorem globStep_holds (hK : X.LevelSubgroupCharacter) : GlobalCondition X u hK := by
  intro _hL hC h γ hγ hfo
  obtain ⟨hGF, hH⟩ := Subgroup.mem_inf.1 γ.2
  have hGF' : (γ : X.B.I.GA) ∈ X.B.I.GFset := hGF
  obtain ⟨M, hM, -, hf⟩ := hGF'
  have hfin := (Subgroup.mem_prod.1 hH).2
  set δ := matEC X M with hδ
  have hincl : ∀ y, incl X.B.I (X.crd (δ y)) = X.B.I.fmat (γ : X.B.I.GA).2 *ᵥ incl X.B.I (X.crd y) :=
    fun y => by rw [hδ, matE_inclC, hf]
  have hinj : ∀ y y' : (VS D).V, incl X.B.I (X.crd y) = incl X.B.I (X.crd y') → y = y' := by
    intro y y' h1
    apply X.bas.equivFun.injective
    funext i
    exact X.ιE.symm.injective (inclInjC X (congrFun h1 i))
  have hfix : ∀ y, X.crd y ∈ fixSet X u → δ y = y := fun y hy =>
    hinj _ _ (by rw [hincl]; exact hfin _ hy)
  have hδiso : δ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := matE_isomC X M hM
  clear_value δ
  obtain ⟨Λ, hΛ, hΛlat⟩ := latOfLattice_holds X u h
  haveI := hΛlat
  have hκ' : (X.xu u)⁻¹ * ((h : X.B.I.Gf)⁻¹ * ((iotaF X u γ : Hfin X u) : X.B.I.Gf) * h) * X.xu u ∈ X.K2 := by
    simpa [Ku] using hγ
  have hκ : (X.xu u)⁻¹ * ((h : X.B.I.Gf)⁻¹ * (γ : X.B.I.GA).2 * h) * X.xu u ∈ X.K2 := hκ'
  have hmemΛ : ∀ w, w ∈ Λ ↔ hatv X u h w ∈ X.B.I.Lf := by
    intro w; rw [← SetLike.mem_coe, hΛ]; rfl
  have hPκ : X.B.I.fmat ((X.xu u)⁻¹ * ((h : X.B.I.Gf)⁻¹ * (γ : X.B.I.GA).2 * h) * X.xu u) *
      X.B.I.fmat ((h : X.B.I.Gf) * X.xu u)⁻¹ = X.B.I.fmat ((h : X.B.I.Gf) * X.xu u)⁻¹ * X.B.I.fmat (γ : X.B.I.GA).2 := by
    have e : (X.xu u)⁻¹ * ((h : X.B.I.Gf)⁻¹ * (γ : X.B.I.GA).2 * h) * X.xu u * ((h : X.B.I.Gf) * X.xu u)⁻¹ =
        ((h : X.B.I.Gf) * X.xu u)⁻¹ * (γ : X.B.I.GA).2 := by group
    rw [← fmat_mul, ← fmat_mul, e]
  have hδΛ : ∀ v, δ v ∈ Λ ↔ v ∈ Λ := by
    intro v
    rw [hmemΛ, hmemΛ]
    unfold hatv
    rw [hincl, mulVec_mulVec, ← hPκ, ← mulVec_mulVec]
    exact ((hκ.1 _)).symm
  have hUfix : ∀ w ∈ Submodule.span D.host.E (Set.range X.eX ∪ Set.range X.fY ∪ {X.zu u}), δ w = w := by
    have hle : Submodule.span D.host.E (Set.range X.eX ∪ Set.range X.fY ∪ {X.zu u}) ≤
        LinearMap.ker ((δ : (VS D).V →ₗ[D.host.E] (VS D).V) - LinearMap.id) := by
      rw [Submodule.span_le]
      rintro w ((⟨a, rfl⟩ | ⟨a, rfl⟩) | hz)
      · simp [hfix _ (eR_mem_fix X u a)]
      · simp [hfix _ (fR_mem_fix X u a)]
      · rw [Set.mem_singleton_iff.1 hz]; simp [hfix _ (zR_mem_fix X u)]
    intro w hw
    have := hle hw
    simpa [sub_eq_zero] using this
  set U : Submodule D.host.E (VS D).V := Submodule.span D.host.E (Set.range X.eX ∪ Set.range X.fY ∪ {X.zu u}) with hU
  set W := orth (VS D) U with hWdef
  have hUmap : U.map (δ : (VS D).V →ₗ[D.host.E] (VS D).V) = U := map_eq_of_iff fun w => by
    constructor
    · intro hw
      have e : δ w = w := δ.injective (hUfix _ hw)
      rw [← e]; exact hw
    · intro hw; rw [hUfix w hw]; exact hw
  have hWmap : W.map (δ : (VS D).V →ₗ[D.host.E] (VS D).V) = W := by
    rw [orth_map_bl hδiso U, hUmap]
  have hX : (⊥ : Submodule D.host.E (VS D).V).map (δ : (VS D).V →ₗ[D.host.E] (VS D).V) = ⊥ := Submodule.map_bot _

  have hη : (h : X.B.I.Gf)⁻¹ * (γ : X.B.I.GA).2 * h ∈ Hfin X u := mul_mem (mul_mem (inv_mem h.2) hfin) h.2
  have hunipY := hC _ hκ (hK.2.2.1 _ hκ) (Yu X u) (fun v hv => hv.1)
    (yu_stable X u _ hη hκ.1)
    (fun v hv => ⟨fun a => ⟨hermitian_e0_congruent X u hv a, hermitian_f0_congruent X u hv a⟩, hermitian_z0_congruent X u hv⟩)

  have hA1 : ∀ y, hatv X u h (dm1 δ y) = (X.B.I.fmat ((X.xu u)⁻¹ * ((h : X.B.I.Gf)⁻¹ * (γ : X.B.I.GA).2 * h) * X.xu u) - 1) *ᵥ
      hatv X u h y := by
    intro y
    rw [dm1_apply, hatv_sub, sub_mulVec, one_mulVec]
    congr 1
    unfold hatv
    rw [hincl, mulVec_mulVec, mulVec_mulVec, hPκ]
  have hApow : ∀ j : ℕ, ∀ y, hatv X u h (((dm1 δ) ^ j) y) =
      ((X.B.I.fmat ((X.xu u)⁻¹ * ((h : X.B.I.Gf)⁻¹ * (γ : X.B.I.GA).2 * h) * X.xu u) - 1) ^ j) *ᵥ hatv X u h y := by
    intro j
    induction j with
    | zero => intro y; rw [pow_zero, pow_zero, one_mulVec]; rfl
    | succ j ih =>
      intro y
      rw [pow_succ, Module.End.mul_apply, ih, hA1, pow_succ, ← mulVec_mulVec]
  have hAW : ∀ w ∈ W, dm1 δ w ∈ W := by
    intro w hw
    rw [dm1_apply]; exact sub_mem ((mem_of_map_eq hWmap w).2 hw) hw
  have hApowW : ∀ j : ℕ, ∀ w ∈ W, ((dm1 δ) ^ j) w ∈ W := by
    intro j
    induction j with
    | zero => intro w hw; rw [pow_zero]; exact hw
    | succ j ih => intro w hw; rw [pow_succ, Module.End.mul_apply]; exact ih _ (hAW w hw)
  have hg0 : (X.B.g : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (modulus_g_ne_zero X)
  have hkey : ∀ y ∈ Λ, y ∈ W → ∃ z' ∈ Λ, z' ∈ W ∧ ((dm1 δ) ^ D.R.k) y = ((X.B.g : ℕ) : 𝓞 D.host.E) • z' := by
    intro y hyΛ hyW
    have h1 := hunipY (hatv X u h y) (hatv_Y X u h y ((hmemΛ y).1 hyΛ) hyW)
    rw [← hApow] at h1
    obtain ⟨x, hx, hxe⟩ := mL_exists X h1
    refine ⟨((X.B.g : D.host.E)⁻¹) • ((dm1 δ) ^ D.R.k) y, ?_, W.smul_mem _ (hApowW _ _ hyW), ?_⟩
    · rw [hmemΛ, hatv_smul, hxe, smul_smul, inv_g_cancel, one_smul]; exact hx
    · rw [← algebraMap_smul D.host.E ((X.B.g : ℕ) : 𝓞 D.host.E), map_natCast, smul_smul, mul_inv_cancel₀ hg0,
        one_smul]

  have hlat := qLat_isLattice Λ W ⊥
  have haut := q_aut δ W hWmap hX Λ hδΛ
  have hunip : ∀ PP : Ideal (𝓞 D.host.E), ((X.B.g : ℕ) : 𝓞 D.host.E) ∈ PP →
      Formalism.L2.Col.UnipMod PP (qLat Λ W ⊥) (qEquiv δ W ⊥ hWmap hX) := by
    intro PP hPP
    refine ⟨haut, D.R.k, fun q hq => ?_⟩
    obtain ⟨w, hwΛ, rfl⟩ := mem_qLat.1 hq
    obtain ⟨z', hz'Λ, hz'W, hz'e⟩ := hkey w hwΛ w.2
    have e := q_powB δ W hWmap hX D.R.k w ⟨((X.B.g : ℕ) : 𝓞 D.host.E) • z', W.smul_of_tower_mem _ hz'W⟩ hz'e.symm
    show ((dm1 (qEquiv δ W ⊥ hWmap hX)) ^ D.R.k) (Submodule.Quotient.mk w) ∈ _
    rw [e]
    have hmk : (Submodule.Quotient.mk ⟨((X.B.g : ℕ) : 𝓞 D.host.E) • z', W.smul_of_tower_mem _ hz'W⟩ : QW W ⊥) =
        ((X.B.g : ℕ) : 𝓞 D.host.E) • (Submodule.Quotient.mk ⟨z', hz'W⟩ : QW W ⊥) := by
      rw [← Submodule.Quotient.mk_smul]
      rfl
    rw [hmk]
    exact Submodule.smul_mem_smul hPP (mem_qLat.2 ⟨⟨z', hz'W⟩, hz'Λ, rfl⟩)

  obtain ⟨m, hm, hγm⟩ := isOfFinOrder_iff_pow_eq_one.1 hfo
  have hγ2 : ((γ : X.B.I.GA).2) ^ m = 1 := by
    have := congrArg (fun x : Gam X u => ((x : X.B.I.GA)).2) hγm
    simpa using this
  have hpowI : ∀ j : ℕ, ∀ y, incl X.B.I (X.crd ((δ ^ j) y)) =
      X.B.I.fmat ((γ : X.B.I.GA).2 ^ j) *ᵥ incl X.B.I (X.crd y) := by
    intro j
    induction j with
    | zero => intro y; rw [pow_zero, pow_zero, fmat_one', one_mulVec]; rfl
    | succ j ih =>
      intro y
      rw [pow_succ, LinearEquiv.mul_apply, ih, hincl, mulVec_mulVec, ← fmat_mul, pow_succ]
  have hδm : ∀ y, (δ ^ m) y = y := fun y => hinj _ _ (by rw [hpowI, hγ2, fmat_one', one_mulVec])
  have hQfin : IsOfFinOrder (qEquiv δ W ⊥ hWmap hX) :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, q_pow_one δ W hWmap hX m hδm⟩

  obtain ⟨P₁, hP₁, hg₁P⟩ := Formalism.L2.SG.LemmaN.exists_prime_over D.host.E (D.host.g_prime 0)
  obtain ⟨P₂, hP₂, hg₂P⟩ := Formalism.L2.SG.LemmaN.exists_prime_over D.host.E (D.host.g_prime 1)
  have hmul : ((X.B.g : ℕ) : 𝓞 D.host.E) = ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) := by
    rw [X.g_eq, Nat.cast_mul]
  have hone := Formalism.L2.SG.LemmaN.lemmaNcGlob_of_exists D.host.E (QW W ⊥) (qLat Λ W ⊥) hlat _ hQfin
    (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne hP₁.ne_top hP₂.ne_top hg₁P hg₂P
    (hunip P₁ (by rw [hmul]; exact Ideal.mul_mem_right _ _ hg₁P))
    (hunip P₂ (by rw [hmul]; exact Ideal.mul_mem_left _ _ hg₂P))
  have hWfix := q_fix δ W hWmap hX hone
  have hall : ∀ v, δ v = v := by
    intro v
    obtain ⟨s, hs, hws⟩ := Formalism.L2.SG.PoincareInHH.Cut.decomp X u v
    have e : v = (v - s) + s := by abel
    rw [e, map_add, hWfix _ hws, hUfix s hs]
  have h2 : (γ : X.B.I.GA).2 = 1 := by
    apply fmat_eq_one_of_fix X
    intro y
    rw [← hincl, hall]
  exact Subtype.ext (gf_eq_one_of_snd X (γ : X.B.I.GA) hGF h2)

end Formalism.L2.SG.PoincareInHH.Cut.GU
