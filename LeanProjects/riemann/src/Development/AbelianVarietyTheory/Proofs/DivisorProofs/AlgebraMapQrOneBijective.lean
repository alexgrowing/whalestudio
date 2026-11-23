import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormGroupToPadicPointsDegreeOneEqUnitaryPoints
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.TorCls.AtP
variable {p : ℕ} [Fact p.Prime]

theorem qr_one_eq_bot : Qr p 1 = ⊥ := by
  have h := ReciprocityTheory.DiscreteGroups.LocalClassField.finrank_Kn p (Q0 p) (by infer_instance) one_pos
  rw [IntermediateField.finrank_bot, one_mul] at h
  exact IntermediateField.finrank_eq_one_iff.1 h

theorem algebraMap_qr_one_bijective : Function.Bijective (algebraMap ℚ_[p] (Qr p 1)) := by
  refine ⟨(algebraMap ℚ_[p] (Qr p 1)).injective, fun x => ?_⟩
  have hx : (x : PadicAlgCl p) ∈ (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p)) := by
    rw [← qr_one_eq_bot]; exact x.2
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.1 hx
  exact ⟨a, Subtype.ext ha⟩

theorem inclK_one_bijective (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    Function.Bijective (inclK p K 1) := by
  let e : ℚ_[p] ≃ₐ[ℚ_[p]] Qr p 1 := AlgEquiv.ofBijective (Algebra.ofId ℚ_[p] (Qr p 1)) algebraMap_qr_one_bijective
  let E : K ≃ₐ[ℚ_[p]] KQ p K 1 :=
    (Algebra.TensorProduct.rid ℚ_[p] ℚ_[p] K).symm.trans (Algebra.TensorProduct.congr AlgEquiv.refl e)
  have h : ∀ a, inclK p K 1 a = E a := by
    intro a
    change a ⊗ₜ[ℚ_[p]] (1 : Qr p 1) = Algebra.TensorProduct.congr AlgEquiv.refl e ((Algebra.TensorProduct.rid ℚ_[p] ℚ_[p] K).symm a)
    rw [Algebra.TensorProduct.rid_symm_apply, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one]
    rfl
  have : (inclK p K 1 : K → KQ p K 1) = E := funext h
  rw [this]; exact E.bijective

theorem glMap_bijective {R S : Type*} [CommRing R] [CommRing S] (n : ℕ) (f : R →+* S) (hf : Function.Bijective f) :
    Function.Bijective (GeneralLinearGroup.map (n := Fin n) f) := by
  let g : S ≃+* R := (RingEquiv.ofBijective f hf).symm
  refine ⟨fun A B h => ?_, fun B => ⟨GeneralLinearGroup.map (g : S →+* R) B, ?_⟩⟩
  · ext i j
    have := congrArg (fun X : GL (Fin n) S => (X : Matrix (Fin n) (Fin n) S) i j) h
    simp only [GeneralLinearGroup.map_apply] at this
    exact hf.1 this
  · ext i j
    simp only [GeneralLinearGroup.map_apply, RingHom.coe_coe]
    exact (RingEquiv.ofBijective f hf).apply_symm_apply _

theorem scalar_one_bijective (R : Type*) [CommRing R] :
    Function.Bijective (GeneralLinearGroup.scalar (Fin 1) : Rˣ →* GL (Fin 1) R) := by
  refine ⟨fun a b h => ?_, fun B => ?_⟩
  · have := congrArg (fun X : GL (Fin 1) R => (X : Matrix (Fin 1) (Fin 1) R) 0 0) h
    simp at this
    exact Units.ext this
  · refine ⟨⟨(B : Matrix (Fin 1) (Fin 1) R) 0 0, (B⁻¹ : GL (Fin 1) R) 0 0, ?_, ?_⟩, ?_⟩
    · have := congrArg (fun X : Matrix (Fin 1) (Fin 1) R => X 0 0) B.mul_inv
      simpa [Matrix.mul_apply] using this
    · have := congrArg (fun X : Matrix (Fin 1) (Fin 1) R => X 0 0) B.inv_mul
      simpa [Matrix.mul_apply] using this
    · ext i j
      fin_cases i; fin_cases j
      simp

theorem inclG_one_bijective (G : HTGroup p) : Function.Bijective (inclG G 1) := by
  have h1 : Function.Bijective ((GeneralLinearGroup.scalar (Fin 1)).comp
      (Units.map (algebraMap ℚ_[p] (Qr p 1)).toMonoidHom)) := by
    refine (scalar_one_bijective _).comp ⟨fun a b h => Units.ext (algebraMap_qr_one_bijective.1 (congrArg Units.val h)), fun b => ?_⟩
    let f := RingEquiv.ofBijective (algebraMap ℚ_[p] (Qr p 1)) algebraMap_qr_one_bijective
    refine ⟨Units.map (f.symm : Qr p 1 →+* ℚ_[p]).toMonoidHom b, Units.ext ?_⟩
    exact f.apply_symm_apply (b : Qr p 1)
  have h2 : ∀ w, Function.Bijective (GeneralLinearGroup.map (n := Fin G.n) (inclK p (G.Fw w) 1).toRingHom) :=
    fun w => glMap_bijective _ _ (inclK_one_bijective (G.Fw w))
  refine ⟨fun a b h => ?_, fun c => ?_⟩
  · have hh := Prod.ext_iff.1 h
    refine Prod.ext (h1.1 hh.1) (funext fun w => (h2 w).1 (congrFun hh.2 w))
  · obtain ⟨a, ha⟩ := h1.2 c.1
    choose b hb using fun w => (h2 w).2 (c.2 w)
    exact ⟨(a, b), Prod.ext ha (funext hb)⟩

end GlobalTheory.TorCls.AtP

namespace GlobalTheory.TorCls.AtP
variable {p : ℕ} [Fact p.Prime]

theorem exists_anti (G : HTGroup p) : ∃ (δ : G.Kq) (d : ℚ), δ ^ 2 = (d : G.Kq) ∧
    IsCMField.complexConj G.F (δ : G.F) = -(δ : G.F) ∧ δ ≠ 0 := by
  let τ : G.F →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := G.F)).toRingHom
  obtain ⟨x, hxK, hx⟩ := G.hKq.2 τ
  let xk : G.Kq := ⟨x, hxK⟩
  have : FiniteDimensional ℚ G.Kq := Module.finite_of_finrank_pos (by rw [G.hKq.1]; norm_num)
  have hint : IsIntegral ℚ xk := IsIntegral.of_finite ℚ xk
  have hle : (minpoly ℚ xk).natDegree ≤ 2 := G.hKq.1 ▸ minpoly.natDegree_le xk
  have hpos : 0 < (minpoly ℚ xk).natDegree := minpoly.natDegree_pos hint
  have hne1 : (minpoly ℚ xk).natDegree ≠ 1 := by
    intro h1
    obtain ⟨q, hq⟩ := (minpoly.natDegree_eq_one_iff (A := ℚ) (x := xk)).1 h1
    have hq' : (q : G.F) = x := by
      have := congrArg (fun y : G.Kq => (y : G.F)) hq
      simpa using this
    apply hx
    rw [← hq', map_ratCast]
    simp
  have h2 : (minpoly ℚ xk).natDegree = 2 := by omega
  have hmon := minpoly.monic hint
  have hc2 : (minpoly ℚ xk).coeff 2 = 1 := by
    have := hmon.coeff_natDegree; rwa [h2] at this
  have hev := minpoly.aeval ℚ xk
  rw [Polynomial.aeval_eq_sum_range, h2] at hev
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hc2, zero_add, pow_zero, pow_one, one_smul] at hev
  set b := (minpoly ℚ xk).coeff 1
  set c := (minpoly ℚ xk).coeff 0
  rw [Rat.smul_def, Rat.smul_def, mul_one] at hev
  have hsq : (2 * xk + (b : G.Kq)) ^ 2 = (((b ^ 2 - 4 * c : ℚ)) : G.Kq) := by
    push_cast
    linear_combination 4 * hev
  have h2c : ((2 : G.Kq) : G.F) = 2 := map_ofNat G.Kq.subtype 2
  have h4c : ((4 : G.Kq) : G.F) = 4 := map_ofNat G.Kq.subtype 4
  have hsqF : (2 * x + (b : G.F)) ^ 2 = (((b ^ 2 - 4 * c : ℚ)) : G.F) := by
    have := congrArg (fun y : G.Kq => (y : G.F)) hsq
    simpa [xk, h2c, h4c] using this
  set δF : G.F := 2 * x + (b : G.F) with hδF
  have hcF : IsCMField.complexConj G.F δF ^ 2 = δF ^ 2 := by
    rw [← map_pow, hsqF, map_ratCast]
  have hneq : IsCMField.complexConj G.F δF ≠ δF := by
    intro h
    have hτ : τ (IsCMField.complexConj G.F δF) = (starRingEnd ℂ) (τ δF) :=
      IsCMField.complexEmbedding_complexConj G.F τ δF
    rw [h] at hτ
    have him : (τ δF).im = 0 := Complex.conj_eq_iff_im.1 hτ.symm
    apply hx
    have : τ δF = 2 * τ x + (b : ℂ) := by simp [hδF, map_ratCast, map_ofNat τ 2]
    rw [this] at him
    simp at him
    exact him
  have hanti : IsCMField.complexConj G.F δF = -δF := by
    have h0 : (IsCMField.complexConj G.F δF - δF) * (IsCMField.complexConj G.F δF + δF) = 0 := by
      linear_combination hcF
    rcases mul_eq_zero.1 h0 with h | h
    · exact absurd (sub_eq_zero.1 h) hneq
    · exact eq_neg_of_add_eq_zero_left h
  refine ⟨2 * xk + (b : G.Kq), b ^ 2 - 4 * c, hsq, ?_, ?_⟩
  · have e : (((2 * xk + (b : G.Kq) : G.Kq)) : G.F) = δF := by simp [xk, hδF, h2c]
    rw [e]; exact hanti
  · intro h0
    apply hneq
    have e : δF = 0 := by
      have := congrArg (fun y : G.Kq => (y : G.F)) h0
      simpa [xk, hδF, h2c] using this
    rw [e, map_zero]

end GlobalTheory.TorCls.AtP

namespace GlobalTheory.TorCls.AtP

theorem triv_of_idem {R : Type*} [Ring R] (σ : R →+* Rᵐᵒᵖ) (e B Bi : R) (he : ∀ z, e * z = z * e)
    (hee : e * e = e) (hσe : (σ e).unop = 1 - e) (hB : (σ B).unop = B) (hBi : B * Bi = 1) (hBi' : Bi * B = 1) :
    (e + (1 - e) * B) * (e + (1 - e) * Bi) = 1 ∧ (e + (1 - e) * Bi) * (e + (1 - e) * B) = 1 ∧
      (e + (1 - e) * B) * (σ (e + (1 - e) * B)).unop = B := by
  set f := 1 - e with hf
  have hfz : ∀ z, f * z = z * f := fun z => by rw [hf, sub_mul, mul_sub, one_mul, mul_one, he]
  have hff : f * f = f := by rw [hf, sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, hee, sub_self, sub_zero]
  have hef : e * f = 0 := by rw [hf, mul_sub, mul_one, hee, sub_self]
  have hfe : f * e = 0 := by rw [hfz, hef]
  have hef' : e + f = 1 := by rw [hf]; abel
  have hσf : (σ f).unop = e := by
    rw [hf, map_sub, map_one, MulOpposite.unop_sub, MulOpposite.unop_one, hσe, hf]; abel
  have inv : ∀ X Y : R, X * Y = 1 → (e + f * X) * (e + f * Y) = 1 := by
    intro X Y hXY
    have h1 : e * (f * Y) = 0 := by rw [← mul_assoc, hef, zero_mul]
    have h2 : f * (X * e) = 0 := by rw [← he X, ← mul_assoc, hfe, zero_mul]
    have h3 : f * (X * (f * Y)) = f := by rw [← mul_assoc X, ← hfz X, mul_assoc, hXY, mul_one, hff]
    simp only [mul_add, add_mul, mul_assoc]
    rw [h1, h2, h3, hee]
    simp only [add_zero, zero_add]
    exact hef'
  refine ⟨inv B Bi hBi, inv Bi B hBi', ?_⟩
  rw [map_add, map_mul, MulOpposite.unop_add, MulOpposite.unop_mul, hσe, hB, hσf]
  have k2 : e * (B * e) = B * e := by rw [← mul_assoc, he B, mul_assoc, hee]
  have k3 : f * (B * f) = B * f := by rw [← mul_assoc, hfz B, mul_assoc, hff]
  have k4 : f * (B * (B * e)) = 0 := by rw [← mul_assoc B, ← he (B * B), ← mul_assoc, hfe, zero_mul]
  simp only [mul_add, add_mul, mul_assoc]
  rw [hef, k2, k3, k4]
  simp only [add_zero, zero_add]
  rw [← mul_add, add_comm, hef', mul_one]

end GlobalTheory.TorCls.AtP

namespace GlobalTheory.TorCls.AtP
variable {p : ℕ} [Fact p.Prime]

theorem exists_idem (G : HTGroup p) : ∃ e : ℚ_[p] ⊗[ℚ] G.C, (∀ z, e * z = z * e) ∧ e * e = e ∧
    (starT G.star ℚ_[p] e).unop = 1 - e := by
  obtain ⟨δ, d, hδ2, hconj, hδ0⟩ := exists_anti G
  set δC : G.C := algebraMap G.F G.C (δ : G.F) with hδC
  set s : ℚ_[p] := G.u δ with hs
  have hs0 : s ≠ 0 := by
    intro h; apply hδ0; exact G.u.injective (by rw [← hs, h, map_zero])
  have hs2 : s ^ 2 = (d : ℚ_[p]) := by rw [hs, ← map_pow, hδ2, map_ratCast]
  have hδC2 : δC * δC = algebraMap ℚ G.C d := by
    have : ((δ : G.F)) * (δ : G.F) = (d : G.F) := by
      have := congrArg (fun y : G.Kq => (y : G.F)) hδ2
      simpa [sq] using this
    rw [hδC, ← map_mul, this, ← eq_ratCast (algebraMap ℚ G.F) d, ← IsScalarTower.algebraMap_apply]
  have hδcomm : ∀ c : G.C, δC * c = c * δC := fun c => Algebra.commutes _ c
  have hδstar : (G.star δC).unop = -δC := by
    rw [hδC, G.star_F, hconj, map_neg]

  let E : ℚ_[p] → ℚ_[p] → ℚ_[p] ⊗[ℚ] G.C := fun h k => h ⊗ₜ (1 : G.C) + k ⊗ₜ δC
  have hmul : ∀ h k h' k', E h k * E h' k' = E (h * h' + k * k' * d) (h * k' + k * h') := by
    intro h k h' k'
    simp only [E, mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, hδC2]
    have hd1 : ∀ x : ℚ_[p], x ⊗ₜ[ℚ] (algebraMap ℚ G.C d) = (x * d) ⊗ₜ (1 : G.C) := by
      intro x
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Rat.smul_def, mul_comm]
    rw [hd1, TensorProduct.add_tmul, TensorProduct.add_tmul]
    abel
  have hcent : ∀ h k (z : ℚ_[p] ⊗[ℚ] G.C), E h k * z = z * E h k := by
    intro h k z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a c =>
      simp only [E, mul_add, add_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, hδcomm c, mul_comm h a,
        mul_comm k a]
    | add x y hx hy => rw [mul_add, hx, hy, ← add_mul]
  have hstar : ∀ h k, (starT G.star ℚ_[p] (E h k)).unop = E h (-k) := by
    intro h k
    simp only [E, map_add, MulOpposite.unop_add, starT_tmul, map_one, MulOpposite.unop_one, hδstar,
      TensorProduct.tmul_neg, TensorProduct.neg_tmul]
  have hsub : ∀ h k, 1 - E h k = E (1 - h) (-k) := by
    intro h k
    simp only [E, Algebra.TensorProduct.one_def, TensorProduct.sub_tmul, TensorProduct.neg_tmul]
    abel
  refine ⟨E (1 / 2) (1 / (2 * s)), hcent _ _, ?_, ?_⟩
  · rw [hmul]
    congr 2
    · rw [← hs2]; field_simp; ring
    · field_simp; ring
  · rw [hstar, hsub]
    congr 1
    norm_num

end GlobalTheory.TorCls.AtP

namespace GlobalTheory.TorCls.AtP
variable {p : ℕ} [Fact p.Prime]

theorem exists_triv (G : HTGroup p) (β : G.Cˣ) (hβ : sh G β = β) :
    ∃ X : (ℚ_[p] ⊗[ℚ] G.C)ˣ, Triv G ℚ_[p] β X 1 := by
  obtain ⟨e, he, hee, hσe⟩ := exists_idem G
  have hB : (starT G.star ℚ_[p] (inC G ℚ_[p] β)).unop = inC G ℚ_[p] β := by
    change (starT G.star ℚ_[p] ((1 : ℚ_[p]) ⊗ₜ (β : G.C))).unop = (1 : ℚ_[p]) ⊗ₜ (β : G.C)
    rw [starT_tmul]
    exact congrArg _ hβ
  have hBi : inC G ℚ_[p] β * inC G ℚ_[p] ((β⁻¹ : G.Cˣ) : G.C) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  have hBi' : inC G ℚ_[p] ((β⁻¹ : G.Cˣ) : G.C) * inC G ℚ_[p] β = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  obtain ⟨h1, h2, h3⟩ := triv_of_idem (starT G.star ℚ_[p]) e _ _ he hee hσe hB hBi hBi'
  let Y : (ℚ_[p] ⊗[ℚ] G.C)ˣ := ⟨_, _, h1, h2⟩
  refine ⟨Y⁻¹, ?_⟩
  have hY : (Y : ℚ_[p] ⊗[ℚ] G.C) * (starT G.star ℚ_[p] (Y : ℚ_[p] ⊗[ℚ] G.C)).unop = inC G ℚ_[p] β := h3
  unfold Triv
  rw [← hY, Units.val_one, map_one]
  calc ((Y⁻¹ : (ℚ_[p] ⊗[ℚ] G.C)ˣ) : ℚ_[p] ⊗[ℚ] G.C) * (Y * (starT G.star ℚ_[p] (Y : ℚ_[p] ⊗[ℚ] G.C)).unop) *
        (starT G.star ℚ_[p] ((Y⁻¹ : (ℚ_[p] ⊗[ℚ] G.C)ˣ) : ℚ_[p] ⊗[ℚ] G.C)).unop
      = ((Y⁻¹ : (ℚ_[p] ⊗[ℚ] G.C)ˣ) : ℚ_[p] ⊗[ℚ] G.C) * Y *
          ((starT G.star ℚ_[p] (Y : ℚ_[p] ⊗[ℚ] G.C)).unop *
            (starT G.star ℚ_[p] ((Y⁻¹ : (ℚ_[p] ⊗[ℚ] G.C)ˣ) : ℚ_[p] ⊗[ℚ] G.C)).unop) := by
        simp only [mul_assoc]
    _ = 1 := by
        rw [Units.inv_mul, one_mul, ← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]

def phiP (G : HTGroup p) : (ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ →* Gp G :=
  (MonoidHom.snd _ _).prod (Pi.monoidHom fun w =>
    (Units.map ((G.locW w).toRingHom.toMonoidHom)).comp (MonoidHom.fst _ _))

theorem psiP_eq (G : HTGroup p) (z : (ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ) : psiP G z = inclG G 1 (phiP G z) := rfl

theorem localization_eq (G : HTGroup p) (g : G.GQp) : G.localization₂ g = phiP G (g : (ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ) := rfl

end GlobalTheory.TorCls.AtP

namespace GlobalTheory.TorCls.AtP
variable {p : ℕ} [Fact p.Prime]

def conjW (G : HTGroup p) (X : (ℚ_[p] ⊗[ℚ] G.C)ˣ) : Gp G →* Gp G :=
  (MonoidHom.id _).prodMap (Pi.monoidHom fun w =>
    (MulAut.conj (Units.map ((G.locW w).toRingHom.toMonoidHom) X)).toMonoidHom.comp (Pi.evalMonoidHom _ w))

theorem phiP_conj (G : HTGroup p) (X : (ℚ_[p] ⊗[ℚ] G.C)ˣ) (z : (ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ) :
    phiP G (X * z.1 * X⁻¹, z.2) = conjW G X (phiP G z) := by
  refine Prod.ext rfl (funext fun w => ?_)
  show Units.map ((G.locW w).toRingHom.toMonoidHom) (X * z.1 * X⁻¹) =
    Units.map ((G.locW w).toRingHom.toMonoidHom) X * Units.map ((G.locW w).toRingHom.toMonoidHom) z.1 *
      (Units.map ((G.locW w).toRingHom.toMonoidHom) X)⁻¹
  rw [map_mul, map_mul, map_inv]

theorem conjW_injective (G : HTGroup p) (X : (ℚ_[p] ⊗[ℚ] G.C)ˣ) : Function.Injective (conjW G X) := by
  intro a b h
  have hh := Prod.ext_iff.1 h
  refine Prod.ext hh.1 (funext fun w => ?_)
  have := congrFun hh.2 w
  change Units.map ((G.locW w).toRingHom.toMonoidHom) X * a.2 w * (Units.map ((G.locW w).toRingHom.toMonoidHom) X)⁻¹ =
    Units.map ((G.locW w).toRingHom.toMonoidHom) X * b.2 w * (Units.map ((G.locW w).toRingHom.toMonoidHom) X)⁻¹ at this
  exact mul_left_cancel (mul_right_cancel this)

theorem atp_of_bijective (G : HTGroup p) (hb : Function.Bijective G.localization₂) (β : G.Cˣ) (hβ : sh G β = β)
    (y₀ : grp G β) (c : Gr G 1) (hc : c * toP1 G β y₀ = toP1 G β y₀ * c) :
    ∃ z : (ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ, InT G ℚ_[p] β (((y₀ : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) z ∧ psiP G z = c := by
  obtain ⟨X, hX⟩ := exists_triv G β hβ
  obtain ⟨d, rfl⟩ := (inclG_one_bijective G).2 c
  set q0 := (dg G.C p (y₀ : G.Cˣ × ℚˣ)).2 with hq0
  have hd : d * phiP G q0 = phiP G q0 * d := by
    apply (inclG_one_bijective G).1
    rw [map_mul, map_mul, ← psiP_eq, ← formGroupToPadicPointsDegreeOne_eq_unitaryPoints]
    exact hc
  obtain ⟨h, hh⟩ := hb.2 (conjW G X d)
  have hy : ((q0.1 : (ℚ_[p] ⊗[ℚ] G.C)ˣ) : ℚ_[p] ⊗[ℚ] G.C) * inC G ℚ_[p] β *
      (starT G.star ℚ_[p] ((q0.1 : (ℚ_[p] ⊗[ℚ] G.C)ˣ) : ℚ_[p] ⊗[ℚ] G.C)).unop =
      algebraMap ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C) ((q0.2 : ℚ_[p]ˣ) : ℚ_[p]) * inC G ℚ_[p] β := by
    have h' := congrArg (inC G ℚ_[p]) y₀.2.1
    rw [map_mul, map_mul, map_mul] at h'
    have e1 : inC G ℚ_[p] (sh G y₀.1.1) = (starT G.star ℚ_[p] (inC G ℚ_[p] y₀.1.1)).unop :=
      (starT_tmul G.star ℚ_[p] 1 _).symm
    have e2 : inC G ℚ_[p] (algebraMap ℚ G.C y₀.1.2) =
        algebraMap ℚ_[p] (ℚ_[p] ⊗[ℚ] G.C) (algebraMap ℚ ℚ_[p] y₀.1.2) := by
      rw [← IsScalarTower.algebraMap_apply]
      exact (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] ℚ_[p] ⊗[ℚ] G.C).commutes _
    rw [e1, e2] at h'
    exact h'
  have hmem0 : (X * q0.1 * X⁻¹, q0.2) ∈ UPts G.star ℚ_[p] :=
    conj_mul_star (starT G.star ℚ_[p]) (inC G ℚ_[p] β) X q0.1 (1 : ℚ_[p]ˣ) _ hX hy
  let H0 : G.GQp := ⟨(X * q0.1 * X⁻¹, q0.2), hmem0⟩
  have hl : G.localization₂ H0 = conjW G X (phiP G q0) := by rw [localization_eq]; exact phiP_conj G X q0
  have hcomm : h * H0 = H0 * h := hb.1 (by rw [map_mul, map_mul, hh, hl, ← map_mul, ← map_mul, hd])
  have hU := congrArg (fun g : G.GQp => ((g : (ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ).1)) hcomm
  simp only [Subgroup.coe_mul, Prod.fst_mul] at hU
  set h1 := ((h : (ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ).1)
  set Y := q0.1
  refine ⟨(X⁻¹ * h1 * X, (h : (ℚ_[p] ⊗[ℚ] G.C)ˣ × ℚ_[p]ˣ).2), ⟨?_, ?_⟩, ?_⟩
  · exact conj_back (starT G.star ℚ_[p]) (inC G ℚ_[p] β) X h1 ((1 : ℚ_[p]ˣ) : ℚ_[p]) _ hX h.2
  · have hUU : (X⁻¹ * h1 * X) * Y = Y * (X⁻¹ * h1 * X) := by
      calc (X⁻¹ * h1 * X) * Y = X⁻¹ * (h1 * (X * Y * X⁻¹)) * X := by group
        _ = X⁻¹ * ((X * Y * X⁻¹) * h1) * X := by rw [hU]
        _ = Y * (X⁻¹ * h1 * X) := by group
    exact congrArg Units.val hUU
  · rw [psiP_eq]
    congr 1
    apply conjW_injective G X
    rw [← phiP_conj, ← hh, localization_eq]
    congr 1
    refine Prod.ext ?_ rfl
    show X * (X⁻¹ * h1 * X) * X⁻¹ = h1
    group

end GlobalTheory.TorCls.AtP
