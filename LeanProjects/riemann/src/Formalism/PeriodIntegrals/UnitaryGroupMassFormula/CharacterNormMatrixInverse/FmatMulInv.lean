import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiNCut

noncomputable section

open Matrix NumberField Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped TensorProduct

namespace PIW.NormChiNBi

section Alg

variable (I : AutInst)

theorem fmat_mul' (a b : I.Gf) : I.fmat (a * b) = I.fmat a * I.fmat b := by
  rfl

theorem fmat_mul_inv' (a : I.Gf) : I.fmat a * I.fmat a⁻¹ = 1 := by
  rw [← fmat_mul', mul_inv_cancel]
  rfl

theorem kset_mem {k : I.Gf} (hk : k ∈ I.Kset) {y : VA I} (hy : y ∈ I.Lf) : I.fmat k *ᵥ y ∈ I.Lf := by
  have h' : ∀ x, x ∈ I.Lf ↔ I.fmat k *ᵥ x ∈ I.Lf := hk
  exact (h' y).1 hy

theorem kset_inv {k : I.Gf} (hk : k ∈ I.Kset) : k⁻¹ ∈ I.Kset := by
  exact (Formalism.UG.stabGL I.Lf).inv_mem (show (k : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) ∈ Formalism.UG.stabGL I.Lf from hk)

private theorem hform_mulVec_mulVec_of_cT_mul_mul_eq {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J M : Matrix n n A) (hM : Formalism.UG.cT σ M * J * M = J) (x y : n → A) :
    Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = Formalism.UG.hform σ J x y := by
  have key : ∀ u v : n → A, Formalism.UG.hform σ J u v = (fun i => σ (u i)) ⬝ᵥ (J *ᵥ v) := by
    intro u v
    simp only [Formalism.UG.hform, dotProduct, mulVec, Finset.mul_sum, mul_assoc]
  rw [key, key]
  have e₁ : (fun i => σ ((M *ᵥ x) i)) = M.map σ *ᵥ (fun i => σ (x i)) :=
    funext fun i => RingHom.map_mulVec σ M x i
  rw [e₁]
  conv_rhs => rw [← hM]
  rw [Formalism.UG.cT, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec _ (M.map σ)ᵀ, vecMul_transpose]

theorem hA_fmat' (k : I.Gf) (x y : VA I) : hA I (I.fmat k *ᵥ x) (I.fmat k *ᵥ y) = hA I x y := by
  exact hform_mulVec_mulVec_of_cT_mul_mul_eq (Formalism.UG.sigR I.cm.sig (Af I.F)) (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)))
    (I.fmat k) k.2 x y

theorem hA_left_inv (k : I.Gf) (x y : VA I) : hA I x (I.fmat k *ᵥ y) = hA I (I.fmat k⁻¹ *ᵥ x) y := by
  have h := hA_fmat' I k⁻¹ x (I.fmat k *ᵥ y)
  have h1 : I.fmat 1 = 1 := rfl
  rw [mulVec_mulVec, ← fmat_mul', inv_mul_cancel, h1, one_mulVec] at h
  exact h.symm

theorem hA_add_left (x x' y : VA I) : hA I (x + x') y = hA I x y + hA I x' y := by
  simp only [hA, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hA_sub_left (x x' y : VA I) : hA I (x - x') y = hA I x y - hA I x' y := by
  simp only [hA, Formalism.UG.hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem hA_add_right (x y y' : VA I) : hA I x (y + y') = hA I x y + hA I x y' := by
  simp only [hA, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hA_sub_right (x y y' : VA I) : hA I x (y - y') = hA I x y - hA I x y' := by
  simp only [hA, Formalism.UG.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem hA_zero_left (y : VA I) : hA I 0 y = 0 := by
  simp [hA, Formalism.UG.hform]

theorem hA_zero_right (x : VA I) : hA I x 0 = 0 := by
  simp [hA, Formalism.UG.hform]

theorem hA_smul_left (c : I.E ⊗[I.F] Af I.F) (x y : VA I) : hA I (c • x) y = sigA I c * hA I x y := by
  simp only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hA_smul_right (c : I.E ⊗[I.F] Af I.F) (x y : VA I) : hA I x (c • y) = c * hA I x y := by
  simp only [hA, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem inclE_int {e : I.E} (he : e ∈ (algebraMap (𝓞 I.E) I.E).range) :
    Formalism.UG.inclE (F := I.F) (Af I.F) e ∈ IntAf I.F I.E := by
  exact Subring.subset_closure (Or.inl ⟨⟨e, he⟩, rfl⟩)

theorem sigA_int {c : I.E ⊗[I.F] Af I.F} (hc : c ∈ IntAf I.F I.E) : sigA I c ∈ IntAf I.F I.E := by
  have key : IntAf I.F I.E ≤ (IntAf I.F I.E).comap (sigA I) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · obtain ⟨a, rfl⟩ := hx
      show Formalism.UG.sigR I.cm.sig (Af I.F) ((algebraMap (𝓞 I.E) I.E a) ⊗ₜ[I.F] (1 : Af I.F)) ∈ IntAf I.F I.E
      rw [Formalism.UG.sigR, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      have hi : IsIntegral ℤ (I.cm.sig (algebraMap (𝓞 I.E) I.E a)) :=
        map_isIntegral_int I.cm.sig.toRingHom (RingOfIntegers.isIntegral_coe a)
      exact Subring.subset_closure (Or.inl ⟨⟨_, ⟨⟨_, hi⟩, rfl⟩⟩, rfl⟩)
    · show Formalism.UG.sigR I.cm.sig (Af I.F) ((1 : I.E) ⊗ₜ[I.F] y) ∈ IntAf I.F I.E
      rw [Formalism.UG.sigR, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
      exact Subring.subset_closure (Or.inr ⟨⟨y, hy⟩, rfl⟩)
  exact key hc

theorem sigA_inclE' (e : I.E) :
    sigA I (Formalism.UG.inclE (F := I.F) (Af I.F) e) = Formalism.UG.inclE (F := I.F) (Af I.F) (starRingEnd I.E e) := by
  show (Algebra.TensorProduct.map I.cm.sig (AlgHom.id I.F (Af I.F))) (e ⊗ₜ[I.F] (1 : Af I.F)) =
    (starRingEnd I.E e) ⊗ₜ[I.F] (1 : Af I.F)
  rw [Algebra.TensorProduct.map_tmul]
  rfl

theorem hA_incl' (x y : Fin I.n → I.E) :
    hA I (incl I x) (incl I y) =
      Formalism.UG.inclE (F := I.F) (Af I.F) (Formalism.UG.hform (starRingEnd I.E) I.J x y) := by
  simp only [hA, Formalism.UG.hform, incl, Matrix.map_apply, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [show Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) (x i)) =
    Formalism.UG.inclE (F := I.F) (Af I.F) (starRingEnd I.E (x i)) from sigA_inclE' I (x i)]

theorem hA_int {x y : VA I} (hx : x ∈ I.Lf) (hy : y ∈ I.Lf) : hA I x y ∈ IntAf I.F I.E := by
  have gen : ∀ a ∈ I.L, ∀ b ∈ I.L, hA I (incl I a) (incl I b) ∈ IntAf I.F I.E := by
    intro a ha b hb
    rw [hA_incl']
    exact inclE_int I ((I.L_dual b).1 hb a ha)
  have step : ∀ b ∈ I.L, ∀ u ∈ I.Lf, hA I u (incl I b) ∈ IntAf I.F I.E := by
    intro b hb u hu
    have hu' : u ∈ Submodule.span (IntAf I.F I.E)
        (Set.range fun z : I.L => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((z : Fin I.n → I.E) i)) := hu
    clear hu
    induction hu' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨⟨a, ha⟩, rfl⟩ := hz
      exact gen a ha b hb
    | zero => rw [hA_zero_left]; exact zero_mem _
    | add u v _ _ hu hv => rw [hA_add_left]; exact add_mem hu hv
    | smul c u _ hu => rw [Subring.smul_def, hA_smul_left]; exact mul_mem (sigA_int I c.2) hu
  have hy' : y ∈ Submodule.span (IntAf I.F I.E)
      (Set.range fun z : I.L => fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((z : Fin I.n → I.E) i)) := hy
  clear hy
  induction hy' using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨b, hb⟩, rfl⟩ := hz
    exact step b hb x hx
  | zero => rw [hA_zero_right]; exact zero_mem _
  | add u v _ _ hu hv => rw [hA_add_right]; exact add_mem hu hv
  | smul c u _ hu => rw [Subring.smul_def, hA_smul_right]; exact mul_mem c.2 hu

theorem hA_mL_left (m : ℕ) {δ w : VA I} (hδ : δ ∈ mL I m) (hw : w ∈ I.Lf) :
    ∃ t ∈ IntAf I.F I.E, hA I δ w = (m : I.E ⊗[I.F] Af I.F) * t := by
  have hδ' : δ ∈ Submodule.span (IntAf I.F I.E)
      {y | ∃ x ∈ I.Lf, y = (m : I.E ⊗[I.F] Af I.F) • x} := hδ
  clear hδ
  induction hδ' using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    exact ⟨hA I x w, hA_int I hx hw, by rw [hA_smul_left, map_natCast]⟩
  | zero => exact ⟨0, zero_mem _, by rw [hA_zero_left, mul_zero]⟩
  | add u v _ _ hu hv =>
    obtain ⟨t₁, ht₁, e₁⟩ := hu
    obtain ⟨t₂, ht₂, e₂⟩ := hv
    exact ⟨t₁ + t₂, add_mem ht₁ ht₂, by rw [hA_add_left, e₁, e₂, mul_add]⟩
  | smul c u _ hu =>
    obtain ⟨t, ht, e⟩ := hu
    exact ⟨sigA I c * t, mul_mem (sigA_int I c.2) ht, by rw [Subring.smul_def, hA_smul_left, e]; ring⟩

theorem hA_mL_right (m : ℕ) {δ w : VA I} (hδ : δ ∈ mL I m) (hw : w ∈ I.Lf) :
    ∃ t ∈ IntAf I.F I.E, hA I w δ = (m : I.E ⊗[I.F] Af I.F) * t := by
  have hδ' : δ ∈ Submodule.span (IntAf I.F I.E)
      {y | ∃ x ∈ I.Lf, y = (m : I.E ⊗[I.F] Af I.F) • x} := hδ
  clear hδ
  induction hδ' using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨x, hx, rfl⟩ := hz
    exact ⟨hA I w x, hA_int I hw hx, by rw [hA_smul_right]⟩
  | zero => exact ⟨0, zero_mem _, by rw [hA_zero_right, mul_zero]⟩
  | add u v _ _ hu hv =>
    obtain ⟨t₁, ht₁, e₁⟩ := hu
    obtain ⟨t₂, ht₂, e₂⟩ := hv
    exact ⟨t₁ + t₂, add_mem ht₁ ht₂, by rw [hA_add_right, e₁, e₂, mul_add]⟩
  | smul c u _ hu =>
    obtain ⟨t, ht, e⟩ := hu
    exact ⟨c * t, mul_mem c.2 ht, by rw [Subring.smul_def, hA_smul_right, e]; ring⟩

theorem bezout_cast {c g : ℕ} (hc : Nat.Coprime c g) :
    ∃ u v : ℤ, (u : I.E ⊗[I.F] Af I.F) * c + (v : I.E ⊗[I.F] Af I.F) * g = 1 := by
  refine ⟨Nat.gcdA c g, Nat.gcdB c g, ?_⟩
  have h := Nat.gcd_eq_gcd_ab c g
  rw [Nat.Coprime.gcd_eq_one hc] at h
  have h' := congrArg (Int.cast : ℤ → I.E ⊗[I.F] Af I.F) h
  push_cast at h'
  linear_combination -h'

theorem hA_inAt_left {g : ℕ} {δ w : VA I} (hδ : InAt I g g δ) (hδL : δ ∈ I.Lf) (hw : w ∈ I.Lf) :
    ∃ t ∈ IntAf I.F I.E, hA I δ w = (g : I.E ⊗[I.F] Af I.F) * t := by
  obtain ⟨c, hc, hcδ⟩ := hδ
  obtain ⟨t₁, ht₁, e₁⟩ := hA_mL_left I g hcδ hw
  rw [hA_smul_left, map_natCast] at e₁
  obtain ⟨u, v, huv⟩ := bezout_cast I hc
  refine ⟨u * t₁ + v * hA I δ w,
    add_mem (mul_mem (intCast_mem _ u) ht₁) (mul_mem (intCast_mem _ v) (hA_int I hδL hw)), ?_⟩
  linear_combination (-hA I δ w) * huv + (u : I.E ⊗[I.F] Af I.F) * e₁

theorem hA_inAt_right {g : ℕ} {δ w : VA I} (hδ : InAt I g g δ) (hw : w ∈ I.Lf) (hδL : δ ∈ I.Lf) :
    ∃ t ∈ IntAf I.F I.E, hA I w δ = (g : I.E ⊗[I.F] Af I.F) * t := by
  obtain ⟨c, hc, hcδ⟩ := hδ
  obtain ⟨t₁, ht₁, e₁⟩ := hA_mL_right I g hcδ hw
  rw [hA_smul_right] at e₁
  obtain ⟨u, v, huv⟩ := bezout_cast I hc
  refine ⟨u * t₁ + v * hA I w δ,
    add_mem (mul_mem (intCast_mem _ u) ht₁) (mul_mem (intCast_mem _ v) (hA_int I hw hδL)), ?_⟩
  linear_combination (-hA I w δ) * huv + (u : I.E ⊗[I.F] Af I.F) * e₁

theorem divN_zero' (x : I.E ⊗[I.F] Af I.F) : divN I 0 x = 0 := by
  simp [divN]

theorem divN_add_mul {g : ℕ} (hg : g ≠ 0) (x t : I.E ⊗[I.F] Af I.F) :
    divN I g (x + (g : I.E ⊗[I.F] Af I.F) * t) = divN I g x + t := by
  have h : algebraMap I.F (I.E ⊗[I.F] Af I.F) ((g : I.F)⁻¹) * (g : I.E ⊗[I.F] Af I.F) = 1 := by
    rw [← map_natCast (algebraMap I.F (I.E ⊗[I.F] Af I.F)) g, ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hg), map_one]
  simp only [divN]
  rw [mul_add, ← mul_assoc, h, one_mul]

theorem term_step (g : ℕ) {κ k₁ k₂ : I.Gf} (hκ : κ ∈ I.Kset) (h₁ : k₁ ∈ I.Kset) (h₂ : k₂ ∈ I.Kset)
    {f v : VA I} (hf : f ∈ I.Lf) (hv : v ∈ I.Lf)
    (c₁ : InAt I g g (I.fmat k₁⁻¹ *ᵥ f - f)) (c₂ : InAt I g g (I.fmat k₂ *ᵥ v - v)) :
    ∃ t ∈ IntAf I.F I.E, hA I f (I.fmat (k₁ * κ * k₂) *ᵥ v) =
      hA I f (I.fmat κ *ᵥ v) + (g : I.E ⊗[I.F] Af I.F) * t := by
  have hk₁ := kset_inv I h₁
  have hκ' := kset_inv I hκ
  have hw₁ : I.fmat κ *ᵥ (I.fmat k₂ *ᵥ v) ∈ I.Lf := kset_mem I hκ (kset_mem I h₂ hv)
  have hd₁ : I.fmat k₁⁻¹ *ᵥ f - f ∈ I.Lf := sub_mem (kset_mem I hk₁ hf) hf
  have hd₂ : I.fmat k₂ *ᵥ v - v ∈ I.Lf := sub_mem (kset_mem I h₂ hv) hv
  have hw₂ : I.fmat κ⁻¹ *ᵥ f ∈ I.Lf := kset_mem I hκ' hf
  obtain ⟨t₁, ht₁, e₁⟩ := hA_inAt_left I c₁ hd₁ hw₁
  obtain ⟨t₂, ht₂, e₂⟩ := hA_inAt_right I c₂ hw₂ hd₂
  refine ⟨t₁ + t₂, add_mem ht₁ ht₂, ?_⟩
  have s₁ : hA I f (I.fmat (k₁ * κ * k₂) *ᵥ v) =
      hA I (I.fmat k₁⁻¹ *ᵥ f) (I.fmat κ *ᵥ (I.fmat k₂ *ᵥ v)) := by
    rw [fmat_mul', fmat_mul', ← mulVec_mulVec, ← mulVec_mulVec, hA_left_inv I k₁]
  have s₂ : hA I (I.fmat k₁⁻¹ *ᵥ f) (I.fmat κ *ᵥ (I.fmat k₂ *ᵥ v)) =
      hA I f (I.fmat κ *ᵥ (I.fmat k₂ *ᵥ v)) + hA I (I.fmat k₁⁻¹ *ᵥ f - f) (I.fmat κ *ᵥ (I.fmat k₂ *ᵥ v)) := by
    rw [← hA_add_left]
    congr 1
    abel
  have s₃ : hA I f (I.fmat κ *ᵥ (I.fmat k₂ *ᵥ v)) =
      hA I f (I.fmat κ *ᵥ v) + hA I (I.fmat κ⁻¹ *ᵥ f) (I.fmat k₂ *ᵥ v - v) := by
    rw [← hA_left_inv I κ, mulVec_sub, hA_sub_right]
    ring
  rw [s₁, s₂, s₃, e₁, e₂]
  ring

theorem sum_step (g : ℕ) {ι : Type} [Fintype ι] (A B : ι → I.E ⊗[I.F] Af I.F)
    (h : ∀ a, ∃ t ∈ IntAf I.F I.E, A a = B a + (g : I.E ⊗[I.F] Af I.F) * t) :
    ∃ t ∈ IntAf I.F I.E, ∑ a, A a = ∑ a, B a + (g : I.E ⊗[I.F] Af I.F) * t := by
  choose t ht e using h
  exact ⟨∑ a, t a, sum_mem fun a _ => ht a, by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => e a⟩

end Alg

section Main

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem nxt_mem {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (a : Fin D.R.rS) :
    nxt X.e0 X.z0 a ∈ X.B.I.Lf := by
  simp only [Formalism.L2.SG.HidaSetting.nxt]
  split
  · exact (X.vectorsInLattice.1 _).1
  · exact X.vectorsInLattice.2.1

theorem chiNBi_holds {D : Formalism.BasicNotions.D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) : Formalism.L2.SG.NormCut.ChiNBi X := by
  intro κ k₁ k₂ hκ h₁ h₂ hf hv
  obtain ⟨t, ht, hS⟩ := sum_step X.B.I X.B.g
    (fun a => hA X.B.I (X.f0 a) (X.B.I.fmat (k₁ * κ * k₂) *ᵥ nxt X.e0 X.z0 a))
    (fun a => hA X.B.I (X.f0 a) (X.B.I.fmat κ *ᵥ nxt X.e0 X.z0 a))
    (fun a => term_step X.B.I X.B.g hκ h₁ h₂ (X.vectorsInLattice.1 a).2 (nxt_mem X a) (hf a) (hv a))
  unfold Formalism.L2.SG.TermOp.chiN
  rw [hS]
  rcases Nat.eq_zero_or_pos X.B.g with h0 | hpos
  · rw [h0, divN_zero', divN_zero']
  · rw [divN_add_mul X.B.I hpos.ne', X.psiEf_add, X.psiEf_int t ht, mul_one]

end Main

end PIW.NormChiNBi
