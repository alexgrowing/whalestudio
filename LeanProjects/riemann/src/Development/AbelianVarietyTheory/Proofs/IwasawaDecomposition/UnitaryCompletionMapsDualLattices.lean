import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
import Formalism.SharpRestriction.GrowthBounds.IntegralWeylLatticeSpan.LatSOfLocBasis
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.DualCompletion

open Formalism.L2.G.RelativeIndexFlags

theorem hform_mulVec_left {A : Type} [CommRing A] {n : ℕ} (τ : A →+* A) (J B : Matrix (Fin n) (Fin n) A)
    (t x : Fin n → A) : hform τ J (B *ᵥ t) x = ∑ a, τ (t a) * ((cT τ B * J) *ᵥ x) a := by
  simp only [hform, cT, Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => by ring

theorem hform_col {A : Type} [CommRing A] {n : ℕ} (τ : A →+* A) (J B : Matrix (Fin n) (Fin n) A)
    (a : Fin n) (c : A) (x : Fin n → A) :
    hform τ J (B *ᵥ Pi.single a c) x = τ c * ((cT τ B * J) *ᵥ x) a := by
  rw [hform_mulVec_left, Finset.sum_eq_single a]
  · rw [Pi.single_eq_same]
  · intro b _ hb; rw [Pi.single_eq_of_ne hb, map_zero, zero_mul]
  · intro h; exact (h (Finset.mem_univ a)).elim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mem_dualL (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (y : Fin n → E) :
    y ∈ dualL σ J Λ ↔ y ∈ dualSet σ J Λ := by
  refine ⟨fun hy => ?_, fun hy => Submodule.subset_span hy⟩
  induction hy using Submodule.span_induction with
  | mem y hy => exact hy
  | zero => intro x _; simp [hform]
  | add y z _ _ hy hz =>
    intro x hx
    have : hform σ J x (y + z) = hform σ J x y + hform σ J x z := by
      simp [hform, mul_add, Finset.sum_add_distrib]
    rw [this]; exact add_mem (hy x hx) (hz x hx)
  | smul a y _ hy =>
    intro x hx
    have : hform σ J x (a • y) = algebraMap (𝓞 E) E a * hform σ J x y := by
      simp only [hform, Finset.mul_sum, Pi.smul_apply, Algebra.smul_def]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this]; exact mul_mem ⟨a, rfl⟩ (hy x hx)

theorem exists_common_den {p : ℕ} (hp : p.Prime) (M : Submodule (𝓞 E) (Fin n → E)) (hM : M.FG) (B : GL (Fin n) E)
    (hB : IsLocBasis p (M : Set (Fin n → E)) B) :
    ∃ s : ℕ, ¬ p ∣ s ∧ ∀ m ∈ M, ∀ a, (s : E) * ((B⁻¹).1 *ᵥ m) a ∈ (algebraMap (𝓞 E) E).range := by
  classical
  have h1 : ¬ p ∣ 1 := fun h => hp.ne_one (Nat.dvd_one.1 h)
  obtain ⟨S, rfl⟩ := hM
  choose s hs H using fun m : S => (hB m.1).1 ⟨1, h1, by
    rw [Nat.cast_one, one_smul]; exact Submodule.subset_span m.2⟩
  refine ⟨∏ m, s m, fun hd => ?_, fun m hm => ?_⟩
  · obtain ⟨a, _, ha⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hd
    exact hs a ha
  · induction hm using Submodule.span_induction with
    | mem y hy =>
      intro a
      rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ ⟨y, hy⟩), mul_comm (s _), Nat.cast_mul, mul_assoc]
      exact mul_mem (natCast_mem _ _) (H ⟨y, hy⟩ a)
    | zero => intro a; simp
    | add y z _ _ hy hz => intro a; rw [Matrix.mulVec_add, Pi.add_apply, mul_add]; exact add_mem (hy a) (hz a)
    | smul c y _ hy =>
      intro a
      rw [Matrix.mulVec_smul, Pi.smul_apply, Algebra.smul_def, mul_left_comm]
      exact mul_mem ⟨c, rfl⟩ (hy a)

theorem isLocBasis_dual (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) {p : ℕ} (hp : p.Prime)
    (M : Submodule (𝓞 E) (Fin n → E)) (hM : M.FG) (B : GL (Fin n) E)
    (hB : IsLocBasis p (M : Set (Fin n → E)) B) (C : GL (Fin n) E) (hC : C.1 = cT (σ : E →+* E) B.1 * J) :
    IsLocBasis p (dualL (σ : E →+* E) J M : Set (Fin n → E)) C⁻¹ := by
  classical
  have h1 : ¬ p ∣ 1 := fun h => hp.ne_one (Nat.dvd_one.1 h)
  intro x
  rw [inv_inv, hC]
  simp only [SetLike.mem_coe, mem_dualL]
  constructor
  · rintro ⟨s, hs, hx⟩
    choose t ht H using fun a : Fin n => (hB (B.1 *ᵥ Pi.single a 1)).2 ⟨1, h1, fun b => by
      rw [Nat.cast_one, one_mul]; exact latB_col B a b⟩
    refine ⟨(∏ a, t a) * s, fun hd => ?_, fun a => ?_⟩
    · rcases (Nat.Prime.dvd_mul hp).1 hd with hd | hd
      · obtain ⟨a, _, ha⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 hd
        exact ht a ha
      · exact hs hd
    · have h := hx _ (H a)
      rw [Formalism.UG.P.csDual_hform_smul_left, hform_col, map_one, one_mul, map_natCast, Matrix.mulVec_smul,
        Pi.smul_apply, smul_eq_mul] at h
      rw [← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ a), mul_comm (t a), Nat.cast_mul, Nat.cast_mul,
        mul_assoc, mul_assoc]
      exact mul_mem (natCast_mem _ _) h
  · rintro ⟨s, hs, hx⟩
    obtain ⟨t, ht, H⟩ := exists_common_den hp M hM B hB
    refine ⟨t * s, fun hd => ((Nat.Prime.dvd_mul hp).1 hd).elim ht hs, fun m hm => ?_⟩
    have e : m = B.1 *ᵥ ((B⁻¹).1 *ᵥ m) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e, hform_mulVec_left]
    refine sum_mem fun a _ => ?_
    obtain ⟨b, hb⟩ := H m hm a
    have h2 := sig_int σ b
    rw [hb, map_mul, map_natCast] at h2
    have h3 := mul_mem h2 (hx a)
    convert h3 using 1
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, Nat.cast_mul]
    show σ _ * _ = _
    ring

theorem mem_latS_dualL (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (hJ : IsUnit J.det)
    (v : HeightOneSpectrum (𝓞 F)) (M : Submodule (𝓞 E) (Fin n → E)) (hM : Submodule.IsLattice E M)
    (w : Fin n → E ⊗[F] v.adicCompletion F) :
    w ∈ latS (F := F) (v.adicCompletion F) (intV E v) (dualL (σ : E →+* E) J M) ↔
      ∀ u ∈ latS (F := F) (v.adicCompletion F) (intV E v) M,
        hform (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F))) u w ∈ intV E v := by
  classical
  haveI := v.isMaximal
  obtain ⟨p, -, -, hv, hp, -⟩ := Ideal.exists_prime_and_absNorm_eq_pow v.asIdeal
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨B, hB⟩ := LocB.exists_isLocBasis p E M hM.fg hM.span_eq_top
  have hu : IsUnit (cT (σ : E →+* E) B.1 * J).det := by
    rw [Matrix.det_mul, cT, Matrix.det_transpose]
    refine IsUnit.mul ?_ hJ
    have := ((Matrix.isUnit_iff_isUnit_det _).1 B.isUnit).map (σ : E →+* E)
    rwa [RingHom.map_det] at this
  let C : GL (Fin n) E := Matrix.GeneralLinearGroup.mk'' _ hu
  have hC : C.1 = cT (σ : E →+* E) B.1 * J := rfl
  have hD := isLocBasis_dual σ J hp M hM.fg B hB C hC
  rw [latS_of_locBasis v hp hv _ _ hD, latS_of_locBasis v hp hv _ _ hB, mem_latS_latB, map_inv, inv_inv]
  have hC' : (bc (inclE (F := F) (v.adicCompletion F)) C).1 =
      cT (sigR σ (v.adicCompletion F)) (bc (inclE (F := F) (v.adicCompletion F)) B).1 *
        J.map (inclE (F := F) (v.adicCompletion F)) := by
    show C.1.map (inclE (F := F) (v.adicCompletion F)) =
      cT (sigR σ (v.adicCompletion F)) (B.1.map (inclE (F := F) (v.adicCompletion F))) * _
    rw [hC, Matrix.map_mul]
    congr 1
  rw [hC']
  set B' := bc (inclE (F := F) (v.adicCompletion F)) B with hB'
  constructor
  · intro h u hu
    rw [mem_latS_latB] at hu
    have e : u = B'.1 *ᵥ ((B'⁻¹).1 *ᵥ u) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e, hform_mulVec_left]
    exact sum_mem fun a _ => mul_mem (sigR_mem v σ (hu a)) (h a)
  · intro h a
    have h1 := h (B'.1 *ᵥ Pi.single a 1) (by
      rw [mem_latS_latB]
      intro b
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      by_cases hb : b = a
      · subst hb; rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne hb]; exact zero_mem _)
    rwa [hform_col, map_one, one_mul] at h1

theorem dual_move (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F)) (L Lb : Submodule (𝓞 E) (Fin n → E))
    (y : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hJ : IsUnit J.det) (hL : Submodule.IsLattice E L)
    (hLb : Submodule.IsLattice E Lb) (hy : y ∈ UPts σ J (v.adicCompletion F))
    (hyl : ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) L ↔
      (y⁻¹).1 *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) Lb) :
    ∀ x, x ∈ latS (F := F) (v.adicCompletion F) (intV E v) (dualL (σ : E →+* E) J L) ↔
      (y⁻¹).1 *ᵥ x ∈ latS (F := F) (v.adicCompletion F) (intV E v) (dualL (σ : E →+* E) J Lb) := by
  have hyU : cT (sigR σ (v.adicCompletion F)) y.1 * J.map (inclE (F := F) (v.adicCompletion F)) * y.1 =
      J.map (inclE (F := F) (v.adicCompletion F)) := hy
  have key : ∀ z x : Fin n → E ⊗[F] v.adicCompletion F,
      hform (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F))) z ((y⁻¹).1 *ᵥ x) =
      hform (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F))) (y.1 *ᵥ z) x := by
    intro z x
    have e := Formalism.UG.P.hform_mulVec (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F)))
      y.1 z ((y⁻¹).1 *ᵥ x)
    rw [hyU, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at e
    exact e.symm
  intro x
  rw [mem_latS_dualL σ J hJ v L hL, mem_latS_dualL σ J hJ v Lb hLb]
  refine ⟨fun H z hz => ?_, fun H z hz => ?_⟩
  · rw [key]
    refine H _ ((hyl _).2 ?_)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    exact hz
  · have h1 := H _ ((hyl z).1 hz)
    rw [key, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec] at h1
    exact h1

end GlobalTheory.DualCompletion

end
