import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermHyperbolic
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAnisotropicOrthogonalBasisHermitian
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryGroupWeakApproximationAtPrimesStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryTransvectionSubmonoidAdjustIntegralAwayStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.TransvectionIdentitiesUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryEqQuasiReflectionMulTransvectionsStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryTransvectionSubmonoidNormalDetOneStatement

open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

namespace GlobalTheory.UTrans.StrongApprox

section Abstract

variable {R : Type} [CommRing R] {n : ℕ}

def stab (H : AddSubgroup (Fin n → R)) : Subring (Matrix (Fin n) (Fin n) R) where
  carrier := {A | ∀ z ∈ H, A *ᵥ z ∈ H}
  mul_mem' := fun {A B} hA hB z hz => by
    rw [← Matrix.mulVec_mulVec]; exact hA _ (hB z hz)
  one_mem' := fun z hz => by rw [Matrix.one_mulVec]; exact hz
  add_mem' := fun {A B} hA hB z hz => by
    rw [Matrix.add_mulVec]; exact add_mem (hA z hz) (hB z hz)
  zero_mem' := fun z _ => by rw [Matrix.zero_mulVec]; exact zero_mem _
  neg_mem' := fun {A} hA z hz => by rw [Matrix.neg_mulVec]; exact neg_mem (hA z hz)

theorem mem_stab {H : AddSubgroup (Fin n → R)} {A : Matrix (Fin n) (Fin n) R} :
    A ∈ stab H ↔ ∀ z ∈ H, A *ᵥ z ∈ H := Iff.rfl

theorem exists_of_cong {H : AddSubgroup (Fin n → R)} {D : ℕ} (hD : IsUnit (D : R))
    {A : Matrix (Fin n) (Fin n) R} (h : ∀ z ∈ H, ∃ w ∈ H, A *ᵥ z = D • w) :
    ∃ B ∈ stab H, A = (D : R) • B := by
  obtain ⟨i, hi⟩ := hD.exists_left_inv
  refine ⟨i • A, fun z hz => ?_, by rw [smul_smul, mul_comm, hi, one_smul]⟩
  obtain ⟨w, hw, e⟩ := h z hz
  rw [Matrix.smul_mulVec, e, ← Nat.cast_smul_eq_nsmul R, smul_smul, hi, one_smul]
  exact hw

theorem natCast_smul_mem {H : AddSubgroup (Fin n → R)} (k : ℕ) {A : Matrix (Fin n) (Fin n) R}
    (h : A ∈ stab H) : (k : R) • A ∈ stab H := by
  rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem h k

theorem mem_of_coprime {H : AddSubgroup (Fin n → R)} {k l : ℕ} (hkl : k.Coprime l)
    {A : Matrix (Fin n) (Fin n) R} (hk : (k : R) • A ∈ stab H) (hl : (l : R) • A ∈ stab H) :
    A ∈ stab H := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hkl
  have e : A = a • ((k : R) • A) + b • ((l : R) • A) := by
    rw [← Int.cast_smul_eq_zsmul R, ← Int.cast_smul_eq_zsmul R, smul_smul, smul_smul, ← add_smul]
    have := congrArg (Int.cast : ℤ → R) hab
    push_cast at this
    rw [this, one_smul]
  rw [e]
  exact add_mem (zsmul_mem hk a) (zsmul_mem hl b)

def scal (H : AddSubgroup (Fin n → R)) : Subring R :=
  (stab H).comap (algebraMap R (Matrix (Fin n) (Fin n) R))

theorem mem_scal {H : AddSubgroup (Fin n → R)} {a : R} :
    a ∈ scal H ↔ a • (1 : Matrix (Fin n) (Fin n) R) ∈ stab H := by
  rw [scal, Subring.mem_comap, Algebra.algebraMap_eq_smul_one]

theorem exists_entry_bound {H : AddSubgroup (Fin n → R)}
    (hb : ∀ A : Matrix (Fin n) (Fin n) R, ∃ d : ℕ, 0 < d ∧ (d : R) • A ∈ stab H) :
    ∃ d : ℕ, 0 < d ∧ ∀ B ∈ stab H, ∀ i j, (d : R) * B i j ∈ scal H := by
  classical
  choose f hf0 hf using fun p : Fin n × Fin n => hb (Matrix.single p.1 p.2 1)
  have h1 : ∀ a b, ((∏ p, f p : ℕ) : R) • Matrix.single a b (1 : R) ∈ stab H := by
    intro a b
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem f (Finset.mem_univ (a, b))
    rw [hk, mul_comm, Nat.cast_mul, mul_smul]
    exact natCast_smul_mem k (hf (a, b))
  have h0 : 0 < ∏ p, f p := Finset.prod_pos fun p _ => hf0 p
  generalize ∏ p, f p = d at h1 h0
  refine ⟨d * d, Nat.mul_pos h0 h0, fun B hB i j => ?_⟩
  rw [mem_scal]
  have e : (((d * d : ℕ) : R) * B i j) • (1 : Matrix (Fin n) (Fin n) R) =
      ∑ k, ((d : R) • Matrix.single k i (1 : R)) * B * ((d : R) • Matrix.single j k (1 : R)) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.single_mul_mul_single, smul_smul]
    ext a b
    simp only [Matrix.smul_apply, Matrix.sum_apply, Matrix.single_apply, Matrix.one_apply, smul_eq_mul]
    rw [Finset.sum_eq_single a]
    · by_cases h : a = b <;> simp [h]
    · intro c _ hc; simp [hc]
    · simp
  rw [e]
  exact sum_mem fun k _ => mul_mem (mul_mem (h1 _ _) hB) (h1 _ _)

theorem det_cong (S : Subring R) (t D : ℕ) (B : Matrix (Fin n) (Fin n) R) (hB : ∀ i j, B i j ∈ S) :
    ∃ s ∈ S, ((t : R) • (1 : Matrix (Fin n) (Fin n) R) + (D : R) • B).det = (t : R) ^ n + D * s := by
  let B' : Matrix (Fin n) (Fin n) S := Matrix.of fun i j => ⟨B i j, hB i j⟩
  let I : Ideal S := Ideal.span {(D : S)}
  have h1 : ((t : S) • (1 : Matrix (Fin n) (Fin n) S) + (D : S) • B').det - (t : S) ^ n ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, RingHom.map_det]
    have hD : Ideal.Quotient.mk I (D : S) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    have : (Ideal.Quotient.mk I).mapMatrix ((t : S) • (1 : Matrix (Fin n) (Fin n) S) + (D : S) • B') =
        (Ideal.Quotient.mk I t) • (1 : Matrix (Fin n) (Fin n) (S ⧸ I)) := by
      ext i j
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
        smul_eq_mul, map_add, map_mul, hD, zero_mul, add_zero, Matrix.one_apply]
      split_ifs <;> simp
    rw [this, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one, map_pow, sub_self]
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 h1
  refine ⟨s, s.2, ?_⟩
  have h2 : S.subtype.mapMatrix ((t : S) • (1 : Matrix (Fin n) (Fin n) S) + (D : S) • B') =
      (t : R) • (1 : Matrix (Fin n) (Fin n) R) + (D : R) • B := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, map_add, map_mul, Matrix.one_apply, map_natCast]
    split_ifs <;> simp [B']
  rw [← h2, ← RingHom.map_det, ← sub_eq_iff_eq_add',
    show (t : R) ^ n = S.subtype ((t : S) ^ n) by simp, ← map_sub, ← hs]
  simp [mul_comm]

theorem glue {H : AddSubgroup (Fin n → R)} {M d t k e : ℕ} (hM : IsUnit (M : R))
    (ht : t.Coprime (M * d)) (hk : k.Coprime (M * d)) {g m m' C W : Matrix (Fin n) (Fin n) R}
    (hg : (d : R) • g ∈ stab H) (hC : C ∈ stab H) (hW : W ∈ stab H)
    (hm' : (((M * d) ^ e : ℕ) : R) • m' ∈ stab H)
    (h1 : (t : R) • (m * g - 1) = (M : R) • C) (h2 : (k : R) • (m' - m) = ((M * d : ℕ) : R) • W) :
    ∃ Y ∈ stab H, m' * g = 1 + (M : R) • Y := by
  obtain ⟨i, hi⟩ := hM.exists_left_inv
  refine ⟨i • (m' * g - 1), ?_, by rw [smul_smul, mul_comm, hi, one_smul, add_sub_cancel]⟩
  refine mem_of_coprime (k := k * t) (l := (M * d) ^ (e + 1))
    (Nat.Coprime.pow_right _ (Nat.Coprime.mul_left hk ht)) ?_ ?_
  · have : ((k * t : ℕ) : R) • i • (m' * g - 1) =
        (t : R) • (W * ((d : R) • g)) + (k : R) • C := by
      have e1 : m' * g - 1 = (m' - m) * g + (m * g - 1) := by noncomm_ring
      have e2 : ((k * t : ℕ) : R) • i • (m' * g - 1) =
          (i * t) • (((k : R) • (m' - m)) * g) + (i * k) • ((t : R) • (m * g - 1)) := by
        rw [e1, Matrix.smul_mul]; push_cast; module
      rw [e2, h1, h2, Matrix.smul_mul, Matrix.mul_smul]
      push_cast
      simp only [smul_smul]
      congr 2
      · linear_combination (t * d : R) * hi
      · linear_combination (k : R) * hi
    rw [this]
    exact add_mem (natCast_smul_mem _ (mul_mem hW hg)) (natCast_smul_mem _ hC)
  · have : (((M * d) ^ (e + 1) : ℕ) : R) • i • (m' * g - 1) =
        ((((M * d) ^ e : ℕ) : R) • m') * ((d : R) • g) - (((M * d) ^ e * d : ℕ) : R) • 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul]
      push_cast
      simp only [smul_smul, ← smul_sub]
      congr 1
      linear_combination ((M : R) * d) ^ e * d * hi
    rw [this]
    exact sub_mem (mul_mem hm' hg) (natCast_smul_mem _ (one_mem _))

theorem mul_cong {H : AddSubgroup (Fin n → R)} {M t t' : ℕ} {A A' C C' : Matrix (Fin n) (Fin n) R}
    (hC : C ∈ stab H) (hC' : C' ∈ stab H) (h : (t : R) • (A - 1) = (M : R) • C)
    (h' : (t' : R) • (A' - 1) = (M : R) • C') :
    ∃ B ∈ stab H, ((t * t' : ℕ) : R) • (A * A' - 1) = (M : R) • B := by
  refine ⟨(M : R) • (C * C') + (t' : R) • C + (t : R) • C', add_mem (add_mem
    (natCast_smul_mem _ (mul_mem hC hC')) (natCast_smul_mem _ hC)) (natCast_smul_mem _ hC'), ?_⟩
  have e1 : A * A' - 1 = (A - 1) * (A' - 1) + (A - 1) + (A' - 1) := by noncomm_ring
  have e2 : ((t * t' : ℕ) : R) • (A * A' - 1) = ((t : R) • (A - 1)) * ((t' : R) • (A' - 1)) +
      (t' : R) • ((t : R) • (A - 1)) + (t : R) • ((t' : R) • (A' - 1)) := by
    rw [e1, Matrix.smul_mul, Matrix.mul_smul]; push_cast; module
  rw [e2, h, h', Matrix.smul_mul, Matrix.mul_smul]
  module

end Abstract

section Adelic

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

noncomputable def emb : E →+* RA F E :=
  (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E).toRingHom

omit [NumberField E] in
theorem emb_mulVec (γ : Matrix (Fin n) (Fin n) E) (v : Fin n → E) :
    (emb F).mapMatrix γ *ᵥ fv F v = fv F (γ *ᵥ v) := by
  funext i
  exact (RingHom.map_mulVec (emb F) γ v i).symm

omit [NumberField E] in
theorem isUnit_nat {D : ℕ} (hD : 0 < D) : IsUnit (D : RA F E) := by
  rw [← map_natCast (algebraMap F (RA F E))]
  exact (IsUnit.mk0 _ (by exact_mod_cast hD.ne')).map _

omit [NumberField E] in
theorem emb_smul (a : E) (γ : Matrix (Fin n) (Fin n) E) :
    (emb F).mapMatrix (a • γ) = emb F a • (emb F).mapMatrix γ := by
  ext i j; simp

omit [NumberField E] in
theorem emb_mem_stab {L : Submodule (𝓞 E) (Fin n → E)} {γ : Matrix (Fin n) (Fin n) E}
    (h : ∀ v ∈ L, γ *ᵥ v ∈ L) : (emb F).mapMatrix γ ∈ stab (hat F (L : Set (Fin n → E))) := by
  intro z hz
  refine Translate.mulVec_mem_hat (fun v hv => ?_) hz
  rw [SetLike.mem_coe, Translate.mem_pre, emb_mulVec]
  exact Translate.fv_mem_hat (h v hv)

theorem conj_mem_scal (c : E ≃ₐ[F] E) {L : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) (i : Fin n) {s : E}
    (hs : emb F s ∈ scal (hat F (L : Set (Fin n → E)))) :
    emb F (c s) ∈ scal (hat F (L : Set (Fin n → E))) := by
  have h1 := (hat_rational_points_and_approx F E n L hL hsp).1
  have hne : L ≠ ⊥ := by
    rintro rfl
    have : (Pi.single i 1 : Fin n → E) ∈ Submodule.span E
        (((⊥ : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E))) := by rw [hsp]; trivial
    simp at this
  have hint : IsIntegral (𝓞 E) s := by
    refine isIntegral_of_smul_mem_submodule L hne hL s fun v hv => ?_
    rw [← h1, Translate.fv_smul]
    have := mem_scal.1 hs _ (Translate.fv_mem_hat hv)
    rwa [Matrix.smul_mulVec, Matrix.one_mulVec] at this
  have hz : IsIntegral ℤ s := isIntegral_trans s hint
  have hc : IsIntegral ℤ (c s) := hz.map c.toRingEquiv.toRingHom.toIntAlgHom
  rw [mem_scal]
  intro z hz
  rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  exact Translate.hat_smul_ring L ⟨c s, hc⟩ hz

theorem exists_bound_stab {L : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) (A : Matrix (Fin n) (Fin n) (RA F E)) :
    ∃ d : ℕ, 0 < d ∧ (d : RA F E) • A ∈ stab (hat F (L : Set (Fin n → E))) := by
  obtain ⟨d, hd, h⟩ := Translate.exists_bound A hL
    (hat_rational_points_and_approx F E n L hL hsp).2.2.2
  refine ⟨d, hd, fun z hz => ?_⟩
  rw [Nat.cast_smul_eq_nsmul, Matrix.smul_mulVec]
  exact h z hz

end Adelic

theorem strong_approximation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), Module.finrank F E = 2 → IsHerm (c : E →+* E) G → (∃ z : Fin n → E, z ≠ 0 ∧ hf (c : E →+* E) G z z = 0) → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ g : GL (Fin n) (RA F E), (∀ x y, hermA c G ((g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ x) ((g : Matrix (Fin n) (Fin n) (RA F E)) *ᵥ y) = hermA c G x y) → (g : Matrix (Fin n) (Fin n) (RA F E)).det = 1 → ∀ M : ℕ, 0 < M → ∃ γ : Matrix (Fin n) (Fin n) E, IsU (c : E →+* E) G γ ∧ γ.det = 1 ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), ∃ w ∈ hat F (L : Set (Fin n → E)), ((γ.map (fun a => ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] a : RA F E))) * (g : Matrix (Fin n) (Fin n) (RA F E))) *ᵥ z = z + M • w := by
  intro F E _ _ _ _ _ c n G hrk hG hiso L hL hsp g hg hdet M hM
  have hG' : GlobalTheory.UnRep.IsHermForm c G := by
    refine ⟨hG.invol, ?_, hG.herm, hG.det_ne⟩
    rintro rfl
    obtain ⟨a, ha⟩ := hG.ne_id
    exact ha rfl
  obtain ⟨i₀, -⟩ := Function.ne_iff.1 hiso.choose_spec.1
  obtain ⟨xs, hxs, -⟩ := GlobalTheory.UnRep.exists_anisotropic_orthogonal_basis F E c n G hG'
  have hx : hf (c : E →+* E) G (xs i₀) (xs i₀) ≠ 0 := hxs i₀
  generalize xs i₀ = x at hx
  set h := hf (c : E →+* E) G x x with hh
  set H := hat F (L : Set (Fin n → E)) with hH
  set g' : Matrix (Fin n) (Fin n) (RA F E) := (g : Matrix (Fin n) (Fin n) (RA F E)) with hg'
  let P : Matrix (Fin n) (Fin n) E := Matrix.of fun a b => h⁻¹ * x a * ∑ e, G b e * c (x e)
  have hP : ∀ a : E, tv (c : E →+* E) G x (a / h) - 1 = a • P := by
    intro a
    rw [tv, add_sub_cancel_left]
    ext i j
    simp only [P, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, RingHom.coe_coe]
    ring
  obtain ⟨d, hd, hdB⟩ := exists_entry_bound (exists_bound_stab F hL hsp)
  obtain ⟨dg, hdg, hdg'⟩ := exists_bound_stab F hL hsp g'
  obtain ⟨dP, hdP, hdP'⟩ := exists_bound_stab F hL hsp ((emb F).mapMatrix P)
  have hb : 0 < M * dg := Nat.mul_pos hM hdg
  have hD₁ : 0 < M * dP := Nat.mul_pos hM hdP
  have hD : 0 < M * dP * d := Nat.mul_pos hD₁ hd
  obtain ⟨γ₀, hγ₀, t, ht, hcong⟩ := GlobalTheory.T.unitaryGroup_weak_approximation_at_primes F E c n G hG' hrk L hL hsp g (M * dg) (M * dP * d)
    hg hb hD
  have hU : IsU (c : E →+* E) G γ₀.1 := hγ₀
  set γ : Matrix (Fin n) (Fin n) E := γ₀.1 with hγ
  obtain ⟨B, hB, hBe⟩ := exists_of_cong (H := H) (isUnit_nat F hD)
    (A := (t : RA F E) • ((emb F).mapMatrix γ * g' - 1)) (fun z hz => by
      obtain ⟨w, hw, e⟩ := hcong z hz
      refine ⟨w, hw, ?_⟩
      rw [Nat.cast_smul_eq_nsmul, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec]
      exact e)
  obtain ⟨s, hs, hse⟩ := det_cong (scal H) t (M * dP) ((d : RA F E) • B) (hdB B hB)
  have e0 : (t : RA F E) • (1 : Matrix (Fin n) (Fin n) (RA F E)) + ((M * dP : ℕ) : RA F E) •
      (d : RA F E) • B = (t : RA F E) • ((emb F).mapMatrix γ * g') := by
    rw [smul_smul, ← Nat.cast_mul, ← hBe, ← smul_add, add_sub_cancel]
  rw [e0, Matrix.det_smul, Fintype.card_fin, Matrix.det_mul, hdet, mul_one, ← RingHom.map_det] at hse
  set u := γ.det with hu
  have hD₁E : ((M * dP : ℕ) : E) ≠ 0 := by exact_mod_cast hD₁.ne'
  let s₀ : E := (t : E) ^ n * (u - 1) / ((M * dP : ℕ) : E)
  have hs₀ : ((M * dP : ℕ) : E) * s₀ = (t : E) ^ n * (u - 1) := mul_div_cancel₀ _ hD₁E
  have hs₁ : emb F s₀ = s := by
    refine (isUnit_nat F hD₁).mul_left_cancel ?_
    have := congrArg (emb F) hs₀
    simp only [map_mul, map_natCast, map_pow, map_sub, map_one] at this
    rw [this]
    linear_combination hse
  have hcs := mem_scal.1 (conj_mem_scal F c hL hsp i₀ (hs₁ ▸ hs))
  have hs₂ : ((M * dP : ℕ) : RA F E) * emb F (c s₀) = (t : RA F E) ^ n * emb F (c u - 1) := by
    have := congrArg (fun a => emb F (c a)) hs₀
    simpa only [map_mul, map_natCast, map_pow, map_sub, map_one] using this
  obtain ⟨hnorm, hnormal⟩ := GlobalTheory.T.unitaryTransvectionSubmonoid_normal_det_one E n (c : E →+* E) G hG
  have hu1 : u * c u = 1 := (hnorm γ hU).1
  obtain ⟨m, hm, hme⟩ := (GlobalTheory.T.unitary_eq_quasiReflection_mul_transvections F E c n G hG hiso γ hU).1 x hx
  have hmul := (GlobalTheory.T.transvection_identities_unitary E n (c : E →+* E) G hG.invol hG.herm).2.2.1 x
  have hm' : m = tv (c : E →+* E) G x ((c u - 1) / h) * γ := by
    have h0 : (c u - 1) / h + (u - 1) / h + (c u - 1) / h * ((u - 1) / h) * h = 0 := by
      field_simp
      linear_combination hu1
    have h1 : tv (c : E →+* E) G x 0 = 1 := by
      have := hP 0
      rwa [zero_div, zero_smul, sub_eq_zero] at this
    rw [hme, ← Matrix.mul_assoc, hmul, ← hu, ← hh, h0, h1, Matrix.one_mul]
  have hc1 : ((t ^ n : ℕ) : RA F E) • ((emb F).mapMatrix (tv (c : E →+* E) G x ((c u - 1) / h)) - 1) =
      (M : RA F E) • ((emb F (c s₀) • (1 : Matrix (Fin n) (Fin n) (RA F E))) *
        ((dP : RA F E) • (emb F).mapMatrix P)) := by
    rw [← map_one (emb F).mapMatrix, ← map_sub, hP, emb_smul, map_one, Matrix.smul_mul,
      Matrix.one_mul, smul_smul, smul_smul, smul_smul]
    congr 1
    push_cast at hs₂ ⊢
    linear_combination -hs₂
  have hc2 : (t : RA F E) • ((emb F).mapMatrix γ * g' - 1) =
      (M : RA F E) • (((dP * d : ℕ) : RA F E) • B) := by
    rw [hBe, smul_smul, ← Nat.cast_mul, mul_assoc]
  obtain ⟨C, hC, hCe⟩ := mul_cong (mul_mem hcs hdP') (natCast_smul_mem _ hB) hc1 hc2
  rw [← Matrix.mul_assoc, ← map_mul, ← hm'] at hCe
  obtain ⟨m', hm'T, k, e, hk, hadj⟩ := GlobalTheory.T.unitaryTransvectionSubmonoid_adjust_integral_away F E c n G hrk hG L hL hsp m hm (M * dg) hb 1
  have hbE : ((M * dg : ℕ) : E) ≠ 0 := by exact_mod_cast hb.ne'
  have hW : (emb F).mapMatrix (((k : E) / ((M * dg : ℕ) : E)) • (m' - m)) ∈ stab H := by
    refine emb_mem_stab F fun v hv => ?_
    obtain ⟨w, hw, e⟩ := (hadj v hv).1
    rw [pow_one, ← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E] at e
    rw [Matrix.smul_mulVec, Matrix.sub_mulVec, div_eq_inv_mul, mul_smul, e, smul_smul,
      inv_mul_cancel₀ hbE, one_smul]
    exact hw
  have hint : (((M * dg) ^ e : ℕ) : RA F E) • (emb F).mapMatrix m' ∈ stab H := by
    rw [← map_natCast (emb F), ← emb_smul]
    refine emb_mem_stab F fun v hv => ?_
    rw [Nat.cast_smul_eq_nsmul, Matrix.smul_mulVec]
    exact (hadj v hv).2.1
  obtain ⟨Y, hY, hYe⟩ := glue (isUnit_nat F hM)
    (Nat.Coprime.mul_left (Nat.Coprime.pow_left n ht) ht) hk hdg' hC hW hint hCe (by
      rw [← map_sub, ← map_natCast (emb F), ← map_natCast (emb F), ← emb_smul, ← emb_smul,
        smul_smul, mul_div_cancel₀ _ hbE])
  refine ⟨m', (hnormal m' hm'T).1, (hnormal m' hm'T).2.1, fun z hz => ⟨Y *ᵥ z, hY z hz, ?_⟩⟩
  change ((emb F).mapMatrix m' * g') *ᵥ z = _
  rw [hYe, Matrix.add_mulVec, Matrix.one_mulVec, Nat.cast_smul_eq_nsmul, Matrix.smul_mulVec]

end GlobalTheory.UTrans.StrongApprox
