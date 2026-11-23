import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GramUnimodular
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsAHEqOfMemRatPts

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SelfDualStabConj

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_sq_conj_sub (h : IsCMExt F E σ) (hU : Algebra.Unramified (𝓞 F) (𝓞 E)) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ (x : 𝓞 E) (d : 𝓞 F), d ∉ v.asIdeal ∧ algebraMap F E d = ((x : E) - σ x) ^ 2 := by
  have : Algebra.IsQuadraticExtension F E := { finrank_eq_two' := h.2.2.1 }
  have : IsGalois F E := inferInstance
  have := v.isMaximal
  have hσ := GlobalTheory.LFun.InertChart.conj_conj h
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := E ≃ₐ[F] E) v.asIdeal Q
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal Q (E ≃ₐ[F] E),
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt] at hcard
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom σ σ (AlgHom.ext hσ) (AlgHom.ext hσ)
  have hs1 : s ≠ 1 := fun hs => GlobalTheory.LFun.InertChart.conj_ne h fun x => congrArg (fun t : E ≃ₐ[F] E => t x) hs
  obtain ⟨x, hx⟩ : ∃ x : 𝓞 E, s • x - x ∉ Q := by
    by_contra hn
    push Not at hn
    have hs : s ∈ Q.inertia (E ≃ₐ[F] E) := AddSubgroup.mem_inertia.2 hn
    rw [Subgroup.eq_bot_of_card_eq _ hcard, Subgroup.mem_bot] at hs
    exact hs1 hs
  have hfix : ∀ t : E ≃ₐ[F] E, t (((x : E) - σ x) ^ 2) = ((x : E) - σ x) ^ 2 := fun t => by
    have hc : Nat.card (E ≃ₐ[F] E) = 2 := (IsGalois.card_aut_eq_finrank F E).trans h.2.2.1
    obtain ⟨u, -, hu⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hc
    by_cases ht : t = 1
    · rw [ht]; rfl
    · rw [(hu t ht).trans (hu s hs1).symm]
      change σ _ = _
      rw [map_pow, map_sub, hσ]; ring
  obtain ⟨d, hd⟩ := (IsGalois.mem_range_algebraMap_iff_fixed _).2 hfix
  have e : (((s • x - x) ^ 2 : 𝓞 E) : E) = ((x : E) - σ x) ^ 2 := by
    change (σ x - (x : E)) ^ 2 = _
    ring
  have hi : IsIntegral ℤ d := by
    rw [← isIntegral_algebraMap_iff (algebraMap F E).injective, hd, ← e]
    exact RingOfIntegers.isIntegral_coe _
  refine ⟨x, ⟨d, hi⟩, fun hm => hx (hQ.isPrime.mem_of_pow_mem 2 ?_), hd⟩
  have : (s • x - x) ^ 2 = algebraMap (𝓞 F) (𝓞 E) ⟨d, hi⟩ := RingOfIntegers.ext (e.trans hd.symm)
  rw [this]
  rwa [hQv.over] at hm

def conjInt (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) : intLoc F E v →+* intLoc F E v :=
  (sigR (Fv F v) σ).restrict _ _ fun _ => sigR_mem_intLoc σ

theorem exists_isUnit_sub_conj (h : IsCMExt F E σ) (hU : Algebra.Unramified (𝓞 F) (𝓞 E))
    (v : HeightOneSpectrum (𝓞 F)) : ∃ ω : intLoc F E v, IsUnit (ω - conjInt σ v ω) := by
  obtain ⟨x, d, hd, e⟩ := exists_sq_conj_sub h hU v
  have hd0 : (d : F) ≠ 0 := fun h0 => hd (by
    rw [show d = 0 from RingOfIntegers.coe_injective (by simpa using h0)]; exact zero_mem _)
  have ha : algebraMap F (Fv F v) (d : F)⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have h1 : v.valuation F (d : F) = 1 := (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) v).2 hd
    have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (d : F)⁻¹
    exact le_of_eq (h2.trans (by rw [map_inv₀, h1, inv_one]))
  refine ⟨⟨_, tmul_mem_intLoc (one_mem _) x⟩, (isUnit_pow_iff two_ne_zero).1
    (IsUnit.of_mul_eq_one ⟨_, tmul_mem_intLoc ha 1⟩ (Subtype.ext ?_))⟩
  change (inclR (Fv F v) (x : E) - inclR (Fv F v) (σ x)) ^ 2 * (algebraMap F (Fv F v) (d : F)⁻¹ ⊗ₜ[F] (1 : E)) = 1
  rw [← map_sub, ← map_pow, ← e, Algebra.algebraMap_eq_smul_one (d : F)⁻¹, TensorProduct.smul_tmul,
    ← Algebra.algebraMap_eq_smul_one]
  change inclR (Fv F v) _ * inclR (Fv F v) _ = 1
  rw [← map_mul, ← map_mul, mul_inv_cancel₀ hd0, map_one, map_one]

theorem exists_norm (h : IsCMExt F E σ) (hU : Algebra.Unramified (𝓞 F) (𝓞 E)) (v : HeightOneSpectrum (𝓞 F))
    {n : ℕ} {B : Matrix (Fin n) (Fin n) (intLoc F E v)} (hB : cT (conjInt σ v) B = B) (hu : IsUnit B) :
    ∃ u : GL (Fin n) (intLoc F E v), cT (conjInt σ v) u.1 * u.1 = B := by
  let O := intLoc F E v
  let _ := (GlobalTheory.Orb.intLocMap E v).toAlgebra
  have : Module.Finite (v.adicCompletionIntegers F) O := GlobalTheory.Orb.finite_intLocMap v
  have := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  have : Finite (v.adicCompletionIntegers F ⧸ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) :=
    Formalism.UG.P.glint_finite_residueField v
  have := GlobalTheory.InertNorm.isAdicComplete_map_of_finite (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) O
  have := GlobalTheory.InertNorm.finite_quotient_map_of_finite (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)) O
  have : IsNoetherianRing O := Algebra.FiniteType.isNoetherianRing (v.adicCompletionIntegers F) O
  let s : O →+* O := conjInt σ v
  have hs : ∀ y : O, s (s y) = y := fun y =>
    Subtype.ext (GlobalTheory.Doubling.sigR_invol (GlobalTheory.LFun.InertChart.conj_conj h) y.1)
  have hk : ∀ c, s (algebraMap (v.adicCompletionIntegers F) O c) = algebraMap (v.adicCompletionIntegers F) O c :=
    fun c => Subtype.ext (by
      change sigR (Fv F v) σ ((c : Fv F v) ⊗ₜ[F] (1 : E)) = (c : Fv F v) ⊗ₜ[F] (1 : E)
      simp [sigR])
  let I := (IsLocalRing.maximalIdeal (v.adicCompletionIntegers F)).map (algebraMap (v.adicCompletionIntegers F) O)
  have hI : I ≤ I.comap s := Ideal.map_le_iff_le_comap.2 fun c hc => by
    rw [Ideal.mem_comap, Ideal.mem_comap, hk]
    exact Ideal.mem_map_of_mem _ hc
  obtain ⟨p, hp⟩ := GlobalTheory.UnitaryDoubleCoset.exists_poly_norm hs
    (GlobalTheory.InertNorm.exists_dvd_mul_map_sub_X O I s hs (fun y hy => hI hy) (exists_isUnit_sub_conj h hU v)) hB hu
  have h2 : IsUnit (Polynomial.aeval B p) := isUnit_of_mul_isUnit_right (hp ▸ hu)
  exact ⟨h2.unit, hp⟩

theorem cT_mul {A : Type} [CommRing A] (s : A →+* A) {n : ℕ} (P Q : Matrix (Fin n) (Fin n) A) :
    cT s (P * Q) = cT s Q * cT s P := by
  unfold cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one {A : Type} [CommRing A] (s : A →+* A) {n : ℕ} : cT s (1 : Matrix (Fin n) (Fin n) A) = 1 := by
  unfold cT
  rw [Matrix.map_one _ (map_zero s) (map_one s), Matrix.transpose_one]

theorem exists_orthonormal_frame (h : IsCMExt F E σ) (hU : Algebra.Unramified (𝓞 F) (𝓞 E)) {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) (L : Submodule (𝓞 E) (Fin n → E)) [Submodule.IsLattice E L]
    {v : HeightOneSpectrum (𝓞 F)} (hL : IsSelfDualAt σ J L v) :
    ∃ b : GL (Fin n) (Fv F v ⊗[F] E), cT (sigR _ σ) b.1 * JR (Fv F v) J * b.1 = 1 ∧
      ∀ y, (∀ i, y i ∈ intLoc F E v) ↔ b.1 *ᵥ y ∈ latLoc F L v := by
  obtain ⟨a₀, ha₀⟩ := Frames.exists_isLatticeFrame (F := F) L
  have ha := ha₀ v
  generalize bc (compFin F E v) a₀ = a at ha
  have hσ := GlobalTheory.Doubling.sigR_invol (R := Fv F v) (GlobalTheory.LFun.InertChart.conj_conj h)
  have hJu : IsUnit (JR (F := F) (Fv F v) J) := (Matrix.isUnit_iff_isUnit_det _).2 (GlobalTheory.Doubling.isUnit_det_JR hJ.2)
  have hJh : cT (sigR _ σ) (JR (F := F) (Fv F v) J) = JR (Fv F v) J := by
    ext i j; exact congrArg (fun x => (1 : Fv F v) ⊗ₜ[F] x) (hJ.1 i j)
  have hau : IsUnit (cT (sigR _ σ) a.1) := IsUnit.of_mul_eq_one (cT (sigR _ σ) (a⁻¹).1) (by
    rw [← cT_mul, Units.inv_mul, cT_one])
  obtain ⟨H, hH⟩ := (hau.mul hJu).mul a.isUnit
  obtain ⟨h1, h2⟩ := GlobalTheory.StdUnn.Unimod.gram_int (sigR _ σ) (intLoc F E v) (fun _ => sigR_mem_intLoc σ)
    (JR (Fv F v) J) a.1 (a⁻¹).1 (H⁻¹).1 (fun y => y ∈ latLoc F L v) a.mul_inv (hH ▸ H.mul_inv) ha
    (fun y => SetLike.ext_iff.1 hL y)
  let ι := (intLoc F E v).subtype
  have hinj : ∀ {M N : Matrix (Fin n) (Fin n) (intLoc F E v)}, M.map ι = N.map ι → M = N :=
    fun e => Matrix.map_injective Subtype.val_injective e
  have hcT : ∀ M : Matrix (Fin n) (Fin n) (intLoc F E v), (cT (conjInt σ v) M).map ι = cT (sigR _ σ) (M.map ι) :=
    fun _ => rfl
  let B : Matrix (Fin n) (Fin n) (intLoc F E v) := Matrix.of fun i j => ⟨_, h1 i j⟩
  let B' : Matrix (Fin n) (Fin n) (intLoc F E v) := Matrix.of fun i j => ⟨_, h2 i j⟩
  have eB : B.map ι = cT (sigR _ σ) a.1 * JR (Fv F v) J * a.1 := rfl
  obtain ⟨u, hu⟩ := exists_norm h hU v (B := B)
    (hinj (by rw [hcT, eB, cT_mul, cT_mul, hJh, GlobalTheory.UnitaryDoubleCoset.cT_cT hσ, Matrix.mul_assoc]))
    (IsUnit.of_mul_eq_one B' (hinj (by
      rw [Matrix.map_mul, eB, ← hH, Matrix.map_one _ (map_zero ι) (map_one ι)]; exact H.mul_inv)))
  have hu' : cT (sigR _ σ) (bc ι u).1 * (bc ι u).1 = cT (sigR _ σ) a.1 * JR (Fv F v) J * a.1 := by
    rw [← eB, ← hu, Matrix.map_mul]; rfl
  have hm : ∀ (k : GL (Fin n) (intLoc F E v)) (y : Fin n → Fv F v ⊗[F] E), (∀ i, y i ∈ intLoc F E v) →
      ∀ i, ((bc ι k).1 *ᵥ y) i ∈ intLoc F E v := fun k y hy i => by
    rw [Matrix.mulVec, dotProduct]
    exact sum_mem fun j _ => mul_mem (k.1 i j).2 (hy j)
  refine ⟨a * (bc ι u)⁻¹, ?_, fun y => ?_⟩
  · have : cT (sigR _ σ) (a * (bc ι u)⁻¹).1 * JR (Fv F v) J * (a * (bc ι u)⁻¹).1 =
        cT (sigR _ σ) ((bc ι u)⁻¹).1 * (cT (sigR _ σ) a.1 * JR (Fv F v) J * a.1) * ((bc ι u)⁻¹).1 := by
      simp only [Units.val_mul, cT_mul, Matrix.mul_assoc]
    rw [this, ← hu', ← Matrix.mul_assoc, ← cT_mul, Units.mul_inv, cT_one, Matrix.one_mul, Units.mul_inv]
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← ha]
    refine ⟨fun hy => by rw [← map_inv]; exact hm _ y hy, fun hy => ?_⟩
    have := hm u _ hy
    rwa [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at this

theorem exists_conj_stabLoc : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E),
    IsHermND σ J → ∀ (L L' : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E L → Submodule.IsLattice E L' →
    ∀ v : HeightOneSpectrum (𝓞 F), IsSelfDualAt σ J L v → IsSelfDualAt σ J L' v →
    ∃ g : GLoc σ J v, ∀ k : GLoc σ J v, k ∈ stabLoc σ J L' v ↔ g⁻¹ * k * g ∈ stabLoc σ J L v := by
  intro F E _ _ _ _ _ σ h hU n J hJ L L' _ _ v hL hL'
  obtain ⟨b, hb, fb⟩ := exists_orthonormal_frame h hU hJ L hL
  obtain ⟨c, hc, fc⟩ := exists_orthonormal_frame h hU hJ L' hL'
  have hg : cT (sigR _ σ) (c * b⁻¹).1 * JR (Fv F v) J * (c * b⁻¹).1 = JR (Fv F v) J := by
    have : cT (sigR _ σ) (c * b⁻¹).1 * JR (Fv F v) J * (c * b⁻¹).1 =
        cT (sigR _ σ) (b⁻¹).1 * (cT (sigR _ σ) c.1 * JR (Fv F v) J * c.1) * (b⁻¹).1 := by
      simp only [Units.val_mul, cT_mul, Matrix.mul_assoc]
    rw [this, hc, ← hb, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← cT_mul, Units.mul_inv, cT_one, Matrix.one_mul,
      Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  let g : GLoc σ J v := ⟨c * b⁻¹, hg⟩
  have eg : matHom _ σ J g = c * b⁻¹ := rfl
  have hm : ∀ y, y ∈ latLoc F L v ↔ (matHom _ σ J g).1 *ᵥ y ∈ latLoc F L' v := fun y => by
    rw [eg, Units.val_mul, ← Matrix.mulVec_mulVec, ← fc, fb, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hact : ∀ (p q : GLoc σ J v) y,
      (matHom _ σ J p).1 *ᵥ ((matHom _ σ J q).1 *ᵥ y) = (matHom _ σ J (p * q)).1 *ᵥ y := fun p q y => by
    rw [Matrix.mulVec_mulVec, map_mul, Units.val_mul]
  refine ⟨g, fun k => ?_⟩
  rw [mem_stabLoc, mem_stabLoc]
  refine ⟨fun hk y => ?_, fun hk y => ?_⟩
  · rw [hm, hm, hk, hact, hact, ← mul_assoc, mul_inv_cancel_left]
  · have := hk ((matHom _ σ J g⁻¹).1 *ᵥ y)
    rwa [hm, hm, hact, hact, hact, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec, mul_assoc,
      mul_inv_cancel_right, mul_inv_cancel_left] at this

end GlobalTheory.SelfDualStabConj
