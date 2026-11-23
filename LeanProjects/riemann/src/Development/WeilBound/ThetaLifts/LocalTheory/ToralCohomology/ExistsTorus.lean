import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.EqZeroOfPiInf

noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CompanionTheory.CMAdele
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.ThKG.CayleyTransformDarboux

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_re (hF : IsTotallyReal F) (s : InfinitePlace F → ℝ) : ∃ a : AF F, (∀ u : AF F, evI F u = 0 → u * a = 0) ∧
    ∀ w, InfinitePlace.Completion.extensionEmbedding w (a.1 w) = s w := by
  refine ⟨((fun w => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm (s w)), 0),
    fun u hu => ?_, fun w => ?_⟩
  · have h1 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (hu.trans (map_zero _).symm)
    refine Prod.ext ?_ ?_
    · change u.1 * _ = 0
      rw [h1, zero_mul]
    · change u.2 * 0 = 0
      rw [mul_zero]
  · rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply (IsTotallyReal.isReal w)]
    congr 1
    exact (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).apply_symm_apply (s w)

theorem exists_inf (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (c : InfinitePlace F → ℂ) :
    ∃ a : AE F E, At (evI F) a ∧ ∀ w, piInf (τ w) a = c w := by
  obtain ⟨β, hβ⟩ := exists_moved h
  obtain ⟨t, ht, ht'⟩ := exists_re h.1 fun w => (c w).im / ((τ w).1 β).im
  obtain ⟨s, hs, hs'⟩ := exists_re h.1 fun w => (c w).re - (c w).im / ((τ w).1 β).im * ((τ w).1 β).re
  refine ⟨s ⊗ₜ[F] 1 + t ⊗ₜ[F] β, fun u hu => ?_, fun w => ?_⟩
  · rw [smul_add, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, hs u hu, ht u hu,
      TensorProduct.zero_tmul, TensorProduct.zero_tmul, add_zero]
  · have := im_ne_zero h hβ (τ w).1
    rw [map_add, piInf_tmul, piInf_tmul, hs', ht', map_one, mul_one]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
    · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]; field_simp; ring

theorem piInf_cA (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E) :
    piInf τ (cA σ z) = star (piInf τ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, star_zero]
  | add x y hx hy => simp only [map_add, hx, hy, star_add]
  | tmul a x =>
    change piInf τ (a ⊗ₜ[F] σ x) = _
    rw [piInf_tmul, piInf_tmul, h.2.2.2, star_mul', show star (InfinitePlace.Completion.extensionEmbedding w (a.1 w)) = _ from
      Complex.conj_eq_iff_im.2 (im_extension h.1 w _)]

def atI (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] : Ideal (AE F E) where
  carrier := {a | At (evI F) a}
  add_mem' := fun {a b} ha hb u hu => by rw [smul_add, ha u hu, hb u hu, add_zero]
  zero_mem' := fun u _ => smul_zero u
  smul_mem' := fun c a ha u hu => by rw [smul_eq_mul, ← mul_smul_comm, ha u hu, mul_zero]

theorem mem_atI {a : AE F E} : a ∈ atI F E ↔ At (evI F) a := Iff.rfl

theorem at_entry {m n : Type} {M : Matrix m n (AE F E)} (h : At (evI F) M) (i j) : M i j ∈ atI F E :=
  fun u hu => congrFun (congrFun (h u hu) i) j

theorem at_cA {a : AE F E} (h : a ∈ atI F E) : cA σ a ∈ atI F E := fun u hu => by rw [← map_smul, h u hu, map_zero]

theorem eq_of_inf (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {a b : AE F E} (hab : a - b ∈ atI F E)
    (e : ∀ w, piInf (τ w) a = piInf (τ w) b) : a = b :=
  sub_eq_zero.1 (eq_zero_of_piInf σ h τ _ hab fun w => by rw [map_sub, e, sub_self])

theorem exists_unit (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (c : InfinitePlace F → ℂ) (hc : ∀ w, c w ≠ 0) :
    ∃ t : (AE F E)ˣ, (t : AE F E) - 1 ∈ atI F E ∧ ∀ w, piInf (τ w) t = c w := by
  obtain ⟨a, ha, ha'⟩ := exists_inf h τ fun w => c w - 1
  obtain ⟨b, hb, hb'⟩ := exists_inf h τ fun w => (c w)⁻¹ - 1
  refine ⟨Units.mkOfMulEqOne (1 + a) (1 + b) (eq_of_inf h τ ?_ fun w => ?_), by simpa [mem_atI] using ha, fun w => by simp [ha']⟩
  · rw [show (1 + a) * (1 + b) - 1 = a * (1 + b) + b by ring]
    exact add_mem (Ideal.mul_mem_right _ _ ha) hb
  · simp [ha', hb', hc w]

theorem inv_at {t : (AE F E)ˣ} (h : (t : AE F E) - 1 ∈ atI F E) : ((t⁻¹ : (AE F E)ˣ) : AE F E) - 1 ∈ atI F E := by
  have := neg_mem (Ideal.mul_mem_left _ ((t⁻¹ : (AE F E)ˣ) : AE F E) h)
  rwa [mul_sub, Units.inv_mul, mul_one, neg_sub] at this

theorem absE_inf (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {t : (AE F E)ˣ} (ht : (t : AE F E) - 1 ∈ atI F E) :
    (absE F E t : ℝ) = ∏ w, ‖piInf (τ w) t‖ ^ 2 := by
  have e : ∀ v, GlobalTheory.Doubling.unitFin F E v t = 1 := fun v => by
    obtain ⟨u, hu, hu'⟩ : ∃ u : AF F, evI F u = 0 ∧ evFin F v u = 1 :=
      ⟨(0, 1), map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F), map_one (evalV F v)⟩
    have h0 : algebraMap (AF F) (AE F E) u * ((t : AE F E) - 1) = 0 := (Algebra.smul_def _ _).symm.trans (ht u hu)
    have h1 := congrArg (compFin F E v) h0
    have h2 : compFin F E v (algebraMap (AF F) (AE F E) u) = 1 := by
      change evFin F v u ⊗ₜ[F] (1 : E) = 1
      rw [hu']; rfl
    rw [map_mul, map_zero, h2, one_mul, map_sub, map_one, sub_eq_zero] at h1
    exact Units.ext h1
  rw [GlobalTheory.Doubling.absE_apply]
  simp only [e, map_one, finprod_one, mul_one, GlobalTheory.Doubling.absEw_eq_sq h (τ _)]
  push_cast
  rfl

theorem exists_torus (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (l : InfinitePlace F → ℂ) (χ : Chr F E)
    {m : InfinitePlace F → ℤ} (hχ : HasExp τ χ m) (r : ℝ) :
    ∃ (t : ℝ → (AE F E)ˣ) (c : ℂ), (∀ s, (t s : AE F E) - 1 ∈ atI F E ∧ ∀ w, piInf (τ w) (t s) = Complex.exp (s * l w)) ∧
      HasDerivAt (fun s => (χ (t s) : ℂ) * (((absE F E (t s) : ℝ) ^ r : ℝ) : ℂ)) c 0 := by
  choose t ht ht' using fun s : ℝ => exists_unit h τ (fun w => Complex.exp (s * l w)) fun w => Complex.exp_ne_zero _
  have e : (fun s => (χ (t s) : ℂ) * (((absE F E (t s) : ℝ) ^ r : ℝ) : ℂ)) =
      fun s : ℝ => Complex.exp (s * ∑ w, ((l w - (l w).re) * m w + 2 * (l w).re * r)) := by
    funext s
    rw [hχ _ (ht s), absE_inf h τ (ht s), Finset.mul_sum, Complex.exp_sum,
      ← Real.finset_prod_rpow _ _ fun _ _ => by positivity, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [ht', Complex.norm_exp, ← Real.exp_nat_mul, ← Real.exp_mul, Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_sub,
      ← Complex.exp_int_mul, ← Complex.exp_add]
    congr 1
    simp only [Complex.re_ofReal_mul]
    push_cast; ring
  exact ⟨t, _, fun s => ⟨ht s, ht' s⟩, e ▸ ((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const _).cexp⟩

end PositivityTheory.ThKG.CayleyTransformDarboux

end
