import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureDivMem

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
open Filter Topology

namespace GlobalTheory.SUTrunc

section Mat

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] {e : R}

theorem idempotentTruncation_preserves_form (he : e * e = e) {A B J : Matrix n n R} (h : A * J * B = J) :
    (1 + e • (A - 1)) * J * (1 + e • (B - 1)) = J := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, smul_add, smul_sub, smul_smul, he, h]
  abel

theorem trunc_mul (he : e * e = e) {A B : Matrix n n R} (h : A * B = 1) :
    (1 + e • (A - 1)) * (1 + e • (B - 1)) = 1 := by
  have := idempotentTruncation_preserves_form he (A := A) (B := B) (J := 1) (by rw [Matrix.mul_one, h])
  rwa [Matrix.mul_one] at this

theorem cT_trunc (c : R →+* R) (hc : c e = e) (A : Matrix n n R) :
    Formalism.UG.cT c (1 + e • (A - 1)) = 1 + e • (Formalism.UG.cT c A - 1) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Formalism.UG.cT, hc]
  · simp [Formalism.UG.cT, hc, Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]

theorem det_trunc (he : e * e = e) {A : Matrix n n R} (h : A.det = 1) : (1 + e • (A - 1)).det = 1 := by
  have key : ∀ (a : R) (B : Matrix n n R), B.det = 1 → (∀ i j, a ∣ (1 + e • (A - 1)) i j - B i j) →
      a ∣ (1 + e • (A - 1)).det - 1 := by
    intro a B hB hd
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, RingHom.map_det, ← hB, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
    exact hd i j
  obtain ⟨x, hx⟩ := key e 1 Matrix.det_one fun i j => ⟨(A - 1) i j, by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring⟩
  obtain ⟨y, hy⟩ := key (1 - e) A h fun i j => ⟨-((A - 1) i j), by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply]; ring⟩
  linear_combination (1 - e) * hx + e * hy + (-x - y) * he

end Mat

variable {F : Type} [Field F] [NumberField F]

theorem idem_mul_self {S₁ : Finset (InfinitePlace F)} {S₂ : Finset (HeightOneSpectrum (𝓞 F))} {η : AF F}
    (h : IsPlacesIdem S₁ S₂ η) : η * η = η := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine Prod.ext (funext fun w => ?_) (RestrictedProduct.ext _ _ fun v => ?_)
  · change fstA F η w * fstA F η w = fstA F η w
    by_cases hw : w ∈ S₁
    · rw [h1 w hw, mul_one]
    · rw [h2 w hw, mul_zero]
  · change evalV F v (sndA F η) * evalV F v (sndA F η) = evalV F v (sndA F η)
    by_cases hw : v ∈ S₂
    · rw [h3 v hw, mul_one]
    · rw [h4 v hw, mul_zero]

theorem tendsto_idem (η : Finset (HeightOneSpectrum (𝓞 F)) → AF F)
    (hη : ∀ T, IsPlacesIdem Finset.univ T (η T)) : Tendsto η atTop (𝓝 1) := by
  classical
  let y : Finset (HeightOneSpectrum (𝓞 F)) → ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F :=
    fun T v => if v ∈ T then 1 else 0
  have hy : Tendsto y atTop (𝓝 1) := by
    rw [tendsto_pi_nhds]
    intro v
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop {v}] with T hT
    exact (if_pos (hT (Finset.mem_singleton_self v))).symm
  let s : (∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F) → Af F :=
    RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite
  have hs : Continuous s := RestrictedProduct.isEmbedding_structureMap.continuous
  have hp : Continuous fun z => pairA F 1 (s z) := continuous_const.prodMk hs
  have h1 : pairA F 1 (s 1) = 1 := rfl
  have h2 : η = fun T => pairA F 1 (s (y T)) := by
    funext T
    obtain ⟨h1, -, h3, h4⟩ := hη T
    refine Prod.ext (funext fun w => h1 w (Finset.mem_univ w)) (RestrictedProduct.ext _ _ fun v => ?_)
    change evalV F v (sndA F (η T)) = ((y T v : v.adicCompletionIntegers F) : v.adicCompletion F)
    by_cases hv : v ∈ T
    · rw [h3 v hv]; simp [y, hv]
    · rw [h4 v hv]; simp [y, hv]
  rw [h2, ← h1]
  exact (hp.tendsto 1).comp hy

theorem mem_closure_supp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ g ∈ SUAdelic σ J, g ∈ closure {x : HA (AF F) σ J | ∃ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (η : AF F), IsPlacesIdem T₁ T₂ η ∧ x ∈ SUSupp σ J η} := by
  intro F E _ _ _ _ _ σ _ M J _ g hg
  choose η hη using fun T : Finset (HeightOneSpectrum (𝓞 F)) => StrongApprox.exists_isPlacesIdem Finset.univ T
  have hlim := tendsto_idem η hη
  set ι := algebraMap (AF F) (AF F ⊗[F] E) with hι
  have he : ∀ T, ι (η T) * ι (η T) = ι (η T) := fun T => by rw [← map_mul, idem_mul_self (hη T)]
  let u : Finset (HeightOneSpectrum (𝓞 F)) → GL (Fin M) (AF F ⊗[F] E) := fun T =>
    ⟨1 + ι (η T) • (SUSuppSub.mv σ J g - 1), 1 + ι (η T) • (SUSuppSub.mv σ J g⁻¹ - 1),
      trunc_mul (he T) (SUSuppSub.mv_mul_inv σ J g), trunc_mul (he T) (SUSuppSub.mv_inv_mul σ J g)⟩
  have hu : ∀ T, u T ∈ HR (AF F) σ J := by
    intro T
    change Formalism.UG.cT (sigR (AF F) σ) (1 + ι (η T) • (SUSuppSub.mv σ J g - 1)) * JR (AF F) J *
      (1 + ι (η T) • (SUSuppSub.mv σ J g - 1)) = JR (AF F) J
    rw [cT_trunc _ (StrongApprox.sigR_algebraMap σ _)]
    exact idempotentTruncation_preserves_form (he T) (g : HR (AF F) σ J).2
  let x : Finset (HeightOneSpectrum (𝓞 F)) → HA (AF F) σ J := fun T => (⟨u T, hu T⟩ : HR (AF F) σ J)
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (AF F ⊗[F] E) := IsModuleTopology.toContinuousAdd (AF F) _
  have hmat : ∀ A : Matrix (Fin M) (Fin M) (AF F ⊗[F] E),
      Tendsto (fun T => 1 + ι (η T) • (A - 1)) atTop (𝓝 A) := by
    intro A
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    have h := (hlim.smul_const ((A - 1) i j)).const_add ((1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j)
    rw [one_smul, Matrix.sub_apply, add_sub_cancel] at h
    refine h.congr fun T => ?_
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Algebra.smul_def]
  have hx : Tendsto x atTop (𝓝 g) := by
    refine (tendsto_subtype_rng (p := fun a => a ∈ HR (AF F) σ J)).2 ?_
    rw [Units.isInducing_embedProduct.tendsto_nhds_iff]
    exact (hmat (SUSuppSub.mv σ J g)).prodMk_nhds
      ((MulOpposite.continuous_op.tendsto _).comp (hmat (SUSuppSub.mv σ J g⁻¹)))
  refine mem_closure_of_tendsto hx (Eventually.of_forall fun T => ⟨Finset.univ, T, η T, hη T, ?_⟩)
  rw [SUSuppSub.mem_SUSupp_iff]
  refine ⟨StrongApprox.mem_SUAdelic.2 (det_trunc (he T) (StrongApprox.mem_SUAdelic.1 hg)), ?_⟩
  change ι (η T) • (1 + ι (η T) • (SUSuppSub.mv σ J g - 1) - 1) = 1 + ι (η T) • (SUSuppSub.mv σ J g - 1) - 1
  rw [add_sub_cancel_left, smul_smul, he]

end GlobalTheory.SUTrunc

end
