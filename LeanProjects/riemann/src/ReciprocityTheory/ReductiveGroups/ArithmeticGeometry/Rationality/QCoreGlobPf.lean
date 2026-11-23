import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QCoreH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.GlobQuotPf

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open NumberField IsDedekindDomain
open scoped TensorProduct

section Mean

variable {K K₁ : Type*} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]

theorem sum_embeddings_restrict (g : (K →+* ℂ) → ℝ) :
    ∑ φ : K₁ →+* ℂ, g (φ.comp (algebraMap K K₁)) =
      (Module.finrank K K₁ : ℝ) * ∑ τ : K →+* ℂ, g τ := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun φ : K₁ →+* ℂ => φ.comp (algebraMap K K₁)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_congr rfl (fun φ hφ => by rw [(Finset.mem_filter.mp hφ).2]), Finset.sum_const,
    nsmul_eq_mul]
  congr 1
  norm_cast
  letI : Algebra K ℂ := τ.toAlgebra
  let eqv : {φ : K₁ →+* ℂ // φ.comp (algebraMap K K₁) = τ} ≃ (K₁ →ₐ[K] ℂ) :=
    { toFun := fun φ => { φ.1 with commutes' := fun r => RingHom.congr_fun φ.2 r }
      invFun := fun ψ => ⟨ψ.toRingHom, RingHom.ext fun r => ψ.commutes r⟩
      left_inv := fun φ => rfl
      right_inv := fun ψ => rfl }
  rw [← Fintype.card_subtype, Fintype.card_congr eqv, AlgHom.card]

theorem sum_places_restrict (g : (K →+* ℂ) → ℝ) (hg : ∀ τ, g ((starRingEnd ℂ).comp τ) = g τ) :
    ∑ σ : InfinitePlace K₁, (σ.mult : ℝ) * g (σ.embedding.comp (algebraMap K K₁)) =
      (Module.finrank K K₁ : ℝ) * ∑ τ : K →+* ℂ, g τ := by
  rw [← sum_embeddings_restrict g]
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun φ : K₁ →+* ℂ => InfinitePlace.mk φ)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hc : ∀ φ ∈ Finset.univ.filter (fun φ : K₁ →+* ℂ => InfinitePlace.mk φ = σ),
      g (φ.comp (algebraMap K K₁)) = g (σ.embedding.comp (algebraMap K K₁)) := by
    intro φ hφ
    have h1 := (Finset.mem_filter.mp hφ).2
    rw [← InfinitePlace.mk_embedding σ, InfinitePlace.mk_eq_iff] at h1
    rcases h1 with h1 | h1
    · rw [h1]
    · rw [← h1]
      have h2 : (ComplexEmbedding.conjugate φ).comp (algebraMap K K₁)
          = (starRingEnd ℂ).comp (φ.comp (algebraMap K K₁)) := RingHom.ext fun x => rfl
      rw [h2, hg]
  rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul, InfinitePlace.card_filter_mk_eq]

end Mean

section Regroup

variable {K K₁ : Type*} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]

noncomputable def under (w : HeightOneSpectrum (𝓞 K₁)) : HeightOneSpectrum (𝓞 K) where
  asIdeal := w.asIdeal.comap (algebraMap (𝓞 K) (𝓞 K₁))
  isPrime := Ideal.IsPrime.comap _
  ne_bot := by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
    exact Ideal.comap_ne_bot_of_integral_mem hx0 hx (Algebra.IsIntegral.isIntegral x)

theorem liesOver_iff_under (w : HeightOneSpectrum (𝓞 K₁)) (la : HeightOneSpectrum (𝓞 K)) :
    LiesOver w la ↔ under (K := K) w = la := by
  unfold LiesOver
  constructor
  · intro h
    exact HeightOneSpectrum.ext h
  · intro h
    subst h
    rfl

theorem logN_of_liesOver {w : HeightOneSpectrum (𝓞 K₁)} {la : HeightOneSpectrum (𝓞 K)}
    (h : LiesOver w la) : logN w = (w.asIdeal.inertiaDeg (𝓞 K) : ℝ) * logN la := by
  have : w.asIdeal.LiesOver la.asIdeal := ⟨by rw [Ideal.under_def]; exact h.symm⟩
  have hn := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver w.asIdeal la.asIdeal la.isPrime la.ne_bot
  rw [Ideal.inertiaDeg'_eq_inertiaDeg] at hn
  simp only [logN, hn, Nat.cast_pow, Real.log_pow]

theorem finsum_regroup (F : HeightOneSpectrum (𝓞 K₁) → ℝ) (hF : (Function.support F).Finite) :
    (Function.support fun la : HeightOneSpectrum (𝓞 K) =>
        ∑ᶠ w : {w // LiesOver w la}, (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w.1).Finite ∧
    ∑ᶠ la : HeightOneSpectrum (𝓞 K),
        (∑ᶠ w : {w // LiesOver w la}, (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w.1) * logN la =
      ∑ᶠ w, F w * logN w := by
  classical
  set S := hF.toFinset
  set T : Finset (HeightOneSpectrum (𝓞 K)) := S.image under
  have hinner : ∀ la : HeightOneSpectrum (𝓞 K),
      ∑ᶠ w : {w // LiesOver w la}, (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w.1 =
        ∑ w ∈ S.filter (fun w => under (K := K) w = la),
          (w.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w := by
    intro la
    rw [finsum_eq_sum_of_support_subset _ (s := S.subtype (fun w => LiesOver w la)) ?_,
      Finset.sum_subtype_eq_sum_filter
        (fun w : HeightOneSpectrum (𝓞 K₁) => (w.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w)]
    · refine Finset.sum_congr ?_ fun _ _ => rfl
      ext w; simp [liesOver_iff_under]
    · intro w hw
      rw [Finset.mem_coe, Finset.mem_subtype, Set.Finite.mem_toFinset, Function.mem_support]
      intro h0
      exact hw (by simp [h0])
  have hsupp : (Function.support fun la : HeightOneSpectrum (𝓞 K) =>
      ∑ᶠ w : {w // LiesOver w la}, (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w.1) ⊆ T := by
    intro la hla
    rw [Function.mem_support, hinner] at hla
    obtain ⟨w, hw, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hla
    rw [Finset.mem_filter] at hw
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨w, hw.1, hw.2⟩)
  refine ⟨T.finite_toSet.subset hsupp, ?_⟩
  rw [finsum_eq_sum_of_support_subset _ (s := T) (fun la hla => hsupp (by
      intro h; apply hla; simp [h])),
    finsum_eq_sum_of_support_subset _ (s := S) (fun w hw => by
      simp only [Finset.mem_coe, Set.Finite.mem_toFinset, S]
      intro h; apply hw; simp [h])]
  simp_rw [hinner, Finset.sum_mul]
  rw [← Finset.sum_fiberwise_of_maps_to (s := S) (t := T) (g := under)
    (fun w hw => Finset.mem_image_of_mem _ hw)]
  refine Finset.sum_congr rfl fun la _ => Finset.sum_congr rfl fun w hw => ?_
  rw [Finset.mem_filter] at hw
  rw [logN_of_liesOver ((liesOver_iff_under w la).mpr hw.2)]
  ring

end Regroup

theorem qcoreGlobal_holds : QCoreGlobalStatement := by
  intro K K₁ V _ _ _ _ _ _ _ _ M ρ θ c hD s hs supN a Bθ Carch Bdeg hconj hmean harch hdeg
  classical
  set D := detCT c θ with hDdef
  let F : HeightOneSpectrum (𝓞 K₁) → ℝ := fun w => (ordAt w D : ℝ) + ∑ i, s i w
  have hordfin : (Function.support fun w : HeightOneSpectrum (𝓞 K₁) => (ordAt w D : ℝ)).Finite := by
    refine (finite_ordAt hD).subset fun w hw => ?_
    have hpos : (0 : ℝ) < logN w := Real.log_pos (one_lt_absNorm_real w)
    simp only [Function.mem_support] at hw ⊢
    exact mul_ne_zero hw hpos.ne'
  have hFfin : (Function.support F).Finite := by
    refine (hordfin.union (Set.finite_iUnion fun i => hs i)).subset fun w hw => ?_
    by_contra hnot
    simp only [Set.mem_union, Set.mem_iUnion, Function.mem_support, not_or, not_exists,
      not_not] at hnot
    apply hw
    simp [F, hnot.1, hnot.2]
  obtain ⟨hfinsupp, hregroup⟩ := finsum_regroup (K := K) F hFfin
  have hnn : ∀ la, nnFun (K := K) D s la =
      (∑ᶠ w : {w // LiesOver w la}, (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w.1) /
        (Module.finrank K K₁ : ℝ) := fun la => rfl
  have hK₁K : (0 : ℝ) < Module.finrank K K₁ := by
    have : Module.Finite K K₁ := Module.Finite.of_restrictScalars_finite ℚ K K₁
    exact_mod_cast Module.finrank_pos
  have hKQ : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have htower : (Module.finrank ℚ K₁ : ℝ) = Module.finrank ℚ K * Module.finrank K K₁ := by
    exact_mod_cast (Module.finrank_mul_finrank ℚ K K₁).symm
  refine ⟨hfinsupp.subset fun la hla => by
    rw [Function.mem_support, hnn] at hla
    intro h; apply hla; simp [h], ?_⟩

  have hsum : (∑ᶠ la : HeightOneSpectrum (𝓞 K), nnFun (K := K) D s la * logN la) =
      (∑ᶠ w, F w * logN w) / (Module.finrank K K₁ : ℝ) := by
    have hfin2 : (Function.support fun la : HeightOneSpectrum (𝓞 K) =>
        (∑ᶠ w : {w // LiesOver w la}, (w.1.asIdeal.inertiaDeg (𝓞 K) : ℝ) * F w.1) * logN la).Finite :=
      hfinsupp.subset fun la hla => by
        rw [Function.mem_support] at hla ⊢
        intro h; apply hla; rw [h, zero_mul]
    rw [← hregroup, div_eq_mul_inv, finsum_mul]
    refine finsum_congr fun la => ?_
    rw [hnn]; ring

  let m : Matrix (Fin ρ) (Fin ρ) K₁ := Matrix.of fun i j => c i ((1 : K₁) ⊗ₜ[K] ((θ j : M) : V))
  have hmD : m.det = D := rfl
  let b : Fin ρ → InfinitePlace K₁ → ℝ := fun j σ =>
    Real.log (supN (σ.embedding.comp (algebraMap K K₁)) ((θ j : M) : V)) + Carch
  have hG := globalQuot_holds K₁ ρ m (by rw [hmD]; exact hD) s (fun _ => 0) a b (fun _ => Bdeg) 0 hs
    (by simp) (fun σ i j hij => harch σ i j hij) hdeg (by simp)
  have hLHS : (∑ᶠ w, ((ordAt w m.det : ℝ) + ∑ i, s i w + (ρ : ℝ) * (fun _ => (0 : ℝ)) w) * logN w) =
      ∑ᶠ w, F w * logN w := finsum_congr fun w => by simp [F, hmD]
  rw [hLHS] at hG
  have hKQc : (Fintype.card (K →+* ℂ) : ℝ) = Module.finrank ℚ K := by
    exact_mod_cast Embeddings.card K ℂ
  have hbj : ∀ j, (∑ σ : InfinitePlace K₁, (σ.mult : ℝ) * b j σ) / (Module.finrank ℚ K₁ : ℝ) ≤
      Bθ + Carch := by
    intro j
    have e0 : ∀ σ : InfinitePlace K₁, (σ.mult : ℝ) * b j σ =
        (σ.mult : ℝ) * Real.log (supN (σ.embedding.comp (algebraMap K K₁)) ((θ j : M) : V)) +
          Carch * (σ.mult : ℝ) := fun σ => by simp only [b]; ring
    have e2 := sum_places_restrict (K := K) (K₁ := K₁)
      (fun τ => Real.log (supN τ ((θ j : M) : V))) (fun τ => by rw [hconj])
    have e3 : (∑ σ : InfinitePlace K₁, (σ.mult : ℝ)) = Module.finrank ℚ K₁ := by
      exact_mod_cast InfinitePlace.sum_mult_eq
    rw [Finset.sum_congr rfl (fun σ _ => e0 σ), Finset.sum_add_distrib, ← Finset.mul_sum, e2, e3]
    have hm := hmean j
    rw [hKQc] at hm
    have hsplit : ((Module.finrank K K₁ : ℝ) * ∑ τ : K →+* ℂ, Real.log (supN τ ((θ j : M) : V)) +
        Carch * (Module.finrank ℚ K₁ : ℝ)) / (Module.finrank ℚ K₁ : ℝ) =
        (∑ τ : K →+* ℂ, Real.log (supN τ ((θ j : M) : V))) / (Module.finrank ℚ K : ℝ) + Carch := by
      rw [htower]; field_simp
    rw [hsplit]; linarith
  have hsumj : ∑ j : Fin ρ, (∑ σ : InfinitePlace K₁, (σ.mult : ℝ) * b j σ) /
      (Module.finrank ℚ K₁ : ℝ) ≤ (ρ : ℝ) * (Bθ + Carch) := by
    calc _ ≤ ∑ _j : Fin ρ, (Bθ + Carch) := Finset.sum_le_sum fun j _ => hbj j
      _ = (ρ : ℝ) * (Bθ + Carch) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hBdeg : ∑ _i : Fin ρ, Bdeg = (ρ : ℝ) * Bdeg := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hBdeg] at hG
  rw [hsum, div_div, mul_comm (Module.finrank K K₁ : ℝ), ← htower]
  nlinarith [hG, hsumj]

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
