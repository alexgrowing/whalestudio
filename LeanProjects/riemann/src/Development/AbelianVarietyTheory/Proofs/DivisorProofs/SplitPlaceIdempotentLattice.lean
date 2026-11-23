import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiCols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Formalism.LocalRingCardinality.SpanPowerMembership.Adelic
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.SplitPlaceIdem

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem conj_conj {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem exists_of_fixed {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {x : E} (hx : σ x = x) :
    ∃ a : F, algebraMap F E a = x := by
  have hs := Subalgebra.isSimpleOrder_of_finrank h.2.2.1
  rcases hs.eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with hb | ht
  · have : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := hx
    rw [hb] at this
    exact Algebra.mem_bot.1 this
  · exfalso
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    have := h.2.1
    apply IsTotallyComplex.complexEmbedding_not_isReal τ
    rw [ComplexEmbedding.isReal_iff]
    ext y
    have h1 : σ y = y := show y ∈ AlgHom.equalizer σ (AlgHom.id F E) from ht ▸ Algebra.mem_top
    have h2 := h.2.2.2 τ y
    rw [h1] at h2
    simpa [ComplexEmbedding.conjugate_coe_eq] using h2.symm

theorem exists_int_of_fixed {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {x : 𝓞 E} (hx : σ x = x) :
    ∃ a : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) a = x := by
  obtain ⟨a, ha⟩ := exists_of_fixed h hx
  have hi : IsIntegral ℤ a := by
    have : IsIntegral ℤ (x : E) := x.isIntegral_coe
    rw [← ha] at this
    exact (isIntegral_algebraMap_iff (algebraMap F E).injective).1 this
  exact ⟨⟨a, hi⟩, Subtype.ext ha⟩

theorem exists_trace_norm {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : Pl F} (hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v) :
    ∃ (ξ : 𝓞 E) (t n : 𝓞 F), (ξ : E) + σ ξ = algebraMap F E t ∧ (ξ : E) * σ ξ = algebraMap F E n ∧
      t ∉ v.asIdeal ∧ n ∈ v.asIdeal := by
  obtain ⟨P, Q, hPQ, hP, hQ⟩ := hv
  have hne : ¬ P.asIdeal ≤ Q.asIdeal := fun hle =>
    hPQ (HeightOneSpectrum.ext (P.isMaximal.eq_of_le Q.isPrime.ne_top hle))
  obtain ⟨ξ, hξP, hξQ⟩ := SetLike.not_le_iff_exists.1 hne
  have hi : IsIntegral ℤ (σ (ξ : E)) := (ξ.isIntegral_coe).map (σ.toRingHom.toIntAlgHom)
  set η : 𝓞 E := ⟨σ (ξ : E), hi⟩ with hη
  obtain ⟨t, ht⟩ := exists_int_of_fixed h (x := ξ + η) (by
    show σ ((ξ : E) + σ (ξ : E)) = (ξ : E) + σ (ξ : E)
    rw [map_add, conj_conj h, add_comm])
  obtain ⟨n, hn⟩ := exists_int_of_fixed h (x := ξ * η) (by
    show σ ((ξ : E) * σ (ξ : E)) = (ξ : E) * σ (ξ : E)
    rw [map_mul, conj_conj h, mul_comm])
  have hnv : n ∈ v.asIdeal := by
    rw [← hP, Ideal.mem_comap, hn]
    exact P.asIdeal.mul_mem_right _ hξP
  have hηQ : η ∈ Q.asIdeal := by
    have : ξ * η ∈ Q.asIdeal := by
      rw [← hn, ← Ideal.mem_comap, hQ]; exact hnv
    exact (Q.isPrime.mem_or_mem this).resolve_left hξQ
  refine ⟨ξ, t, n, ?_, ?_, fun htv => hξQ ?_, hnv⟩
  · exact (congrArg (fun z : 𝓞 E => (z : E)) ht).symm
  · exact (congrArg (fun z : 𝓞 E => (z : E)) hn).symm
  · rw [← hQ, Ideal.mem_comap, ht] at htv
    simpa using Q.asIdeal.sub_mem htv hηQ

theorem exists_root (v : Pl F) {t n : 𝓞 F} (ht : t ∉ v.asIdeal) (hn : n ∈ v.asIdeal) :
    ∃ α c : Fv F v, α ∈ v.adicCompletionIntegers F ∧ c ∈ v.adicCompletionIntegers F ∧
      α * α - algebraMap F (Fv F v) t * α + algebraMap F (Fv F v) n = 0 ∧
      c * (algebraMap F (Fv F v) t - 2 * α) = 1 := by
  set T : v.adicCompletionIntegers F := algebraMap (𝓞 F) _ t with hT
  set N : v.adicCompletionIntegers F := algebraMap (𝓞 F) _ n with hN
  have hTc : (T : Fv F v) = algebraMap F (Fv F v) t := rfl
  have hNc : (N : Fv F v) = algebraMap F (Fv F v) n := rfl
  have hNm : N ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    rw [Formalism.BasicNotions.Examples₂.adicInt_mem_max_iff, hNc, Formalism.BasicNotions.Examples₂.adicCompl_val_algebraMap]
    exact (v.valuation_lt_one_iff_mem n).2 hn
  have hTm : T ∉ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
    rw [Formalism.BasicNotions.Examples₂.adicInt_mem_max_iff, hTc, Formalism.BasicNotions.Examples₂.adicCompl_val_algebraMap]
    exact fun h => ht ((v.valuation_lt_one_iff_mem t).1 h)
  have hTu : IsUnit T := by
    by_contra h; exact hTm h
  have hmon : (Polynomial.X ^ 2 - Polynomial.C T * Polynomial.X + Polynomial.C N).Monic := by
    monicity!
  obtain ⟨a, ha, ham⟩ := HenselianLocalRing.is_henselian _ hmon 0 (by simpa using hNm) (by simpa using hTu)
  rw [sub_zero] at ham
  have hu : IsUnit (T - 2 * a) := by
    by_contra h
    apply hTm
    have h' : T - 2 * a ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := h
    simpa using add_mem h' (Ideal.mul_mem_left _ 2 ham)
  obtain ⟨c, hc⟩ := hu.exists_left_inv
  refine ⟨a, c, a.2, c.2, ?_, ?_⟩
  · have h1 : a * a - T * a + N = 0 := by
      have := ha.eq_zero
      simpa [pow_two] using this
    rw [← hTc, ← hNc]
    exact_mod_cast congrArg (fun z : v.adicCompletionIntegers F => (z : Fv F v)) h1
  · rw [← hTc]
    exact congrArg (fun z : v.adicCompletionIntegers F => (z : Fv F v)) hc

theorem eq_of_at {v : Pl F} {a b : AF F} (ha : At (evFin F v) a) (hb : At (evFin F v) b)
    (h : evFin F v a = evFin F v b) : a = b := by
  have h1 : evFin F v (1 - GlobalTheory.LatVac.liftV v 1) = 0 := by
    rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self]
  have h2 := ha _ h1
  have h3 := hb _ h1
  have h4 := GlobalTheory.LatVac.at_liftV v 1 (a - b) (by rw [map_sub, h, sub_self])
  simp only [smul_eq_mul] at h2 h3 h4
  linear_combination h2 - h3 + h4

theorem at_mul {v : Pl F} {a : AF F} (ha : At (evFin F v) a) (b : AF F) : At (evFin F v) (a * b) := by
  intro u hu
  have := ha u hu
  simp only [smul_eq_mul] at this ⊢
  rw [← mul_assoc, this, zero_mul]

theorem tmul_smul_mem {d : ℕ} (W : Spc F E d) (v : Pl F) {b : AF F} (hb : evFin F v b ∈ v.adicCompletionIntegers F)
    (x : 𝓞 E) {z : Fin d → AE F E} (hz : z ∈ GlobalTheory.InertSph.latAt W v) :
    (b ⊗ₜ[F] (x : E) : AE F E) • z ∈ GlobalTheory.InertSph.latAt W v := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, hv, y, hy, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a * b, at_mul ha b, ?_, x • y, W.L.smul_mem x hy, ?_⟩
    · rw [map_mul]; exact mul_mem hv hb
    · funext i
      show (b ⊗ₜ[F] (x : E) : AE F E) * (a • ((1 : AF F) ⊗ₜ[F] (y i))) = (a * b) • ((1 : AF F) ⊗ₜ[F] ((x : E) * y i))
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', Algebra.TensorProduct.tmul_mul_tmul]
      simp [mul_comm]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem exists_split_idem : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v →
    ∃ (e : AF F) (θ : AE F E), At (evFin F v) e ∧ evFin F v e = 1 ∧ e * e = e ∧ θ * θ = θ ∧ θ * cA σ θ = 0 ∧
      θ + cA σ θ = algebraMap (AF F) (AE F E) e ∧
      ∀ {d : ℕ} (W : Spc F E d), ∀ z ∈ GlobalTheory.InertSph.latAt W v, θ • z ∈ GlobalTheory.InertSph.latAt W v ∧ cA σ θ • z ∈ GlobalTheory.InertSph.latAt W v := by
  intro F E _ _ _ _ _ σ B hB v hv
  obtain ⟨ξ, t, n, ht, hn, htv, hnv⟩ := exists_trace_norm hB.cm hv
  obtain ⟨α, c, hα, hc, hroot, hinv⟩ := exists_root v htv hnv
  obtain ⟨e, he, hev⟩ : ∃ e : AF F, At (evFin F v) e ∧ evFin F v e = 1 :=
    ⟨_, GlobalTheory.LatVac.at_liftV v 1, GlobalTheory.LatVac.evFin_liftV v 1⟩
  obtain ⟨C, hC, hCv⟩ : ∃ C : AF F, At (evFin F v) C ∧ evFin F v C = c :=
    ⟨_, GlobalTheory.LatVac.at_liftV v c, GlobalTheory.LatVac.evFin_liftV v c⟩
  obtain ⟨A, hAv⟩ : ∃ A : AF F, evFin F v A = α := ⟨_, GlobalTheory.LatVac.evFin_liftV v α⟩
  have hee : e * e = e := eq_of_at (at_mul he e) he (by rw [map_mul, hev, one_mul])
  have hCe : C * e = C := eq_of_at (at_mul hC e) hC (by rw [map_mul, hev, mul_one])
  have h1 : C * (algebraMap F (AF F) t - 2 * A) = e := eq_of_at (at_mul hC _) he (by
    rw [map_mul, map_sub, map_mul, AlgHom.commutes, map_ofNat, hCv, hAv, hev, hinv])
  have h2 : C * (A * A - algebraMap F (AF F) t * A + algebraMap F (AF F) n) = 0 := by
    rw [mul_comm]
    refine hC _ ?_
    rw [map_add, map_sub, map_mul, map_mul, AlgHom.commutes, AlgHom.commutes, hAv, hroot]
  set φ := algebraMap (AF F) (AE F E) with hφ
  set x : AE F E := (1 : AF F) ⊗ₜ[F] (ξ : E) with hx
  set y : AE F E := (1 : AF F) ⊗ₜ[F] (σ (ξ : E)) with hy
  have hFE : ∀ s : F, ((1 : AF F) ⊗ₜ[F] (algebraMap F E s) : AE F E) = φ (algebraMap F (AF F) s) := by
    intro s
    rw [hφ, ← IsScalarTower.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply']
  have hxy1 : x + y = φ (algebraMap F (AF F) t) := by
    rw [hx, hy, ← TensorProduct.tmul_add, ht, hFE]
  have hxy2 : x * y = φ (algebraMap F (AF F) n) := by
    rw [hx, hy, Algebra.TensorProduct.tmul_mul_tmul, hn, one_mul, hFE]
  have hcx : cA σ x = y := by simp [hx, hy, cA]
  have hcθ : cA σ (φ C * (x - φ A)) = φ C * (y - φ A) := by
    rw [map_mul, map_sub, hcx, hφ, AlgHom.commutes, AlgHom.commutes]
  have g1 := congrArg φ h1
  have g2 := congrArg φ h2
  have g3 := congrArg φ hCe
  simp only [map_mul, map_sub, map_add, map_ofNat, map_zero, ← hxy1, ← hxy2] at g1 g2 g3
  have s1 : φ C * (x - φ A) + φ C * (y - φ A) = φ e := by linear_combination g1
  have s2 : φ C * (x - φ A) * (φ C * (y - φ A)) = 0 := by linear_combination φ C * g2
  have hθ : ∀ {d : ℕ} (W : Spc F E d), ∀ z ∈ GlobalTheory.InertSph.latAt W v,
      (φ C * (x - φ A)) • z ∈ GlobalTheory.InertSph.latAt W v := by
    intro d W z hz
    have e1 : φ C * (x - φ A) = (C ⊗ₜ[F] (ξ : E) : AE F E) - (C * A) ⊗ₜ[F] ((1 : 𝓞 E) : E) := by
      simp [hφ, hx, mul_sub, Algebra.TensorProduct.tmul_mul_tmul]
    rw [e1, sub_smul]
    refine sub_mem (tmul_smul_mem W v (hCv ▸ hc) ξ hz) (tmul_smul_mem W v ?_ 1 hz)
    rw [map_mul, hCv, hAv]; exact mul_mem hc hα
  refine ⟨e, φ C * (x - φ A), he, hev, hee, ?_, ?_, ?_, fun W z hz => ⟨hθ W z hz, ?_⟩⟩
  · linear_combination (φ C * (x - φ A)) * s1 - s2 + (x - φ A) * g3
  · rw [hcθ, s2]
  · rw [hcθ, s1]
  · have e2 : cA σ (φ C * (x - φ A)) = (e ⊗ₜ[F] ((1 : 𝓞 E) : E) : AE F E) - φ C * (x - φ A) := by
      rw [hcθ, eq_sub_iff_add_eq', s1]
      simp [hφ]
    rw [e2, sub_smul]
    exact sub_mem (tmul_smul_mem W v (hev ▸ one_mem _) 1 hz) (hθ W z hz)

end GlobalTheory.SplitPlaceIdem
