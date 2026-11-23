import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen.IsoOpen

section Form

variable {R : Type} [CommRing R] {M : ℕ} (c : R →+* R) (Jm : Matrix (Fin M) (Fin M) R)

theorem form_left (p q : R) (a b w : Fin M → R) :
    Formalism.UG.hform c Jm (p • a + q • b) w =
      c p * Formalism.UG.hform c Jm a w + c q * Formalism.UG.hform c Jm b w := by
  simp only [Formalism.UG.hform, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem form_right (p q : R) (a b w : Fin M → R) :
    Formalism.UG.hform c Jm w (p • a + q • b) =
      p * Formalism.UG.hform c Jm w a + q * Formalism.UG.hform c Jm w b := by
  simp only [Formalism.UG.hform, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

variable {c Jm}

theorem form_conj (hc : ∀ t, c (c t) = t) (hJ : ∀ i j, c (Jm j i) = Jm i j) (x y : Fin M → R) :
    c (Formalism.UG.hform c Jm x y) = Formalism.UG.hform c Jm y x := by
  simp only [Formalism.UG.hform, map_sum, map_mul, hc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hJ a b]
  ring

theorem exists_diag (hc : ∀ t, c (c t) = t) (hJ : ∀ i j, c (Jm j i) = Jm i j) (i2 : R) (h2 : i2 * 2 = 1)
    (hi2 : c i2 = i2) (u v : Fin M → R) (huu : Formalism.UG.hform c Jm u u = 0) (huv : Formalism.UG.hform c Jm u v = 1) :
    ∃ a b : Fin M → R, Formalism.UG.hform c Jm a a = 2 ∧ Formalism.UG.hform c Jm b b = -2 ∧
      Formalism.UG.hform c Jm a b = 0 ∧ Formalism.UG.hform c Jm b a = 0 := by
  have hvu : Formalism.UG.hform c Jm v u = 1 := by rw [← form_conj hc hJ u v, huv, map_one]
  set e := Formalism.UG.hform c Jm v v with he
  have hce : c e = e := form_conj hc hJ v v
  set r := i2 * e with hr
  have hcr : c r = r := by rw [hr, map_mul, hi2, hce]
  have h2r : r + r = e := by rw [hr]; linear_combination e * h2
  obtain ⟨w, hw⟩ : ∃ w, w = (1 : R) • v + (-r) • u := ⟨_, rfl⟩
  have huw : Formalism.UG.hform c Jm u w = 1 := by
    rw [hw, form_right, huu, huv]; ring
  have hwu : Formalism.UG.hform c Jm w u = 1 := by
    rw [← form_conj hc hJ u w, huw, map_one]
  have hvw : Formalism.UG.hform c Jm v w = e - r := by
    rw [hw, form_right, hvu, ← he]; ring
  have hww : Formalism.UG.hform c Jm w w = 0 := by
    nth_rw 1 [hw]
    rw [form_left, hvw, huw, map_one, map_neg, hcr]
    linear_combination -h2r
  refine ⟨(1 : R) • u + (1 : R) • w, (1 : R) • u + (-1 : R) • w, ?_, ?_, ?_, ?_⟩
  · rw [form_left, form_right, form_right, huu, huw, hwu, hww]; simp only [map_one, map_neg]; ring
  · rw [form_left, form_right, form_right, huu, huw, hwu, hww]; simp only [map_one, map_neg]; ring
  · rw [form_left, form_right, form_right, huu, huw, hwu, hww]; simp only [map_one, map_neg]; ring
  · rw [form_left, form_right, form_right, huu, huw, hwu, hww]; simp only [map_one, map_neg]; ring

theorem plane_of (hc : ∀ t, c (c t) = t) (hJ : ∀ i j, c (Jm j i) = Jm i j) (a b : Fin M → R) (T S : R)
    (hT : c T = T) (hS : c S = S) (hSA : S * Formalism.UG.hform c Jm a a = 1)
    (hTD : T * T * (Formalism.UG.hform c Jm a a * Formalism.UG.hform c Jm b b -
      Formalism.UG.hform c Jm a b * Formalism.UG.hform c Jm b a) = -(Formalism.UG.hform c Jm a a * Formalism.UG.hform c Jm a a)) :
    ∃ (x y : R) (z : Fin M → R), Formalism.UG.hform c Jm (x • a + y • b) (x • a + y • b) = 0 ∧
      Formalism.UG.hform c Jm (x • a + y • b) z = 1 := by
  have hB : c (Formalism.UG.hform c Jm a b) = Formalism.UG.hform c Jm b a := form_conj hc hJ a b
  set A := Formalism.UG.hform c Jm a a with hA
  set B := Formalism.UG.hform c Jm a b with hBd
  set B' := Formalism.UG.hform c Jm b a with hB'
  set C := Formalism.UG.hform c Jm b b with hC
  have hcx : c (1 - T * B * S) = 1 - T * B' * S := by
    rw [map_sub, map_one, map_mul, map_mul, hT, hS, hB]
  refine ⟨1 - T * B * S, T, S • a + (0 : R) • a, ?_, ?_⟩
  · rw [form_left, form_right, form_right, hcx, hT, ← hA, ← hBd, ← hB', ← hC]
    linear_combination S * hTD + (-T * B - T * B' + T * T * B * B' * S - A - T * T * C) * hSA
  · rw [form_left, form_right, form_right, hcx, hT, ← hA, ← hB']
    linear_combination (1 - T * B' * S) * hSA

end Form

theorem sq_near_one {K : Type} [NontriviallyNormedField K] [CompleteSpace K] (h2 : (2 : K) ≠ 0) :
    ∀ᶠ y in 𝓝 (1 : K), ∃ t : K, t * t = y := by
  have hd : HasStrictDerivAt (fun t : K => t * t) (1 * 1 + 1 * 1) (1 : K) :=
    (hasStrictDerivAt_id (1 : K)).mul (hasStrictDerivAt_id (1 : K))
  have hm := hd.map_nhds_eq (by norm_num; exact h2)
  rw [mul_one] at hm
  rw [← hm, Filter.eventually_map]
  exact Filter.Eventually.of_forall fun t => ⟨t, rfl⟩

section Tens

variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)

theorem sigR_twice (hσ : ∀ x, σ (σ x) = x) (K : Type) [CommRing K] [Algebra F K] (t : K ⊗[F] E) :
    sigR K σ (sigR K σ t) = t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR, hσ]
  | add y z hy hz => rw [map_add, map_add, hy, hz]

theorem sigR_iota (K : Type) [CommRing K] [Algebra F K] (t : K) :
    sigR K σ (algebraMap K (K ⊗[F] E) t) = algebraMap K (K ⊗[F] E) t := by
  simp [sigR, Algebra.TensorProduct.algebraMap_apply]

theorem sigR_JR {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : ∀ i j, σ (J j i) = J i j)
    (K : Type) [CommRing K] [Algebra F K] (i j : Fin M) :
    sigR K σ (JR K J j i) = JR K J i j := by
  simp [sigR, JR, inclR, hJ]

theorem exists_lam (K : Type) [Field K] [Algebra F K] :
    ∃ lam : K ⊗[F] E →ₗ[K] K, ∀ t, lam (algebraMap K (K ⊗[F] E) t) = t := by
  obtain ⟨φ, hφ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F E)
    (LinearMap.ker_eq_bot.2 (algebraMap F E).injective)
  have hφ1 : φ 1 = 1 := by simpa using LinearMap.congr_fun hφ 1
  refine ⟨(TensorProduct.AlgebraTensorModule.rid F K K).toLinearMap ∘ₗ φ.baseChange K, fun t => ?_⟩
  simp [Algebra.TensorProduct.algebraMap_apply, hφ1]

theorem fixed_eq (htr : ∀ e : E, ∃ f : F, e + σ e = algebraMap F E f) (K : Type) [Field K] [Algebra F K]
    (h2 : (2 : K) ≠ 0) {x : K ⊗[F] E} (hx : sigR K σ x = x) : ∃ t : K, x = algebraMap K (K ⊗[F] E) t := by
  have hsum : ∀ y : K ⊗[F] E, ∃ t : K, y + sigR K σ y = algebraMap K (K ⊗[F] E) t := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul k e =>
      obtain ⟨f, hf⟩ := htr e
      refine ⟨f • k, ?_⟩
      have h1 : sigR K σ (k ⊗ₜ[F] e) = k ⊗ₜ[F] σ e := by simp [sigR]
      rw [h1, ← TensorProduct.tmul_add, hf, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      simp
    | add y z hy hz =>
      obtain ⟨s, hs⟩ := hy
      obtain ⟨t, ht⟩ := hz
      refine ⟨s + t, ?_⟩
      rw [map_add, map_add, ← hs, ← ht]
      ring
  obtain ⟨t, ht⟩ := hsum x
  rw [hx] at ht
  refine ⟨2⁻¹ * t, ?_⟩
  have h3 : algebraMap K (K ⊗[F] E) 2⁻¹ * 2 = 1 := by
    rw [← map_ofNat (algebraMap K (K ⊗[F] E)) 2, ← map_mul, inv_mul_cancel₀ h2, map_one]
  rw [map_mul, ← ht]
  linear_combination (-x) * h3

end Tens

section CM

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sig_twice (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sig_ne (h : IsCMExt F E σ) : ∃ y : E, σ y ≠ y := by
  by_contra hc
  push_neg at hc
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  have hcx := h.2.1.isComplex (InfinitePlace.mk τ)
  rw [InfinitePlace.isComplex_mk_iff] at hcx
  refine hcx (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_))
  rw [ComplexEmbedding.conjugate_coe_eq]
  change star (τ x) = τ x
  rw [← h.2.2.2, hc]

theorem trace_mem (h : IsCMExt F E σ) (e : E) : ∃ f : F, e + σ e = algebraMap F E f := by
  classical
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let φ : E →ₗ[F] E := σ.toLinearMap - LinearMap.id
  have hφ : ∀ x, φ x = σ x - x := fun x => rfl
  have hker : (Submodule.span F {(1 : E)}) = LinearMap.ker φ := by
    apply Submodule.eq_of_le_of_finrank_le
    · intro x hx
      obtain ⟨f, rfl⟩ := Submodule.mem_span_singleton.1 hx
      rw [LinearMap.mem_ker, hφ, ← Algebra.algebraMap_eq_smul_one, AlgHom.commutes, sub_self]
    · have h1 := φ.finrank_range_add_finrank_ker
      rw [h.2.2.1] at h1
      have hr : 0 < Module.finrank F (LinearMap.range φ) := by
        obtain ⟨y, hy⟩ := sig_ne h
        refine Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨φ y, LinearMap.mem_range_self _ _⟩, fun h0 => hy ?_⟩
        have h3 : φ y = 0 := congrArg Subtype.val h0
        rw [hφ] at h3
        exact sub_eq_zero.1 h3
      rw [finrank_span_singleton (one_ne_zero)]
      omega
  have hm : e + σ e ∈ LinearMap.ker φ := by
    rw [LinearMap.mem_ker, hφ, map_add, sig_twice h]
    ring
  rw [← hker] at hm
  obtain ⟨f, hf⟩ := Submodule.mem_span_singleton.1 hm
  exact ⟨f, by rw [← hf, Algebra.algebraMap_eq_smul_one]⟩

end CM

theorem eventually_sq {X K : Type} [TopologicalSpace X] [NontriviallyNormedField K] [CompleteSpace K]
    (h2 : (2 : K) ≠ 0) (s g n : X → K) (x₀ : X) (cs : Continuous s) (cg : Continuous g) (cn : Continuous n)
    (s0 : s x₀ = 2) (g0 : g x₀ = -2) (n0 : n x₀ = 0) :
    ∀ᶠ p in 𝓝 x₀, s p ≠ 0 ∧ s p * g p - n p ≠ 0 ∧ ∃ t : K, t * t * (s p * g p - n p) = -(s p * s p) := by
  have hD0 : s x₀ * g x₀ - n x₀ ≠ 0 := by
    rw [s0, g0, n0]
    intro h
    exact mul_ne_zero h2 h2 (by linear_combination -h)
  have cD : Continuous fun p => s p * g p - n p := (cs.mul cg).sub cn
  have hq : ContinuousAt (fun p => -(s p * s p) / (s p * g p - n p)) x₀ :=
    ((cs.mul cs).neg.continuousAt).div cD.continuousAt hD0
  have q0 : -(s x₀ * s x₀) / (s x₀ * g x₀ - n x₀) = 1 := by
    rw [div_eq_one_iff_eq hD0, s0, g0, n0]
    ring
  have e1 : ∀ᶠ p in 𝓝 x₀, ∃ t : K, t * t = -(s p * s p) / (s p * g p - n p) := by
    have ht : Filter.Tendsto (fun p => -(s p * s p) / (s p * g p - n p)) (𝓝 x₀) (𝓝 1) := by
      have := hq.tendsto
      rwa [q0] at this
    exact ht.eventually (sq_near_one h2)
  have e2 : ∀ᶠ p in 𝓝 x₀, s p ≠ 0 := cs.continuousAt.eventually_ne (by rw [s0]; exact h2)
  have e3 : ∀ᶠ p in 𝓝 x₀, s p * g p - n p ≠ 0 := cD.continuousAt.eventually_ne hD0
  filter_upwards [e1, e2, e3] with p h1 h2' h3'
  obtain ⟨t, ht⟩ := h1
  exact ⟨h2', h3', t, by rw [ht, div_mul_cancel₀ _ h3']⟩

theorem isoPlane_eventually : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ {K : Type} [NontriviallyNormedField K] [ProperSpace K] [Algebra F K], IsoAt K σ J →
    ∃ a₀ b₀ : Fin M → K ⊗[F] E, ∀ᶠ p in nhds (a₀, b₀), IsoPlane K σ J p.1 p.2 := by
  intro F E _ _ _ _ _ σ hcm M J hJ K _ _ _ hiso
  obtain ⟨u, v, huu, huv⟩ := hiso
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  have h2K : (2 : K) ≠ 0 := two_ne_zero
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology K (K ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (K ⊗[F] E) := IsModuleTopology.isTopologicalRing K (K ⊗[F] E)
  have hs : Continuous (sigR K σ) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.map (AlgHom.id K K) σ).toLinearMap
  have hc : ∀ t, sigR K σ (sigR K σ t) = t := sigR_twice σ (sig_twice hcm) K
  have hJ' : ∀ i j, sigR K σ (JR K J j i) = JR K J i j := sigR_JR σ hJ.1 K
  obtain ⟨lam, hlam⟩ := exists_lam (F := F) (E := E) K
  have hlamC : Continuous lam := IsModuleTopology.continuous_of_linearMap lam
  have hfix : ∀ x, sigR K σ x = x → x = algebraMap K (K ⊗[F] E) (lam x) := by
    intro x hx
    obtain ⟨t, rfl⟩ := fixed_eq σ (trace_mem hcm) K h2K hx
    rw [hlam]
  have h3 : algebraMap K (K ⊗[F] E) 2⁻¹ * 2 = 1 := by
    rw [← map_ofNat (algebraMap K (K ⊗[F] E)) 2, ← map_mul, inv_mul_cancel₀ h2K, map_one]
  obtain ⟨a₀, b₀, haa, hbb, hab, -⟩ :=
    exists_diag hc hJ' (algebraMap K (K ⊗[F] E) 2⁻¹) h3 (sigR_iota σ K _) u v huu huv
  have haa' : hR K σ J a₀ a₀ = 2 := haa
  have hbb' : hR K σ J b₀ b₀ = -2 := hbb
  have hab' : hR K σ J a₀ b₀ = 0 := hab
  have hconj : ∀ x y, sigR K σ (hR K σ J x y) = hR K σ J y x := fun x y => form_conj hc hJ' x y
  refine ⟨a₀, b₀, ?_⟩
  have hh : ∀ {f g : (Fin M → K ⊗[F] E) × (Fin M → K ⊗[F] E) → Fin M → K ⊗[F] E},
      Continuous f → Continuous g → Continuous fun p => hR K σ J (f p) (g p) := by
    intro f g hf hg
    unfold hR Formalism.UG.hform
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    exact ((hs.comp ((continuous_apply i).comp hf)).mul continuous_const).mul ((continuous_apply j).comp hg)
  have hev := eventually_sq h2K
    (fun p : (Fin M → K ⊗[F] E) × (Fin M → K ⊗[F] E) => lam (hR K σ J p.1 p.1))
    (fun p => lam (hR K σ J p.2 p.2)) (fun p => lam (hR K σ J p.1 p.2 * hR K σ J p.2 p.1)) (a₀, b₀)
    (hlamC.comp (hh continuous_fst continuous_fst)) (hlamC.comp (hh continuous_snd continuous_snd))
    (hlamC.comp ((hh continuous_fst continuous_snd).mul (hh continuous_snd continuous_fst)))
    (by
      change lam (hR K σ J a₀ a₀) = 2
      rw [haa', ← map_ofNat (algebraMap K (K ⊗[F] E)) 2, hlam])
    (by
      change lam (hR K σ J b₀ b₀) = -2
      rw [hbb', ← map_ofNat (algebraMap K (K ⊗[F] E)) 2, ← map_neg, hlam])
    (by
      change lam (hR K σ J a₀ b₀ * hR K σ J b₀ a₀) = 0
      rw [hab', zero_mul, map_zero])
  filter_upwards [hev] with p hp
  obtain ⟨hs0, hD0, t, ht⟩ := hp
  obtain ⟨a, b⟩ := p
  simp only at hs0 hD0 ht ⊢
  have hA := hfix _ (hconj a a)
  have hC := hfix _ (hconj b b)
  have hBB := hfix (hR K σ J a b * hR K σ J b a) (by rw [map_mul, hconj, hconj, mul_comm])
  set s := lam (hR K σ J a a)
  set g := lam (hR K σ J b b)
  set n := lam (hR K σ J a b * hR K σ J b a)
  have hDι : hR K σ J a a * hR K σ J b b - hR K σ J a b * hR K σ J b a =
      algebraMap K (K ⊗[F] E) (s * g - n) := by
    rw [map_sub, map_mul, ← hA, ← hC, ← hBB]
  refine ⟨?_, ?_⟩
  · rw [hDι]
    intro h0
    have h1 := hlam (s * g - n)
    rw [h0, map_zero] at h1
    exact hD0 h1.symm
  · refine plane_of hc hJ' a b (algebraMap K (K ⊗[F] E) t) (algebraMap K (K ⊗[F] E) s⁻¹) (sigR_iota σ K _)
      (sigR_iota σ K _) ?_ ?_
    · change algebraMap K (K ⊗[F] E) s⁻¹ * hR K σ J a a = 1
      rw [hA, ← map_mul, inv_mul_cancel₀ hs0, map_one]
    · change algebraMap K (K ⊗[F] E) t * algebraMap K (K ⊗[F] E) t *
        (hR K σ J a a * hR K σ J b b - hR K σ J a b * hR K σ J b a) = -(hR K σ J a a * hR K σ J a a)
      rw [hDι, hA]
      have h4 := congrArg (algebraMap K (K ⊗[F] E)) ht
      simpa only [map_mul, map_neg] using h4

end GlobalTheory.CompanionTheory.SaGen.IsoOpen

end
