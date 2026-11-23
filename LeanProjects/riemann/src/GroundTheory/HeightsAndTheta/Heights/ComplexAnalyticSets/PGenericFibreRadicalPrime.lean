import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericFibreRadicalPrime
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGenericFibreTor
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHypersurfacePresentation
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

theorem fibreMap_eval₂_aeval {σ ι : Type*} {d : ℕ} (t : σ → ℂ)
    (y : Fin d → MvPolynomial ι (MvPolynomial σ ℂ)) (θ : MvPolynomial ι (MvPolynomial σ ℂ))
    (H : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ))) :
    MvPolynomial.map (eval t) (Polynomial.eval₂ (aeval y).toRingHom θ H) =
      Polynomial.eval₂ (aeval fun j => MvPolynomial.map (eval t) (y j)).toRingHom
        (MvPolynomial.map (eval t) θ) (H.map (MvPolynomial.map (eval t))) := by
  rw [Polynomial.hom_eval₂, Polynomial.eval₂_map]
  congr 1
  apply MvPolynomial.ringHom_ext
  · intro s
    simp [MvPolynomial.algebraMap_eq]
  · intro j
    simp

theorem exists_pow_mul_sub_eval₂_mem {σ ι : Type*} {d : ℕ} (K : Ideal (MvPolynomial ι (MvPolynomial σ ℂ)))
    (y : Fin d → MvPolynomial ι (MvPolynomial σ ℂ)) (θ : MvPolynomial ι (MvPolynomial σ ℂ))
    (D : MvPolynomial (Fin d) (MvPolynomial σ ℂ)) (q : ι → Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)))
    (hq : ∀ i, aeval y D * X i - Polynomial.eval₂ (aeval y).toRingHom θ (q i) ∈ K)
    (p : MvPolynomial ι (MvPolynomial σ ℂ)) :
    ∃ (e : ℕ) (H : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ))),
      aeval y D ^ e * p - Polynomial.eval₂ (aeval y).toRingHom θ H ∈ K := by
  induction p using MvPolynomial.induction_on with
  | C s =>
    refine ⟨0, Polynomial.C (C s), ?_⟩
    simp [MvPolynomial.algebraMap_eq]
  | add p₁ p₂ h₁ h₂ =>
    obtain ⟨e₁, H₁, h₁⟩ := h₁
    obtain ⟨e₂, H₂, h₂⟩ := h₂
    refine ⟨e₁ + e₂, Polynomial.C (D ^ e₂) * H₁ + Polynomial.C (D ^ e₁) * H₂, ?_⟩
    have e : aeval y D ^ (e₁ + e₂) * (p₁ + p₂) -
        Polynomial.eval₂ (aeval y).toRingHom θ (Polynomial.C (D ^ e₂) * H₁ + Polynomial.C (D ^ e₁) * H₂) =
        aeval y D ^ e₂ * (aeval y D ^ e₁ * p₁ - Polynomial.eval₂ (aeval y).toRingHom θ H₁) +
          aeval y D ^ e₁ * (aeval y D ^ e₂ * p₂ - Polynomial.eval₂ (aeval y).toRingHom θ H₂) := by
      simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow, map_pow,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      ring
    rw [e]
    exact K.add_mem (K.mul_mem_left _ h₁) (K.mul_mem_left _ h₂)
  | mul_X p i h =>
    obtain ⟨e, H, h⟩ := h
    refine ⟨e + 1, H * q i, ?_⟩
    have e' : aeval y D ^ (e + 1) * (p * X i) - Polynomial.eval₂ (aeval y).toRingHom θ (H * q i) =
        (aeval y D ^ e * p - Polynomial.eval₂ (aeval y).toRingHom θ H) * (aeval y D * X i) +
          Polynomial.eval₂ (aeval y).toRingHom θ H *
            (aeval y D * X i - Polynomial.eval₂ (aeval y).toRingHom θ (q i)) := by
      rw [Polynomial.eval₂_mul]
      ring
    rw [e']
    exact K.add_mem (K.mul_mem_right _ h) (K.mul_mem_left _ (hq i))

theorem exists_of_mem_ker_fibreMap {σ ι : Type*} {d : ℕ} (K : Ideal (MvPolynomial ι (MvPolynomial σ ℂ)))
    (y : Fin d → MvPolynomial ι (MvPolynomial σ ℂ)) (θ : MvPolynomial ι (MvPolynomial σ ℂ))
    (D : MvPolynomial (Fin d) (MvPolynomial σ ℂ)) (q : ι → Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)))
    (hq : ∀ i, aeval y D * X i - Polynomial.eval₂ (aeval y).toRingHom θ (q i) ∈ K) (t : σ → ℂ)
    (w : MvPolynomial ι (MvPolynomial σ ℂ))
    (hw : w ∈ RingHom.ker (MvPolynomial.map (eval t) :
      MvPolynomial ι (MvPolynomial σ ℂ) →+* MvPolynomial ι ℂ)) :
    ∃ (e : ℕ) (W : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ))),
      W.map (MvPolynomial.map (eval t)) = 0 ∧
        aeval y D ^ e * w - Polynomial.eval₂ (aeval y).toRingHom θ W ∈ K := by
  set δ : MvPolynomial ι (MvPolynomial σ ℂ) := aeval y D
  set ev : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)) → MvPolynomial ι (MvPolynomial σ ℂ) :=
    Polynomial.eval₂ (aeval y).toRingHom θ
  let J : Ideal (MvPolynomial ι (MvPolynomial σ ℂ)) :=
    { carrier := {w | ∃ (e : ℕ) (W : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ))),
        W.map (MvPolynomial.map (eval t)) = 0 ∧ δ ^ e * w - ev W ∈ K}
      add_mem' := by
        rintro a b ⟨e₁, W₁, hW₁, h₁⟩ ⟨e₂, W₂, hW₂, h₂⟩
        refine ⟨e₁ + e₂, Polynomial.C (D ^ e₂) * W₁ + Polynomial.C (D ^ e₁) * W₂, ?_, ?_⟩
        · simp [Polynomial.map_add, Polynomial.map_mul, hW₁, hW₂]
        · have e : δ ^ (e₁ + e₂) * (a + b) - ev (Polynomial.C (D ^ e₂) * W₁ + Polynomial.C (D ^ e₁) * W₂) =
              δ ^ e₂ * (δ ^ e₁ * a - ev W₁) + δ ^ e₁ * (δ ^ e₂ * b - ev W₂) := by
            simp only [ev, δ, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow,
              map_pow, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
            ring
          rw [e]
          exact K.add_mem (K.mul_mem_left _ h₁) (K.mul_mem_left _ h₂)
      zero_mem' := ⟨0, 0, by simp, by simp [ev]⟩
      smul_mem' := by
        rintro r a ⟨e, W, hW, h⟩
        obtain ⟨e', H, hH⟩ := exists_pow_mul_sub_eval₂_mem K y θ D q hq r
        refine ⟨e' + e, H * W, by simp [Polynomial.map_mul, hW], ?_⟩
        have e'' : δ ^ (e' + e) * (r • a) - ev (H * W) =
            δ ^ e * a * (δ ^ e' * r - ev H) + ev H * (δ ^ e * a - ev W) := by
          simp only [ev, Polynomial.eval₂_mul, smul_eq_mul]
          ring
        rw [e'']
        exact K.add_mem (K.mul_mem_left _ hH) (K.mul_mem_left _ h) }
  have hle : RingHom.ker (MvPolynomial.map (eval t) :
      MvPolynomial ι (MvPolynomial σ ℂ) →+* MvPolynomial ι ℂ) ≤ J := by
    rw [ker_fibreMap, Ideal.map_le_iff_le_comap]
    intro c hc
    refine ⟨0, Polynomial.C (C c), ?_, ?_⟩
    · rw [RingHom.mem_ker] at hc
      simp [hc]
    · simp [ev, MvPolynomial.algebraMap_eq]
  exact hle hw

theorem dvd_of_eval₂_mem_fibre {σ ι : Type*} {d : ℕ} (K : Ideal (MvPolynomial ι (MvPolynomial σ ℂ)))
    (y : Fin d → MvPolynomial ι (MvPolynomial σ ℂ)) (θ : MvPolynomial ι (MvPolynomial σ ℂ))
    (m : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ))) (D : MvPolynomial (Fin d) (MvPolynomial σ ℂ))
    (q : ι → Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)))
    (hker : ∀ H : Polynomial (MvPolynomial (Fin d) (MvPolynomial σ ℂ)),
      Polynomial.eval₂ (aeval y).toRingHom θ H ∈ K ↔ m ∣ H)
    (hq : ∀ i, aeval y D * X i - Polynomial.eval₂ (aeval y).toRingHom θ (q i) ∈ K) (t : σ → ℂ)
    (h : Polynomial (MvPolynomial (Fin d) ℂ))
    (hh : Polynomial.eval₂ (aeval fun j => MvPolynomial.map (eval t) (y j)).toRingHom
        (MvPolynomial.map (eval t) θ) h ∈ K.map (MvPolynomial.map (eval t))) :
    ∃ e : ℕ, m.map (MvPolynomial.map (eval t)) ∣
      Polynomial.C (MvPolynomial.map (eval t) D) ^ e * h := by
  have hs : Function.Surjective (eval t : MvPolynomial σ ℂ →+* ℂ) := fun c => ⟨C c, eval_C c⟩
  obtain ⟨H, rfl⟩ := Polynomial.map_surjective _ (MvPolynomial.map_surjective _ hs) h
  rw [← fibreMap_eval₂_aeval] at hh
  obtain ⟨κ, hκ, hκH⟩ := (Ideal.mem_map_iff_of_surjective _ (MvPolynomial.map_surjective _ hs)).1 hh
  have hw : Polynomial.eval₂ (aeval y).toRingHom θ H - κ ∈ RingHom.ker (MvPolynomial.map (eval t) :
      MvPolynomial ι (MvPolynomial σ ℂ) →+* MvPolynomial ι ℂ) := by
    rw [RingHom.mem_ker, map_sub, hκH, sub_self]
  obtain ⟨e, W, hW, hWK⟩ := exists_of_mem_ker_fibreMap K y θ D q hq t _ hw
  refine ⟨e, ?_⟩
  have hmem : Polynomial.eval₂ (aeval y).toRingHom θ (Polynomial.C D ^ e * H - W) ∈ K := by
    have e' : Polynomial.eval₂ (aeval y).toRingHom θ (Polynomial.C D ^ e * H - W) =
        (aeval y D ^ e * (Polynomial.eval₂ (aeval y).toRingHom θ H - κ) -
          Polynomial.eval₂ (aeval y).toRingHom θ W) + aeval y D ^ e * κ := by
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      ring
    rw [e']
    exact K.add_mem hWK (K.mul_mem_left _ hκ)
  have hd := Polynomial.map_dvd (MvPolynomial.map (eval t)) ((hker _).1 hmem)
  simpa [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, hW] using hd

theorem Monic.dvd_of_dvd_C_pow_mul_pow {R : Type*} [CommRing R] [IsDomain R] {m u v h : Polynomial R} {c : R}
    (hm : m.Monic) (hc : c ≠ 0) (huv : u * m + v * Polynomial.derivative m = Polynomial.C c) {e N : ℕ}
    (hN : N ≠ 0) (hd : m ∣ Polynomial.C c ^ e * h ^ N) : m ∣ h := by
  have hf : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R (FractionRing R)
  have hfc : algebraMap R (FractionRing R) c ≠ 0 :=
    (map_ne_zero_iff _ hf).2 hc
  have hsep : (m.map (algebraMap R (FractionRing R))).Separable := by
    rw [Polynomial.separable_def']
    refine ⟨Polynomial.C (algebraMap R (FractionRing R) c)⁻¹ * u.map (algebraMap R (FractionRing R)),
      Polynomial.C (algebraMap R (FractionRing R) c)⁻¹ * v.map (algebraMap R (FractionRing R)), ?_⟩
    have h1 := congrArg (Polynomial.map (algebraMap R (FractionRing R))) huv
    rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C,
      ← Polynomial.derivative_map] at h1
    rw [mul_assoc, mul_assoc, ← mul_add, h1, ← Polynomial.C_mul, inv_mul_cancel₀ hfc, Polynomial.C_1]
  have hd' : m.map (algebraMap R (FractionRing R)) ∣
      Polynomial.C (algebraMap R (FractionRing R) c) ^ e * (h.map (algebraMap R (FractionRing R))) ^ N := by
    have := Polynomial.map_dvd (algebraMap R (FractionRing R)) hd
    rwa [Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_pow, Polynomial.map_C] at this
  have hu : IsUnit (Polynomial.C (algebraMap R (FractionRing R) c) ^ e) :=
    (Polynomial.isUnit_C.2 (Ne.isUnit hfc)).pow e
  have h2 : m.map (algebraMap R (FractionRing R)) ∣ h.map (algebraMap R (FractionRing R)) :=
    (hsep.squarefree.dvd_pow_iff_dvd hN).1 ((hu.dvd_mul_left).1 hd')
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd (hm.map _), ← Polynomial.map_modByMonic _ hm] at h2
  rw [← Polynomial.modByMonic_eq_zero_iff_dvd hm]
  exact Polynomial.map_injective _ hf (by rw [h2, Polynomial.map_zero])

theorem mem_map_of_mul_mem_map {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R')
    (hφ : Function.Surjective φ) (K : Ideal R) (hK : K.IsPrime) (b : R) (hb : b ∉ K)
    (h : (K ⊔ Ideal.span {b}) ⊓ RingHom.ker φ ≤ RingHom.ker φ * (K ⊔ Ideal.span {b}))
    (g : R') (hg : φ b * g ∈ K.map φ) : g ∈ K.map φ := by
  obtain ⟨a, rfl⟩ := hφ g
  rw [← map_mul] at hg
  obtain ⟨κ, hκ, hκa⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).1 hg
  have hμ : b * a - κ ∈ (K ⊔ Ideal.span {b}) ⊓ RingHom.ker φ :=
    ⟨Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self b)))
      (Ideal.mem_sup_left hκ), RingHom.mem_ker.2 (by rw [map_sub, hκa, sub_self])⟩
  have h2 := h hμ
  rw [Ideal.mul_sup] at h2
  obtain ⟨κ', hκ', w, hw, hsum⟩ := Submodule.mem_sup.1 h2
  obtain ⟨ν, hν, hνw⟩ := (Ideal.mem_mul_span_singleton (I := RingHom.ker φ)).1 hw
  have hκ'K : κ' ∈ K := (Ideal.mul_le_inf hκ').2
  have hb' : b * (a - ν) ∈ K := by
    have e : b * (a - ν) = κ + κ' := by linear_combination -hsum - hνw
    rw [e]
    exact K.add_mem hκ hκ'K
  have haν : a - ν ∈ K := (hK.mem_or_mem hb').resolve_left hb
  have : φ a = φ (a - ν) := by rw [map_sub, RingHom.mem_ker.1 hν, sub_zero]
  rw [this]
  exact Ideal.mem_map_of_mem φ haν

theorem GenericFibreRadicalPrime.proof (hT : GenericFibreTor.Statement)
    (hP : HypersurfacePresentation.Statement) : GenericFibreRadicalPrime.Statement := by
  intro σ _ ι _ K hK
  classical
  have hs : ∀ t : σ → ℂ, Function.Surjective (eval t : MvPolynomial σ ℂ →+* ℂ) := fun t c => ⟨C c, eval_C c⟩
  by_cases h0 : ∃ s : MvPolynomial σ ℂ, C s ∈ K ∧ s ≠ 0
  · obtain ⟨s, hsK, hs0⟩ := h0
    refine ⟨s, hs0, fun t ht => ?_⟩
    have hu : IsUnit (MvPolynomial.map (eval t) (C s : MvPolynomial ι (MvPolynomial σ ℂ))) := by
      rw [MvPolynomial.map_C]
      exact (Ne.isUnit ht).map C
    rw [Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hsK) hu]
    exact fun _ _ => Submodule.mem_top
  push Not at h0
  obtain ⟨d, y, θ, m, D, q, u, v, hm, hD, huv, hker, hq⟩ := hP σ ι K hK h0
  have hb : aeval y D ∉ K := by
    intro hb
    have hdvd : m ∣ Polynomial.C D := (hker _).1 (by simpa using hb)
    have hdeg : m.natDegree = 0 := by
      have := Polynomial.natDegree_le_of_dvd hdvd (by simpa using hD)
      rw [Polynomial.natDegree_C] at this
      omega
    have h1 : m = 1 := hm.natDegree_eq_zero.1 hdeg
    exact hK.ne_top ((Ideal.eq_top_iff_one K).2 (by simpa using (hker 1).2 (by rw [h1])))
  obtain ⟨F₁, hF₁, hF₁t⟩ := hT σ ι (K ⊔ Ideal.span {aeval y D})
  obtain ⟨μ, hμ⟩ := MvPolynomial.ne_zero_iff.1 hD
  refine ⟨F₁ * D.coeff μ, mul_ne_zero hF₁ hμ, fun t ht => ?_⟩
  rw [map_mul, mul_ne_zero_iff] at ht
  obtain ⟨ht₁, ht₂⟩ := ht
  set φ : MvPolynomial ι (MvPolynomial σ ℂ) →+* MvPolynomial ι ℂ := MvPolynomial.map (eval t)
  set ψ : MvPolynomial (Fin d) (MvPolynomial σ ℂ) →+* MvPolynomial (Fin d) ℂ := MvPolynomial.map (eval t)
  have hφ : Function.Surjective φ := MvPolynomial.map_surjective _ (hs t)
  have hψD : ψ D ≠ 0 := by
    intro h0'
    apply ht₂
    have := congrArg (MvPolynomial.coeff μ) h0'
    simpa [ψ, MvPolynomial.coeff_map] using this

  have hnzd : ∀ (k : ℕ) (g : MvPolynomial ι ℂ), φ (aeval y D) ^ k * g ∈ K.map φ → g ∈ K.map φ := by
    intro k
    induction k with
    | zero => intro g hg; simpa using hg
    | succ k ih =>
      intro g hg
      refine ih g (mem_map_of_mul_mem_map φ hφ K hK _ hb (hF₁t t ht₁) _ ?_)
      rw [pow_succ] at hg
      simpa [mul_assoc, mul_comm, mul_left_comm] using hg
  intro g ⟨N, hgN⟩
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [(Ideal.eq_top_iff_one (K.map φ)).2 (by simpa using hgN)]
    exact Submodule.mem_top
  obtain ⟨G, rfl⟩ := hφ g
  obtain ⟨e, H, hH⟩ := exists_pow_mul_sub_eval₂_mem K y θ D q hq G
  set evt := Polynomial.eval₂ (aeval (R := ℂ) fun j => φ (y j)).toRingHom (φ θ)
  have h1 : φ (aeval y D) ^ e * φ G - evt (H.map ψ) ∈ K.map φ := by
    have := Ideal.mem_map_of_mem φ hH
    rwa [map_sub, map_mul, map_pow, fibreMap_eval₂_aeval] at this
  have h2 : evt (H.map ψ ^ N) ∈ K.map φ := by
    have hdv := sub_dvd_pow_sub_pow (φ (aeval y D) ^ e * φ G) (evt (H.map ψ)) N
    have h3 : (φ (aeval y D) ^ e * φ G) ^ N - evt (H.map ψ) ^ N ∈ K.map φ :=
      Ideal.mem_of_dvd _ hdv h1
    have h4 : (φ (aeval y D) ^ e * φ G) ^ N ∈ K.map φ := by
      rw [mul_pow]
      exact Ideal.mul_mem_left _ _ hgN
    have h5 := Ideal.sub_mem _ h4 h3
    rw [sub_sub_cancel] at h5
    simpa [evt, Polynomial.eval₂_pow] using h5
  obtain ⟨e', he'⟩ := dvd_of_eval₂_mem_fibre K y θ m D q hker hq t _ h2
  have huv' : u.map ψ * m.map ψ + v.map ψ * Polynomial.derivative (m.map ψ) = Polynomial.C (ψ D) := by
    have := congrArg (Polynomial.map ψ) huv
    simpa [Polynomial.map_add, Polynomial.map_mul, Polynomial.derivative_map] using this
  have hmh : m.map ψ ∣ H.map ψ :=
    Monic.dvd_of_dvd_C_pow_mul_pow (hm.map ψ) hψD huv' hN.ne' he'
  obtain ⟨s, hs'⟩ := hmh
  have hmK : evt (m.map ψ) ∈ K.map φ := by
    have := Ideal.mem_map_of_mem φ ((hker m).2 dvd_rfl)
    rwa [fibreMap_eval₂_aeval] at this
  have h6 : evt (H.map ψ) ∈ K.map φ := by
    rw [hs']
    simp only [evt, Polynomial.eval₂_mul]
    exact Ideal.mul_mem_right _ _ hmK
  exact hnzd e _ (by simpa using Ideal.add_mem _ h1 h6)

end

end GroundTheory.Heights₂.Heights
