import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpHorizontal
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.AevalChartSubstMemOfMemBlowUpOf
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

noncomputable section

section Saturation

variable {K : Type*} {ι : K → Type} {J : Type} {R : Type*} [CommRing R]

theorem exists_pow_mul_mem_of_aeval_chartSubst_mem {P : Ideal (MRing ι R)} {u a : J → MRing ι R}
    {W : Ideal (MRing ι R)} (j₀ : J)
    (hrel : ∀ j, newVar j * liftForm (a j₀) - newVar j₀ * liftForm (a j) ∈ blowUpOf P u)
    {F : MRing (extIdx ι J) R}
    (hF : aeval (chartSubst a) F ∈ Ideal.map (Polynomial.C : MRing ι R →+* Polynomial (MRing ι R)) W) :
    ∃ n : ℕ, liftForm (a j₀ ^ n) * F ∈
      blowUpOf P u ⊔ Ideal.map (liftForm (J := J) : MRing ι R →ₐ[R] MRing (extIdx ι J) R) W := by
  set B' := blowUpOf P u ⊔ Ideal.map (liftForm (J := J) : MRing ι R →ₐ[R] MRing (extIdx ι J) R) W
  let π := Ideal.Quotient.mk B'
  let x₀ := π (liftForm (a j₀))
  let L := Localization.Away x₀
  let q : MRing (extIdx ι J) R →+* L := (algebraMap _ L).comp π
  let t : L := IsLocalization.Away.invSelf x₀
  have hinv : q (liftForm (a j₀)) * t = 1 := IsLocalization.Away.mul_invSelf x₀
  let ψ : Polynomial (MRing ι R) →+* L :=
    Polynomial.eval₂RingHom (q.comp (liftForm (J := J) : MRing ι R →ₐ[R] _).toRingHom) (q (newVar j₀) * t)
  have key : ψ.comp (aeval (R := R) (chartSubst a)).toRingHom = q := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [ψ]
    · rintro ⟨_ | k, i⟩
      · change J at i
        have hm : π (newVar i * liftForm (a j₀) - newVar j₀ * liftForm (a i)) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (hrel i))
        have h1 : q (newVar i * liftForm (a j₀) - newVar j₀ * liftForm (a i)) = 0 := by
          show algebraMap _ L (π _) = 0
          rw [hm, map_zero]
        rw [map_sub, map_mul, map_mul, sub_eq_zero] at h1
        simp only [ψ, chartSubst, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
          aeval_X, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, Polynomial.eval₂_C,
          Polynomial.eval₂_X]
        change q (liftForm (a i)) * (q (newVar j₀) * t) = q (newVar i)
        linear_combination (-t) * h1 + q (newVar i) * hinv
      · simp [ψ, chartSubst, liftForm]
  have hle : Ideal.map (Polynomial.C : MRing ι R →+* Polynomial (MRing ι R)) W ≤ RingHom.ker ψ := by
    rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, RingHom.mem_ker]
    simp only [ψ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, q]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hp)), map_zero]
  have h2 := RingHom.mem_ker.mp (hle hF)
  have h3 := DFunLike.congr_fun key F
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at h3
  rw [h3] at h2
  obtain ⟨⟨m, n, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers x₀) L (π F)).mp h2
  refine ⟨n, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow, map_pow]
  exact hm

end Saturation

theorem BlowUpHorizontalSat.full : BlowUpHorizontalSat.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP W hW hϖW F
  classical
  have hPp : P.IsPrime := hP.multiProj.isPrime

  have hmin : W ∈ (blowUpOf P u ⊔ Ideal.span {liftForm x}).minimalPrimes := by
    unfold divCycle at hW
    split_ifs at hW with h
    · exact h.1
    · exact absurd rfl hW
  obtain ⟨hWp, hBW, hWrel⟩ := le_and_isRelevant_of_divCycle_ne_zero hW
  set W₀ := W.comap (liftForm (ι := ι) (J := J) (R := O)) with hW₀
  obtain ⟨hW₀p, hPW₀, hrel₀, -⟩ := comap_liftForm_facts hWp hBW hWrel
  have hϖW₀ : (C ϖ : MRing ι O) ∉ W₀ := by rw [Ideal.mem_comap, liftForm_C]; exact hϖW
  obtain ⟨j₀, hj₀⟩ := hloc W₀ hW₀p hPW₀ hrel₀ hϖW₀
  choose v w hv hvw using hj₀

  have huj₀ : u j₀ ∉ P := by
    intro h
    obtain ⟨j, hj⟩ := hex
    have h1 : v j * u j ∈ P := by
      have := P.add_mem (hvw j) (P.mul_mem_left (w j) h)
      rwa [sub_add_cancel] at this
    exact hj ((hPp.mem_or_mem h1).resolve_left fun h' => hv j (hPW₀ h'))

  obtain ⟨u₀, a, hu₀W, hrelP⟩ : ∃ (u₀ : MRing ι O) (a : J → MRing ι O), u₀ ∉ W₀ ∧
      ∀ j, u₀ * u j - u j₀ * a j ∈ P := by
    have := hW₀p
    refine ⟨∏ j, v j, fun j => w j * ∏ j' ∈ Finset.univ.erase j, v j',
      fun h => W₀.primeCompl.prod_mem (fun j _ => hv j) h, fun j => ?_⟩
    have e : (∏ j, v j) * u j - u j₀ * (w j * ∏ j' ∈ Finset.univ.erase j, v j') =
        (∏ j' ∈ Finset.univ.erase j, v j') * (v j * u j - w j * u j₀) := by
      rw [← Finset.mul_prod_erase Finset.univ v (Finset.mem_univ j)]; ring
    rw [e]
    exact P.mul_mem_left _ (hvw j)
  have hu₀P : u₀ ∉ P := fun h => hu₀W (hPW₀ h)
  have ha₀ : a j₀ ∉ W₀ := by
    intro h
    have h1 : u j₀ * (u₀ - a j₀) ∈ P := by
      have := hrelP j₀
      rwa [show u₀ * u j₀ - u j₀ * a j₀ = u j₀ * (u₀ - a j₀) by ring] at this
    have h2 : u₀ - a j₀ ∈ W₀ := hPW₀ ((hPp.mem_or_mem h1).resolve_left huj₀)
    exact hu₀W (by simpa using W₀.add_mem h2 h)

  have hrelB : ∀ j, newVar j * liftForm (a j₀) - newVar j₀ * liftForm (a j) ∈ blowUpOf P u := by
    intro j
    apply mem_blowUpOf_of_sub
    have e : u₀ * (u j * a j₀ - u j₀ * a j) =
        a j₀ * (u₀ * u j - u j₀ * a j) - a j * (u₀ * u j₀ - u j₀ * a j₀) := by ring
    have h1 : u₀ * (u j * a j₀ - u j₀ * a j) ∈ P := by
      rw [e]; exact P.sub_mem (P.mul_mem_left _ (hrelP j)) (P.mul_mem_left _ (hrelP j₀))
    exact (hPp.mem_or_mem h1).resolve_left hu₀P

  have := hW₀p
  let Q' := (Ideal.map (Polynomial.C : MRing ι O →+* Polynomial (MRing ι O)) W₀).comap
    (aeval (R := O) (chartSubst a))
  have hQ'p : Q'.IsPrime := Ideal.comap_isPrime _ _
  have hxW : liftForm x ∈ W := hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hBQ' : blowUpOf P u ⊔ Ideal.span {liftForm x} ≤ Q' := by
    refine sup_le (fun G hG => ?_) ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    · exact Ideal.map_mono hPW₀ (aeval_chartSubst_mem_of_mem_blowUpOf hPp huj₀ hrelP hG)
    · rw [Ideal.mem_comap, aeval_chartSubst_liftForm]
      exact Ideal.mem_map_of_mem _ hxW
  have hQ'W : Q' ≤ W := fun G hG =>
    mem_of_aeval_chartSubst_mem hWp le_rfl j₀ ha₀ (fun j => hBW (hrelB j)) hG
  have hWQ' : W ≤ Q' := hmin.2 ⟨hQ'p, hBQ'⟩ hQ'W
  constructor
  · intro hF
    obtain ⟨m, hm⟩ := exists_pow_mul_mem_of_aeval_chartSubst_mem j₀ hrelB (hWQ' hF)
    exact ⟨a j₀ ^ m, fun h => ha₀ (hW₀p.mem_of_pow_mem _ h), hm⟩
  · rintro ⟨s, hs, hsF⟩
    have h1 : liftForm s * F ∈ W := sup_le hBW Ideal.map_comap_le hsF
    exact (hWp.mem_or_mem h1).resolve_left hs

end

end GroundTheory.Heights₂.Heights.NumbersDVR
