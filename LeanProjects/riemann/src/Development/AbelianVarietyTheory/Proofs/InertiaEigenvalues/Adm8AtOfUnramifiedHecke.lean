import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Eps0UnramFrob
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.AdmFrobTriple

theorem not_mem_placesOver_of_ne (E : Type) [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : p ≠ q) {v : HeightOneSpectrum (𝓞 E)} (h1 : v ∈ placesOver E p) : v ∉ placesOver E q := by
  intro h2
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 h)
  obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom (𝓞 E))
  have h1' : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal := h1
  have h2' : ((q : ℕ) : 𝓞 E) ∈ v.asIdeal := h2
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  simp only [eq_intCast, Int.cast_natCast]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1') (Ideal.mul_mem_left _ _ h2')

theorem continuous_algebraMap_padicInt {O : Type} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    {l : ℕ} [Fact l.Prime] [Algebra ℤ_[l] O] (I : Ideal O) (hI : IsAdic I) (hO : (l : O) ∈ I) :
    Continuous (algebraMap ℤ_[l] O) := by
  refine continuous_of_continuousAt_zero (algebraMap ℤ_[l] O) ?_
  rw [ContinuousAt, map_zero, hI.hasBasis_nhds_zero.tendsto_right_iff]
  intro n _
  have hl : (0 : ℝ) < (l : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℤ_[l]) hl] with x hx
  rw [mem_closedBall_zero_iff, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hO n)

theorem sum_coeff_charpolyRev {R : Type} [CommRing R] [Nontrivial R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    ∑ k ∈ Finset.range (n + 1), M.charpolyRev.coeff k = (1 - M).det := by
  have hdeg : M.charpolyRev.natDegree < n + 1 := by
    rw [← Matrix.reverse_charpoly]
    have := Polynomial.reverse_natDegree_le M.charpoly
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at this
    omega
  have h1 := Polynomial.eval_eq_sum_range' hdeg (1 : R)
  simp only [one_pow, mul_one] at h1
  rw [← h1, Matrix.charpolyRev, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, RingHom.mapMatrix_apply]
  split_ifs <;> simp

variable {D : D7}

theorem l_mem (i : D.ntw.Tw) : ((D.ntw.l i : ℕ) : D.ntw.O0 i) ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i) := by
  intro h
  have h2 := h.map (algebraMap (D.ntw.O0 i) (D.ntw.O i))
  rw [map_natCast] at h2
  exact D.ntw.O_l i h2

theorem continuous_twistCyclotomicCharacter (i : D.ntw.Tw) :
    Continuous fun g : Gen.GE D.nd => ((eps0 D.ntw i g : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) :=
  (continuous_algebraMap_padicInt _ (D.ntw.twistBaseCoefficientRing_isAdic i) (l_mem i)).comp
    (Units.continuous_val.comp (continuous_cycZ D.host.E D.nd.Om (D.ntw.l i)))

theorem pD_not (i : D.ntw.Tw) (v) (hv : v ∈ D.ntw.pD i) :
    v ∉ placesOver D.host.E (D.ntw.l i) ∧ ∀ k, v ∉ placesOver D.host.E (D.host.g k) := by
  have h2 : v ∈ (D.ntw.pD i : Set _) := hv
  rw [D.ntw.pD_eq] at h2
  have hl := (D.ntw.lPrime i).out
  split_ifs at h2 with h
  · refine ⟨not_mem_placesOver_of_ne _ D.host.pde'_prime hl ?_ h2, fun k =>
      not_mem_placesOver_of_ne _ D.host.pde'_prime (D.host.g_prime k) (D.host.pde_ne_g k).2 h2⟩
    rw [h]; exact D.host.pde_ne.symm
  · exact ⟨not_mem_placesOver_of_ne _ D.host.pde_prime hl (Ne.symm h) h2, fun k =>
      not_mem_placesOver_of_ne _ D.host.pde_prime (D.host.g_prime k) (D.host.pde_ne_g k).1 h2⟩

end GlobalTheory.AdmFrobTriple

namespace GlobalTheory.AdmFrobTriple

theorem eta_smul {D : D7} (i : D.ntw.Tw) (s : D.ntw.Sig i) (σ : Gen.GE D.nd) :
    ((((eps0 D.ntw i) ^ D.R.t * (chiS i s)⁻¹) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) •
      ((D.ntw.rhoS i s σ : GL (Fin D.R.r) (D.ntw.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)) =
    (((eps0 D.ntw i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) ^ D.R.t) • Tmat i s σ := by
  simp only [Tmat, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, Units.val_mul,
    Units.val_pow_eq_pow_val, mul_smul]

theorem adm8At_of_hkFrob : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i), UnrRho i s → HkFrob i s →
    characterTwistExists D.ntw D.nexp i s := by
  intro D i s hU hH _
  refine ⟨(eps0 D.ntw i) ^ D.R.t * (chiS i s)⁻¹, ?_, ?_, ?_, ?_⟩
  · have hc : Continuous fun g : Gen.GE D.nd => (((chiS i s g)⁻¹ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) := by
      simp_rw [← map_inv]
      exact (D.ntw.twistCharacterFamily_continuous i _ _).comp continuous_inv
    have he : (fun g : Gen.GE D.nd => ((((eps0 D.ntw i) ^ D.R.t * (chiS i s)⁻¹) g : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) =
        fun g => ((eps0 D.ntw i g : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) ^ D.R.t *
          (((chiS i s g)⁻¹ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) := by
      funext g
      simp only [MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, Units.val_mul,
        Units.val_pow_eq_pow_val]
    rw [he]
    exact ((continuous_twistCyclotomicCharacter i).pow _).mul hc
  · intro P hP _ A hA σ hσ
    have hPl : P ∉ placesOver D.host.E (D.ntw.l i) := fun h => hP (D.ntw.twistExcludedPlaces_contains_residueChar i h)
    have hPg : ∀ k, P ∉ placesOver D.host.E (D.host.g k) := fun k h => hP (D.ntw.placesOver_subset_exceptional i k h)
    have hPd : P ∉ D.ntw.pD i := fun h => hP (D.ntw.primes_subset_exceptional i h)
    have h1 : D.ntw.rhoS i s σ = 1 := hU P hPl hPg A hA σ hσ
    have h2 : chiS i s σ = 1 := D.ntw.twistCharacterFamily_unramified i _ _ P hPl hPg hPd A hA σ hσ
    have h3 : eps0 D.ntw i σ = 1 := (GlobalTheory.TripleGal.eps0_unram_frob D i P hPl A hA).1 σ hσ
    simp [MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, h1, h2, h3]
  · intro v hv A hA
    obtain ⟨hl, hg⟩ := pD_not i v hv
    have h1 : ∀ σ ∈ Ine (F := D.host.E) A, D.ntw.rhoS i s σ = 1 := fun σ hσ => hU v hl hg A hA σ hσ
    have h3 : ∀ σ ∈ Ine (F := D.host.E) A, eps0 D.ntw i σ = 1 := (GlobalTheory.TripleGal.eps0_unram_frob D i v hl A hA).1
    have h2 := D.ntw.twistCharacterFamily_at_auxiliaryPlaces i (D.ntw.jS i s) (D.ntw.side i s) v hv A hA
    cases hb : D.ntw.side i s
    · left
      intro σ hσ
      have h2' : chiS i s σ = (D.ntw.delta i σ)⁻¹ := by
        have := h2 σ hσ; rw [hb] at this; simpa [chiS, hb] using this
      simp [MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, h1 σ hσ, h2', h3 σ hσ]
    · right
      intro σ hσ
      have h2' : chiS i s σ = D.ntw.delta i σ := by
        have := h2 σ hσ; rw [hb] at this; simpa [chiS, hb] using this
      simp [MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, h1 σ hσ, h2', h3 σ hσ]
  · intro P hP hs σ hσ
    rw [eta_smul, ← sum_coeff_charpolyRev, map_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    exact hH P hP hs σ hσ k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))

end GlobalTheory.AdmFrobTriple
