import Mathlib
import Formalism.LocalRingCardinality.DataSpaces
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIdealCoprimeConjMulEqSpanSingletonStatement

open NumberField IsDedekindDomain Formalism.BasicNotions

namespace GlobalTheory.HypPrimVec

section
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem hconj (x y : S.V) : star (S.hT x y) = S.hT y x :=
  LinearMap.isSymm_def.mp S.herm x y

theorem mem_dual_iff (Λ : Submodule (𝓞 E) S.V) (x : S.V) :
    x ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ ↔ ∀ y ∈ Λ, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = S.hT y x := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one]

theorem mem_of_dual {Λ : Submodule (𝓞 E) S.V} (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) {x : S.V}
    (h : ∀ y ∈ Λ, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = S.hT y x) : x ∈ Λ := by
  have hx : x ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := (mem_dual_iff Λ x).2 h
  rwa [hU] at hx

theorem pair_mem {Λ : Submodule (𝓞 E) S.V} (hU : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) {x y : S.V}
    (hx : x ∈ Λ) (hy : y ∈ Λ) : ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = S.hT y x := by
  have hx' : x ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ := by rw [hU]; exact hx
  exact (mem_dual_iff Λ x).1 hx' y hy

end

theorem exists_primitive_norm_neg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], CMData F E → ∀ (S : HSpace E) (Λ : Submodule (𝓞 E) S.V), Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ → (∃ x : 𝓞 E, (x : E) + star (x : E) = 1) → ∀ (e f : S.V) (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), c ≠ 0 → S.hT e e = 0 → S.hT f f = 0 → S.hT e f = 1 → (∀ x ∈ c, x • e ∈ Λ) → (∀ y ∈ Λ, S.hT f y ∈ c) → ∀ T : ℕ, T ≠ 0 → ∃ z : S.V, z ∈ Submodule.span E {e, f} ∧ z ∈ Λ ∧ S.hT z z = -((T : ℕ) : E) ∧ ∀ γ : E, γ • z ∈ Λ → ∃ o : 𝓞 E, (o : E) = γ := by
  intro F E _ _ _ _ _ _ hcm S Λ hU hx e f c hc hee hff hef hce hfc T hT
  obtain ⟨x, hx⟩ := hx

  have hσ : ∀ r : 𝓞 E, ((RingOfIntegers.mapRingHom (starRingEnd E) r : 𝓞 E) : E) = star (r : E) :=
    fun r => rfl
  have hTne : (T : 𝓞 E) ≠ 0 := by
    intro h
    apply hT
    have h' := congrArg (fun r : 𝓞 E => (r : E)) h
    simpa using h'

  obtain ⟨P, hP0, hPP, ⟨t, p0, hp0, htp⟩, α, hα⟩ := GlobalTheory.T.exists_ideal_coprime_conj_mul_eq_spanSingleton' F E hcm c hc (T : 𝓞 E) hTne
  have htpE : (t : E) * (T : E) + (p0 : E) = 1 := by
    have h' := congrArg (fun r : 𝓞 E => (r : E)) htp
    simpa using h'

  obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1
    (show (1 : 𝓞 E) ∈ P ⊔ P.comap (RingOfIntegers.mapRingHom (starRingEnd E)) by
      rw [hPP]; exact Submodule.mem_top)
  have hq' : RingOfIntegers.mapRingHom (starRingEnd E) q ∈ P := Ideal.mem_comap.1 hq
  have hpqE : (p : E) + (q : E) = 1 := by
    have h' := congrArg (fun r : 𝓞 E => (r : E)) hpq
    simpa using h'
  set w : 𝓞 E := p * x + RingOfIntegers.mapRingHom (starRingEnd E) q *
    RingOfIntegers.mapRingHom (starRingEnd E) x with hw
  have hwP : w ∈ P := P.add_mem (P.mul_mem_right _ hp) (P.mul_mem_right _ hq')
  have hwE : (w : E) + star (w : E) = 1 := by
    have e1 : (w : E) = (p : E) * x + star (q : E) * star (x : E) := by
      rw [hw]; push_cast; rfl
    have hs : star (p : E) + star (q : E) = 1 := by rw [← star_add, hpqE, star_one]
    rw [e1, star_add, star_mul', star_mul', star_star, star_star]
    linear_combination (x : E) * hpqE + star (x : E) * hs + hx

  have hPc : ∀ r ∈ P, ∀ s ∈ c, ∃ o : 𝓞 E, (o : E) * α = (r : E) * s := by
    intro r hr s hs
    have hm : (r : E) * s ∈ (P : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c :=
      FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal _).2 ⟨r, hr, rfl⟩) hs
    rw [hα, FractionalIdeal.mem_spanSingleton] at hm
    obtain ⟨o, ho⟩ := hm
    exact ⟨o, by rw [← ho, Algebra.smul_def]⟩
  have hαc : α ∈ c := by
    have h1 : α ∈ (P : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
      rw [hα]; exact FractionalIdeal.mem_spanSingleton_self _ _
    have hle : (P : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c ≤ c :=
      FractionalIdeal.mul_le.2 fun i hi j hj => by
        obtain ⟨r, -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hi
        rw [← Algebra.smul_def]
        exact (c : Submodule (𝓞 E) E).smul_mem r hj
    exact hle h1
  have hα0 : α ≠ 0 := by
    obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
    obtain ⟨s, hs, hs0⟩ : ∃ s ∈ c, s ≠ 0 := by
      by_contra h
      push_neg at h
      apply hc
      ext y
      simp only [FractionalIdeal.mem_zero_iff]
      exact ⟨h y, fun hy => hy ▸ (c : Submodule (𝓞 E) E).zero_mem⟩
    obtain ⟨o, ho⟩ := hPc r hr s hs
    intro h0
    rw [h0, mul_zero] at ho
    have hr0' : (r : E) ≠ 0 := by exact_mod_cast hr0
    exact mul_ne_zero hr0' hs0 ho.symm
  have hfe : S.hT f e = 1 := by rw [← hconj e f, hef, star_one]

  set b : E := star (-(T : E) * (w : E) / α) with hb
  have h1 : star α * b = -(T : E) * star (w : E) := by
    rw [hb, ← star_mul', show α * (-(T : E) * (w : E) / α) = -(T : E) * w by field_simp,
      star_mul', star_neg, star_natCast]
  have h2 : star b * α = -(T : E) * (w : E) := by
    rw [hb, star_star]; field_simp
  refine ⟨α • e + b • f, ?_, ?_, ?_, ?_⟩
  · exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · refine Λ.add_mem (hce α hαc) (mem_of_dual hU fun y hy => ?_)
    obtain ⟨o, ho⟩ := hPc w hwP (S.hT f y) (hfc y hy)
    refine ⟨-(T : 𝓞 E) * RingOfIntegers.mapRingHom (starRingEnd E) o, ?_⟩
    have key : -(T : E) * w / α * S.hT f y = -(T : E) * o := by
      calc -(T : E) * w / α * S.hT f y = -(T : E) * ((w : E) * S.hT f y) / α := by ring
        _ = -(T : E) * ((o : E) * α) / α := by rw [ho]
        _ = -(T : E) * o := by field_simp
    rw [LinearMap.map_smul, ← hconj f y, smul_eq_mul, hb, ← star_mul', key, star_mul', star_neg,
      star_natCast]
    show ((-(T : 𝓞 E) * RingOfIntegers.mapRingHom (starRingEnd E) o : 𝓞 E) : E) = _
    push_cast
    rfl
  · simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply,
      LinearMap.map_smul, smul_eq_mul, hee, hff, hef, hfe, mul_zero, mul_one, zero_add, add_zero,
      starRingEnd_apply]
    linear_combination h1 + h2 - (T : E) * hwE
  · intro γ hγ
    have hfz : S.hT f (γ • (α • e + b • f)) = γ * α := by
      simp only [map_add, LinearMap.map_smul, smul_eq_mul, hff, hfe, RingHom.id_apply]; ring
    have hγα : γ * α ∈ c := hfz ▸ hfc _ hγ
    obtain ⟨o1, ho1⟩ := hPc p0 hp0 _ hγα
    obtain ⟨o2, ho2⟩ := hPc w hwP _ hγα
    obtain ⟨o3, ho3⟩ := pair_mem hU hγ (hce α hαc)
    have E1 : (o1 : E) = p0 * γ := mul_right_cancel₀ hα0 (by rw [ho1]; ring)
    have E2 : (o2 : E) = w * γ := mul_right_cancel₀ hα0 (by rw [ho2]; ring)
    have E3 : (o3 : E) = -(T : E) * γ * star (w : E) := by
      have hez : S.hT (α • e) (γ • (α • e + b • f)) = γ * (star α * b) := by
        simp only [map_add, LinearMap.map_smulₛₗ, LinearMap.smul_apply, LinearMap.map_smul,
          smul_eq_mul, hee, hef, starRingEnd_apply, RingHom.id_apply]; ring
      rw [hez, h1] at ho3
      change (o3 : E) = _ at ho3
      rw [ho3]; ring
    refine ⟨o2 + (-t * o3 + RingOfIntegers.mapRingHom (starRingEnd E) w * o1), ?_⟩
    have hcast : ((o2 + (-t * o3 + RingOfIntegers.mapRingHom (starRingEnd E) w * o1) : 𝓞 E) : E) =
        (o2 : E) + (-(t : E) * o3 + star (w : E) * o1) := by
      push_cast; rfl
    rw [hcast]
    linear_combination E2 - (t : E) * E3 + star (w : E) * E1 + γ * star (w : E) * htpE + γ * hwE

end GlobalTheory.HypPrimVec
