import Formalism.LocalToGlobal.GroupLattices.PerfectRings.CharZeroWittQuadratic

noncomputable section

namespace Formalism.L2.G

open Formalism.MainNotions.G IsLocalRing IntermediateField NumberField IsDedekindDomain

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ} {LL : Type} [Field LL] [NumberField LL]

theorem dvd_of_mem {R : Type*} [CommRing R] (I : Ideal R) (hI : I ≠ ⊤) {q M : ℕ} (hq : q.Prime) (h1 : (q : R) ∈ I)
    (h2 : (M : R) ∈ I) : q ∣ M := by
  by_contra h
  have hc : Nat.Coprime q M := (Nat.Prime.coprime_iff_not_dvd hq).2 h
  have hb := Nat.gcd_eq_gcd_ab q M
  simp only [hc.gcd_eq_one, Nat.cast_one] at hb
  apply hI
  rw [Ideal.eq_top_iff_one]
  have e : (1 : R) = (q : R) * ((Nat.gcdA q M : ℤ) : R) + (M : R) * ((Nat.gcdB q M : ℤ) : R) := by
    have := congrArg (fun z : ℤ => (z : R)) hb
    push_cast at this
    exact this
  rw [e]
  exact I.add_mem (I.mul_mem_right _ h1) (I.mul_mem_right _ h2)

theorem p_inv_not_integral : ¬ IsIntegral (OO p n) ((p : Om p n)⁻¹) := by
  intro h
  have hK : IsIntegral (OO p n) ((p : KO p n)⁻¹) := by
    have e : ((p : Om p n)⁻¹) = IsScalarTower.toAlgHom (OO p n) (KO p n) (Om p n) ((p : KO p n)⁻¹) := by
      simp
    rw [e] at h
    exact (isIntegral_algHom_iff _ (algebraMap (KO p n) (Om p n)).injective).1 h
  let y : OL p n (KO p n) := ⟨(p : KO p n)⁻¹, hK⟩
  have hp0 : (p : KO p n) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hu : IsUnit (algebraMap (OO p n) (OL p n (KO p n)) (p : OO p n)) := by
    have h1 : algebraMap (OO p n) (OL p n (KO p n)) (p : OO p n) * y = 1 := by
      apply Subtype.ext
      simp [y, hp0]
    exact ⟨⟨_, y, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  have hmem : (p : OO p n) ∈ maximalIdeal (OO p n) := by
    have hw := wU_mem_max (p := p) (n := n)
    have e : (p : OO p n) = wU p n * wU p n := by
      ext <;> simp [wU]
    rw [e]
    exact Ideal.mul_mem_left _ _ hw
  rw [← under_max (p := p) (n := n) (KO p n), Ideal.mem_comap] at hmem
  exact (IsLocalRing.mem_maximalIdeal _).1 hmem hu

theorem inv_integral (τ : LL →+* Om p n) {d : 𝓞 LL} (hd : d ∉ placeIdeal τ) :
    IsIntegral (OO p n) (τ (d : LL))⁻¹ := by
  obtain ⟨u, hu⟩ := isUnit_embO (τ := τ) hd
  have hint : IsIntegral (OO p n) (((u⁻¹ : (Ot τ)ˣ) : Ot τ) : Lt τ) := ((u⁻¹ : (Ot τ)ˣ) : Ot τ).2
  have hint' : IsIntegral (OO p n) ((((u⁻¹ : (Ot τ)ˣ) : Ot τ) : Lt τ) : Om p n) :=
    hint.map ((Lt τ).val.restrictScalars (OO p n))
  have hval : (((u : Ot τ) : Lt τ) : Om p n) = τ (d : LL) := by
    rw [hu, embO_val, embL_val]
  have hmul : (((u : Ot τ) : Lt τ) : Om p n) * ((((u⁻¹ : (Ot τ)ˣ) : Ot τ) : Lt τ) : Om p n) = 1 := by
    rw [← IntermediateField.coe_mul, ← Subalgebra.coe_mul, u.mul_inv]
    simp
  rw [hval] at hmul
  rw [← eq_inv_of_mul_eq_one_right hmul]
  exact hint'

theorem exists_emb (w : HeightOneSpectrum (𝓞 LL)) (hw : (p : 𝓞 LL) ∈ w.asIdeal) :
    ∃ τ : LL →+* Om p n, placeOf τ = w := by
  classical
  haveI : CharZero (Om p n) :=
    charZero_of_injective_algebraMap (algebraMap (KO p n) (Om p n)).injective
  by_contra hno
  push_neg at hno
  let τ0 : LL →ₐ[ℚ] Om p n := IsAlgClosed.lift

  have hav : ¬ ((w.asIdeal : Set (𝓞 LL)) ⊆ ⋃ σ ∈ ((Finset.univ : Finset (LL →ₐ[ℚ] Om p n)) :
      Set (LL →ₐ[ℚ] Om p n)), ((placeIdeal σ.toRingHom : Ideal (𝓞 LL)) : Set (𝓞 LL))) := by
    intro hsub
    obtain ⟨σ, _, hle⟩ := (Ideal.subset_union_prime (s := Finset.univ)
      (f := fun σ : LL →ₐ[ℚ] Om p n => placeIdeal σ.toRingHom) τ0 τ0
      (fun σ _ _ _ => (placeOf σ.toRingHom).isPrime)).1 hsub
    apply hno σ.toRingHom
    apply HeightOneSpectrum.ext
    exact ((w.isMaximal).eq_of_le (placeOf σ.toRingHom).isPrime.ne_top hle).symm
  obtain ⟨e, hew, hen⟩ : ∃ e ∈ w.asIdeal, ∀ σ : LL →ₐ[ℚ] Om p n, e ∉ placeIdeal σ.toRingHom := by
    by_contra h
    push_neg at h
    exact hav (fun x hx => by
      obtain ⟨σ, hσ⟩ := h x hx
      exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_univ σ)) hσ)

  have hint : IsIntegral (OO p n) (∏ σ : LL →ₐ[ℚ] Om p n, (σ (e : LL))⁻¹) := by
    have := (integralClosure (OO p n) (Om p n)).prod_mem (t := Finset.univ) (fun (σ : LL →ₐ[ℚ] Om p n) _ =>
      (show (σ (e : LL))⁻¹ ∈ integralClosure (OO p n) (Om p n) from
        inv_integral σ.toRingHom (hen σ)))
    exact this
  set Nz : ℤ := Algebra.norm ℤ e with hNz
  have hN_eq : (∏ σ : LL →ₐ[ℚ] Om p n, (σ (e : LL))⁻¹) = ((Nz : Om p n))⁻¹ := by
    rw [Finset.prod_inv_distrib, ← Algebra.norm_eq_prod_embeddings ℚ (Om p n) (e : LL),
      ← Algebra.coe_norm_int e, map_intCast]
  have he0 : e ≠ 0 := fun h => hen τ0 (h ▸ (placeIdeal τ0.toRingHom).zero_mem)
  have hN0 : Nz ≠ 0 := by
    rw [hNz, Ne, Algebra.norm_eq_zero_iff]
    exact he0

  have hmemN : ((Nz : ℤ) : 𝓞 LL) ∈ w.asIdeal := by
    have hd := Algebra.dvd_algebraMap_intNorm_self ℤ (𝓞 LL) e
    rw [Algebra.intNorm_eq_norm] at hd
    obtain ⟨c, hc⟩ := hd
    have h1 : algebraMap ℤ (𝓞 LL) Nz ∈ w.asIdeal := by
      rw [hNz, hc]
      exact Ideal.mul_mem_right _ _ hew
    simpa only [algebraMap_int_eq, eq_intCast] using h1
  have hNabs : ((Nz.natAbs : ℕ) : 𝓞 LL) ∈ w.asIdeal := by
    rcases Int.natAbs_eq Nz with h | h
    · rw [h, Int.cast_natCast] at hmemN
      exact hmemN
    · rw [h] at hmemN
      have := w.asIdeal.neg_mem hmemN
      rwa [Int.cast_neg, neg_neg, Int.cast_natCast] at this
  have hdvd : p ∣ Nz.natAbs := dvd_of_mem w.asIdeal w.isPrime.ne_top hp.out hw hNabs
  obtain ⟨m, hm⟩ := Int.ofNat_dvd_left.2 hdvd
  have hm0 : (m : Om p n) ≠ 0 := by
    have : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hm
      exact hN0 hm
    exact_mod_cast this
  have hp0 : (p : Om p n) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have key : ((p : Om p n))⁻¹ = (m : Om p n) * ((Nz : Om p n))⁻¹ := by
    rw [hm]
    push_cast
    field_simp
  apply p_inv_not_integral (p := p) (n := n)
  rw [key]
  have hmI : IsIntegral (OO p n) ((m : ℤ) : Om p n) := (integralClosure (OO p n) (Om p n)).intCast_mem m
  exact hmI.mul (hN_eq ▸ hint)

theorem exists_ringAt (w : HeightOneSpectrum (𝓞 LL)) (hw : (p : 𝓞 LL) ∈ w.asIdeal) :
    ∃ τ : LL →+* Om p n, ∀ x : LL,
      w.valuation LL x ≤ 1 ↔ embL τ x ∈ Set.range (algebraMap (Ot τ) (Lt τ)) := by
  obtain ⟨τ, hτ⟩ := exists_emb (p := p) (n := n) w hw
  refine ⟨τ, fun x => ?_⟩
  have := induces (τ := τ) x
  rwa [hτ] at this

def tauAt (p : ℕ) [Fact p.Prime] (n : ℕ) (w : HeightOneSpectrum (𝓞 LL)) (hw : (p : 𝓞 LL) ∈ w.asIdeal) :
    LL →+* Om p n := (exists_emb (p := p) (n := n) w hw).choose

theorem placeOf_tauAt (w : HeightOneSpectrum (𝓞 LL)) (hw : (p : 𝓞 LL) ∈ w.asIdeal) :
    placeOf (tauAt p n w hw) = w := (exists_emb (p := p) (n := n) w hw).choose_spec

theorem induces_tauAt (w : HeightOneSpectrum (𝓞 LL)) (hw : (p : 𝓞 LL) ∈ w.asIdeal) (x : LL) :
    w.valuation LL x ≤ 1 ↔
      embL (tauAt p n w hw) x ∈ Set.range (algebraMap (Ot (tauAt p n w hw)) (Lt (tauAt p n w hw))) := by
  have := induces (τ := tauAt p n w hw) x
  rwa [placeOf_tauAt] at this

end Formalism.L2.G
