import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.RepSmul
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.RepUniq

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

namespace UpperTheory.Kd.C7

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

private theorem apply_inv_conj (t s : G ℚ Ω) (x : Ω) :
    s ((t⁻¹ : G ℚ Ω) x) = (t⁻¹ : G ℚ Ω) ((t * s * t⁻¹) x) := by
  simp [AlgEquiv.mul_apply]

private def decompositionInvRingHom (A : ValuationSubring Ω) (t : G ℚ Ω) (ht : t ∈ Dec (F := ℚ) A) : R0 A →+* R0 A where
  toFun y := ⟨(t⁻¹ : G ℚ Ω) (y : Ω), (apply_mem_iff_of_mem_Dec (inv_mem ht) _).2 y.2.1, fun s hs => by
    rw [apply_inv_conj t s, y.2.2 _ (conj_mem_Ine ht hs)]⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

private theorem residueInverse_coe (A : ValuationSubring Ω) (t : G ℚ Ω) (ht : t ∈ Dec (F := ℚ) A) (y : R0 A) :
    ((decompositionInvRingHom A t ht y : R0 A) : Ω) = (t⁻¹ : G ℚ Ω) (y : Ω) := rfl

end SlopeTestRemainingChoices

section Frame

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω}
  {j : Ω →+* Qbar l} (Φ : Fr l A j)

end Frame

private theorem apply_root_eq_of_cycBar_eq_one {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] (s : G ℚ Ω)
    (hs : cycBar ℚ Ω l s = 1) (ζ : ℕ → Ω) (hζ : Roots l ζ) (m : ℕ) : s (ζ m) = ζ m := by
  have hZ : cycZ ℚ Ω l s = 1 := by
    have h := congrArg Units.val hs
    simp [cycBar] at h
    ext1
    rw [Units.val_one]
    apply Subtype.ext
    exact h
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => ⟨⟨ζ i, (hζ i).1⟩, rootsOfUnity.isCyclic _ _⟩
  have h1 := cyclotomicCharacter.spec l (n := m) (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) (ζ m)
    ((hζ m).1.pow_eq_one)
  have hc : cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) = 1 := hZ
  rw [hc] at h1
  simp only [Units.val_one, map_one] at h1
  rcases m with _ | m
  · have h0 : ζ 0 = 1 := by simpa using (hζ 0).1
    rw [h0, map_one]
  · have hlt : 1 < l ^ (m + 1) := Nat.one_lt_pow (Nat.succ_ne_zero m) (Fact.out : l.Prime).one_lt
    haveI : Fact (1 < l ^ (m + 1)) := ⟨hlt⟩
    exact h1.trans (by rw [ZMod.val_one, pow_one])

private theorem lc_map' {R : Type} [CommRing R] (e : R →+* R) (l m n : ℕ) (f g : PowerSeries R)
    (h : LC l m n f g) : LC l m n (PowerSeries.map e f) (PowerSeries.map e g) := by
  have hcyc : PowerSeries.map e (GlobalTheory.Col.cyc R l m) = GlobalTheory.Col.cyc R l m := by
    unfold GlobalTheory.Col.cyc
    rw [Polynomial.hom_eval₂]
    have : (PowerSeries.map e).comp PowerSeries.C = PowerSeries.C.comp e := by
      ext x : 1
      simp
    rw [this, ← Polynomial.eval₂_map, Polynomial.map_cyclotomic]
    simp
  unfold LC at *
  rw [← map_sub] at h ⊢
  rw [← map_sub]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hb : b * (l : PowerSeries R) ^ n - (f - g) ∈ Ideal.span {GlobalTheory.Col.cyc R l m} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simp only [map_sub, map_mul, map_pow, map_natCast]
    exact sub_eq_zero.2 ha
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hb
  have hfg : f - g = b * (l : PowerSeries R) ^ n - c * GlobalTheory.Col.cyc R l m := by
    rw [hc]
    ring
  have hz : ev R l m (GlobalTheory.Col.cyc R l m) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  rw [hfg]
  refine Ideal.mem_span_singleton'.2 ⟨ev R l m (PowerSeries.map e b), ?_⟩
  simp only [map_sub, map_mul, map_pow, map_natCast, hcyc, hz, mul_zero, sub_zero]

private theorem dl_map_ringEquiv {R : Type} [CommRing R] (e : R ≃+* R) (f : PowerSeries R) :
    dl (PowerSeries.map (e : R →+* R) f) = PowerSeries.map (e : R →+* R) (dl f) := by
  have hinv : ∀ g : PowerSeries R,
      PowerSeries.map (e.symm : R →+* R) (PowerSeries.map (e : R →+* R) g) = g := by
    intro g
    ext n
    simp
  have hd : dd (PowerSeries.map (e : R →+* R) f) = PowerSeries.map (e : R →+* R) (dd f) := by
    unfold dd
    rw [map_mul]
    congr 1
    · simp
    · ext n
      simp [PowerSeries.coeff_derivative]
  have hr : Ring.inverse (PowerSeries.map (e : R →+* R) f) =
      PowerSeries.map (e : R →+* R) (Ring.inverse f) := by
    by_cases hu : IsUnit f
    · have hu' : IsUnit (PowerSeries.map (e : R →+* R) f) := hu.map _
      apply hu'.mul_left_cancel
      rw [Ring.mul_inverse_cancel _ hu', ← map_mul, Ring.mul_inverse_cancel _ hu, map_one]
    · have hu' : ¬ IsUnit (PowerSeries.map (e : R →+* R) f) := by
        intro h
        apply hu
        simpa [hinv] using h.map (PowerSeries.map (e.symm : R →+* R))
      rw [Ring.inverse_non_unit _ hu, Ring.inverse_non_unit _ hu', map_zero]
  unfold dl
  rw [hd, hr, map_mul]

private theorem fr_ser_map_decompositionInv_eq {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]
    {A : ValuationSubring Ω} {j : Ω →+* Qbar l} (Φ : Fr l A j) (P : Polynomial (R0 A)) :
    Φ.ser (P.map (decompositionInvRingHom A Φ.fr Φ.fr_dec)) = PowerSeries.map (Φ.σ.symm : Φ.R →+* Φ.R) (Φ.ser P) := by
  have hi : Φ.i0.comp (decompositionInvRingHom A Φ.fr Φ.fr_dec) = (Φ.σ.symm : Φ.R →+* Φ.R).comp Φ.i0 := by
    ext y
    have h := Φ.frobenius_compat_inclusion (decompositionInvRingHom A Φ.fr Φ.fr_dec y) y (by
      rw [residueInverse_coe]
      simp)
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom]
    rw [← h, RingEquiv.symm_apply_apply]
  unfold Fr.ser
  rw [Polynomial.map_map, hi, ← Polynomial.map_map, Polynomial.hom_eval₂]
  have : (PowerSeries.map (Φ.σ.symm : Φ.R →+* Φ.R)).comp PowerSeries.C =
      PowerSeries.C.comp (Φ.σ.symm : Φ.R →+* Φ.R) := by
    ext x : 1
    simp
  rw [this, ← Polynomial.eval₂_map]
  simp

private theorem dec_frob_of_mem_dec_rat {Ω : Type} [Field Ω] [Algebra ℚ Ω] (A : ValuationSubring Ω) (t : G ℚ Ω)
    (ht : t ∈ Dec (F := ℚ) A) (P : Polynomial (R0 A)) (z : Ω) (hz : t z = z) :
    pv (P.map (decompositionInvRingHom A t ht)) z = (t⁻¹ : G ℚ Ω) (pv P z) := by
  have hz' : (t⁻¹ : G ℚ Ω) z = z := by
    conv_lhs => rw [← hz]
    simp [AlgEquiv.aut_inv]
  have hc : (R0 A).subtype.comp (decompositionInvRingHom A t ht) = ((t⁻¹ : G ℚ Ω) : Ω →+* Ω).comp (R0 A).subtype := by
    ext y
    exact residueInverse_coe A t ht y
  unfold pv
  rw [Polynomial.eval₂_map, hc]
  conv_lhs => rw [← hz']
  exact (Polynomial.hom_eval₂ P (R0 A).subtype ((t⁻¹ : G ℚ Ω) : Ω →+* Ω) z).symm

private theorem dec_frob_of_mem_dec_rat_prime {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]
    (A : ValuationSubring Ω) (t : G ℚ Ω) (ht : t ∈ Dec (F := ℚ) A) (n r : ℕ) (z : Ω) (hz : t z = z)
    (Z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) {ι : Type} [Fintype ι] (u : ι → Ω) (o : ι → Qbar l)
    (h : KumPres A n r z Z u o) :
    KumPres A n r z (fun s x => Z (t * s * t⁻¹) x) (fun i => (t⁻¹ : G ℚ Ω) (u i)) o := by
  have hz' : (t⁻¹ : G ℚ Ω) z = z := by
    conv_lhs => rw [← hz]
    simp [AlgEquiv.aut_inv]
  obtain ⟨hprim, hnr, hu, ho, hK⟩ := h
  refine ⟨hprim, hnr, fun i => ?_, ho, fun s hs hcyc hsz => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := hu i
    refine ⟨(apply_mem_iff_of_mem_Dec (inv_mem ht) _).2 h1, (map_ne_zero _).2 h2, ?_⟩
    rw [← map_inv₀]
    exact (apply_mem_iff_of_mem_Dec (inv_mem ht) _).2 h3
  · have hs' := conj_mem_Ine ht hs
    have hc' : cycMod ℚ Ω l r (t * s * t⁻¹) = 1 := by
      rw [map_mul, map_mul, hcyc, mul_one, ← map_mul, mul_inv_cancel, map_one]
    have hz2 : (t * s * t⁻¹) z = z := by
      simp only [AlgEquiv.mul_apply, hz', hsz, hz]
    obtain ⟨k, hk, hcg⟩ := hK _ hs' hc' hz2
    refine ⟨k, fun i => ?_, hcg⟩
    obtain ⟨v, hv1, hv2⟩ := hk i
    refine ⟨(t⁻¹ : G ℚ Ω) v, by rw [← map_pow, hv1], ?_⟩
    rw [apply_inv_conj t s v, hv2, map_mul, map_pow, hz']

theorem pRepFrob :
    SRepFrob := by
  intro l _ hl2 Ω _ _ _ A hA j Φ c β ζ hζ Z D a hR hZ i
  have hfix : ∀ m, Φ.fr (ζ m) = ζ m := apply_root_eq_of_cycBar_eq_one Φ.fr Φ.fr_cyc ζ hζ
  let Z' : Sy Ω l := fun r s x => Z r (Φ.fr * s * Φ.fr⁻¹) x
  have hR' : Rep Φ β ζ Z' (fun i => Φ.tw 1 (D i)) := by
    obtain ⟨c₁, m₁, hm⟩ := hR
    refine ⟨c₁, m₁, fun m hm1 => ?_⟩
    obtain ⟨P, hP, hL⟩ := hm m hm1
    refine ⟨fun i => (P i).map (decompositionInvRingHom A Φ.fr Φ.fr_dec), ?_, fun i => ?_⟩
    · unfold BPres at *
      have h6 := dec_frob_of_mem_dec_rat_prime A Φ.fr Φ.fr_dec (m - c₁) m (ζ (m - c₁)) (hfix _) (Z m) _ _ hP
      convert h6 using 2
      exact dec_frob_of_mem_dec_rat A Φ.fr Φ.fr_dec (P _) (ζ m) (hfix m)
    · rw [fr_ser_map_decompositionInv_eq, dl_map_ringEquiv]
      have h2 := lc_map' (Φ.σ.symm : Φ.R →+* Φ.R) l m (m - c₁) _ _ (hL i)
      have htw : Φ.tw m (Φ.tw 1 (D i)) =
          PowerSeries.map (Φ.σ.symm : Φ.R →+* Φ.R) (Φ.tw m (D i)) := by
        unfold Fr.tw
        ext n
        simp only [PowerSeries.coeff_map, pow_one]
        rw [← RingHom.comp_apply, ← RingHom.comp_apply, ← RingHom.mul_def, ← RingHom.mul_def,
          ← pow_succ, ← pow_succ']
      rw [htw]
      exact h2
  have hS := pRepSmul l hl2 Ω A hA j Φ c β ζ hζ Z D a hR
  have hU := pRepUniq l hl2 Ω A hA j Φ c β ζ hζ Z' (fun r s x => (a : Qbar l) * Z r s x)
    (fun i => Φ.tw 1 (D i)) (Φ.act (β.mat a) D) hR' hS (fun m s hs => hZ m s hs)
  exact congrFun hU i

end UpperTheory.Kd.C7
