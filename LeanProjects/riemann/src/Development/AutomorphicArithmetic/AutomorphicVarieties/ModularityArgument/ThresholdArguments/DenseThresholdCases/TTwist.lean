import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.NotLtOfCoprime
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Base
namespace UpperTheory.V.Sd.Tw
section
variable {Ω : Type} [Field Ω]
private theorem not_lt_of_coprime (A : ValuationSubring Ω) {q n : ℕ} (hq : A.valuation (q : Ω) < 1) (h : q.Coprime n) :
    ¬ A.valuation (n : Ω) < 1 := by
  intro hn
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have e : (1 : Ω) = (a : Ω) * q + (b : Ω) * n := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab.symm
  have h1 : ∀ (a : ℤ) (x : Ω), A.valuation x < 1 → A.valuation ((a : Ω) * x) < 1 := fun a x hx => by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((A.valuation_le_one_iff _).2 (intCast_mem A a))) hx
  have := Valuation.map_add_lt A.valuation (h1 a _ hq) (h1 b _ hn)
  rw [← e, map_one] at this
  exact lt_irrefl _ this
variable [CharZero Ω] [IsAlgClosure ℚ Ω]
private theorem cls_frob {A : ValuationSubring Ω} {q N : ℕ} [NeZero N] (hq : A.valuation (q : Ω) < 1) (h : q.Coprime N)
    {t : G ℚ Ω} (ht : IsFrob (F := ℚ) A q t) : Chr.cls ℚ Ω N t = ZMod.unitOfCoprime q h := by
  refine (Chr.clsFacts ℚ Ω N).2.2.1 t _ fun ζ hζ => ?_
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← pow_eq_pow_mod q hζ]
  refine eq_of_pow_eq_one A (not_lt_of_coprime A hq h) ?_ ?_
    (ht.2 ζ (valuation_eq_one_of_pow_eq_one A (NeZero.ne N) hζ).le)
  · rw [← map_pow, hζ, map_one]
  · rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
private theorem cyc_frob {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {q : ℕ} (hp : q.Prime) (hq : A.valuation (q : Ω) < 1)
    (h : q.Coprime l) {t : G ℚ Ω} (ht : IsFrob (F := ℚ) A q t) : ((cycBar ℚ Ω l t : (Qbar l)ˣ) : Qbar l) = q := by
  haveI : Fact q.Prime := ⟨hp⟩
  obtain ⟨v, hv⟩ := (places ℚ Ω q A).1 fun hA => ((places ℚ Ω q A).2.1 hA).2 hq
  have hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := fun hm =>
    not_lt_of_coprime A hq h (((places ℚ Ω l A).2.2.1 v hv).2 hm)
  have e : ((cycZ ℚ Ω l t : ℤ_[l]ˣ) : ℤ_[l]) = (q : ℤ_[l]) :=
    PadicInt.ext_of_toZModPow.mp fun n => cycZ_toZModPow_eq hl hv ht.2 n
  change ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom) ((cycZ ℚ Ω l t : ℤ_[l]ˣ) : ℤ_[l]) = _
  rw [e, map_natCast]
private theorem continuous_cyc (l : ℕ) [Fact l.Prime] :
    Continuous fun t : G ℚ Ω => ((cycBar ℚ Ω l t : (Qbar l)ˣ) : Qbar l) :=
  ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val).comp
    ((Units.continuous_val (M := ℤ_[l])).comp (continuous_cycZ ℚ Ω l))
variable (K : Type) [Field K] [NumberField K] [Algebra K Ω]
omit [IsAlgClosure ℚ Ω] in
private theorem cc_notMem [IsTotallyComplex K] {c : G ℚ Ω} (hc : Sd.IsCC c) : c ∉ galOf ℚ K Ω := by
  obtain ⟨j, hj⟩ := hc
  intro h
  refine IsTotallyComplex.complexEmbedding_not_isReal (j.comp (algebraMap K Ω)) ?_
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := hj (algebraMap K Ω x)
  rw [h x] at this
  exact this.symm
omit [IsAlgClosure ℚ Ω] in
private theorem cc_sq {c : G ℚ Ω} (hc : Sd.IsCC c) : c * c = 1 := by
  obtain ⟨j, hj⟩ := hc
  ext x
  apply j.injective
  rw [AlgEquiv.mul_apply, hj, hj, Complex.conj_conj, AlgEquiv.one_apply]
private theorem exists_chi [IsAlgClosure K Ω] (hK : Module.finrank ℚ K = 2) (N : ℕ) [NeZero N] (hN : N = (discr K).natAbs) :
    (Chr.cls ℚ Ω N).ker ≤ galOf ℚ K Ω ∧ ∃ χ : (ZMod N)ˣ →* ℂˣ, χ ^ 2 = 1 ∧
      ∀ t : G ℚ Ω, t ∉ galOf ℚ K Ω → χ (Chr.cls ℚ Ω N t) = -1 := by
  classical
  have hker : (Chr.cls ℚ Ω N).ker ≤ galOf ℚ K Ω := fun s hs => quadMu K Ω hK s fun ζ hζ => by
    rw [← hN] at hζ
    rw [Chr.cls_spec N s ζ hζ, MonoidHom.mem_ker.1 hs, Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hζ, pow_one]
  have hi : (galOf ℚ K Ω).index = 2 := (galEmbTop ℚ K Ω).2.2.trans hK
  let δ : G ℚ Ω →* ℂˣ := MonoidHom.mk' (fun s => if s ∈ galOf ℚ K Ω then 1 else -1) fun a b => by
    by_cases ha : a ∈ galOf ℚ K Ω <;> by_cases hb : b ∈ galOf ℚ K Ω <;>
      simp [Subgroup.mul_mem_iff_of_index_two hi, ha, hb]
  have hδ : (Chr.cls ℚ Ω N).ker ≤ δ.ker := fun s hs => if_pos (hker hs)
  have hs := (Chr.clsOnto Ω N).1
  have e : ∀ t, (Chr.cls ℚ Ω N).liftOfSurjective hs ⟨δ, hδ⟩ (Chr.cls ℚ Ω N t) = δ t := fun t =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ t
  refine ⟨hker, (Chr.cls ℚ Ω N).liftOfSurjective hs ⟨δ, hδ⟩, MonoidHom.ext fun u => ?_, fun t ht => (e t).trans (if_neg ht)⟩
  obtain ⟨t, rfl⟩ := hs u
  rw [MonoidHom.pow_apply, e]
  change (if t ∈ galOf ℚ K Ω then (1 : ℂˣ) else -1) ^ 2 = 1
  split_ifs <;> simp
private theorem ver_of_frob [IsAlgClosure K Ω] (hK : Module.finrank ℚ K = 2) {l : ℕ} [Fact l.Prime] (κ : G K Ω →* (Qbar l)ˣ)
    (hκ : Continuous κ) (T : ℕ) (hT : T ≠ 0)
    (H : ∀ (q : ℕ) (A : ValuationSubring Ω) (t : G ℚ Ω) (s : G K Ω), q.Prime → ¬ q ∣ T → A.valuation (q : Ω) < 1 →
      IsFrob (F := ℚ) A q t → t ∉ galOf ℚ K Ω → galEmb ℚ K Ω s = t * t →
      (κ s : Qbar l) * (cycBar ℚ Ω l t : (Qbar l)ˣ) = -1)
    (s : G K Ω) (t : G ℚ Ω) (ht : t ∉ galOf ℚ K Ω) (hs : galEmb ℚ K Ω s = t * t) : κ s = -(cycBar ℚ Ω l t)⁻¹ := by
  obtain ⟨hemb, hopen, hi⟩ := galEmbTop ℚ K Ω
  have hsq : ∀ t : G ℚ Ω, ∃ s, galEmb ℚ K Ω s = t * t := fun t => by
    have := Subgroup.mul_self_mem_of_index_two (hi.trans hK) t
    rw [← range_galEmb] at this
    exact this
  choose g hg using hsq
  have hgc : Continuous g := hemb.continuous_iff.2 ((continuous_id.mul continuous_id).congr fun t => (hg t).symm)
  have hcl : IsClosed {t : G ℚ Ω | (κ (g t) : Qbar l) * (cycBar ℚ Ω l t : (Qbar l)ˣ) = -1} :=
    isClosed_eq ((Units.continuous_val.comp (hκ.comp hgc)).mul (continuous_cyc l)) continuous_const
  have key : (κ (g t) : Qbar l) * (cycBar ℚ Ω l t : (Qbar l)ˣ) = -1 := by
    by_contra hne
    obtain ⟨q, A, φ, hq, hqT, hA, hφ, h1, h2⟩ := ML.chebQ Ω _
      (hcl.isOpen_compl.inter ((galOf ℚ K Ω).isClosed_of_isOpen hopen).isOpen_compl) ⟨t, hne, ht⟩ T hT
    exact h1 (H q A φ (g φ) hq hqT hA hφ h2 (hg φ))
  rw [hemb.injective ((hg t).trans hs.symm)] at key
  rw [← mul_left_inj (cycBar ℚ Ω l t), neg_mul, inv_mul_cancel]
  exact Units.ext key
end
end UpperTheory.V.Sd.Tw
open UpperTheory.V.Sd.Tw in
theorem UpperTheory.V.Sd.twist_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → UpperTheory.V.Sd.Twist := by
  intro hP K Ω _ _ _ _ _ _ _ hK l hl hl2 hld ι c hc
  haveI : IsAlgClosure K Ω :=
    ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) K⟩
  set N := (discr K).natAbs with hN
  have hN3 : 3 ≤ N := by
    have := abs_discr_gt_two (K := K) (by omega)
    rw [Int.abs_eq_natAbs] at this
    omega
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨hker, χ, hχ2, hχ⟩ := exists_chi (Ω := Ω) K hK N hN
  have hχ1 : χ (-1) = -1 := by
    rw [← (Chr.clsFacts ℚ Ω N).2.2.2.1 c hc]
    exact hχ c (cc_notMem K hc)
  obtain ⟨Y, a, τ, hYa, ha1, ha0, hYu, ⟨m, hm0, hml, hm⟩, hYv⟩ := hecke K hK l hl.out hl2 hld N hN3 χ hχ2 hχ1
  obtain ⟨art, hart⟩ : ∃ art : Ideles K →* Gab K Ω, IsGlobalArtin art := hP.litN.aut.art K Ω
  obtain ⟨κ, hκ, hL⟩ := hart.exists_isLAdicOf ι (isAlgPos_of_isAlg hYa)
  have hNd : ∀ v : HeightOneSpectrum (𝓞 K), ((discr K : ℤ) : 𝓞 K) ∉ v.asIdeal → (N : 𝓞 K) ∉ v.asIdeal := fun v hv h => by
    apply hv
    rcases Int.natAbs_eq (discr K) with e | e
    · rw [e, Int.cast_natCast]
      exact h
    · rw [e, Int.cast_neg, Int.cast_natCast]
      exact neg_mem h
  have hnat : ∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 K)), IsPlaceOver A w → ∀ n : ℤ,
      ¬ A.valuation (n : Ω) < 1 → (n : 𝓞 K) ∉ w.asIdeal := fun A w hw n hn h => by
    have := (hw (n : 𝓞 K)).2 h
    exact hn (by simpa using this)
  have hnat' : ∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 K)), IsPlaceOver A w → ∀ n : ℕ,
      ¬ A.valuation (n : Ω) < 1 → (n : 𝓞 K) ∉ w.asIdeal := fun A w hw n hn => by
    simpa using hnat A w hw n (by simpa using hn)
  have hver := ver_of_frob K hK κ hκ (l * N) (mul_ne_zero hl.out.ne_zero (NeZero.ne N)) fun q A t s hq hqT hA ht htK hs => by
    have hc' := (Nat.Prime.coprime_iff_not_dvd hq).2 hqT
    have hql := hc'.coprime_mul_right_right
    have hqN := hc'.coprime_mul_left_right
    have hAN := not_lt_of_coprime A hA hqN
    obtain ⟨w, hw, hwq, hfr⟩ := inert K Ω hK q hq A hA (((Chr.clsFacts ℚ Ω N).2.2.2.2 A hAN).trans hker) t ht htK
    rw [hL.frob_unr hart (Or.inl (hnat' A w hw l (not_lt_of_coprime A hA hql))) (hYu w (hnat' A w hw N hAN)) hw (hfr s hs),
      hYv q hqN w hwq, ← cls_frob hA hqN ht, hχ t htK, cyc_frob hq hA hql ht]
    have hq0 : (q : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
    simp [hq0]
  refine ⟨κ, hκ, ⟨art, Y, a, τ, hart, isAlgPos_of_isAlg hYa, hL, ha1, ha0, fun v hv => hYu v (hNd v hv)⟩,
    fun s s' h => ?_, hver, fun A hAl hAd s hs => ?_, m, hm0, hml, fun A hAl s hs => ?_⟩
  · have hi : (galOf ℚ K Ω).index = 2 := (galEmbTop ℚ K Ω).2.2.trans hK
    have h1 : galEmb ℚ K Ω s * c ∉ galOf ℚ K Ω := fun h' =>
      cc_notMem K hc (((galOf ℚ K Ω).mul_mem_cancel_left (galEmb_mem ℚ K Ω s)).1 h')
    have h2 : c⁻¹ = c := inv_eq_of_mul_eq_one_right (cc_sq hc)
    have h3 : cycBar ℚ Ω l c = -1 := by
      have h4 : cycZ ℚ Ω l c = -1 := IsConjOm.cyc (E := ℚ) (show IsConjOm c.toRingEquiv from hc)
      change Units.map _ (cycZ ℚ Ω l c) = -1
      rw [h4]
      exact Units.ext (by simp)
    rw [← map_mul, hver (s * s') _ h1 (by rw [map_mul, h, h2]; simp only [mul_assoc]), map_mul, h3, mul_neg_one, inv_neg, neg_neg]
    rfl
  · by_cases hA : A = ⊤
    · rw [((places K Ω l A).2.1 hA).1, Subgroup.mem_bot] at hs
      rw [hs, map_one]
    · obtain ⟨w, hw⟩ := (places K Ω l A).1 hA
      exact (hL.unr_iff hart (Or.inl (hnat' A w hw l hAl)) hw).2 (hYu w (hNd w (hnat A w hw _ hAd))) s hs
  · by_cases hA : A = ⊤
    · rw [((places K Ω l A).2.1 hA).1, Subgroup.mem_bot] at hs
      rw [hs, map_one, one_pow]
    · obtain ⟨w, hw⟩ := (places K Ω l A).1 hA
      obtain ⟨x, hx, e⟩ := (hL.ine_image hart (Or.inl (hnat' A w hw l hAl)) hw _).1 ⟨s, hs, rfl⟩
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, ← e, ← map_pow, ← Units.val_pow_eq_pow_val, hm w x hx]
      simp
end
