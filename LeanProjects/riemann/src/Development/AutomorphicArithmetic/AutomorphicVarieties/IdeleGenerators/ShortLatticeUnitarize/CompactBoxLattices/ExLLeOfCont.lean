import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShortLatticeUnitarize.Unitarize
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.LocComplY

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual UpperTheory.V.Sd

namespace UpperTheory.V.Sd.Wc

section

variable {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime]

private theorem exL_norm_l : ‖(l : Qbar l)‖ < 1 := by
  have : (l : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := (map_natCast _ l).symm
  rw [this, norm_algebraMap']
  exact Padic.norm_p_lt_one

omit [NumberField F] in
private theorem exL_le (σ : F →+* Qbar l) (x : 𝓞 F) : ‖σ (x : F)‖ ≤ 1 := by
  have hy : IsIntegral ℤ (σ (x : F)) := map_isIntegral_int σ (RingOfIntegers.isIntegral_coe x)
  have h : IsIntegral (NormedField.valuation (K := Qbar l)).integer (σ (x : F)) := hy.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := Qbar l))).mem_of_integral h
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h2
  exact_mod_cast h2

omit [NumberField F] in
private theorem exL_mem {w : Pl F} {σ : F →+* Qbar l} (h : EmbAt w σ) : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal := by
  rw [h, show ((l : 𝓞 F) : F) = (l : F) from map_natCast (algebraMap (𝓞 F) F) l, map_natCast]
  exact exL_norm_l

private theorem exL_place (σ : F →+* Qbar l) : ∃ w : Pl F, EmbAt w σ := by
  let ν : Valuation (𝓞 F) NNReal := (NormedField.valuation (K := Qbar l)).comap (σ.comp (algebraMap (𝓞 F) F))
  have hν : ∀ x : 𝓞 F, ν x < 1 ↔ ‖σ (x : F)‖ < 1 := fun x => Iff.rfl
  have hle : ∀ x : 𝓞 F, ν x ≤ 1 := fun x => exL_le σ x
  let I : Ideal (𝓞 F) :=
    { carrier := {x | ν x < 1}
      add_mem' := fun hx hy => ν.map_add_lt hx hy
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        change ν (c * x) < 1
        rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle c)) hx }
  have hI : ∀ x, x ∈ I ↔ ν x < 1 := fun x => Iff.rfl
  refine ⟨⟨I, ⟨?_, ?_⟩, ?_⟩, fun x => Iff.rfl⟩
  · rw [Ideal.ne_top_iff_one, hI]; simp
  · intro x y hxy
    by_contra hc
    push Not at hc
    rw [hI, map_mul, le_antisymm (hle x) (not_lt.1 hc.1), le_antisymm (hle y) (not_lt.1 hc.2), one_mul] at hxy
    exact lt_irrefl _ hxy
  · intro h
    have : ((l : ℕ) : 𝓞 F) ∈ I := by
      rw [hI, hν, show ((l : 𝓞 F) : F) = (l : F) from map_natCast (algebraMap (𝓞 F) F) l, map_natCast]
      exact exL_norm_l
    rw [h, Ideal.mem_bot] at this
    exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast this)

private theorem exL_val (w : Pl F) (x : F) :
    Valued.v (algebraMap F (w.adicCompletion F) x) = w.valuation F x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w x

private theorem exL_valO (w : Pl F) (x : 𝓞 F) :
    Valued.v (algebraMap F (w.adicCompletion F) (x : F)) = w.intValuation x := by
  rw [exL_val]; exact w.valuation_of_algebraMap x

private theorem exL_int (w : Pl F) (k : ℤ) : Valued.v ((k : ℤ) : w.adicCompletion F) ≤ 1 := by
  have := exL_valO w (k : 𝓞 F)
  rw [show ((k : 𝓞 F) : F) = (k : F) from map_intCast (algebraMap (𝓞 F) F) k, map_intCast] at this
  rw [this]; exact w.intValuation_le_one _

omit [Fact l.Prime] in
private theorem exL_unif {w : Pl F} (h1 : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) (h2 : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal ^ 2) :
    Valued.v ((l : ℕ) : w.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
  have := exL_valO w (l : 𝓞 F)
  rw [show ((l : 𝓞 F) : F) = (l : F) from map_natCast (algebraMap (𝓞 F) F) l, map_natCast] at this
  rw [this]
  rw [← pow_one w.asIdeal, ← w.intValuation_le_pow_iff_mem] at h1
  rw [← w.intValuation_le_pow_iff_mem, not_le] at h2
  have h0 : w.intValuation (l : 𝓞 F) ≠ 0 := (lt_of_le_of_lt zero_le h2).ne'
  rw [← WithZero.exp_log h0] at h1 h2 ⊢
  rw [WithZero.exp_le_exp] at h1
  rw [WithZero.exp_lt_exp] at h2
  congr 1
  push_cast at h1 h2
  omega

private theorem exL_lt_of_cont {w : Pl F} (J : w.adicCompletion F →+* Qbar l) (hJ : Continuous J)
    (x : w.adicCompletion F) (hx : Valued.v x < 1) : ‖J x‖ < 1 := by
  have h1 : Filter.Tendsto (fun n : ℕ => x ^ n) Filter.atTop (nhds 0) := Valued.tendsto_zero_pow_of_v_lt_one hx
  have h2 := (hJ.tendsto 0).comp h1
  rw [map_zero] at h2
  rw [← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
  simpa [Function.comp_def] using h2

private theorem exL_le_of_cont {w : Pl F} (hl : Valued.v ((l : ℕ) : w.adicCompletion F) < 1)
    (J : w.adicCompletion F →+* Qbar l) (hJ : Continuous J)
    (x : w.adicCompletion F) (hx : Valued.v x ≤ 1) : ‖J x‖ ≤ 1 := by
  by_contra hc
  rw [not_le] at hc
  have hp : 0 < ‖(l : Qbar l)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ‖(l : Qbar l)‖⁻¹ hc
  have h := exL_lt_of_cont J hJ (x ^ n * l) (by
    rw [map_mul, map_pow]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (pow_le_one' hx n)) hl)
  rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow] at h
  rw [inv_lt_iff_one_lt_mul₀ hp] at hn
  linarith

private theorem exL_iff {w : Pl F} (hl : Valued.v ((l : ℕ) : w.adicCompletion F) < 1)
    (J : w.adicCompletion F →+* Qbar l) (hJ : Continuous J) (x : w.adicCompletion F) :
    (‖J x‖ ≤ 1 ↔ Valued.v x ≤ 1) ∧ (‖J x‖ < 1 ↔ Valued.v x < 1) := by
  refine ⟨⟨fun h => ?_, exL_le_of_cont hl J hJ x⟩, ⟨fun h => ?_, exL_lt_of_cont J hJ x⟩⟩
  · by_contra hc
    rw [not_le] at hc
    have h0 : x ≠ 0 := by rintro rfl; simp at hc
    have h1 := exL_lt_of_cont J hJ x⁻¹ (by rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ hc)
    rw [map_inv₀, norm_inv, inv_lt_one₀ (norm_pos_iff.2 ((map_ne_zero J).2 h0))] at h1
    linarith
  · by_contra hc
    rw [not_lt] at hc
    have h0 : x ≠ 0 := by rintro rfl; simp at hc
    have h1 := exL_le_of_cont hl J hJ x⁻¹ (by rw [map_inv₀]; exact inv_le_one_of_one_le₀ hc)
    rw [map_inv₀, norm_inv, inv_le_one₀ (norm_pos_iff.2 ((map_ne_zero J).2 h0))] at h1
    linarith

private theorem exL_digit {w : Pl F} (hN : Ideal.absNorm w.asIdeal = l) (x : w.adicCompletion F) (hx : Valued.v x ≤ 1) :
    ∃ a : ℤ, Valued.v (x - a) < 1 := by
  have ho : IsOpen {y : w.adicCompletion F | Valued.v (x - y) < 1} := by
    have : IsOpen {y : w.adicCompletion F | Valued.v y < 1} := by
      have := Valued.isOpen_ball (w.adicCompletion F) 1
      simpa [Valuation.restrict_lt_one_iff] using this
    exact this.preimage (continuous_const.sub continuous_id)
  obtain ⟨y, hy⟩ := (w.denseRange_algebraMap F).exists_mem_open ho ⟨x, by simp⟩
  replace hy : Valued.v (x - algebraMap F _ y) < 1 := hy
  have hy1 : w.valuation F y ≤ 1 := by
    rw [← exL_val, show algebraMap F (w.adicCompletion F) y = x - (x - algebraMap F _ y) by ring]
    exact Valuation.map_sub_le _ hx hy.le
  obtain ⟨b, hb⟩ := w.exists_valuation_sub_lt_of_integer hy1 1
  rw [Units.val_one, ← exL_val, map_sub] at hb
  have hc : Nat.card (𝓞 F ⧸ w.asIdeal) = l := by rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have : Finite (𝓞 F ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero (hc ▸ (Fact.out : l.Prime).ne_zero)
  let := Fintype.ofFinite (𝓞 F ⧸ w.asIdeal)
  let e := ZMod.ringEquivOfPrime (𝓞 F ⧸ w.asIdeal) (Fact.out : l.Prime) (by rw [← Nat.card_eq_fintype_card, hc])
  obtain ⟨z, hz⟩ := e.surjective (Ideal.Quotient.mk _ b)
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective z
  rw [map_intCast, ← map_intCast (Ideal.Quotient.mk w.asIdeal), eq_comm, Ideal.Quotient.eq, ← w.intValuation_lt_one_iff_mem,
    ← exL_valO] at hz
  have hz' : Valued.v (algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F (b - a))) < 1 := hz
  rw [map_sub, map_sub, map_intCast, map_intCast] at hz'
  refine ⟨a, ?_⟩
  have := Valuation.map_add_lt _ (Valuation.map_sub_lt _ hy hb) hz'
  convert this using 2
  ring

private theorem exL_pow {R Γ : Type*} [CommRing R] [LinearOrderedCommGroupWithZero Γ] (ν : Valuation R Γ) {x y : R}
    (hx : ν x ≤ 1) (hy : ν y ≤ 1) (h : ν (x - y) < 1) (m : ℕ) : ν (x ^ m - y ^ m) < 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show x ^ (m + 1) - y ^ (m + 1) = x * (x ^ m - y ^ m) + y ^ m * (x - y) by ring]
    refine ν.map_add_lt ?_ ?_
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' hx) ih
    · rw [map_mul, map_pow]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (pow_le_one' hy m)) h

private theorem exL_res {w : Pl F} (hN : Ideal.absNorm w.asIdeal = l) (hl : Valued.v ((l : ℕ) : w.adicCompletion F) < 1)
    (x : w.adicCompletion F) (hx : Valued.v x = 1) : Valued.v (x ^ (l - 1) - 1) < 1 := by
  obtain ⟨a, ha⟩ := exL_digit hN x hx.le
  have hdiv : ∀ k : ℤ, (l : ℤ) ∣ k → Valued.v ((k : ℤ) : w.adicCompletion F) < 1 := by
    rintro _ ⟨k, rfl⟩
    rw [Int.cast_mul, Int.cast_natCast, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' (exL_int w k)) hl
  have ha0 : (a : ZMod l) ≠ 0 := by
    intro h
    have := Valuation.map_add_lt _ ha (hdiv a ((ZMod.intCast_zmod_eq_zero_iff_dvd a l).1 h))
    rw [sub_add_cancel, hx] at this
    exact lt_irrefl _ this
  have h1 := hdiv (a ^ (l - 1) - 1) ((ZMod.intCast_zmod_eq_zero_iff_dvd _ l).1 (by
    push_cast
    rw [ZMod.pow_card_sub_one_eq_one ha0, sub_self]))
  have := Valuation.map_add_lt _ (exL_pow _ hx.le (exL_int w a) ha (l - 1)) h1
  convert this using 2
  push_cast
  ring

private theorem exL_uniq {w : Pl F} (hN : Ideal.absNorm w.asIdeal = l)
    (hl : Valued.v ((l : ℕ) : w.adicCompletion F) = WithZero.exp (-1 : ℤ)) (J J' : w.adicCompletion F →+* Qbar l)
    (hJ : ∀ x, Valued.v x ≤ 1 → ‖J x‖ ≤ 1) (hJ' : ∀ x, Valued.v x ≤ 1 → ‖J' x‖ ≤ 1) : J = J' := by
  have hl0 : ((l : ℕ) : w.adicCompletion F) ≠ 0 := by
    intro h
    rw [h, map_zero] at hl
    exact WithZero.exp_ne_zero hl.symm
  have key : ∀ n : ℕ, ∀ x, Valued.v x ≤ 1 → ‖J x - J' x‖ ≤ ‖(l : Qbar l)‖ ^ n := by
    intro n
    induction n with
    | zero =>
      intro x hx
      rw [pow_zero, sub_eq_add_neg]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hJ x hx) (by rw [norm_neg]; exact hJ' x hx))
    | succ n ih =>
      intro x hx
      obtain ⟨a, ha⟩ := exL_digit hN x hx
      have hy : Valued.v ((x - a) / l) ≤ 1 := by
        rw [map_div₀, hl, div_le_one₀ (by simp)]
        by_cases h0 : Valued.v (x - a) = 0
        · rw [h0]; exact zero_le
        · rw [← WithZero.exp_log h0] at ha ⊢
          rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at ha
          rw [WithZero.exp_le_exp]
          omega
      have e : x = a + l * ((x - a) / l) := by field_simp; ring
      have e2 : J x - J' x = l * (J ((x - a) / l) - J' ((x - a) / l)) := by
        generalize (x - a) / l = y at e
        rw [e]; simp only [map_add, map_mul, map_intCast, map_natCast]; ring
      rw [e2, norm_mul, pow_succ']
      exact mul_le_mul_of_nonneg_left (ih _ hy) (norm_nonneg _)
  have key2 : ∀ x, Valued.v x ≤ 1 → J x = J' x := by
    intro x hx
    rw [← sub_eq_zero, ← norm_le_zero_iff]
    exact ge_of_tendsto' (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) exL_norm_l) fun n => key n x hx
  ext x
  rcases le_total (Valued.v x) 1 with h | h
  · exact key2 x h
  · have := key2 x⁻¹ (by rw [map_inv₀]; exact inv_le_one_of_one_le₀ h)
    rwa [map_inv₀, map_inv₀, inv_inj] at this

end

end UpperTheory.V.Sd.Wc

open UpperTheory.V.Sd.Wc in
theorem UpperTheory.V.Sd.Wc.exL :
    UpperTheory.V.Sd.Wc.ExL := by
  intro F _ _ _ l _ ι hS
  let τ : InfinitePlace F → F →+* Qbar l := fun v => ι.symm.toRingHom.comp v.embedding
  choose pl hpl using fun v => exL_place (τ v)
  have hext : ∀ (w : Pl F) (σ : F →+* Qbar l), EmbAt w σ → ∃ J : w.adicCompletion F →+* Qbar l,
      (∀ x : F, J (algebraMap F _ x) = σ x) ∧
      ∀ x, (‖J x‖ ≤ 1 ↔ Valued.v x ≤ 1) ∧ (‖J x‖ < 1 ↔ Valued.v x < 1) := by
    intro w σ h
    obtain ⟨J, hJ, hJ1, -⟩ := KStar.IdealValuations.exists_completion_map w σ fun x => (h x).symm
    refine ⟨J, hJ1, exL_iff ?_ J hJ⟩
    rw [exL_unif (exL_mem h) (hS w (exL_mem h)).2, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hplace : ∀ (σ : F →+* Qbar l) (w w' : Pl F), EmbAt w σ → EmbAt w' σ → w = w' := fun σ w w' h h' =>
    HeightOneSpectrum.ext (Ideal.ext fun x => (h x).trans (h' x).symm)
  have hτ : ∀ σ : F →+* Qbar l, τ (InfinitePlace.mk (ι.toRingHom.comp σ)) = σ := by
    intro σ
    ext x
    simp only [τ]
    rw [InfinitePlace.embedding_mk_eq_of_isReal (IsTotallyReal.complexEmbedding_isReal _)]
    simp
  choose J hJ1 hJ2 using fun v => hext (pl v) (τ v) (hpl v)
  have hnu : ∀ y : Qbar l, nu ι (ι y) = ‖y‖₊ := fun y => by rw [nu_apply, RingEquiv.symm_apply_apply]
  have hu := fun v => exL_unif (exL_mem (hpl v)) (hS _ (exL_mem (hpl v))).2
  have hlt : ∀ v x, nu ι (ι.toRingHom.comp (J v) x) < 1 ↔ Valued.v x < 1 := fun v x => by
    rw [← (hJ2 v x).2]
    change nu ι (ι (J v x)) < 1 ↔ _
    rw [hnu]
    exact Iff.rfl
  have hemb : ∀ (σ : F →+* Qbar l) (w : Pl F), EmbAt w σ ↔ pl (InfinitePlace.mk (ι.toRingHom.comp σ)) = w := by
    intro σ w
    have h := hpl (InfinitePlace.mk (ι.toRingHom.comp σ))
    rw [hτ] at h
    exact ⟨fun h' => hplace σ _ _ h h', fun e => e ▸ h⟩
  refine ⟨
    { pl := pl
      em := fun v => ι.toRingHom.comp (J v)
      em_alg := fun v x => ?_
      le := fun v x => ?_
      lt := hlt
      res := fun v x hx => ?_
      mem := fun v => exL_mem (hpl v)
      inj := fun v v' e => ?_
      surj := fun w hw => ?_
      norm := fun v => ?_
      unif := hu
      embAt := hemb }⟩
  · change ι (J v _) = _
    rw [hJ1]
    exact ι.apply_symm_apply _
  · rw [← (hJ2 v x).1]
    change nu ι (ι (J v x)) ≤ 1 ↔ _
    rw [hnu]
    exact Iff.rfl
  · have := (hlt v _).2 (exL_res (hS _ (exL_mem (hpl v))).1 (by
      rw [hu, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num) x hx)
    rwa [map_sub, map_pow, map_one] at this
  · obtain ⟨J', h1, h2⟩ := hext (pl v) (τ v') (e ▸ hpl v')
    have hJJ := exL_uniq (hS _ (exL_mem (hpl v))).1 (hu v) (J v) J' (fun x => (hJ2 v x).1.2) fun x => (h2 x).1.2
    have : v.embedding = v'.embedding := by
      ext x
      apply ι.symm.injective
      exact ((hJ1 v x).symm.trans (by rw [hJJ])).trans (h1 x)
    rw [← v.mk_embedding, this, v'.mk_embedding]
  · obtain ⟨σ, hσ⟩ := KStar.IdealValuations.exists_embedding_place w hw
    exact ⟨_, (hemb σ w).1 fun x => (hσ x).symm⟩
  · rw [← (hS _ (exL_mem (hpl v))).1, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
