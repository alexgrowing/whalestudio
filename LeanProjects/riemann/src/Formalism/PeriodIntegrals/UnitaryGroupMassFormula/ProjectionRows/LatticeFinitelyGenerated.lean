import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionRows.Pieces
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndexDeterminant.NegLogValuation

noncomputable section

namespace PI.DvRows

open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv

section ConjP

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def starO (K : Type) [Field K] [NumberField K] [StarRing K] : 𝓞 K ≃+* 𝓞 K :=
  RingOfIntegers.mapRingEquiv (starRingAut : K ≃+* K)

lemma starO_coe (a : 𝓞 K) : ((starO K a : 𝓞 K) : K) = star (a : K) := rfl

lemma starO_starO (a : 𝓞 K) : starO K (starO K a) = a := by
  apply RingOfIntegers.ext
  rw [starO_coe, starO_coe, star_star]

lemma mem_comap_pow (I : Ideal (𝓞 K)) (n : ℕ) (a : 𝓞 K) :
    a ∈ (I.comap (starO K)) ^ n ↔ starO K a ∈ I ^ n := by
  have e : (I.comap (starO K)) ^ n = (I ^ n).comap (starO K) := by
    rw [← Ideal.map_symm, ← Ideal.map_symm, Ideal.map_pow]
  rw [e, Ideal.mem_comap]

def conjW (w : HeightOneSpectrum (𝓞 K)) : HeightOneSpectrum (𝓞 K) where
  asIdeal := w.asIdeal.comap (starO K)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro hb
    apply w.ne_bot
    rw [eq_bot_iff]
    intro x hx
    have h1 : starO K x ∈ w.asIdeal.comap (starO K) := by
      show starO K (starO K x) ∈ w.asIdeal
      rwa [starO_starO]
    rw [hb, Ideal.mem_bot] at h1
    rw [Ideal.mem_bot]
    have h2 := congrArg (starO K) h1
    rwa [starO_starO, map_zero] at h2

lemma conjW_conjW (w : HeightOneSpectrum (𝓞 K)) : conjW (conjW w) = w := by
  ext a
  show starO K (starO K a) ∈ w.asIdeal ↔ a ∈ w.asIdeal
  rw [starO_starO]

lemma intVal_conj (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) :
    (conjW w).intValuation a = w.intValuation (starO K a) := by
  by_cases ha : a = 0
  · subst ha; simp
  have ha' : starO K a ≠ 0 := by
    intro h0; apply ha
    have := congrArg (starO K) h0
    rwa [starO_starO, map_zero] at this
  have key : ∀ n : ℕ, (conjW w).intValuation a ≤ WithZero.exp (-(n : ℤ)) ↔
      w.intValuation (starO K a) ≤ WithZero.exp (-(n : ℤ)) := by
    intro n
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem]
    exact mem_comap_pow w.asIdeal n a
  obtain ⟨m1, h1⟩ : ∃ m : ℕ, (conjW w).intValuation a = WithZero.exp (-(m : ℤ)) :=
    ⟨_, (conjW w).intValuation_eq_exp_neg_multiplicity ha⟩
  obtain ⟨m2, h2⟩ : ∃ m : ℕ, w.intValuation (starO K a) = WithZero.exp (-(m : ℤ)) :=
    ⟨_, w.intValuation_eq_exp_neg_multiplicity ha'⟩
  have k1 := (key m1).1 (le_of_eq h1)
  have k2 := (key m2).2 (le_of_eq h2)
  rw [h2, WithZero.exp_le_exp] at k1
  rw [h1, WithZero.exp_le_exp] at k2
  have : m1 = m2 := by omega
  rw [h1, h2, this]

lemma val_conj (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    (conjW w).valuation K x = w.valuation K (star x) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have e : star (algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) =
      algebraMap (𝓞 K) K (starO K a) / algebraMap (𝓞 K) K (starO K b) := by
    rw [← starRingEnd_apply, map_div₀, starRingEnd_apply, starRingEnd_apply]
    rfl
  rw [e, map_div₀, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, intVal_conj, intVal_conj]

lemma vAdd_conj (w : HeightOneSpectrum (𝓞 K)) (x : K) : vAdd (conjW w) x = vAdd w (star x) := by
  unfold vAdd
  rw [val_conj]

lemma absNorm_conj (w : HeightOneSpectrum (𝓞 K)) :
    Ideal.absNorm (conjW w).asIdeal = Ideal.absNorm w.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv _ _ (starO K)
    (Ideal.map_comap_of_surjective _ (starO K).surjective _).symm).toEquiv

end ConjP

theorem conjugate_prime : ConjPrime := by
  intro K _ _ _
  exact ⟨conjW, fun w => conjW_conjW w, fun w => ⟨fun x => vAdd_conj w x, absNorm_conj w⟩⟩

section Norm

variable {K : Type} [Field K] [NumberField K]

lemma norm_embedding_eq_zpow (v : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    ‖FinitePlace.embedding v x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-vAdd v x) := by
  have hv : v.valuation K x ≠ 0 := by simpa using hx
  rw [FinitePlace.norm_embedding, NumberField.HeightOneSpectrum.adicAbv_def,
    WithZeroMulInt.toNNReal_neg_apply _ hv, WithZero.toAdd_unzero_eq_log hv, NNReal.coe_zpow]
  unfold vAdd
  rw [neg_neg]
  norm_cast

end Norm

theorem norm_finite_sum : NormFinsum := by
  intro K _ _ x hx
  set f : HeightOneSpectrum (𝓞 K) → ℝ := fun v => ‖FinitePlace.embedding v x‖ with hf
  have hprod : ∏ᶠ v, f v = |((Algebra.norm ℚ x : ℚ) : ℝ)|⁻¹ := by
    have h := FinitePlace.prod_eq_inv_abs_norm (K := K) hx
    rw [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm] at h
    simp only [FinitePlace.equivHeightOneSpectrum_symm_apply] at h
    rw [hf, h]
    push_cast
    rfl
  have hfin : (Function.mulSupport f).Finite := by
    have h := FinitePlace.hasFiniteMulSupport (K := K) hx
    have e : Function.mulSupport f = FinitePlace.equivHeightOneSpectrum.symm ⁻¹'
        Function.mulSupport (fun w : FinitePlace K => w x) := by
      ext v
      simp only [f, Function.mem_mulSupport, Set.mem_preimage,
        FinitePlace.equivHeightOneSpectrum_symm_apply]
    rw [e]
    exact Set.Finite.preimage (Equiv.injective _).injOn h
  set s := hfin.toFinset with hs
  have hN : ∀ v : HeightOneSpectrum (𝓞 K), (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := fun v => by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hfs : ∀ v, v ∉ s → vAdd v x = 0 := by
    intro v hv
    rw [hs, Set.Finite.mem_toFinset, Function.mem_mulSupport, not_not, hf] at hv
    dsimp only at hv
    rw [norm_embedding_eq_zpow v hx] at hv
    have h2 := congrArg Real.log hv
    rw [Real.log_zpow, Real.log_one] at h2
    have hl : 0 < Real.log (Ideal.absNorm v.asIdeal : ℝ) := Real.log_pos (hN v)
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact_mod_cast neg_eq_zero.1 (by exact_mod_cast h3)
    · exact absurd h3 hl.ne'
  have hlog : ∑ v ∈ s, Real.log (Ideal.absNorm v.asIdeal : ℝ) * (-(vAdd v x : ℝ)) =
      -Real.log |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
    have h := congrArg Real.log hprod
    rw [finprod_eq_prod_of_mulSupport_subset f (s := s) (by
      intro v hv; rw [hs, Finset.mem_coe, Set.Finite.mem_toFinset]; exact hv)] at h
    rw [Real.log_prod (fun v _ => by
      rw [hf]; dsimp only; rw [norm_embedding_eq_zpow v hx]
      exact (zpow_pos (by linarith [hN v]) _).ne'), Real.log_inv] at h
    rw [← h]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hf]; dsimp only
    rw [norm_embedding_eq_zpow v hx, Real.log_zpow]
    push_cast
    ring
  rw [finsum_eq_sum_of_support_subset (s := s)]
  · unfold lw
    have e : ∑ v ∈ s, Real.log (Ideal.absNorm v.asIdeal : ℝ) / (Module.finrank ℚ K : ℝ) *
        (vAdd v x : ℝ) = (∑ v ∈ s, Real.log (Ideal.absNorm v.asIdeal : ℝ) * (-(vAdd v x : ℝ))) *
          (-1) / (Module.finrank ℚ K : ℝ) := by
      rw [Finset.sum_mul, Finset.sum_div]
      refine Finset.sum_congr rfl fun v _ => by ring
    rw [e, hlog]
    ring
  · intro v hv
    rw [Function.mem_support] at hv
    by_contra hc
    apply hv
    rw [hfs v hc]
    simp

section abelian₂

variable {K : Type} [Field K] [NumberField K] [StarRing K]

lemma eq_zero_of_orth (A : HLat K) (e : Module.End K A.V) (n : ℕ) (h : A.V →ₗ⋆[K] A.V →ₗ[K] K)
    (hH : IsHermE A e h) (hee : e * e = e) (hn : 0 < n) (S : Set A.V)
    (hS : Submodule.span K S = ⊤) (y : A.V) (hy : y ∈ LinearMap.range e)
    (h0 : ∀ g ∈ S, h (((n : ℕ) : 𝓞 K) • e g) y = 0) : y = 0 := by
  obtain ⟨hsym, hnd, hself⟩ := hH
  obtain ⟨z, rfl⟩ := hy
  have hez : e (e z) = e z := by
    show (e * e) z = e z
    rw [hee]
  have hS' : ∀ g ∈ S, h g (e z) = 0 := by
    intro g hg
    have := h0 g hg
    rw [h_smul_left, hself, hez] at this
    have hn0 : star (algebraMap (𝓞 K) K ((n : ℕ) : 𝓞 K)) ≠ 0 := by
      rw [map_natCast, star_natCast]
      exact_mod_cast hn.ne'
    exact (mul_eq_zero.1 this).resolve_left hn0
  have hall : ∀ x, h x (e z) = 0 := by
    intro x
    have hker : S ⊆ (LinearMap.ker (h.flip (e z)) : Set A.V) := by
      intro g hg
      rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.flip_apply]
      exact hS' g hg
    have hx : x ∈ LinearMap.ker (h.flip (e z)) := by
      have := Submodule.span_le.2 hker
      rw [hS] at this
      exact this Submodule.mem_top
    rwa [LinearMap.mem_ker, LinearMap.flip_apply] at hx
  apply hnd
  intro x
  rw [hsym x (e z), hall x, star_zero]

end abelian₂

theorem lattice_finitely_generated : LamFG := by
  intro K _ _ _ _ _ A e n h hyp U _
  obtain ⟨-, hP, hH, -⟩ := hyp
  obtain ⟨hG, hn, hee, hnL, -⟩ := hP
  obtain ⟨-, ⟨S, hS⟩, hLsp⟩ := hG
  have htop : Submodule.span K ((S : Set A.V)) = ⊤ := by
    rw [← Submodule.span_span_of_tower (𝓞 K), hS]
    exact hLsp
  set m : A.V → A.V := fun g => ((n : ℕ) : 𝓞 K) • e g with hm
  have hmM : ∀ g ∈ (S : Set A.V), m g ∈ cutE A e A.L := by
    intro g hg
    refine ⟨hnL g (hS ▸ Submodule.subset_span hg), ?_⟩
    exact Submodule.smul_of_tower_mem _ _ (LinearMap.mem_range_self e g)
  have hint : ∀ y ∈ lamSub A e h U, ∀ g ∈ (S : Set A.V), IsIntegral ℤ (h (m g) y) := by
    intro y hy g hg
    obtain ⟨c, hc⟩ := hy.2.2 (m g) (hmM g hg)
    rw [hH.1 y (m g), ← hc]
    exact RingOfIntegers.isIntegral_coe (starO K c)
  let Φ : lamSub A e h U →ₗ[𝓞 K] (S → 𝓞 K) :=
    { toFun := fun y g => ⟨h (m g) y, hint y y.2 g g.2⟩
      map_add' := by
        intro y1 y2
        funext g
        apply RingOfIntegers.ext
        simp only [Submodule.coe_add, map_add]
        rfl
      map_smul' := by
        intro c y
        funext g
        apply RingOfIntegers.ext
        show h (m g) ((c • y : lamSub A e h U) : A.V) = (c : K) * h (m g) y
        rw [Submodule.coe_smul, ← algebraMap_smul K c (y : A.V), map_smul, smul_eq_mul] }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply Subtype.ext
    refine eq_zero_of_orth A e n h hH hee hn (S : Set A.V) htop y y.2.1 fun g hg => ?_
    have := congrFun hy ⟨g, hg⟩
    exact congrArg (fun t : 𝓞 K => (t : K)) this
  have : IsNoetherian (𝓞 K) (lamSub A e h U) := isNoetherian_of_injective Φ hinj
  exact (Submodule.fg_top _).1 (IsNoetherian.noetherian _)

section Idx

open Formalism.HermitianLatticesTheory

variable {R : Type*} [CommRing R] {W W' : Type*} [AddCommGroup W] [Module R W]
  [AddCommGroup W'] [Module R W']

lemma mem_locP' (p : Ideal R) [p.IsPrime] {A : Submodule R W} {x : W} :
    x ∈ localization₂ p A ↔ ∃ s ∈ p.primeCompl, s • x ∈ A := Iff.rfl

lemma localization_map_of_injective (p : Ideal R) [p.IsPrime] (f : W →ₗ[R] W') (hf : Function.Injective f)
    (hsat : ∀ (s : R) (y : W'), s ∈ p.primeCompl → s • y ∈ LinearMap.range f →
      y ∈ LinearMap.range f)
    (A : Submodule R W) : localization₂ p (A.map f) = (localization₂ p A).map f := by
  ext y
  simp only [mem_locP', Submodule.mem_map]
  constructor
  · rintro ⟨s, hs, a, ha, hay⟩
    obtain ⟨x, rfl⟩ := hsat s y hs ⟨a, hay⟩
    refine ⟨x, ⟨s, hs, ?_⟩, rfl⟩
    have : f (s • x) = f a := by rw [map_smul, hay]
    rw [hf this]; exact ha
  · rintro ⟨x, ⟨s, hs, hx⟩, rfl⟩
    exact ⟨s, hs, s • x, hx, by rw [map_smul]⟩

lemma length_map_inj (f : W →ₗ[R] W') (hf : Function.Injective f) (X Z : Submodule R W) :
    Module.length R (↥(Z.map f) ⧸ (X.map f).comap (Z.map f).subtype) =
      Module.length R (↥Z ⧸ X.comap Z.subtype) := by
  symm
  refine LinearEquiv.length_eq
    (Submodule.Quotient.equiv _ _ (Submodule.equivMapOfInjective f hf Z) ?_)
  ext ⟨w, hw⟩
  obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hw
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨⟨z', hz'⟩, hz'X, he⟩
    have : f z' = f z := congrArg Subtype.val he
    rw [← hf this]
    exact ⟨z', hz'X, rfl⟩
  · rintro ⟨z', hz'X, he⟩
    refine ⟨⟨z, hz⟩, ?_, ?_⟩
    · have := hf he
      simpa [this] using hz'X
    · rfl

lemma lidx_map_inj (p : Ideal R) [p.IsPrime] (f : W →ₗ[R] W') (hf : Function.Injective f)
    (hsat : ∀ (s : R) (y : W'), s ∈ p.primeCompl → s • y ∈ LinearMap.range f →
      y ∈ LinearMap.range f)
    (A B : Submodule R W) : lidx p (A.map f) (B.map f) = lidx p A B := by
  unfold lidx locLen
  rw [← Submodule.map_inf f hf, localization_map_of_injective p f hf hsat, localization_map_of_injective p f hf hsat,
    localization_map_of_injective p f hf hsat, length_map_inj f hf, length_map_inj f hf]

lemma localization_eq_of_le_localization (p : Ideal R) [p.IsPrime] {X Y : Submodule R W} (h1 : X ≤ localization₂ p Y)
    (h2 : Y ≤ localization₂ p X) : localization₂ p X = localization₂ p Y := by
  unfold localization₂ at h1 h2 ⊢
  apply le_antisymm
  · calc locS p.primeCompl X ≤ locS p.primeCompl (locS p.primeCompl Y) :=
          locBasic_locS_mono _ h1
      _ = locS p.primeCompl Y := locBasic_locS_idem _ _
  · calc locS p.primeCompl Y ≤ locS p.primeCompl (locS p.primeCompl X) :=
          locBasic_locS_mono _ h2
      _ = locS p.primeCompl X := locBasic_locS_idem _ _

lemma lidx_zero_of_loc (p : Ideal R) [p.IsPrime] {X Y : Submodule R W} (h1 : X ≤ localization₂ p Y)
    (h2 : Y ≤ localization₂ p X) : lidx p X Y = 0 := by
  rw [PI.LatIdxDetW.lidx_congr p (localization_eq_of_le_localization p h1 h2) (rfl : localization₂ p Y = localization₂ p Y)]
  unfold lidx locLen
  simp

end Idx

section Add

open Formalism.HermitianLatticesTheory

variable {R K V : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem le_locS_of_span_le' (X Y : Submodule R V)
    (h : Submodule.span K (X : Set V) ≤ Submodule.span K (Y : Set V)) :
    X ≤ locS (nonZeroDivisors R) Y := by
  let T : Submodule K V :=
    { carrier := locS (nonZeroDivisors R) Y
      add_mem' := (locS (nonZeroDivisors R) Y).add_mem
      zero_mem' := (locS (nonZeroDivisors R) Y).zero_mem
      smul_mem' := by
        rintro c v ⟨d, hd, hdv⟩
        obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective R c
        have hb0 : algebraMap R K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
        refine ⟨b * d, Submonoid.mul_mem _ hb hd, ?_⟩
        have hc : algebraMap R K b * (algebraMap R K a / algebraMap R K b) = algebraMap R K a := by
          field_simp
        have : (b * d) • ((algebraMap R K a / algebraMap R K b) • v) = a • (d • v) := by
          rw [mul_comm, mul_smul, ← algebraMap_smul K b, smul_smul, hc, algebraMap_smul,
            smul_comm]
        rw [this]
        exact Y.smul_mem a hdv }
  have hle : Submodule.span K (Y : Set V) ≤ T :=
    Submodule.span_le.mpr (fun y hy => locBasic_le_locS _ Y hy)
  intro x hx
  exact hle (h (Submodule.subset_span hx))

theorem length_ne_top_of_le_locS' [IsNoetherianRing R] [Ring.KrullDimLE 1 R] (p : Ideal R)
    [p.IsPrime] (X Y : Submodule R V) (hX : X.FG) (hXY : X ≤ locS (nonZeroDivisors R) Y) :
    Module.length R (↥(localization₂ p X) ⧸ (localization₂ p Y).comap (localization₂ p X).subtype) ≠ ⊤ := by
  obtain ⟨d, hd, hdY⟩ := indexBasic_denom (nonZeroDivisors R) X Y hX hXY
  exact Module.length_ne_top_iff.mpr (indexBasic_finLen p X Y hX hd hdY)

theorem lidx_add_of_span_eq' [IsNoetherianRing R] [Ring.KrullDimLE 1 R] (p : Ideal R) [p.IsPrime]
    (A B C : Submodule R V) (hA : A.FG) (hB : B.FG) (hC : C.FG)
    (hAB : Submodule.span K (A : Set V) = Submodule.span K (B : Set V))
    (hBC : Submodule.span K (B : Set V) = Submodule.span K (C : Set V)) :
    lidx p A C = lidx p A B + lidx p B C := by
  have hD : ∀ X : Submodule R V, Submodule.span K (X : Set V) = Submodule.span K (A : Set V) →
      X ≤ locS (nonZeroDivisors R) (A ⊓ B ⊓ C) := by
    intro X hX
    rw [locBasic_locS_inf, locBasic_locS_inf]
    exact le_inf (le_inf (le_locS_of_span_le' (K := K) X A hX.le)
      (le_locS_of_span_le' (K := K) X B (hX.trans hAB).le))
      (le_locS_of_span_le' (K := K) X C (hX.trans (hAB.trans hBC)).le)
  have hAD := length_ne_top_of_le_locS' p A _ hA (hD A rfl)
  have hBD := length_ne_top_of_le_locS' p B _ hB (hD B hAB.symm)
  have hCD := length_ne_top_of_le_locS' p C _ hC (hD C (hAB.trans hBC).symm)
  rw [indexBasic_lidx_via p A C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left) inf_le_right
      hAD hCD,
    indexBasic_lidx_via p A B (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left)
      (le_trans inf_le_left inf_le_right) hAD hBD,
    indexBasic_lidx_via p B C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_right) inf_le_right
      hBD hCD]
  ring

end Add

section Gam

open Formalism.HermitianLatticesTheory

variable {K : Type} [Field K] [NumberField K]

lemma vAdd_mul' (w : HeightOneSpectrum (𝓞 K)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    vAdd w (x * y) = vAdd w x + vAdd w y := by
  unfold vAdd
  rw [map_mul, WithZero.log_mul (by simpa using hx) (by simpa using hy)]
  ring

lemma mem_iff_vAdd_pos (w : HeightOneSpectrum (𝓞 K)) {r : 𝓞 K} (hr : r ≠ 0) :
    r ∈ w.asIdeal ↔ 0 < vAdd w (algebraMap (𝓞 K) K r) := by
  rw [← HeightOneSpectrum.intValuation_lt_one_iff_mem]
  unfold vAdd
  rw [HeightOneSpectrum.valuation_of_algebraMap, w.intValuation_eq_exp_neg_multiplicity hr,
    WithZero.log_exp, neg_neg, ← WithZero.exp_zero, WithZero.exp_lt_exp, neg_lt_zero]

lemma conj_unique [StarRing K] {w a b : HeightOneSpectrum (𝓞 K)} (ha : IsConjPlK w a)
    (hb : IsConjPlK w b) : a = b := by
  have hv : ∀ x : K, vAdd a x = vAdd b x := fun x => by rw [ha x, hb x]
  ext r
  by_cases hr : r = 0
  · subst hr
    exact ⟨fun _ => b.asIdeal.zero_mem, fun _ => a.asIdeal.zero_mem⟩
  · rw [mem_iff_vAdd_pos a hr, mem_iff_vAdd_pos b hr, hv]

variable {V : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def combo {d : ℕ} (y : Fin d → V) : (Fin d → K) →ₗ[K] V where
  toFun c := ∑ i, c i • y i
  map_add' a b := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r a := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum,
    smul_smul]

lemma combo_apply {d : ℕ} (y : Fin d → V) (c : Fin d → K) : combo y c = ∑ i, c i • y i := rfl

lemma lidx_span_act (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (y : Fin d → V)
    (hy : LinearIndependent K y) (P : Matrix (Fin d) (Fin d) K) (hP : P.det ≠ 0) :
    lidx w.asIdeal (Submodule.span (𝓞 K) (Set.range y))
      (Submodule.span (𝓞 K) (Set.range fun j => ∑ k, P k j • y k)) = vAdd w P.det := by
  set E : Fin d → Fin d → K := fun i => Pi.single i 1 with hE
  have hEli : LinearIndependent K E := by
    convert (Pi.basisFun K (Fin d)).linearIndependent using 1
    funext i
    rw [Pi.basisFun_apply]
  have h1 := Formalism.DivisionValues.indexChange_of_det_ne_zero w P hP E hEli
  rw [← PI.LatIdxDetW.neg_log_valuation w hP] at h1
  set f : (Fin d → K) →ₗ[𝓞 K] V := (combo y).restrictScalars (𝓞 K) with hf
  have hfinj : Function.Injective f := by
    intro a b hab
    have h2 : combo y (a - b) = 0 := by
      rw [map_sub]; exact sub_eq_zero.2 hab
    rw [combo_apply] at h2
    have := (Fintype.linearIndependent_iff.1 hy) _ h2
    funext i
    exact sub_eq_zero.1 (this i)
  have hsat : ∀ (s : 𝓞 K) (v : V), s ∈ w.asIdeal.primeCompl → s • v ∈ LinearMap.range f →
      v ∈ LinearMap.range f := by
    intro s v hs hv
    have hs0 : algebraMap (𝓞 K) K s ≠ 0 := by
      intro h0
      apply hs
      have : s = 0 := by simpa using h0
      rw [this]; exact w.asIdeal.zero_mem
    obtain ⟨x, hx⟩ := hv
    refine ⟨(algebraMap (𝓞 K) K s)⁻¹ • x, ?_⟩
    show combo y ((algebraMap (𝓞 K) K s)⁻¹ • x) = v
    rw [map_smul]
    have hx' : combo y x = s • v := hx
    rw [hx', ← algebraMap_smul K s v, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  have hfE : ∀ i, f (E i) = y i := by
    intro i
    show combo y (Pi.single i 1) = y i
    rw [combo_apply]
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, zero_smul])
      (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, one_smul]
  have hfA : ∀ j, f (Formalism.DivisionValues.idxChangeAct E P j) = ∑ k, P k j • y k := by
    intro j
    show combo y (∑ k, P k j • E k) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul]
    congr 1
    exact hfE k
  have e1 : Submodule.span (𝓞 K) (Set.range y) = (Submodule.span (𝓞 K) (Set.range E)).map f := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 1
    ext v
    simp only [Set.mem_range, Function.comp_apply, hfE]
  have e2 : Submodule.span (𝓞 K) (Set.range fun j => ∑ k, P k j • y k) =
      (Submodule.span (𝓞 K) (Set.range (Formalism.DivisionValues.idxChangeAct E P))).map f := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 1
    ext v
    simp only [Set.mem_range, Function.comp_apply, hfA]
  rw [e1, e2, lidx_map_inj w.asIdeal f hfinj hsat, h1]
  rfl

end Gam

open Formalism.HermitianLatticesTheory in
theorem localGamma_of_gramCS (hG : GramCS) : LocalGamma := by
  intro K _ _ _ _ _ A e n h hyp U hU d y hy hyL hspan w k hk w' hw'
  obtain ⟨w'', hw'', d'', y'', hy'', hloc, hkk⟩ := hk
  have hww : w'' = w' := conj_unique hw'' hw'
  subst hww
  subst hkk
  set L := lamSub A e h U with hL
  have hLfg : L.FG := lattice_finitely_generated K A e n h hyp U hU
  have hlw := hloc w (Set.mem_insert _ _)
  have hlw' := hloc w'' (Set.mem_insert_of_mem _ rfl)
  have hs0 : ∀ s : 𝓞 K, s ∉ w.asIdeal → algebraMap (𝓞 K) K s ≠ 0 := by
    intro s hs h0
    apply hs
    have : s = 0 := by simpa using h0
    rw [this]; exact w.asIdeal.zero_mem

  have hmem1 : ∀ i, y'' i ∈ Submodule.span K (Set.range y) := by
    intro i
    obtain ⟨s, hs, hsL⟩ := hlw.1 i
    have h1 : s • y'' i ∈ Submodule.span K (Set.range y) := by
      rw [← hspan]; exact Submodule.subset_span hsL
    have h2 : y'' i = (algebraMap (𝓞 K) K s)⁻¹ • (s • y'' i) := by
      rw [← algebraMap_smul K s (y'' i), smul_smul, inv_mul_cancel₀ (hs0 s hs), one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ h1
  have hmem2 : ∀ i, y i ∈ Submodule.span K (Set.range y'') := by
    intro i
    obtain ⟨s, hs, hsL⟩ := hlw.2 (y i) (hyL i)
    have h1 : s • y i ∈ Submodule.span K (Set.range y'') :=
      Submodule.span_subset_span (𝓞 K) K _ hsL
    have h2 : y i = (algebraMap (𝓞 K) K s)⁻¹ • (s • y i) := by
      rw [← algebraMap_smul K s (y i), smul_smul, inv_mul_cancel₀ (hs0 s hs), one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ h1
  have hsp : Submodule.span K (Set.range y'') = Submodule.span K (Set.range y) :=
    le_antisymm (Submodule.span_le.2 (Set.range_subset_iff.2 hmem1))
      (Submodule.span_le.2 (Set.range_subset_iff.2 hmem2))
  have hdd : d'' = d := by
    have a1 := finrank_span_eq_card hy''
    have a2 := finrank_span_eq_card hy
    rw [hsp, a2] at a1
    simpa using a1.symm
  subst hdd

  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun K).1 (hmem1 j)
  set P : Matrix (Fin d'') (Fin d'') K := Matrix.of fun k j => c j k with hPdef
  have hP : ∀ j, ∑ k, P k j • y k = y'' j := fun j => hc j
  have hgram : (Matrix.of fun i j => h (y'' i) (y'' j)) =
      P.conjTranspose * (Matrix.of fun i j => h (y i) (y j)) * P := by
    ext i j
    simp only [Matrix.of_apply]
    rw [← hP i, ← hP j]
    simp only [Matrix.of_apply, map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply,
      smul_eq_mul, starRingEnd_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Finset.mul_sum, Finset.sum_mul, RingHom.id_apply]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hdet : (Matrix.of fun i j => h (y'' i) (y'' j)).det =
      star P.det * (Matrix.of fun i j => h (y i) (y j)).det * P.det := by
    rw [hgram, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]
  have hG1 := (hG K A e n h hyp d'' y hy).1
  have hG2 := (hG K A e n h hyp d'' y'' hy'').1
  have hP0 : P.det ≠ 0 := by
    intro h0; apply hG2; rw [hdet, h0]; simp
  have hsP0 : star P.det ≠ 0 := by simpa using hP0

  have hOy : Submodule.span K ((Submodule.span (𝓞 K) (Set.range y) : Submodule (𝓞 K) A.V) : Set A.V)
      = Submodule.span K (Set.range y) := Submodule.span_span_of_tower _ _ _
  have hOy'' : Submodule.span K ((Submodule.span (𝓞 K) (Set.range y'') : Submodule (𝓞 K) A.V) :
      Set A.V) = Submodule.span K (Set.range y) := by
    rw [Submodule.span_span_of_tower]; exact hsp
  have hfg1 : (Submodule.span (𝓞 K) (Set.range y)).FG := Submodule.fg_span (Set.finite_range _)
  have hfg2 : (Submodule.span (𝓞 K) (Set.range y'')).FG := Submodule.fg_span (Set.finite_range _)
  have hy''eq : (Set.range fun j => ∑ k, P k j • y k) = Set.range y'' := by
    congr 1; funext j; exact hP j
  have hidx : ∀ u ∈ ({w, w''} : Set (HeightOneSpectrum (𝓞 K))),
      lidx u.asIdeal (Submodule.span (𝓞 K) (Set.range y)) L = vAdd u P.det := by
    intro u hu
    have hlu := hloc u hu
    rw [lidx_add_of_span_eq' (K := K) u.asIdeal _ (Submodule.span (𝓞 K) (Set.range y'')) L hfg1
      hfg2 hLfg (hOy.trans hOy''.symm) (hOy''.trans hspan.symm)]
    have z1 : lidx u.asIdeal (Submodule.span (𝓞 K) (Set.range y''))
        L = 0 := by
      apply lidx_zero_of_loc
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact hlu.1 i
      · intro z hz
        exact hlu.2 z hz
    rw [z1, add_zero, ← hy''eq, lidx_span_act u y hy P hP0]
  rw [hidx w (Set.mem_insert _ _), hidx w'' (Set.mem_insert_of_mem _ rfl), hdet,
    vAdd_mul' w (mul_ne_zero hsP0 hG1) hP0, vAdd_mul' w hsP0 hG1, ← hw'' P.det]
  ring

end PI.DvRows
