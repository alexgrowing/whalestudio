import ReciprocityTheory.NeutralLocalFields.Reciprocity
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HilbertClassFieldA

noncomputable section

open NumberField IsDedekindDomain Neutral.B1
open scoped nonZeroDivisors

namespace ReciprocityTheory.Neutral.Bridge.HCFR

variable (K : Type) [Field K] [NumberField K]

theorem comp_mul (a b : Ideles K) (v : HeightOneSpectrum (𝓞 K)) :
    ((a * b : Ideles K) : AdeleRing (𝓞 K) K).2 v = (a : AdeleRing (𝓞 K) K).2 v * (b : AdeleRing (𝓞 K) K).2 v := rfl

theorem comp_one (v : HeightOneSpectrum (𝓞 K)) : ((1 : Ideles K) : AdeleRing (𝓞 K) K).2 v = 1 := rfl

theorem comp_mul_inv (a : Ideles K) (v : HeightOneSpectrum (𝓞 K)) :
    (a : AdeleRing (𝓞 K) K).2 v * (a⁻¹ : Ideles K).val.2 v = 1 := by
  rw [← comp_mul K a a⁻¹ v, mul_inv_cancel, comp_one]

theorem comp_ne_zero (a : Ideles K) (v : HeightOneSpectrum (𝓞 K)) : (a : AdeleRing (𝓞 K) K).2 v ≠ 0 := by
  intro h
  have := comp_mul_inv K a v
  rw [h, zero_mul] at this
  exact zero_ne_one this

theorem valued_comp_ne_zero (a : Ideles K) (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((a : AdeleRing (𝓞 K) K).2 v) ≠ 0 := (Valuation.ne_zero_iff _).mpr (comp_ne_zero K a v)

theorem valued_comp_eventually (a : Ideles K) :
    ∀ᶠ v in Filter.cofinite, Valued.v ((a : AdeleRing (𝓞 K) K).2 v) = 1 := by
  have h1 := ((a : AdeleRing (𝓞 K) K).2).2
  have h2 := (((a⁻¹ : Ideles K) : AdeleRing (𝓞 K) K).2).2
  filter_upwards [h1, h2] with v hv1 hv2
  have e1 : Valued.v ((a : AdeleRing (𝓞 K) K).2 v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp hv1
  have e2 : Valued.v (((a⁻¹ : Ideles K) : AdeleRing (𝓞 K) K).2 v) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp hv2
  have e3 : Valued.v ((a : AdeleRing (𝓞 K) K).2 v) * Valued.v (((a⁻¹ : Ideles K) : AdeleRing (𝓞 K) K).2 v) = 1 := by
    rw [← map_mul, comp_mul_inv, map_one]
  refine le_antisymm e1 ?_
  calc (1 : _) = _ := e3.symm
    _ ≤ _ := mul_le_of_le_one_right' e2

def ordAt (v : HeightOneSpectrum (𝓞 K)) (a : Ideles K) : ℤ :=
  -WithZero.log (Valued.v ((a : AdeleRing (𝓞 K) K).2 v))

theorem ordAt_mul (v : HeightOneSpectrum (𝓞 K)) (a b : Ideles K) :
    ordAt K v (a * b) = ordAt K v a + ordAt K v b := by
  simp only [ordAt, comp_mul, map_mul,
    WithZero.log_mul (valued_comp_ne_zero K a v) (valued_comp_ne_zero K b v)]
  ring

theorem ordAt_one (v : HeightOneSpectrum (𝓞 K)) : ordAt K v 1 = 0 := by
  rw [ordAt, comp_one]
  simp

theorem ordAt_eq_zero_iff (v : HeightOneSpectrum (𝓞 K)) (a : Ideles K) :
    ordAt K v a = 0 ↔ Valued.v ((a : AdeleRing (𝓞 K) K).2 v) = 1 := by
  have hne := valued_comp_ne_zero K a v
  unfold ordAt
  rw [neg_eq_zero]
  constructor
  · intro h
    rw [← WithZero.exp_log hne, h, WithZero.exp_zero]
  · intro h
    rw [h, WithZero.log_one]

theorem ordAt_eventually (a : Ideles K) : ∀ᶠ v in Filter.cofinite, ordAt K v a = 0 := by
  exact (valued_comp_eventually K a).mono fun v hv => (ordAt_eq_zero_iff K v a).mpr hv

theorem rayUnits_top_iff (u : Ideles K) :
    u ∈ rayUnits K ⊤ ∅ ↔ ∀ v : HeightOneSpectrum (𝓞 K), Valued.v ((u : AdeleRing (𝓞 K) K).2 v) = 1 := by
  constructor
  · intro h v
    exact (h.2 v).1
  · intro h
    refine ⟨fun w hw => absurd hw (Set.notMem_empty w), fun v => ⟨h v, 1, Submodule.mem_top, ?_⟩⟩
    have h1 : Valued.v (algebraMap K (v.adicCompletion K) (((1 : 𝓞 K)) : K)) = 1 := by simp
    rw [h1]
    refine (Valuation.map_sub _ _ _).trans ?_
    simp [h v]

def idealFI (a : Ideles K) : FractionalIdeal (𝓞 K)⁰ K :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K), (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ ordAt K v a

theorem prime_ne_zero (v : HeightOneSpectrum (𝓞 K)) : (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
  exact v.ne_bot

theorem mulSupport_finite (a : Ideles K) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) =>
      (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) ^ ordAt K v a).Finite := by
  refine (Filter.eventually_cofinite.mp (ordAt_eventually K a)).subset ?_
  intro v hv h
  apply hv
  simp [h]

theorem idealFI_ne_zero (a : Ideles K) : idealFI K a ≠ 0 := by
  rw [idealFI, finprod_eq_prod _ (mulSupport_finite K a)]
  exact Finset.prod_ne_zero_iff.mpr fun v _ => zpow_ne_zero _ (prime_ne_zero K v)

theorem idealFI_mul (a b : Ideles K) : idealFI K (a * b) = idealFI K a * idealFI K b := by
  simp only [idealFI, ordAt_mul, zpow_add₀ (prime_ne_zero K _)]
  exact finprod_mul_distrib (mulSupport_finite K a) (mulSupport_finite K b)

theorem idealFI_one : idealFI K 1 = 1 := by
  simp [idealFI, ordAt_one]

theorem count_idealFI (v : HeightOneSpectrum (𝓞 K)) (a : Ideles K) :
    FractionalIdeal.count K v (idealFI K a) = ordAt K v a := FractionalIdeal.count_finprod K v (fun w => ordAt K w a) (ordAt_eventually K a)

def idealOf : Ideles K →* (FractionalIdeal (𝓞 K)⁰ K)ˣ where
  toFun a := Units.mk0 (idealFI K a) (idealFI_ne_zero K a)
  map_one' := Units.ext (idealFI_one K)
  map_mul' a b := Units.ext (idealFI_mul K a b)

def classOf : Ideles K →* ClassGroup (𝓞 K) := (ClassGroup.mk (K := K)).comp (idealOf K)

theorem eq_of_count {I J : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), FractionalIdeal.count K v I = FractionalIdeal.count K v J) : I = J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI,
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ]
  exact finprod_congr fun v => by rw [h v]

theorem count_spanSingleton (v : HeightOneSpectrum (𝓞 K)) {x : K} (hx : x ≠ 0) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) = -WithZero.log (v.valuation K x) := by
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (𝓞 K)⁰ x
  dsimp only at hx ⊢
  have hr : r ≠ 0 := by
    rintro rfl
    simp at hx
  have hs : (s : 𝓞 K) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  rw [FractionalIdeal.count_well_defined K v (a := (s : 𝓞 K)) (J := Ideal.span {r})
    (by rwa [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]) ?_]
  · rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_mk',
      IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg v hr,
      IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg v hs, ← WithZero.exp_sub, WithZero.log_exp]
    ring
  · rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton,
      IsFractionRing.mk'_eq_div, div_eq_inv_mul]

theorem diag_comp (k : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    Valued.v ((diagUnits K k : AdeleRing (𝓞 K) K).2 v) = v.valuation K (k : K) := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (k : K)

theorem ordAt_diag (k : Kˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ordAt K v (diagUnits K k) = -WithZero.log (v.valuation K (k : K)) := by
  unfold ordAt
  rw [diag_comp]

theorem ordAt_inv (v : HeightOneSpectrum (𝓞 K)) (a : Ideles K) : ordAt K v a⁻¹ = -ordAt K v a := by
  have h := ordAt_mul K v a a⁻¹
  rw [mul_inv_cancel, ordAt_one] at h
  linarith

theorem classOf_eq_one_iff (a : Ideles K) :
    classOf K a = 1 ↔ ∃ k : Kˣ, ∃ u ∈ rayUnits K ⊤ ∅, a = diagUnits K k * u := by
  have key : ∀ k : Kˣ, idealFI K (diagUnits K k) = FractionalIdeal.spanSingleton (𝓞 K)⁰ (k : K) := by
    intro k
    apply eq_of_count K (idealFI_ne_zero K _) (by rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact k.ne_zero)
    intro v
    rw [count_idealFI, ordAt_diag, count_spanSingleton K v k.ne_zero]
  have hone : ∀ u ∈ rayUnits K ⊤ ∅, idealFI K u = 1 := by
    intro u hu
    rw [rayUnits_top_iff] at hu
    apply eq_of_count K (idealFI_ne_zero K _) one_ne_zero
    intro v
    rw [count_idealFI, FractionalIdeal.count_one, (ordAt_eq_zero_iff K v u).mpr (hu v)]
  constructor
  · intro h
    rw [classOf, MonoidHom.comp_apply, ClassGroup.mk_eq_one_iff] at h
    obtain ⟨x, hx⟩ := h.principal
    have hI : idealFI K a = FractionalIdeal.spanSingleton (𝓞 K)⁰ x := by
      apply FractionalIdeal.coeToSubmodule_injective
      show ((idealFI K a : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) =
        ((FractionalIdeal.spanSingleton (𝓞 K)⁰ x : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)
      rw [FractionalIdeal.coe_spanSingleton]
      exact hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      apply idealFI_ne_zero K a
      rw [hI, FractionalIdeal.spanSingleton_zero]
    refine ⟨Units.mk0 x hx0, (diagUnits K (Units.mk0 x hx0))⁻¹ * a, ?_, (mul_inv_cancel_left _ _).symm⟩
    rw [rayUnits_top_iff]
    intro v
    rw [← ordAt_eq_zero_iff, ordAt_mul, ordAt_inv, ordAt_diag, Units.val_mk0, ← count_spanSingleton K v hx0,
      ← hI, count_idealFI]
    ring
  · rintro ⟨k, u, hu', rfl⟩
    rw [classOf, MonoidHom.comp_apply, ClassGroup.mk_eq_one_iff]
    have h2 : ((idealOf K (diagUnits K k * u) : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ (k : K) := by
      show idealFI K _ = _
      rw [idealFI_mul, key, hone u hu', mul_one]
    rw [h2, FractionalIdeal.coe_spanSingleton]
    exact ⟨⟨k, rfl⟩⟩

private theorem isUnit_of_valued_eq_one (v : HeightOneSpectrum (𝓞 K)) (y : v.adicCompletionIntegers K)
    (hy : Valued.v (y : v.adicCompletion K) = 1) : IsUnit y := by
  have hy0 : (y : v.adicCompletion K) ≠ 0 := by
    intro h
    rw [h, map_zero] at hy
    exact zero_ne_one hy
  have hinv : (y : v.adicCompletion K)⁻¹ ∈ v.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hy, inv_one]
  have h1 : y * ⟨_, hinv⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hy0)
  exact ⟨⟨y, ⟨_, hinv⟩, h1, by rw [mul_comm]; exact h1⟩, rfl⟩

private theorem valued_eq_one_of_isUnit' (v : HeightOneSpectrum (𝓞 K)) (y : v.adicCompletionIntegers K)
    (hy : IsUnit y) : Valued.v (y : v.adicCompletion K) = 1 := by
  obtain ⟨u, rfl⟩ := hy
  have h1 : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp (u : v.adicCompletionIntegers K).2
  have h2 : Valued.v (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) : v.adicCompletion K) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp ((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K).2
  have h3 : Valued.v ((u : v.adicCompletionIntegers K) : v.adicCompletion K) *
      Valued.v (((u⁻¹ : (v.adicCompletionIntegers K)ˣ) : v.adicCompletionIntegers K) : v.adicCompletion K) = 1 := by
    rw [← map_mul]
    exact (congrArg (fun t : v.adicCompletionIntegers K => Valued.v (t : v.adicCompletion K)) u.mul_inv).trans (map_one _)
  refine le_antisymm h1 ?_
  calc (1 : _) = _ := h3.symm
    _ ≤ _ := mul_le_of_le_one_right' h2

theorem valued_eq_exp_of_isUniformiserAt (v : HeightOneSpectrum (𝓞 K)) (x : v.adicCompletion K)
    (hx : IsUniformiserAt K v x) : Valued.v x = WithZero.exp (-1 : ℤ) := by
  obtain ⟨hxO, hirr⟩ := hx
  have hle : Valued.v x ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 K) K v).mp hxO
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hirr.ne_zero (Subtype.ext rfl)
  have hne1 : Valued.v x ≠ 1 := fun h => hirr.not_isUnit (isUnit_of_valued_eq_one K v _ h)
  obtain ⟨π, hπ⟩ := IsDedekindDomain.HeightOneSpectrum.intValuation_exists_uniformizer v
  have hy' := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := K) v π
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap, hπ] at hy'
  obtain ⟨y, hy⟩ : ∃ y : v.adicCompletion K, Valued.v y = WithZero.exp (-1 : ℤ) := ⟨_, hy'⟩
  have hw0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
  have hlog : WithZero.log (Valued.v x) ≤ 0 := by
    rw [← WithZero.exp_le_exp, WithZero.exp_log hw0, WithZero.exp_zero]
    exact hle
  have hlog1 : WithZero.log (Valued.v x) ≠ 0 := by
    intro h
    apply hne1
    rw [← WithZero.exp_log hw0, h, WithZero.exp_zero]
  rw [← WithZero.exp_log hw0]
  congr 1
  by_contra hne
  have hy0 : y ≠ 0 := by
    intro h
    rw [h, map_zero] at hy
    exact WithZero.exp_ne_zero hy.symm
  have hyO : y ∈ v.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hy, ← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  have hzO : x / y ∈ v.adicCompletionIntegers K := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀, hy, ← WithZero.exp_log hw0, ← WithZero.exp_sub,
      ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have hsplit : (⟨x, hxO⟩ : v.adicCompletionIntegers K) = ⟨y, hyO⟩ * ⟨x / y, hzO⟩ := by
    apply Subtype.ext
    show x = y * (x / y)
    field_simp
  rcases hirr.isUnit_or_isUnit hsplit with h | h
  · have h1 := valued_eq_one_of_isUnit' K v _ h
    change Valued.v y = 1 at h1
    rw [hy] at h1
    have h2 := congrArg WithZero.log h1
    simp at h2
  · have h1 := valued_eq_one_of_isUnit' K v _ h
    change Valued.v (x / y) = 1 at h1
    rw [map_div₀, hy, ← WithZero.exp_log hw0, ← WithZero.exp_sub] at h1
    have h2 := congrArg WithZero.log h1
    simp only [WithZero.log_exp, WithZero.log_one] at h2
    omega

open Classical in
theorem ordAt_localIdele (v w : HeightOneSpectrum (𝓞 K)) (π : (v.adicCompletion K)ˣ)
    (hπ : IsUniformiserAt K v (π : v.adicCompletion K)) :
    ordAt K w (localIdele K v π) = if w = v then 1 else 0 := by
  unfold ordAt
  split_ifs with h
  · subst h
    have hc : ((localIdele K w π : Ideles K) : AdeleRing (𝓞 K) K).2 w = π :=
      RestrictedProduct.mulSingle_eq_same _ _ _
    rw [hc, valued_eq_exp_of_isUniformiserAt K w _ hπ, WithZero.log_exp]
    norm_num
  · have hc : ((localIdele K v π : Ideles K) : AdeleRing (𝓞 K) K).2 w = 1 :=
      RestrictedProduct.mulSingle_eq_of_ne _ _ h
    rw [hc]
    simp

end ReciprocityTheory.Neutral.Bridge.HCFR
