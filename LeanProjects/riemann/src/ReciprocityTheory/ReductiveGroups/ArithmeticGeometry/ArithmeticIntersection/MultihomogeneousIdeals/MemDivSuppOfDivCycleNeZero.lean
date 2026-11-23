import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LengthCokerEqKerAddDimOneOrderSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AI.I1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]

theorem mem_divSupp_of_divCycle_ne_zero {V W : Ideal (MRingOver F ι)} {f : MRingOver F ι}
    (h : divCycle V f W ≠ 0) : W ∈ divSupp V f := by
  classical
  by_contra hW
  exact h (by simp [divCycle, Finsupp.ofSupportFinite_coe, hW])

section DivMul

variable {R : Type*} [CommRing R]

def mulQ (V : Ideal R) (f g : R) : (R ⧸ (V ⊔ Ideal.span {g})) →ₗ[R] (R ⧸ (V ⊔ Ideal.span {f * g})) :=
  Submodule.mapQ _ _ (LinearMap.mulLeft R f) fun x hx => by
    have h : Ideal.span {f} * (V ⊔ Ideal.span {g}) ≤ V ⊔ Ideal.span {f * g} := by
      rw [Ideal.mul_sup, Ideal.span_singleton_mul_span_singleton]
      exact sup_le_sup_right (Ideal.mul_le.mpr fun a _ b hb => V.mul_mem_left a hb) _
    exact h (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self f) hx)

theorem mulQ_injective {V : Ideal R} (hV : V.IsPrime) {f : R} (hf : f ∉ V) (g : R) :
    Function.Injective (mulQ V f g) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [LinearMap.mem_ker, mulQ, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
  obtain ⟨v, hv, w, hw, hvw⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hw
  have h1 : f * (x - c * g) ∈ V := by
    have : f * (x - c * g) = v := by
      simp only [LinearMap.mulLeft_apply] at hvw
      linear_combination -hvw
    rw [this]; exact hv
  have h2 : x - c * g ∈ V := (hV.mem_or_mem h1).resolve_left hf
  have : x = (x - c * g) + c * g := by ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mem_sup_left h2)
    (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self g)))

theorem sup_span_mul_le (V : Ideal R) (f g : R) :
    V ⊔ Ideal.span {f * g} ≤ V ⊔ Ideal.span {f} :=
  sup_le_sup_left (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right f g)) V

theorem mulQ_exact (V : Ideal R) (f g : R) :
    Function.Exact (mulQ V f g) (Submodule.factor (sup_span_mul_le V f g)) := by
  intro y
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  change (Submodule.Quotient.mk y : R ⧸ (V ⊔ Ideal.span {f})) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hy
    obtain ⟨v, hv, w, hw, hvw⟩ := Submodule.mem_sup.mp hy
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hw
    refine ⟨Submodule.Quotient.mk c, ?_⟩
    rw [mulQ, Submodule.mapQ_apply, Submodule.Quotient.eq]
    simp only [LinearMap.mulLeft_apply]
    have : f * c - y = -v := by linear_combination hvw
    rw [this]
    exact Submodule.neg_mem _ (Ideal.mem_sup_left hv)
  · rintro ⟨x, hx⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [mulQ, Submodule.mapQ_apply, LinearMap.mulLeft_apply, Submodule.Quotient.eq] at hx
    have h1 := sup_span_mul_le V f g hx
    have h2 : f * x ∈ V ⊔ Ideal.span {f} :=
      Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f))
    have e : y = f * x - (f * x - y) := by ring
    rw [e]
    exact Submodule.sub_mem _ h2 h1

theorem locLen_mul {V : Ideal R} (hV : V.IsPrime) {f : R} (hf : f ∉ V) (g : R) (p : PrimeSpectrum R) :
    locLen (R ⧸ (V ⊔ Ideal.span {f * g})) p =
      locLen (R ⧸ (V ⊔ Ideal.span {g})) p + locLen (R ⧸ (V ⊔ Ideal.span {f})) p :=
  locLen_add _ _ (mulQ_injective hV hf g) (Submodule.factor_surjective _) (mulQ_exact V f g) p

theorem locLen_ne_top [IsNoetherianRing R] {J W : Ideal R} (hW : W ∈ J.minimalPrimes) :
    locLen (R ⧸ J) ⟨W, hW.1.1⟩ ≠ ⊤ := by
  have := hW.1.1
  let A := Localization.AtPrime W
  have : IsNoetherianRing A := IsLocalization.isNoetherianRing W.primeCompl A inferInstance
  have : Module.Finite A (LocalizedModule W.primeCompl (R ⧸ J)) :=
    Module.Finite.of_isLocalizedModule W.primeCompl (LocalizedModule.mkLinearMap W.primeCompl _)
  unfold locLen
  rw [length_ne_top_iff_support]
  intro p hp
  rw [Module.mem_support_iff_of_finite] at hp
  have hJ : J ≤ p.asIdeal.comap (algebraMap R A) := by
    intro r hr
    refine hp (Module.mem_annihilator.mpr fun n => ?_)
    induction n using LocalizedModule.induction_on with
    | h m s =>
      rw [algebraMap_smul, LocalizedModule.smul'_mk]
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ m
      rw [← Submodule.Quotient.mk_smul, (Submodule.Quotient.mk_eq_zero _).mpr
        (show r • m ∈ J from J.mul_mem_right m hr), LocalizedModule.zero_mk]
  have hle : p.asIdeal.comap (algebraMap R A) ≤ W := by
    have hm : (IsLocalRing.maximalIdeal A).comap (algebraMap R A) = W :=
      Localization.AtPrime.under_maximalIdeal
    exact (Ideal.comap_mono (IsLocalRing.le_maximalIdeal p.isPrime.ne_top)).trans hm.le
  have heq : p.asIdeal.comap (algebraMap R A) = W :=
    le_antisymm hle (hW.2 ⟨Ideal.comap_isPrime _ _, hJ⟩ hle)
  have : p.asIdeal = IsLocalRing.maximalIdeal A := by
    calc p.asIdeal = (p.asIdeal.comap (algebraMap R A)).map (algebraMap R A) :=
          (IsLocalization.map_under W.primeCompl A p.asIdeal).symm
      _ = W.map (algebraMap R A) := congrArg (Ideal.map (algebraMap R A)) heq
      _ = IsLocalRing.maximalIdeal A := Localization.AtPrime.map_eq_maximalIdeal
  rw [this]
  exact IsLocalRing.maximalIdeal.isMaximal A

end DivMul

theorem multAt_eq (J W : Ideal (MRingOver F ι)) (hW : W.IsPrime) :
    multAt J W = (locLen (MRingOver F ι ⧸ J) ⟨W, hW⟩).toNat := by
  simp [multAt, hW, locLen]

section DivMul2

variable {R : Type*} [CommRing R]

theorem map_mk_mem_minimalPrimes {V W : Ideal R} {f : R} (hW : W ∈ (V ⊔ Ideal.span {f}).minimalPrimes) :
    W.map (Ideal.Quotient.mk V) ∈ (Ideal.span {Ideal.Quotient.mk V f}).minimalPrimes := by
  have e : Ideal.span {Ideal.Quotient.mk V f} = (Ideal.span {f}).map (Ideal.Quotient.mk V) := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [e, Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_comm]
  exact ⟨W, hW, rfl⟩

theorem comap_map_mk_of_le {V Q : Ideal R} (h : V ≤ Q) :
    (Q.map (Ideal.Quotient.mk V)).comap (Ideal.Quotient.mk V) = Q := by
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
    Ideal.mk_ker, sup_eq_left.mpr h]

theorem eq_of_le_of_mem_minimalPrimes [IsNoetherianRing R] {V W Q : Ideal R} (hV : V.IsPrime) {f g : R}
    (hW : W ∈ (V ⊔ Ideal.span {f}).minimalPrimes) (hQ : Q.IsPrime) (hVQ : V ≤ Q) (hgQ : g ∈ Q)
    (hgV : g ∉ V) (hQW : Q ≤ W) : Q = W := by
  by_contra hne
  let π := Ideal.Quotient.mk V
  have hW' := map_mk_mem_minimalPrimes hW
  have : (W.map π).IsPrime := hW'.1.1
  have : (Ideal.span {π f}).IsPrincipal := ⟨⟨_, rfl⟩⟩
  have h1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hW'
  have : (Q.map π).IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hVQ)
  have hVW : V ≤ W := le_sup_left.trans hW.1.2
  have hlt : Q.map π < W.map π := by
    refine lt_of_le_of_ne (Ideal.map_mono hQW) fun e => hne ?_
    rw [← comap_map_mk_of_le hVQ, e, comap_map_mk_of_le hVW]
  have hbot : (⊥ : Ideal (R ⧸ V)) < Q.map π := by
    refine bot_lt_iff_ne_bot.mpr fun e => hgV ?_
    have : π g ∈ Q.map π := Ideal.mem_map_of_mem _ hgQ
    rw [e, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    exact this
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h3 := Ideal.height_add_one_le_of_lt_of_isPrime hbot
  have h4 : (2 : ℕ∞) ≤ (W.map π).height := by
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ (⊥ : Ideal (R ⧸ V)).height + 1 + 1 := by gcongr; exact zero_le
      _ ≤ (Q.map π).height + 1 := by gcongr
      _ ≤ _ := h2
  have := h4.trans h1
  norm_num at this

theorem mem_divSupp_mul_left {V W : Ideal (MRingOver F ι)} (hV : V.IsPrime) {f g : MRingOver F ι}
    (hgV : g ∉ V) (hW : W ∈ divSupp V f) : W ∈ divSupp V (f * g) := by
  refine ⟨⟨⟨hW.1.1.1, (sup_span_mul_le V f g).trans hW.1.1.2⟩, fun Q hQ hQW => ?_⟩, hW.2⟩
  have hfg : f * g ∈ Q := hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  rcases hQ.1.mem_or_mem hfg with hf | hg
  · exact hW.1.2 ⟨hQ.1, sup_le (le_sup_left.trans hQ.2) (Ideal.span_singleton_le_iff_mem _ |>.mpr hf)⟩
      hQW
  · exact (eq_of_le_of_mem_minimalPrimes hV hW.1 hQ.1 (le_sup_left.trans hQ.2) hg hgV hQW).ge

theorem mem_divSupp_of_mul {V W : Ideal (MRingOver F ι)} {f g : MRingOver F ι}
    (hW : W ∈ divSupp V (f * g)) (hf : f ∈ W) : W ∈ divSupp V f :=
  ⟨⟨⟨hW.1.1.1, sup_le (le_sup_left.trans hW.1.1.2) (Ideal.span_singleton_le_iff_mem _ |>.mpr hf)⟩,
    fun Q hQ hQW => hW.1.2 ⟨hQ.1, (sup_span_mul_le V f g).trans hQ.2⟩ hQW⟩, hW.2⟩

theorem mem_of_mem_divSupp {V W : Ideal (MRingOver F ι)} {f : MRingOver F ι} (hW : W ∈ divSupp V f) :
    f ∈ W :=
  hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))

theorem locLen_quot_eq_zero {V : Ideal R} {g : R} (p : PrimeSpectrum R) (hg : g ∉ p.asIdeal) :
    locLen (R ⧸ (V ⊔ Ideal.span {g})) p = 0 := by
  refine locLen_eq_zero_of_notMem p fun hp => hg ?_
  rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient, PrimeSpectrum.mem_zeroLocus] at hp
  exact hp (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))

end DivMul2

theorem divCycle_mul {V : Ideal (MRingOver F ι)} (hV : V.IsPrime) {f g : MRingOver F ι}
    (hf : f ∉ V) (hg : g ∉ V) : divCycle V (f * g) = divCycle V f + divCycle V g := by
  classical
  ext W
  simp only [Finsupp.add_apply, divCycle, Finsupp.ofSupportFinite_coe]
  by_cases h : W ∈ divSupp V (f * g)
  · have hWp := h.1.1.1
    have h' : W ∈ divSupp V (g * f) := by rwa [mul_comm]
    have key := locLen_mul hV hf g ⟨W, hWp⟩
    have hfin := locLen_ne_top h.1
    rw [key] at hfin
    rw [if_pos h, multAt_eq _ _ hWp, key]
    by_cases hfW : f ∈ W <;> by_cases hgW : g ∈ W
    · rw [if_pos (mem_divSupp_of_mul h hfW), if_pos (mem_divSupp_of_mul h' hgW),
        multAt_eq _ _ hWp, multAt_eq _ _ hWp, ENat.toNat_add (WithTop.add_ne_top.mp hfin).1
          (WithTop.add_ne_top.mp hfin).2, add_comm]
    · rw [if_pos (mem_divSupp_of_mul h hfW), if_neg fun h2 => hgW (mem_of_mem_divSupp h2),
        multAt_eq _ _ hWp, locLen_quot_eq_zero _ hgW, zero_add, add_zero]
    · rw [if_neg fun h2 => hfW (mem_of_mem_divSupp h2), if_pos (mem_divSupp_of_mul h' hgW),
        multAt_eq _ _ hWp, locLen_quot_eq_zero (V := V) (g := f) _ hfW, add_zero, zero_add]
    · exact absurd (hWp.mem_or_mem (mem_of_mem_divSupp h)) (by tauto)
  · rw [if_neg h, if_neg fun h2 => h (mem_divSupp_mul_left hV hg h2),
      if_neg fun h2 => h (by rw [mul_comm]; exact mem_divSupp_mul_left hV hf h2)]

theorem ratDiv_mul {V : Ideal (MRingOver F ι)} (hV : V.IsPrime) {f g f' g' : MRingOver F ι}
    (hf : f ∉ V) (hg : g ∉ V) (hf' : f' ∉ V) (hg' : g' ∉ V) :
    ratDiv V (f * f') (g * g') = ratDiv V f g + ratDiv V f' g' := by
  simp only [ratDiv, divCycle_mul hV hf hf', divCycle_mul hV hg hg',
    Finsupp.mapRange_add (hf := Nat.cast_zero) (fun a b => Nat.cast_add a b)]
  abel

theorem divCycle_one (V : Ideal (MRingOver F ι)) : divCycle V (1 : MRingOver F ι) = 0 := by
  classical
  ext W
  have h : W ∉ divSupp V (1 : MRingOver F ι) := by
    rintro ⟨hW, -⟩
    rw [Ideal.span_singleton_one, sup_top_eq] at hW
    exact hW.1.1.ne_top (top_le_iff.mp hW.1.2)
  simp [divCycle, Finsupp.ofSupportFinite_coe, h]

theorem ratDiv_eq_sub (V : Ideal (MRingOver F ι)) (f g : MRingOver F ι) :
    ratDiv V f g = ratDiv V f 1 - ratDiv V g 1 := by
  simp [ratDiv, divCycle_one]

theorem ratDiv_swap (V : Ideal (MRingOver F ι)) (f g : MRingOver F ι) :
    ratDiv V g f = -ratDiv V f g := by
  simp [ratDiv]

theorem cycEval_eq_liftAddHom (J : Ideal (MRingOver F ι) → ℤ) (D : Ideal (MRingOver F ι) →₀ ℤ) :
    cycEval J D = Finsupp.liftAddHom (fun W => AddMonoidHom.mulRight (J W)) D := by
  rw [Finsupp.liftAddHom_apply]
  rfl

theorem cycEval_zero (J : Ideal (MRingOver F ι) → ℤ) : cycEval J 0 = 0 := by
  simp [cycEval]

theorem cycEval_add (J : Ideal (MRingOver F ι) → ℤ) (D E : Ideal (MRingOver F ι) →₀ ℤ) :
    cycEval J (D + E) = cycEval J D + cycEval J E := by
  simp only [cycEval_eq_liftAddHom, map_add]

theorem cycEval_sub (J : Ideal (MRingOver F ι) → ℤ) (D E : Ideal (MRingOver F ι) →₀ ℤ) :
    cycEval J (D - E) = cycEval J D - cycEval J E := by
  simp only [cycEval_eq_liftAddHom, map_sub]

theorem cycEval_neg (J : Ideal (MRingOver F ι) → ℤ) (D : Ideal (MRingOver F ι) →₀ ℤ) :
    cycEval J (-D) = -cycEval J D := by
  simp only [cycEval_eq_liftAddHom, map_neg]

theorem cycEval_congr {J J' : Ideal (MRingOver F ι) → ℤ} {D : Ideal (MRingOver F ι) →₀ ℤ}
    (h : ∀ W, D W ≠ 0 → J W = J' W) : cycEval J D = cycEval J' D := by
  unfold cycEval
  exact Finsupp.sum_congr fun W hW => by rw [h W (Finsupp.mem_support_iff.mp hW)]

theorem cycEval_sub_fun (J J' : Ideal (MRingOver F ι) → ℤ) (D : Ideal (MRingOver F ι) →₀ ℤ) :
    cycEval (fun W => J W - J' W) D = cycEval J D - cycEval J' D := by
  unfold cycEval
  simp only [mul_sub, Finsupp.sum_sub]

theorem cycEval_sum_smul (J : Ideal (MRingOver F ι) → ℤ) (D : Ideal (MRingOver F ι) →₀ ℤ)
    (E : Ideal (MRingOver F ι) → Ideal (MRingOver F ι) →₀ ℤ) :
    cycEval J (D.sum fun W m => m • E W) = cycEval (fun W => cycEval J (E W)) D := by
  rw [cycEval_eq_liftAddHom, map_finsuppSum]
  unfold cycEval
  refine Finsupp.sum_congr fun W _ => ?_
  rw [map_zsmul, smul_eq_mul, ← cycEval_eq_liftAddHom]
  rfl

theorem ptDeg_eq_of_isChart {V : Ideal (MRingOver F ι)} (hV : IsProjVarF V 0) {i j : ∀ k, ι k}
    (hi : IsChart V i) (hj : IsChart V j) : ptDeg V i = ptDeg V j := by
  have hu : ∀ k, IsUnit (Ideal.Quotient.mkₐ F (chartIdeal V j) (X ⟨k, i k⟩)) := fun k =>
    isUnit_mk_chartIdeal_X hV j _ (hi k)
  have hv : ∀ k, IsUnit (Ideal.Quotient.mkₐ F (chartIdeal V i) (X ⟨k, j k⟩)) := fun k =>
    isUnit_mk_chartIdeal_X hV i _ (hj k)
  let e := AlgEquiv.ofAlgHom (chartSwap hV.1.2.1 i j hu) (chartSwap hV.1.2.1 j i hv)
    (chartSwap_comp hV.1.2.1 j i hv hu) (chartSwap_comp hV.1.2.1 i j hu hv)
  exact e.toLinearEquiv.finrank_eq

theorem isProjVarF_of_mem_divSupp {V W : Ideal (MRingOver F ι)} {n : ℕ} {f : MRingOver F ι}
    {α : K → ℕ} (hV : IsProjVarF V (n + 1)) (hf : IsMultiHomog f α) (hfV : f ∉ V)
    (hW : W ∈ divSupp V f) : IsProjVarF W n := by
  obtain ⟨⟨hVp, hVh, -⟩, hVdim⟩ := hV
  obtain ⟨hWmin, hWrel⟩ := hW
  have hWmh : IsMultiHomogIdeal W := cyc_isMultiHomogIdeal_of_mem_minimalPrimes hVh hf hWmin
  have h1 := cyc_dim_quot_minimal_add_one hfV hWmin (fun h => by
    rw [hVdim] at h
    exact ENat.natCast_ne_top _ (WithBot.coe_injective h))
  rw [hVdim] at h1
  exact ⟨⟨hWmin.1.1, hWmh, hWrel⟩, cyc_withBot_eq_of_add_one
    (by rw [h1, show n + 1 + Fintype.card K = n + Fintype.card K + 1 by omega])⟩

end ReciprocityTheory.ChartRestriction.G.AI.I1
