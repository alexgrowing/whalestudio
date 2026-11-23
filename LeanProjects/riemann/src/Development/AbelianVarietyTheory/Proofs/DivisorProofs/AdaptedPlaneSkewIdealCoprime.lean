import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfIntegralTraceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitDenominatorIntegralStatement

open NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors Matrix TensorProduct

noncomputable section
namespace GlobalTheory.SkewPlaneIdeal

theorem codiff_le_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ → ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ B.P →
    ∀ c : E, (∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E ((o : E) * c))) → w.valuation E c ≤ 1 :=
  GlobalTheory.T.valuation_le_one_of_integral_trace

theorem exists_unit_mul_integral : ∀ (K : Type) [Field K] [NumberField K] (P : HeightOneSpectrum (𝓞 K))
    (T : Set K) (d : 𝓞 K), d ≠ 0 → (∀ t ∈ T, IsIntegral ℤ ((d : K) * t)) → (∀ t ∈ T, P.valuation K t ≤ 1) →
    ∃ s : 𝓞 K, P.valuation K (s : K) = 1 ∧ ∀ t ∈ T, IsIntegral ℤ ((s : K) * t) :=
  GlobalTheory.T.exists_unit_denominator_integral

theorem exists_valued_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (τ : E →ₐ[F] Fv F v) (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (c : Fin n → E)
    (S : Set E), (0 : E) ∈ S → (∀ z ∈ L, z ⬝ᵥ c ∈ S) → ∀ u ∈ splitLat τ L,
    ∃ s ∈ S, Valued.v (u ⬝ᵥ fun i => τ (c i)) ≤ Valued.v (τ s) := by
  intro F E _ _ _ _ _ v τ n L c S h0 hS u hu
  obtain ⟨y, hy, rfl⟩ := hu
  refine latLoc_induction (p := fun y => ∃ s ∈ S, Valued.v (splitVec τ y ⬝ᵥ fun i => τ (c i)) ≤ Valued.v (τ s))
    ?_ ?_ ?_ ?_ hy
  · intro a ha z hz
    refine ⟨z ⬝ᵥ c, hS z hz, ?_⟩
    have e : (splitVec τ fun i => a ⊗ₜ[F] z i) ⬝ᵥ (fun i => τ (c i)) = a * τ (z ⬝ᵥ c) := by
      simp [splitVec, dotProduct, map_sum, Finset.mul_sum, mul_assoc]
    rw [e, map_mul]
    exact mul_le_of_le_one_left' ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ha)
  · refine ⟨0, h0, ?_⟩
    have : splitVec τ (0 : Fin n → Fv F v ⊗[F] E) = 0 := funext fun i => map_zero _
    rw [this, zero_dotProduct, map_zero]
    exact zero_le
  · rintro y z ⟨s1, hs1, h1⟩ ⟨s2, hs2, h2⟩
    rw [splitVec_add, add_dotProduct]
    rcases le_total (Valued.v (τ s1)) (Valued.v (τ s2)) with h | h
    · exact ⟨s2, hs2, (Valuation.map_add _ _ _).trans (max_le (h1.trans h) h2)⟩
    · exact ⟨s1, hs1, (Valuation.map_add _ _ _).trans (max_le h1 (h2.trans h))⟩
  · rintro y ⟨s1, hs1, h1⟩
    refine ⟨s1, hs1, ?_⟩
    have : splitVec τ (-y) = -splitVec τ y := funext fun i => map_neg _ _
    rw [this, neg_dotProduct, Valuation.map_neg]
    exact h1

theorem exists_denom : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)),
    L.FG → ∀ c : Fin n → E, ∃ d : 𝓞 E, d ≠ 0 ∧ ∀ z ∈ L, IsIntegral ℤ ((d : E) * (z ⬝ᵥ c)) := by
  intro E _ _ n L hL c
  let f : (Fin n → E) →ₗ[𝓞 E] E :=
    { toFun := fun z => z ⬝ᵥ c
      map_add' := fun a b => add_dotProduct a b c
      map_smul' := fun o a => by simp [smul_dotProduct] }
  obtain ⟨a, ha, hint⟩ := FractionalIdeal.isFractional_of_fg (S := (𝓞 E)⁰) (P := E) (hL.map f)
  refine ⟨a, nonZeroDivisors.ne_zero ha, fun z hz => ?_⟩
  obtain ⟨b, hb⟩ := hint _ (Submodule.mem_map_of_mem hz)
  rw [Algebra.smul_def] at hb
  have e : (a : E) * (z ⬝ᵥ c) = (b : E) := hb.symm
  rw [e]
  exact RingOfIntegers.isIntegral_coe b

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

lemma form_add_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J (a + b) c = form σ J a c + form σ J b c := add_dotProduct _ _ _

lemma form_smul_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (t : E) (a c : Fin n → E) :
    form σ J (t • a) c = t * form σ J a c := smul_dotProduct _ _ _

lemma form_add_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b c : Fin n → E) :
    form σ J a (b + c) = form σ J a b + form σ J a c := by
  have e : (fun i => σ ((b + c) i)) = (fun i => σ (b i)) + fun i => σ (c i) := funext fun i => map_add σ _ _
  simp only [form, e, Matrix.mulVec_add, dotProduct_add]

lemma form_smul_right (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (t : E) (a b : Fin n → E) :
    form σ J a (t • b) = σ t * form σ J a b := by
  have e : (fun i => σ ((t • b) i)) = σ t • fun i => σ (b i) := funext fun i => by simp
  simp only [form, e, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

lemma form_swap (σ : E →ₐ[F] E) (hσ : ∀ z, σ (σ z) = z) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = -J i j) (a b : Fin n → E) : form σ J a b = -σ (form σ J b a) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]; ring

lemma map_dotProduct {K : Type} [Field K] [Algebra F K] (τ : E →ₐ[F] K) {n : ℕ} (a c : Fin n → E) :
    (fun i => τ (a i)) ⬝ᵥ (fun i => τ (c i)) = τ (a ⬝ᵥ c) := by
  simp [dotProduct, map_sum, map_mul]

theorem count_eq_zero_of_valuation {K : Type} [Field K] [NumberField K] {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0)
    (w : HeightOneSpectrum (𝓞 K)) (h1 : ∀ s ∈ I, w.valuation K s ≤ 1) (h2 : ∃ s ∈ I, 1 ≤ w.valuation K s) :
    FractionalIdeal.count K w I = 0 := by
  obtain ⟨y, hy, hvy⟩ := GlobalTheory.Idele.exists_mem_valuation_eq hI w
  obtain ⟨s, hs, hvs⟩ := h2
  have a := h1 y hy
  have b := (GlobalTheory.Idele.mem_iff_valuation_le hI s).1 hs w
  rw [hvy, ← WithZero.exp_zero, WithZero.exp_le_exp] at a
  have c := hvs.trans b
  rw [← WithZero.exp_zero, WithZero.exp_le_exp] at c
  omega

lemma mem_splitLat_of_mem {v : HeightOneSpectrum (𝓞 F)} (τ : E →ₐ[F] Fv F v) {n : ℕ}
    {L : Submodule (𝓞 E) (Fin n → E)} {z : Fin n → E} (hz : z ∈ L) : (fun i => τ (z i)) ∈ splitLat τ L :=
  ⟨fun i => (1 : Fv F v) ⊗ₜ[F] z i, tmul_mem_latLoc (one_mem _) hz, funext fun i => by simp [splitVec]⟩

lemma col_prim {v : HeightOneSpectrum (𝓞 F)} {τ : E →ₐ[F] Fv F v} {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)}
    {β : GL (Fin n) (Fv F v)} (hβ : IsSplitBasis τ L β) (j : Fin n) (z : Fin n → E) (hz : ∀ r, β.1 r j = τ (z r)) :
    (fun r => τ (z r)) ∈ splitLat τ L ∧ ∀ t : Fv F v, (fun r => t * τ (z r)) ∈ splitLat τ L → Valued.v t ≤ 1 := by
  classical
  have hcol : β.1 *ᵥ Pi.single j 1 = fun r => τ (z r) := by
    rw [Matrix.mulVec_single_one]; funext r; exact hz r
  refine ⟨hcol ▸ (hβ _).1 fun i => ?_, fun t ht => ?_⟩
  · by_cases h : i = j
    · subst h; simp
    · simp [h]
  · have e : β.1 *ᵥ (t • Pi.single j 1) = fun r => t * τ (z r) := by
      rw [Matrix.mulVec_smul, hcol]; rfl
    have := (hβ _).2 (e ▸ ht) j
    simpa [HeightOneSpectrum.mem_adicCompletionIntegers] using this

theorem skewPlaneIdeal_ne_zero_and_count_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) {n n₁ : ℕ} (H : Plane E n n₁) (Y : Spc F E n) (Y₁ : Spc F E n₁) (i₀ i₁ r s : ℕ),
    B.IsGood σ → Y.IsSkew σ B r s → H.IsAdapted σ B Y Y₁ i₀ i₁ → i₀ < n → i₁ < n →
    H.𝔟 ≠ 0 ∧ ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ B.P → FractionalIdeal.count E w H.𝔟 = 0 := by
  intro F E _ _ _ _ _ σ B n n₁ H Y Y₁ i₀ i₁ r s hB hY hH hi₀ hi₁
  have hσ : ∀ z, σ (σ z) = z := cm_conj_conj hB.cm
  have hyx : form σ Y.J H.y H.x = -1 := by rw [form_swap σ hσ Y.J hY.skew, hH.xy, map_one]
  have hxι : ∀ u, form σ Y.J H.x (H.ι *ᵥ u) = 0 := fun u => by
    rw [form_swap σ hσ Y.J hY.skew, (hH.orth u).1, map_zero, neg_zero]

  have hco : ∀ z ∈ Y.L, form σ Y.J z H.y • H.x ∈ Y.L ∧ (-form σ Y.J z H.x) • H.y ∈ Y.L ∧
      ∀ a : E, form σ Y.J (a • H.x) z = a * σ (-form σ Y.J z H.x) := by
    intro z hz
    obtain ⟨a, t, u, ha, ht, _, rfl⟩ := hH.split z hz
    have e1 : form σ Y.J (a • H.x + H.ι *ᵥ u + t • H.y) H.y = a := by
      rw [form_add_left, form_add_left, form_smul_left, form_smul_left, hH.xy, hH.yy, (hH.orth u).2]; ring
    have e2 : -form σ Y.J (a • H.x + H.ι *ᵥ u + t • H.y) H.x = t := by
      rw [form_add_left, form_add_left, form_smul_left, form_smul_left, hH.xx, hyx, (hH.orth u).1]; ring
    refine ⟨by rw [e1]; exact ha, by rw [e2]; exact ht, fun b => ?_⟩
    rw [e2, form_smul_left, form_add_right, form_add_right, form_smul_right, form_smul_right, hH.xx, hH.xy, hxι]
    ring

  have h0 : H.𝔟 ≠ 0 := by
    intro h0
    let f : (Fin n → E) →ₗ[E] E :=
      { toFun := fun z => form σ Y.J z H.y
        map_add' := fun a b => form_add_left σ Y.J a b H.y
        map_smul' := fun t a => form_smul_left σ Y.J t a H.y }
    have hle : Submodule.span E (Y.L : Set (Fin n → E)) ≤ LinearMap.ker f := by
      rw [Submodule.span_le]
      intro z hz
      have := (hH.ideal _).2 (hco z hz).1
      rw [h0] at this
      exact (FractionalIdeal.mem_zero_iff _).1 this
    haveI := hY.lat
    rw [Submodule.IsLattice.span_eq_top] at hle
    have : f H.x = 0 := hle Submodule.mem_top
    change form σ Y.J H.x H.y = 0 at this
    rw [hH.xy] at this
    exact one_ne_zero this
  refine ⟨h0, fun w hw => ?_⟩
  set v : B.P := ⟨w.under (𝓞 F), hw⟩ with hv
  set τ := B.τ v with hτ
  have hβ := hY.bas v
  obtain ⟨hxL, hxp⟩ := col_prim hβ ⟨i₀, hi₀⟩ H.x fun r => (hH.bas v ⟨i₀, hi₀⟩).1 rfl r
  obtain ⟨hyL, hyp⟩ := col_prim hβ ⟨i₁, hi₁⟩ H.y fun r => (hH.bas v ⟨i₁, hi₁⟩).2.1 rfl r
  have hτs : ∀ a : E, ∀ z : Fin n → E, (fun i => τ ((a • z) i)) = fun i => τ a * τ (z i) := fun a z =>
    funext fun i => by simp

  have hxw : ∀ a : E, a • H.x ∈ Y.L → Valued.v (τ a) ≤ 1 := fun a ha =>
    hxp _ (hτs a H.x ▸ mem_splitLat_of_mem τ ha)
  have hyw : ∀ a : E, a • H.y ∈ Y.L → Valued.v (τ a) ≤ 1 := fun a ha =>
    hyp _ (hτs a H.y ▸ mem_splitLat_of_mem τ ha)

  have hxu : ∃ a : E, a • H.x ∈ Y.L ∧ 1 ≤ Valued.v (τ a) := by
    obtain ⟨a, ha, hle⟩ := exists_valued_le F E v.1 τ n Y.L (Y.J *ᵥ fun i => σ (H.y i)) {a | a • H.x ∈ Y.L}
      (by simp) (fun z hz => (hco z hz).1) _ hxL
    refine ⟨a, ha, le_of_eq_of_le ?_ hle⟩
    rw [map_dotProduct τ]
    change 1 = Valued.v (τ (form σ Y.J H.x H.y))
    rw [hH.xy, map_one, map_one]
  have hyu : ∃ a : E, a • H.y ∈ Y.L ∧ 1 ≤ Valued.v (τ a) := by
    obtain ⟨a, ha, hle⟩ := exists_valued_le F E v.1 τ n Y.L (-(Y.J *ᵥ fun i => σ (H.x i))) {a | a • H.y ∈ Y.L}
      (by simp) (fun z hz => by show (z ⬝ᵥ -(Y.J *ᵥ _)) • H.y ∈ Y.L; rw [dotProduct_neg]; exact (hco z hz).2.1) _ hyL
    refine ⟨a, ha, le_of_eq_of_le ?_ hle⟩
    rw [map_dotProduct τ, dotProduct_neg]
    change 1 = Valued.v (τ (-form σ Y.J H.y H.x))
    rw [hyx, neg_neg, map_one, map_one]

  have hwP : w.asIdeal ∈ v.1.asIdeal.primesOver (𝓞 E) := ⟨w.isPrime, ⟨rfl⟩⟩
  rw [primesOver_eq_split hB.cm τ] at hwP
  rcases hwP with hw1 | hw1
  · have hw2 : w = splitPrime τ := HeightOneSpectrum.ext hw1
    have hval : ∀ a : E, w.valuation E a = Valued.v (τ a) := fun a =>
      (congrArg (fun u : HeightOneSpectrum (𝓞 E) => u.valuation E a) hw2).trans (valued_apply_eq_valuation τ a).symm
    refine count_eq_zero_of_valuation h0 _ (fun a ha => ?_) ?_
    · rw [hval]; exact hxw a ((hH.ideal a).1 ha)
    · obtain ⟨a, ha, h1⟩ := hxu
      exact ⟨a, (hH.ideal a).2 ha, by rw [hval]; exact h1⟩
  · have hw2 : w = splitPrime (τ.comp σ) := HeightOneSpectrum.ext (Set.mem_singleton_iff.1 hw1)
    have hval : ∀ a : E, w.valuation E a = Valued.v (τ (σ a)) := fun a =>
      (congrArg (fun u : HeightOneSpectrum (𝓞 E) => u.valuation E a) hw2).trans (valued_apply_eq_valuation _ a).symm
    have hwP' : w.under (𝓞 F) ∈ B.P := hw
    refine count_eq_zero_of_valuation h0 _ (fun a ha => ?_) ?_
    · obtain ⟨t, ht, h1⟩ := hyu
      have hd := (hY.dual (a • H.x)).1 ((hH.ideal a).1 ha) (t • H.y) ht
      have e : form σ Y.J (a • H.x) (t • H.y) = a * σ t := by
        rw [form_smul_left, form_smul_right, hH.xy]; ring
      rw [e] at hd
      have h2 := codiff_le_one F E σ B hB w hwP' _ hd
      rw [hval, map_mul, hσ, map_mul, map_mul] at h2
      rw [hval]
      calc Valued.v (τ (σ a)) = Valued.v (τ (σ a)) * 1 := (mul_one _).symm
        _ ≤ Valued.v (τ (σ a)) * Valued.v (τ t) := mul_le_mul' le_rfl h1
        _ ≤ 1 := h2
    · obtain ⟨d, hd0, hd⟩ := exists_denom E n Y.L hY.lat.fg (-(Y.J *ᵥ fun i => σ (H.x i)))
      have hdt : ∀ t : E, t • H.y ∈ Y.L → IsIntegral ℤ ((d : E) * t) := fun t ht => by
        have := hd _ ht
        rw [dotProduct_neg] at this
        change IsIntegral ℤ ((d : E) * -form σ Y.J (t • H.y) H.x) at this
        rwa [form_smul_left, hyx, mul_neg_one, neg_neg] at this
      let σZ : E →ₐ[ℤ] E := (σ : E →+* E).toIntAlgHom
      have hd1 : RingOfIntegers.mapRingHom (σ : E →+* E) d ≠ 0 := fun h => hd0 (by
        have h' := congrArg (fun x : 𝓞 E => (x : E)) h
        simp at h'
        exact h')
      obtain ⟨s', hs'1, hs'2⟩ := exists_unit_mul_integral E w {u | ∃ t, t • H.y ∈ Y.L ∧ u = σ t}
        (RingOfIntegers.mapRingHom (σ : E →+* E) d) hd1 (by
          rintro _ ⟨t, ht, rfl⟩
          show IsIntegral ℤ (σ (d : E) * σ t)
          rw [← map_mul]
          exact (hdt t ht).map σZ) (by
          rintro _ ⟨t, ht, rfl⟩
          rw [hval, hσ]
          exact hyw t ht)
      refine ⟨s', (hH.ideal _).2 ((hY.dual _).2 fun z hz o => ?_), by rw [hs'1]⟩
      rw [(hco z hz).2.2]
      exact Algebra.isIntegral_trace ((RingOfIntegers.isIntegral_coe o).mul (hs'2 _ ⟨_, (hco z hz).2.1, rfl⟩))

end GlobalTheory.SkewPlaneIdeal
