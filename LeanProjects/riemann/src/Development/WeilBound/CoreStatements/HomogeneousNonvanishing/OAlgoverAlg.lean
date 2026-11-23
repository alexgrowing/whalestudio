import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.HodgeIPIffHodgeFormConj
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ)
open scoped TensorProduct

namespace PositivityTheory.UnitarySelfGeneration.AlgOv

theorem map_ev {σ A B : Type} [CommRing A] [CommRing B] [Algebra ℤ A] [Algebra ℤ B] (φ : A →+* B) (x : σ → A) (s : MvPolynomial σ ℤ) :
    φ (aeval x s) = aeval (fun p => φ (x p)) s := by
  induction s using MvPolynomial.induction_on with
  | C n => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

theorem exists_point (A : Type) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] [Nontrivial A] :
    Nonempty (A →ₐ[ℂ] ℂ) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI := Ideal.Quotient.field m
  have := finite_of_finite_type_of_isJacobsonRing ℂ (A ⧸ m)
  exact ⟨(IsAlgClosed.lift : (A ⧸ m) →ₐ[ℂ] ℂ).comp (Ideal.Quotient.mkₐ ℂ m)⟩

theorem extend_hom {R₀ R : Type} [CommRing R₀] [CommRing R] (r : R₀ →+* R) (hr : r.FiniteType) (q : Ideal R)
    [q.IsPrime] (φ : R₀ →+* ℂ) (h : RingHom.ker φ = q.comap r) :
    ∃ χ : R →+* ℂ, (∀ a, χ (r a) = φ a) ∧ ∀ b ∈ q, χ b = 0 := by
  letI : Algebra (R₀ ⧸ RingHom.ker φ) ℂ := (RingHom.kerLift φ).toAlgebra
  letI : Algebra (R₀ ⧸ RingHom.ker φ) (R ⧸ q) := (Ideal.quotientMap q r h.le).toAlgebra
  have ft : Algebra.FiniteType (R₀ ⧸ RingHom.ker φ) (R ⧸ q) := by
    have : ((Ideal.quotientMap q r h.le).comp (Ideal.Quotient.mk _)).FiniteType := by
      rw [Ideal.quotientMap_comp_mk]
      exact (RingHom.FiniteType.of_surjective _ Ideal.Quotient.mk_surjective).comp hr
    exact RingHom.FiniteType.of_comp_finiteType this
  have nt : Nontrivial (ℂ ⊗[R₀ ⧸ RingHom.ker φ] (R ⧸ q)) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain _ _ _ (RingHom.kerLift_injective φ)
      (Ideal.quotientMap_injective' h.ge)
  obtain ⟨ev⟩ := exists_point (ℂ ⊗[R₀ ⧸ RingHom.ker φ] (R ⧸ q))
  refine ⟨ev.toRingHom.comp ((Algebra.TensorProduct.includeRight).toRingHom.comp (Ideal.Quotient.mk q)),
    fun a => ?_, fun b hb => ?_⟩
  · have e : ((1 : ℂ) ⊗ₜ[R₀ ⧸ RingHom.ker φ] (Ideal.Quotient.mk q (r a))) =
        algebraMap ℂ (ℂ ⊗[R₀ ⧸ RingHom.ker φ] (R ⧸ q)) (φ a) := by
      have := (Algebra.TensorProduct.includeRight (R := R₀ ⧸ RingHom.ker φ) (A := ℂ) (B := R ⧸ q)).commutes
        (Ideal.Quotient.mk _ a)
      exact this
    exact (congrArg ev e).trans (ev.commutes _)
  · simp [Ideal.Quotient.eq_zero_iff_mem.2 hb]

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem evC_eq (z : (Σ k, ι k) → ℂ) (f : MRing ι) : eval z (map (Int.castRingHom ℂ) f) = aeval z f := by
  rw [MvPolynomial.eval_map]
  rfl

theorem ev_scale_of_mem {y : (Σ k, ι k) → Ω} {f : MRing ι} (hf : f ∈ mCoordIdeal y) (t : K → Ω) :
    aeval (fun p => y p * t p.1) f = 0 := by
  have h := congrArg (eval t) (show mConeMap y f = 0 from hf)
  rw [map_zero, mConeMap, map_ev] at h
  simpa using h

theorem ev_div_of_mem {y : (Σ k, ι k) → Ω} {f : MRing ι} (hf : f ∈ mCoordIdeal y) (t : K → Ω) :
    aeval (fun p => y p / t p.1) f = 0 := by
  simpa only [div_eq_mul_inv] using ev_scale_of_mem hf fun k => (t k)⁻¹

theorem ev_ne_of_notMem {y : (Σ k, ι k) → Ω} {f : MRing ι} {d : K → ℕ} (hd : IsMultiHomog f d)
    (hf : f ∉ mCoordIdeal y) (t : K → Ω) (ht : ∀ k, t k ≠ 0) : aeval (fun p => y p / t p.1) f ≠ 0 := by
  have h1 := aeval_blockScale hd (fun k => (t k)⁻¹) y
  have h2 := aeval_blockScale hd (fun k => (X k : MvPolynomial K Ω)) fun p => C (y p)
  simp only [div_eq_inv_mul]
  rw [h1]
  refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (inv_ne_zero (ht k))) fun h => hf ?_
  refine Eq.trans ?_ (h2.trans (mul_eq_zero_of_right _
    ((map_ev (C : Ω →+* MvPolynomial K Ω) y f).symm.trans (by rw [h, map_zero]))))
  refine (map_ev (RingHom.id (MvPolynomial K Ω)) _ f).trans ?_
  simp only [RingHom.id_apply, mul_comm (C (y _))]
  first | rfl | (congr 2; exact Subsingleton.elim _ _)

theorem coord_ne {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) {p : Σ k, ι k}
    (hp : z p ≠ 0) : y p ≠ 0 := fun h => hp (by
  have : (X p : MRing ι) ∈ mCoordIdeal y := by
    show mConeMap y (X p) = 0
    simp [mConeMap, h]
  simpa using hz.2 _ this)

theorem chart_rel {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) (c : ∀ k, ι k)
    (hc : ∀ k, z ⟨k, c k⟩ ≠ 0) (g : MRing ι) (hg : aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) g = 0) :
    aeval (fun p : Σ k, ι k => z p / z ⟨p.1, c p.1⟩) g = 0 := by
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => coord_ne hz (hc k)
  have key : ∀ g : MRing ι, ∃ (n : ℕ) (h : MRing ι),
      mConeMap y h = (∏ k, C (y ⟨k, c k⟩) * X k) ^ n * C (aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) g) ∧
      aeval z h = (∏ k, z ⟨k, c k⟩) ^ n * aeval (fun p : Σ k, ι k => z p / z ⟨p.1, c p.1⟩) g := by
    classical
    have s1 : mConeMap y (∏ k, X ⟨k, c k⟩) = ∏ k, C (y ⟨k, c k⟩) * X k := by simp [mConeMap]
    have s2 : aeval z (∏ k, X ⟨k, c k⟩ : MRing ι) = ∏ k, z ⟨k, c k⟩ := by simp
    intro g
    induction g using MvPolynomial.induction_on with
    | C n => exact ⟨0, C n, by simp, by simp⟩
    | add p q hp hq =>
      obtain ⟨n, h, h1, h2⟩ := hp
      obtain ⟨n', h', h1', h2'⟩ := hq
      refine ⟨n + n', h * (∏ k, X ⟨k, c k⟩) ^ n' + h' * (∏ k, X ⟨k, c k⟩) ^ n, ?_, ?_⟩
      · simp only [map_add, map_mul, map_pow, s1, h1, h1']
        ring
      · simp only [map_add, map_mul, map_pow, s2, h2, h2']
        ring
    | mul_X g p hp =>
      obtain ⟨n, h, h1, h2⟩ := hp
      refine ⟨n + 1, h * (X p * ∏ k ∈ Finset.univ.erase p.1, X ⟨k, c k⟩), ?_, ?_⟩
      · rw [map_mul, h1, pow_succ, ← Finset.mul_prod_erase _ _ (Finset.mem_univ p.1)]
        have e : (C (y p) : MvPolynomial K Ω) = C (y ⟨p.1, c p.1⟩) * C (y p / y ⟨p.1, c p.1⟩) := by
          rw [← map_mul, mul_div_cancel₀ _ (hy _)]
        simp only [mConeMap, map_mul, map_prod, aeval_X]
        rw [e]
        ring
      · rw [map_mul, h2, pow_succ, ← Finset.mul_prod_erase _ _ (Finset.mem_univ p.1)]
        simp only [map_mul, map_prod, aeval_X]
        have := hc p.1
        field_simp
  obtain ⟨n, h, h1, h2⟩ := key g
  rw [hg, map_zero, mul_zero] at h1
  have h3 := hz.2 h h1
  rw [evC_eq, h2] at h3
  exact (mul_eq_zero.1 h3).resolve_left (pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun k _ => hc k))

theorem scale_mem {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hP : IsMultiHomogIdeal (mCoordIdeal y))
    (hz : z ∈ mcPts (mCoordIdeal y)) {a : ℂ} (ha : a ≠ 0) : (fun p => a * z p) ∈ mcPts (mCoordIdeal y) := by
  refine ⟨fun k => (hz.1 k).imp fun i hi => mul_ne_zero ha hi, fun f hf => ?_⟩
  obtain ⟨S, hS, e⟩ := hP
  have hz2 := hz.2
  rw [e] at hf hz2
  rw [evC_eq]
  induction hf using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨d, hd⟩ := hS s hs
    rw [aeval_blockScale hd (fun _ => a) z, ← evC_eq, hz2 s (Ideal.subset_span hs), mul_zero]
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb]
  | smul a b _ hb => simp [hb]

section Block
variable {I : Type} [Fintype I] (k₀ : K) (ix : I ≃ ι k₀)

def blk : (Σ _ : Unit, I) → Σ k, ι k := fun p => ⟨k₀, ix p.2⟩

theorem imageZ_blk (y : (Σ k, ι k) → Ω) :
    imageZ (ι := fun _ : Unit => I) (blk k₀ ix) (mCoordIdeal y) =
      mCoordIdeal (ι := fun _ : Unit => I) (y ∘ blk k₀ ix) := by
  have h : ∀ f : MRing (fun _ : Unit => I), mConeMap y (rename (blk k₀ ix) f) =
      rename (fun _ : Unit => k₀) (mConeMap (ι := fun _ : Unit => I) (y ∘ blk k₀ ix) f) := fun f => by
    unfold mConeMap
    induction f using MvPolynomial.induction_on with
    | C n => simp
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p i hp => simp only [map_mul, hp, aeval_X, rename_X, rename_C]; rfl
  ext f
  show mConeMap y (rename (blk k₀ ix) f) = 0 ↔ mConeMap _ f = 0
  rw [h]
  exact map_eq_zero_iff _ (rename_injective _ fun _ _ _ => rfl)

theorem blk_onto {y : (Σ k, ι k) → Ω} (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) {z : (Σ _ : Unit, I) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal (ι := fun _ : Unit => I) (y ∘ blk k₀ ix))) :
    ∃ w ∈ mcPts (mCoordIdeal y), ∃ a : ℂ, a ≠ 0 ∧ ∀ p, z p = a * w (blk k₀ ix p) := by
  classical
  obtain ⟨i₀, hi₀⟩ := hz.1 ()
  have hy₀ : y ⟨k₀, ix i₀⟩ ≠ 0 := coord_ne hz hi₀
  let φ : MRing (fun _ : Unit => I) →+* ℂ := (aeval fun p : Σ _ : Unit, I => z p / z ⟨(), i₀⟩).toRingHom
  let a : MRing (fun _ : Unit => I) →+* Ω :=
    (aeval fun p : Σ _ : Unit, I => y (blk k₀ ix p) / y ⟨k₀, ix i₀⟩).toRingHom
  have hker : ∀ g, a g = 0 → φ g = 0 := chart_rel hz (fun _ => i₀) fun _ => hi₀
  have := RingHom.ker_isPrime φ
  have hu : ∀ s : (RingHom.ker φ).primeCompl, IsUnit (a s) := fun s => IsUnit.mk0 _ fun h => s.2 (hker _ h)
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing
    (IsLocalization.lift (S := Localization.AtPrime (RingHom.ker φ)) hu)
  have haV : ∀ g, a g ∈ V := fun g => by
    simpa using hV (algebraMap _ _ g)
  have hmax : ∀ g, (⟨a g, haV g⟩ : V) ∈ IsLocalRing.maximalIdeal V ↔ φ g = 0 := fun g => by
    have e : (⟨a g, haV g⟩ : V) = (IsLocalization.lift (S := Localization.AtPrime (RingHom.ker φ)) hu).codRestrict
        V.toSubring hV (algebraMap _ _ g) := Subtype.ext (by simp)
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, e]
    erw [isUnit_map_iff]
    rw [IsLocalization.AtPrime.isUnit_to_map_iff _ (RingHom.ker φ)]
    exact not_not
  have hc : ∀ k, ∃ c : ι k, (y ⟨k, c⟩ ≠ 0 ∧ ∀ i, y ⟨k, i⟩ / y ⟨k, c⟩ ∈ V) ∧
      (k = k₀ → y ⟨k, c⟩ = y ⟨k₀, ix i₀⟩) := fun k => by
    by_cases hk : k = k₀
    · subst hk
      refine ⟨ix i₀, ⟨hy₀, fun i => ?_⟩, fun _ => rfl⟩
      simpa [a, blk] using haV (X ⟨(), ix.symm i⟩)
    · obtain ⟨i₁, hi₁⟩ := hy k
      obtain ⟨c, -, hc⟩ := Finset.exists_max_image Finset.univ (fun i => V.valuation (y ⟨k, i⟩))
        ⟨i₁, Finset.mem_univ _⟩
      have h0 : y ⟨k, c⟩ ≠ 0 := fun h => hi₁ (by simpa [h] using hc i₁ (Finset.mem_univ _))
      refine ⟨c, ⟨h0, fun i => ?_⟩, fun h => (hk h).elim⟩
      rw [← V.valuation_le_one_iff, map_div₀]
      exact div_le_one_of_le₀ (hc i (Finset.mem_univ _)) zero_le
  choose c hc hc₀ using hc
  let ψ : MRing ι →+* V := (aeval fun p : Σ k, ι k => (⟨y p / y ⟨p.1, c p.1⟩, (hc p.1).2 p.2⟩ : V)).toRingHom
  have hψ : ∀ f, (ψ f : Ω) = aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) f := fun f =>
    map_ev V.subtype _ f
  have hψr : ∀ g, ψ (rename (blk k₀ ix) g) = ⟨a g, haV g⟩ := fun g => Subtype.ext (by
    rw [hψ, aeval_rename]
    congr 2
    funext p
    exact congrArg (y (blk k₀ ix p) / ·) (hc₀ k₀ rfl))
  obtain ⟨χ, h1, h2⟩ := extend_hom (rename (blk k₀ ix) : MRing (fun _ : Unit => I) →ₐ[ℤ] MRing ι).toRingHom
    (RingHom.FiniteType.of_comp_finiteType (f := algebraMap ℤ _) (by
      rw [Subsingleton.elim (RingHom.comp _ _) (algebraMap ℤ (MRing ι))]
      exact RingHom.finiteType_algebraMap.2 inferInstance))
    ((IsLocalRing.maximalIdeal V).comap ψ) φ (Ideal.ext fun g => by
      refine Iff.trans (hmax g).symm ?_
      rw [← hψr]
      rfl)
  refine ⟨fun p => χ (X p), ⟨fun k => ⟨c k, ?_⟩, fun f hf => ?_⟩, z ⟨(), i₀⟩, hi₀, fun p => ?_⟩
  · have := h2 (X ⟨k, c k⟩ - 1) (by
      rw [Ideal.mem_comap, show ψ (X ⟨k, c k⟩ - 1) = 0 from Subtype.ext (by
        rw [hψ]; simp [(hc k).1])]
      exact zero_mem _)
    rw [map_sub, map_one, sub_eq_zero] at this
    simp [this]
  · rw [evC_eq]
    refine ((map_ev χ X f).symm.trans (congrArg χ (aeval_X_left_apply f))).trans (h2 f ?_)
    rw [Ideal.mem_comap, show ψ f = 0 from Subtype.ext (by
      rw [hψ]; exact ev_div_of_mem hf fun k => y ⟨k, c k⟩)]
    exact zero_mem _
  · have := h1 (X p)
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X, φ, aeval_X] at this
    exact (mul_div_cancel₀ _ hi₀).symm.trans (congrArg _ this.symm)

theorem homogenise (i₀ : I) (r : MRing (fun _ : Unit => I)) : ∃ (n : ℕ) (s : MRing (fun _ : Unit => I)),
    s.IsHomogeneous n ∧ ∀ (F : Type) [Field F] (x : (Σ _ : Unit, I) → F), x ⟨(), i₀⟩ ≠ 0 →
      aeval x s = x ⟨(), i₀⟩ ^ n * aeval (fun p => x p / x ⟨(), i₀⟩) r := by
  induction r using MvPolynomial.induction_on with
  | C n => exact ⟨0, C n, isHomogeneous_C _ _, fun F _ x _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨n, s, h1, h2⟩ := hp
    obtain ⟨n', s', h1', h2'⟩ := hq
    refine ⟨n + n', s * X ⟨(), i₀⟩ ^ n' + X ⟨(), i₀⟩ ^ n * s',
      (h1.mul (isHomogeneous_X_pow _ _)).add ((isHomogeneous_X_pow _ _).mul h1'), fun F _ x hx => ?_⟩
    simp only [map_add, map_mul, map_pow, aeval_X, h2 F x hx, h2' F x hx]
    ring
  | mul_X g p hp =>
    obtain ⟨n, s, h1, h2⟩ := hp
    refine ⟨n + 1, s * X p, h1.mul (isHomogeneous_X _ _), fun F _ x hx => ?_⟩
    simp only [map_mul, aeval_X, h2 F x hx]
    rw [pow_succ, mul_assoc, mul_assoc, mul_left_comm (x ⟨(), i₀⟩), mul_div_cancel₀ _ hx]

theorem multi_of_homog {d : ℕ} {s : MRing (fun _ : Unit => I)} (h : s.IsHomogeneous d) :
    IsMultiHomog s (fun _ => d) := by
  intro m hm k
  have h1 : d = m.degree := h.degree_eq_sum_deg_support hm
  show ∑ i, m ⟨k, i⟩ = d
  rw [h1, Finsupp.degree_eq_sum, Fintype.sum_sigma]
  cases k
  exact (Fintype.sum_unique (fun x : Unit => ∑ y, m ⟨x, y⟩)).symm

theorem norm_chart {y : (Σ k, ι k) → Ω} {Ωf : Type} [Field Ωf] [Algebra Ωf Ω] [Algebra.IsAlgebraic Ωf Ω]
    (yf : I → Ωf) (hyf : ∀ i, y ⟨k₀, ix i⟩ = algebraMap Ωf Ω (yf i))
    (gen : Subfield.closure (Set.range fun ij : I × I => yf ij.1 / yf ij.2) = ⊤)
    {b : MRing ι} {d : K → ℕ} (hd : IsMultiHomog b d) (hb : b ∉ mCoordIdeal y) (c : ∀ k, ι k) :
    ∃ (n : ℕ) (s : MRing (fun _ : Unit => I)), s.IsHomogeneous n ∧
      ((∀ k, y ⟨k, c k⟩ ≠ 0) → aeval (y ∘ blk k₀ ix) s ≠ 0) ∧ (¬ (∀ k, y ⟨k, c k⟩ ≠ 0) → s = 1) ∧
      ∀ w ∈ mcPts (mCoordIdeal y), (∀ k, w ⟨k, c k⟩ ≠ 0) → aeval w b = 0 → aeval (w ∘ blk k₀ ix) s = 0 := by
  by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
  swap
  · exact ⟨0, 1, isHomogeneous_one _ _, fun h => (hc h).elim, fun _ => rfl,
      fun w hw hwc => (hc fun k => coord_ne hw (hwc k)).elim⟩
  obtain ⟨i₀, hi₀⟩ := ix.surjective (c k₀)
  have hf₀ : yf i₀ ≠ 0 := fun h => hc k₀ (by rw [← hi₀, hyf, h, map_zero])
  let a : MRing (fun _ : Unit => I) →+* Ωf := (aeval fun p : Σ _ : Unit, I => yf p.2 / yf i₀).toRingHom
  let A : MRing ι →+* Ω := (aeval fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩).toRingHom
  have hAa : ∀ g, A (rename (blk k₀ ix) g) = algebraMap Ωf Ω (a g) := fun g => by
    refine (aeval_rename _ _ g).trans (Eq.trans ?_ (map_ev (algebraMap Ωf Ω) _ g).symm)
    congr 2
    funext p
    show y ⟨k₀, ix p.2⟩ / y ⟨k₀, c k₀⟩ = _
    rw [← hi₀, hyf, hyf, map_div₀]
  have fr : IsFractionRing a.range Ωf := by
    refine IsFractionRing.of_field _ _ fun z => ?_
    have hz : z ∈ Subfield.closure (a.range : Set Ωf) := by
      refine (Subfield.closure_le.2 ?_ : Subfield.closure _ ≤ _) (gen ▸ Subfield.mem_top z)
      rintro _ ⟨⟨i, j⟩, rfl⟩
      have e : yf i / yf j = a (X ⟨(), i⟩) / a (X ⟨(), j⟩) := by
        simp [a, div_div_div_cancel_right₀ hf₀]
      show yf i / yf j ∈ _
      rw [e]
      exact div_mem (Subfield.subset_closure ⟨_, rfl⟩) (Subfield.subset_closure ⟨_, rfl⟩)
    obtain ⟨u, hu, v, hv, rfl⟩ := Subfield.mem_closure_iff.1 hz
    rw [Subring.closure_eq] at hu hv
    exact ⟨⟨u, hu⟩, ⟨v, hv⟩, rfl⟩
  have alg : Algebra.IsAlgebraic a.range Ω := (IsFractionRing.comap_isAlgebraic_iff (K := Ωf)).2 inferInstance
  have ht : A b ≠ 0 := ev_ne_of_notMem hd hb (fun k => y ⟨k, c k⟩) hc
  obtain ⟨t, htm, ⟨_, r, rfl⟩, hr, e⟩ := (alg.isAlgebraic (A b)).exists_nonzero_eq_adjoin_mul
    (mem_nonZeroDivisors_of_ne_zero ht)
  have hr' : a r ≠ 0 := fun h => hr (Subtype.ext h)
  obtain ⟨G, rfl⟩ : ∃ G, A G = t := by
    clear e
    induction htm using Algebra.adjoin_induction with
    | mem x hx => exact ⟨b, hx.symm⟩
    | algebraMap s =>
      obtain ⟨_, g, rfl⟩ := s
      exact ⟨_, hAa g⟩
    | add x x' _ _ h h' =>
      obtain ⟨G, rfl⟩ := h
      obtain ⟨G', rfl⟩ := h'
      exact ⟨G + G', map_add _ _ _⟩
    | mul x x' _ _ h h' =>
      obtain ⟨G, rfl⟩ := h
      obtain ⟨G', rfl⟩ := h'
      exact ⟨G * G', map_mul _ _ _⟩
  have rel : A (b * G - rename (blk k₀ ix) r) = 0 := by
    rw [map_sub, map_mul, e, hAa]
    exact sub_self _
  obtain ⟨n, s, hs, hev⟩ := homogenise i₀ r
  refine ⟨n, s, hs, fun _ => ?_, fun h => (h hc).elim, fun w hw hwc hwb => ?_⟩
  · have h0 : (y ∘ blk k₀ ix) ⟨(), i₀⟩ ≠ 0 := by
      show y ⟨k₀, ix i₀⟩ ≠ 0
      rw [hi₀]; exact hc k₀
    rw [hev Ω _ h0]
    refine mul_ne_zero (pow_ne_zero _ h0) fun h => hr' ((algebraMap Ωf Ω).injective ?_)
    rw [← hAa, map_zero, ← h]
    refine (aeval_rename _ _ r).trans ?_
    congr 2
    funext p
    show y _ / y ⟨k₀, c k₀⟩ = y _ / y ⟨k₀, ix i₀⟩
    rw [hi₀]
  · have h0 : (w ∘ blk k₀ ix) ⟨(), i₀⟩ ≠ 0 := by
      show w ⟨k₀, ix i₀⟩ ≠ 0
      rw [hi₀]; exact hwc k₀
    have h1 := chart_rel hw c hwc _ rel
    have h2 : aeval (fun p : Σ k, ι k => w p / w ⟨p.1, c p.1⟩) b = 0 := by
      simp only [div_eq_inv_mul]
      rw [aeval_blockScale hd (fun k => (w ⟨k, c k⟩)⁻¹) w, hwb, mul_zero]
    rw [map_sub, map_mul, h2, zero_mul, zero_sub, neg_eq_zero, aeval_rename] at h1
    rw [hev ℂ _ h0]
    refine mul_eq_zero_of_right _ (Eq.trans ?_ h1)
    congr 2
    funext p
    show w _ / w ⟨k₀, ix i₀⟩ = w _ / w ⟨k₀, c k₀⟩
    rw [hi₀]

theorem norm_form {y : (Σ k, ι k) → Ω} {Ωf : Type} [Field Ωf] [Algebra Ωf Ω] [Algebra.IsAlgebraic Ωf Ω]
    (yf : I → Ωf) (hyf : ∀ i, y ⟨k₀, ix i⟩ = algebraMap Ωf Ω (yf i))
    (gen : Subfield.closure (Set.range fun ij : I × I => yf ij.1 / yf ij.2) = ⊤)
    {b : MRing ι} {d : K → ℕ} (hd : IsMultiHomog b d) (hb : b ∉ mCoordIdeal y) :
    ∃ (n : ℕ) (s : MRing (fun _ : Unit => I)), IsMultiHomog s (fun _ => n) ∧
      s ∉ mCoordIdeal (ι := fun _ : Unit => I) (y ∘ blk k₀ ix) ∧
      ∀ w ∈ mcPts (mCoordIdeal y), aeval w b = 0 → aeval (w ∘ blk k₀ ix) s = 0 := by
  classical
  choose n s h1 h2 h3 h4 using norm_chart k₀ ix yf hyf gen hd hb
  refine ⟨∑ c, n c, ∏ c, s c, multi_of_homog (IsHomogeneous.prod _ _ _ fun c _ => h1 c), fun h => ?_,
    fun w hw hwb => ?_⟩
  · have := ev_scale_of_mem h fun _ => 1
    simp only [mul_one, map_prod] at this
    obtain ⟨c, -, hc⟩ := Finset.prod_eq_zero_iff.1 this
    by_cases hy : ∀ k, y ⟨k, c k⟩ ≠ 0
    · exact h2 c hy hc
    · simp [h3 c hy] at hc
  · choose c hc using hw.1
    rw [map_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ c) (h4 c w hw hc hwb)

end Block

end PositivityTheory.UnitarySelfGeneration.AlgOv
