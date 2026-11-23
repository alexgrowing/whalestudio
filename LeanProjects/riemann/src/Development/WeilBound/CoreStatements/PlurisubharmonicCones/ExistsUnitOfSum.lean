import Mathlib
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.DeterminantLatticeGradedTensor
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializesOfUnits

open AlgebraicGeometry CategoryTheory Matrix MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.TiePrimes

namespace LevelTowerAlt.N1

section Lin

variable {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V] {r : ℕ}

theorem li_of_det {b₀ b : Fin r → V} {T : Matrix (Fin r) (Fin r) Ω} (hb : LinearIndependent Ω b₀)
    (h : ∀ k, b k = ∑ k', T k' k • b₀ k') (hT : T.det ≠ 0) : LinearIndependent Ω b := by
  rw [Fintype.linearIndependent_iff] at hb ⊢
  intro g hg
  have h1 : ∑ k', (T *ᵥ g) k' • b₀ k' = ∑ k, g k • b k := by
    simp only [h, Finset.smul_sum, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun k' _ => ?_))
    rw [mul_comm]
  have h2 := hb _ (h1.trans hg)
  have h3 := Matrix.eq_zero_of_mulVec_eq_zero hT (funext h2)
  exact fun k => congrFun h3 k

theorem mat_inv {b₀ b : Fin r → V} {T : Matrix (Fin r) (Fin r) Ω}
    (h : ∀ k, b k = ∑ k', T k' k • b₀ k') (hT : T.det ≠ 0) (k : Fin r) : b₀ k = ∑ k', T⁻¹ k' k • b k' := by
  have hu : IsUnit T.det := isUnit_iff_ne_zero.2 hT
  simp only [h, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have h1 : ∀ m, ∑ k', T⁻¹ k' k * T m k' = (T * T⁻¹) m k := by
    intro m
    simp only [Matrix.mul_apply]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  simp only [← Finset.sum_smul, h1, Matrix.mul_nonsing_inv T hu, Matrix.one_apply]
  simp

theorem cast_sum {r' : ℕ} (e : r' = r) {b₀ b : Fin r → V} {T : Matrix (Fin r) (Fin r) Ω}
    (h : ∀ k, b k = ∑ k', T k' k • b₀ k') (k : Fin r') :
    (b ∘ Fin.cast e) k = ∑ k', (T.submatrix (Fin.cast e) (Fin.cast e)) k' k • (b₀ ∘ Fin.cast e) k' := by
  subst e
  exact h k

theorem cast_det {r' : ℕ} (e : r' = r) (T : Matrix (Fin r) (Fin r) Ω) :
    (T.submatrix (Fin.cast e) (Fin.cast e)).det = T.det := by
  subst e
  rfl

end Lin

section Loc

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {V : Type} [AddCommGroup V] [Module Ω V] {r : ℕ}

theorem cast_frame {r' : ℕ} (e : r' = r) {L : Lat ξ V} {b : Fin r → V} {p : Cpt ξ} (h : L.IsFrameAt b p) :
    L.IsFrameAt (b ∘ Fin.cast e) p := by
  subst e
  exact h

theorem le_span_frame {r' : ℕ} {L : Lat ξ V} {U : Submodule Ω V} (hL : L.IsVB r' U) {b : Fin r → V} {p : Cpt ξ}
    (h : L.IsFrameAt b p) : U ≤ Submodule.span Ω (Set.range b) := by
  obtain ⟨U', hpU, b', hspan, hfr⟩ := hL p (Set.mem_univ _)
  rw [← hspan, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have h1 : b' i ∈ L p := by
    rw [(hfr p (Set.mem_univ _) hpU).2]
    exact Submodule.subset_span ⟨i, rfl⟩
  rw [h.2] at h1
  exact Submodule.span_le_restrictScalars (regAt ξ p) Ω _ h1

theorem span_eq_of_unit {p : Cpt ξ} {a b : Ω} (hb : b ≠ 0) (h : unitAt ξ p (a / b)) :
    Submodule.span (regAt ξ p) {a} = Submodule.span (regAt ξ p) {b} := by
  obtain ⟨h0, h1, h2⟩ := h
  have ha : a ≠ 0 := by
    rintro rfl
    simp at h0
  apply le_antisymm
  · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    exact ⟨⟨a / b, h1⟩, by show a / b * b = a; field_simp⟩
  · rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
    exact ⟨⟨(a / b)⁻¹, h2⟩, by show (a / b)⁻¹ * a = b; field_simp⟩

private theorem isLocalRing_regAt' {p : Cpt ξ} : IsLocalRing (regAt ξ p) :=
  IsLocalRing.of_surjective' (genMap ξ p).rangeRestrict (genMap ξ p).rangeRestrict_surjective

private theorem unitAt_of_isUnit' {p : Cpt ξ} (z : regAt ξ p) (hu : IsUnit z) : unitAt ξ p (z : Ω) := by
  obtain ⟨u, rfl⟩ := hu
  refine ⟨?_, (u : regAt ξ p).2, ?_⟩
  · intro h0
    have h00 : (u : regAt ξ p) = 0 := Subtype.ext h0
    exact u.ne_zero h00
  · have h1 : (u : regAt ξ p) * ↑u⁻¹ = 1 := u.mul_inv
    have h2 : ((u : regAt ξ p) : Ω) * (((u⁻¹ : (regAt ξ p)ˣ) : regAt ξ p) : Ω) = 1 :=
      congrArg Subtype.val h1
    rw [← eq_inv_of_mul_eq_one_right h2]
    exact ((u⁻¹ : (regAt ξ p)ˣ) : regAt ξ p).2

theorem exists_unit_of_sum {p : Cpt ξ} {m : ℕ} {f cc : Fin m → Ω} (hf : ∀ l, f l ∈ regAt ξ p)
    (hc : ∀ l, cc l ∈ regAt ξ p) (h : ∑ l, cc l * f l = 1) : ∃ l, unitAt ξ p (f l) := by
  haveI := isLocalRing_regAt' (ξ := ξ) (p := p)
  by_contra hne
  push_neg at hne
  have hnu : ∀ l, ¬ IsUnit (⟨f l, hf l⟩ : regAt ξ p) :=
    fun l hu => hne l (unitAt_of_isUnit' _ hu)
  have hsum : (∑ l, (⟨cc l, hc l⟩ : regAt ξ p) * ⟨f l, hf l⟩) = 1 := by
    apply Subtype.ext
    simpa using h
  have hmem : (∑ l, (⟨cc l, hc l⟩ : regAt ξ p) * ⟨f l, hf l⟩) ∈ IsLocalRing.maximalIdeal (regAt ξ p) :=
    Ideal.sum_mem _ (fun l _ => Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hnu l)))
  rw [hsum] at hmem
  exact (IsLocalRing.mem_maximalIdeal _).1 hmem isUnit_one

theorem not_inFibre_two {p : Cpt ξ} {a b : ℕ} (ha : a.Prime) (hb : b.Prime) (hab : a ≠ b) (h : InFibre ξ a p) :
    ¬ InFibre ξ b p := by
  haveI := isLocalRing_regAt' (ξ := ξ) (p := p)
  intro hb'
  have hcop : Nat.Coprime a b := (Nat.coprime_primes ha hb).2 hab
  have hnA : ¬ IsUnit ((a : regAt ξ p)) := fun hu => h (by simpa using unitAt_of_isUnit' _ hu)
  have hnB : ¬ IsUnit ((b : regAt ξ p)) := fun hu => hb' (by simpa using unitAt_of_isUnit' _ hu)
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have h1 : (u : regAt ξ p) * (a : regAt ξ p) + (v : regAt ξ p) * (b : regAt ξ p) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → regAt ξ p) huv
  have hm : (u : regAt ξ p) * (a : regAt ξ p) + (v : regAt ξ p) * (b : regAt ξ p) ∈
      IsLocalRing.maximalIdeal (regAt ξ p) :=
    Ideal.add_mem _ (Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 hnA))
      (Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 hnB))
  rw [h1] at hm
  exact (IsLocalRing.mem_maximalIdeal _).1 hm isUnit_one

theorem mem_of_pow_mul {p : Cpt ξ} {f u : Ω} (hf : unitAt ξ p f) {n : ℕ} (h : f ^ n * u ∈ regAt ξ p) :
    u ∈ regAt ξ p := by
  obtain ⟨h0, h1, h2⟩ := hf
  have h3 : u = (f⁻¹) ^ n * (f ^ n * u) := by
    rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ h0, one_pow, one_mul]
  rw [h3]
  exact Subring.mul_mem _ (Subring.pow_mem _ h2 n) h

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

omit [∀ k, Fintype (J k)] in
theorem chartMono_add {c : ∀ k, J k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (a b : K → ℤ) :
    chartMono y c (a + b) = chartMono y c a * chartMono y c b := by
  unfold chartMono
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [Pi.add_apply, zpow_add₀ (hc k)]

omit [∀ k, Fintype (J k)] in
theorem chartMono_neg (c : ∀ k, J k) (a : K → ℤ) : chartMono y c (-a) = (chartMono y c a)⁻¹ := by
  unfold chartMono
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  rw [Pi.neg_apply, _root_.zpow_neg]

omit [∀ k, Fintype (J k)] in
theorem chartMono_sum {c : ∀ k, J k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (S : Finset ℕ) (b : ℕ → K → ℤ) :
    chartMono y c (∑ p ∈ S, b p) = ∏ p ∈ S, chartMono y c (b p) := by
  induction S using Finset.induction_on with
  | empty => simp [chartMono]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, chartMono_add hc, ih]

omit [∀ k, Fintype (J k)] in
theorem chartMono_ne {c : ∀ k, J k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (a : K → ℤ) : chartMono y c a ≠ 0 := by
  unfold chartMono
  exact Finset.prod_ne_zero_iff.2 (fun k _ => zpow_ne_zero _ (hc k))

theorem dh_eq_zero {c : ∀ k, J k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {g : MRing J} (hg : g ∈ mCoordIdeal y) :
    dh y c g = 0 := by
  have hker : mConeMap y g = 0 := RingHom.mem_ker.1 hg
  have key : ((dh y c : MRing J →ₐ[ℤ] Ω) : MRing J →+* Ω) =
      (MvPolynomial.eval (fun k => (y ⟨k, c k⟩)⁻¹)).comp
        ((mConeMap y : MRing J →ₐ[ℤ] MvPolynomial K Ω) : MRing J →+* MvPolynomial K Ω) := by
    apply MvPolynomial.ringHom_ext
    · intro n
      simp [dh, mConeMap]
    · intro p
      simp [dh, mConeMap, div_eq_mul_inv]
  have h1 := congrArg (fun φ : MRing J →+* Ω => φ g) key
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.coe_toRingHom] at h1
  rw [h1, hker, map_zero]

private theorem dh_eq_eval_inv_mConeMap (c : ∀ k, J k) (g' : MRing J) :
    dh y c g' = MvPolynomial.eval (fun k => (y ⟨k, c k⟩)⁻¹) (mConeMap y g') := by
  have key : ((dh y c : MRing J →ₐ[ℤ] Ω) : MRing J →+* Ω) =
      (MvPolynomial.eval (fun k => (y ⟨k, c k⟩)⁻¹)).comp
        ((mConeMap y : MRing J →ₐ[ℤ] MvPolynomial K Ω) : MRing J →+* MvPolynomial K Ω) := by
    apply MvPolynomial.ringHom_ext
    · intro n
      simp [dh, mConeMap]
    · intro p
      simp [dh, mConeMap, div_eq_mul_inv]
  exact congrArg (fun φ : MRing J →+* Ω => φ g') key

private theorem mConeMap_eq_C_mul_prod_of_isMultiHomog {g : MRing J} {d : K → ℕ} (hg : IsMultiHomog g d) :
    ∃ a : Ω, mConeMap y g = MvPolynomial.C a * ∏ k, MvPolynomial.X k ^ d k := by
  classical
  refine ⟨∑ m ∈ g.support, ((g.coeff m : ℤ) : Ω) * ∏ p, y p ^ m p, ?_⟩
  rw [show mConeMap y g = MvPolynomial.aeval
      (fun p : (Σ k, J k) => MvPolynomial.C (y p) * MvPolynomial.X p.1) g from rfl,
    MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hd := hg m hm
  simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod, map_mul]
  rw [Fintype.prod_sigma (fun p : (Σ k, J k) => MvPolynomial.X (R := Ω) p.1 ^ m p)]
  simp only [Finset.prod_pow_eq_pow_sum, hd]
  simp [MvPolynomial.algebraMap_apply, mul_assoc]

private theorem isUnit_of_unitAt' {p : Cpt ξ} (z : regAt ξ p) (hu : unitAt ξ p (z : Ω)) : IsUnit z :=
  IsUnit.of_mul_eq_one (a := z) ⟨(z : Ω)⁻¹, hu.2.2⟩ (Subtype.ext (by simp [hu.1]))

theorem unit_off_fibre {c : ∀ k, J k} {p : Cpt ξ} (h : InChart ξ (seg y) c p) {l : ℕ} {b : K → ℤ} {f g : MRing J}
    (hv : IsVerticalDivisorAt (mCoordIdeal y) l b f g) (hl : ¬ InFibre ξ l p) :
    unitAt ξ p (aeval y f / aeval y g * chartMono y c (-b)) := by
  haveI := isLocalRing_regAt' (ξ := ξ) (p := p)
  have hc0 : ∀ k, y ⟨k, c k⟩ ≠ 0 := ne_of_seg h.1
  obtain ⟨bf, bg, hbf, hbg, hbeq⟩ := hv.degrees
  have hPW : mCoordIdeal y ≤ Ideal.comap (dhP h) (IsLocalRing.maximalIdeal (regAt ξ p)) := by
    intro x hx
    rw [Ideal.mem_comap]
    have h0 : dhP h x = 0 := Subtype.ext (by rw [coe_dhP]; exact dh_eq_zero hc0 hx)
    rw [h0]
    exact zero_mem _
  have hrel : IsRelevant (Ideal.comap (dhP h) (IsLocalRing.maximalIdeal (regAt ξ p))) := by
    intro k
    refine ⟨c k, ?_⟩
    rw [Ideal.mem_comap]
    have h1 : dhP h (MvPolynomial.X ⟨k, c k⟩) = 1 :=
      Subtype.ext (by rw [coe_dhP]; exact dh_X_self y c hc0 k)
    rw [h1]
    exact fun hm => (IsLocalRing.mem_maximalIdeal _).1 hm isUnit_one
  have hl' : unitAt ξ p (l : Ω) := by
    by_contra hn
    exact hl hn
  have hCl : MvPolynomial.C (l : ℤ) ∉ Ideal.comap (dhP h) (IsLocalRing.maximalIdeal (regAt ξ p)) := by
    rw [Ideal.mem_comap]
    have e : dhP h (MvPolynomial.C (l : ℤ)) = ((l : ℤ) : regAt ξ p) := eq_intCast ((dhP h).comp MvPolynomial.C) l
    rw [e]
    have hu : IsUnit (((l : ℤ) : regAt ξ p)) := isUnit_of_unitAt' _ (by simpa using hl')
    exact fun hm => (IsLocalRing.mem_maximalIdeal _).1 hm hu
  obtain ⟨u, v, hu, hv', huv⟩ := hv.unit_off_fibre _ inferInstance hPW hrel hCl
  have hunit : ∀ w, w ∉ Ideal.comap (dhP h) (IsLocalRing.maximalIdeal (regAt ξ p)) →
      unitAt ξ p (dh y c w) := by
    intro w hw
    rw [Ideal.mem_comap] at hw
    have h1 : IsUnit (dhP h w) := by
      by_contra hn
      exact hw ((IsLocalRing.mem_maximalIdeal _).2 hn)
    rw [← coe_dhP h]
    exact unitAt_of_isUnit' _ h1
  have hU := hunit u hu
  have hV := hunit v hv'
  have hrel2 : dh y c u * dh y c f = dh y c v * dh y c g := by
    have h0 := dh_eq_zero hc0 huv
    rw [map_sub, map_mul, map_mul] at h0
    exact sub_eq_zero.1 h0
  have hdg : dh y c g ≠ 0 := by
    intro h0
    obtain ⟨a, ha⟩ := mConeMap_eq_C_mul_prod_of_isMultiHomog (y := y) hbg
    rw [dh_eq_eval_inv_mConeMap, ha, map_mul, MvPolynomial.eval_C, map_prod] at h0
    simp only [map_pow, MvPolynomial.eval_X] at h0
    have hprod : ∏ k, ((y ⟨k, c k⟩)⁻¹) ^ bg k ≠ 0 :=
      Finset.prod_ne_zero_iff.2 (fun k _ => pow_ne_zero _ (inv_ne_zero (hc0 k)))
    have ha0 : a = 0 := (mul_eq_zero.1 h0).resolve_right hprod
    apply hv.den_not_mem
    show g ∈ RingHom.ker (mConeMap y)
    rw [RingHom.mem_ker, ha, ha0, map_zero, zero_mul]
  have hPF : ∏ k, y ⟨k, c k⟩ ^ bf k = (∏ k, y ⟨k, c k⟩ ^ bg k) * chartMono y c b := by
    have e1 : ∀ d : K → ℕ, ∏ k, y ⟨k, c k⟩ ^ d k = chartMono y c (fun k => (d k : ℤ)) := by
      intro d
      unfold chartMono
      exact Finset.prod_congr rfl (fun k _ => (zpow_natCast _ _).symm)
    rw [e1, e1, ← chartMono_add hc0]
    congr 1
    rw [← hbeq]
    funext k
    simp
  have hCB := chartMono_ne hc0 b
  have hPG : ∏ k, y ⟨k, c k⟩ ^ bg k ≠ 0 :=
    Finset.prod_ne_zero_iff.2 (fun k _ => pow_ne_zero _ (hc0 k))
  have hdu : dh y c u ≠ 0 := hU.1
  have hQ : aeval y f / aeval y g * chartMono y c (-b) = dh y c v * (dh y c u)⁻¹ := by
    rw [aeval_eq_dh_mul y c hc0 hbf, aeval_eq_dh_mul y c hc0 hbg, chartMono_neg, hPF]
    field_simp
    linear_combination hrel2
  rw [hQ]
  refine ⟨mul_ne_zero hV.1 (inv_ne_zero hdu), Subring.mul_mem _ hV.2.1 hU.2.2, ?_⟩
  rw [mul_inv, inv_inv]
  exact Subring.mul_mem _ hV.2.2 hU.2.1

end Loc

end LevelTowerAlt.N1
