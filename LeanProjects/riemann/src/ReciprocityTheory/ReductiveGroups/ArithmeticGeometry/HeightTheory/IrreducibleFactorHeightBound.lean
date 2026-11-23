import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HeightKerScaledSubstitutionLeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.IrreducibleFactorStructure
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.LogHeightLeTorusHeightSubst

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

abbrev UXVar (D N : ℕ) : Type := (Fin (D + 2) × Fin (N + 1)) ⊕ Fin (D + 2)

def xDeg {D N : ℕ} (s : UXVar D N →₀ ℕ) : ℕ := ∑ i, s (Sum.inr i)

def uDeg {D N : ℕ} (s : UXVar D N →₀ ℕ) : ℕ := ∑ p, s (Sum.inl p)

def XHom {R : Type*} [CommSemiring R] {D N : ℕ} (n : ℕ) (Q : MvPolynomial (UXVar D N) R) : Prop :=
  ∀ s ∈ Q.support, xDeg s = n

def UDegLE {R : Type*} [CommSemiring R] {D N : ℕ} (n : ℕ) (Q : MvPolynomial (UXVar D N) R) :
    Prop :=
  ∀ s ∈ Q.support, uDeg s ≤ n

noncomputable def hT {κ : Type} [Fintype κ] (f : MvPolynomial κ K) : ℝ :=
  ((∑ᶠ w : FinitePlace K, Real.log (ReciprocityTheory.MultiplicativeHeights.gaussAbs w f)) +
      ∑ σ : K →+* ℂ, ReciprocityTheory.MultiplicativeHeights.torusMean (MvPolynomial.map σ f)) / (Module.finrank ℚ K : ℝ)

namespace Data

variable (d : Data K ι Ω WT A)

noncomputable def evc (c : ι) :
    MvPolynomial (UXVar d.D d.N) K →ₐ[K] MvPolynomial (Fin (d.D + 2) × Fin (d.N + 1)) (A c) :=
  MvPolynomial.aeval fun v =>
    match v with
    | Sum.inl p => MvPolynomial.X p
    | Sum.inr i => ∑ j, MvPolynomial.X (i, j) * MvPolynomial.C (d.w j c)

noncomputable def laW : ℝ := meanK fun sg => ⨆ j, Real.log (d.supN sg d.wL (d.w j))

noncomputable def upB : ℝ :=
  d.PP0' * d.wsize d.wL + max 0 d.laW + Real.log (d.N + 1 : ℕ) + 1

theorem lineSection_eq_ratio_smul (hd : d.AxH 𝒜) (c : ι) (j : Fin (d.N + 1)) :
    d.w j c = d.affineCoord c j • d.w (d.jc c) c := by
  exact d.w_eq_scalarRatio_smul hd c j

theorem lineSection_pow_ne_zero (hd : d.AxH 𝒜) (c : ι) (n : ℕ) : d.w (d.jc c) c ^ n ≠ 0 := by
  haveI := hd.graded c
  have hw := hd.w_mem (d.jc c) c
  have hw0 := hd.w_base c
  induction n with
  | zero =>
    rw [pow_zero]
    haveI : Nontrivial (A c) := ⟨⟨_, _, hw0⟩⟩
    exact one_ne_zero
  | succ n ih =>
    rw [pow_succ]
    exact hd.mul_ne_zero c (SetLike.pow_mem_graded n hw) hw ih hw0

private theorem sum_support_inr_eq_xDeg {D N : ℕ} (s : UXVar D N →₀ ℕ) :
    ∑ x ∈ s.support, Sum.elim (fun _ => 0) (fun i => s (Sum.inr i)) x = xDeg s := by
  rw [xDeg, Finset.sum_subset (Finset.subset_univ _), Fintype.sum_sum_type]
  · simp
  · intro x _ hx
    cases x with
    | inl p => rfl
    | inr i => simpa using hx

theorem lineEval_eq_zero_iff (hd : d.AxH 𝒜) (c : ι) (n : ℕ) (Q : MvPolynomial (UXVar d.D d.N) K)
    (hQ : XHom n Q) : d.evc c Q = 0 ↔ d.linearSubstitution c Q = 0 := by
  haveI := hd.tower c
  have hw0 := d.lineSection_pow_ne_zero hd c n
  have hfac : d.evc c Q = MvPolynomial.map (algebraMap (Ω c) (A c)) (d.linearSubstitution c Q) *
      MvPolynomial.C (d.w (d.jc c) c ^ n) := by
    rw [Q.as_sum, map_sum, map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s hs => ?_
    simp only [evc, linearSubstitution, MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_apply, map_mul,
      MvPolynomial.map_C, Finsupp.prod, map_prod, map_pow]
    rw [← IsScalarTower.algebraMap_apply, mul_assoc]
    congr 1
    rw [← hQ s hs, ← sum_support_inr_eq_xDeg s]
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun x _ => ?_
    cases x with
    | inl p => simp
    | inr i =>
      simp only [Sum.elim_inr, map_sum, map_mul, MvPolynomial.map_X, MvPolynomial.map_C]
      rw [← mul_pow, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [d.lineSection_eq_ratio_smul hd c j, Algebra.smul_def, MvPolynomial.C_mul]
      ring
  rw [hfac]
  constructor
  · intro h
    ext β
    have hb := congrArg (MvPolynomial.coeff β) h
    rw [mul_comm, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map, MvPolynomial.coeff_zero, mul_comm,
      ← Algebra.smul_def] at hb
    rw [MvPolynomial.coeff_zero]
    exact (smul_eq_zero.1 hb).resolve_right hw0
  · intro h
    rw [h, map_zero, zero_mul]

theorem irreducible_factor_height_bound (hd : d.AxH 𝒜) (h : d.S1) (F : ι → KTp K d.D d.N)
    (hF : ∀ c, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (F c) = d.fZ h c) (c : ι)
    (hpos : 0 < ReciprocityTheory.MultiplicativeHeights.h0 (F c)) :
    ∃ (F1 : MvPolynomial (UXVar d.D d.N) K) (m deF : ℕ), 1 ≤ m ∧ 1 ≤ deF ∧
      m * deF ≤ d.delc c ∧ Irreducible F1 ∧ XHom deF F1 ∧ UDegLE ((d.D + 1) * d.delc c) F1 ∧
      ReciprocityTheory.MultiplicativeHeights.h0 (F c) ≤ m * hT F1 ∧
      ∀ (n : ℕ) (Q : MvPolynomial (UXVar d.D d.N) K), XHom n Q → (d.evc c Q = 0 ↔ F1 ∣ Q) := by
  obtain ⟨F1, κ, a, m, deF, hκ, hm, hmd, hirr, hx, hu, hG, hphiG, hmh⟩ :=
    d.irreducible_factor_structure hd h F hF c hpos
  have hy : d.affineCoord c (d.jc c) ≠ 0 := by
    intro h0
    apply hd.w_base c
    have e := d.lineSection_eq_ratio_smul hd c (d.jc c)
    rw [h0, zero_smul] at e
    exact e
  have hx0 : d.linearSubstitution c (MvPolynomial.X (Sum.inr 0)) ≠ 0 := by
    intro h0
    have e := congrArg (MvPolynomial.eval (fun p : Fin (d.D + 2) × Fin (d.N + 1) =>
      if p = (0, d.jc c) then (1 : Ω c) else 0)) h0
    simp [linearSubstitution] at e
    exact hy e
  have hκ' : d.linearSubstitution c (MvPolynomial.C κ) ≠ 0 := by
    simp [linearSubstitution, hκ]
  have hF1 : d.linearSubstitution c F1 = 0 := by
    rw [hG, map_mul, map_mul, map_pow, map_pow] at hphiG
    simp only [mul_eq_zero, pow_eq_zero_iff', hκ', hx0, false_and, false_or] at hphiG
    exact hphiG.1
  have hF1ne : F1 ≠ 0 := hirr.ne_zero
  have hspan : (Ideal.span {F1}).IsPrime := (Ideal.span_singleton_prime hF1ne).mpr hirr.prime
  have hle : Ideal.span {F1} ≤ RingHom.ker (d.scaledSubstitution c) := by
    rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, d.scaledSubstitution_of_homogeneous c deF F1 hx, hF1,
      map_zero, mul_zero]
  have hPp : (RingHom.ker (d.scaledSubstitution c)).IsPrime := RingHom.ker_isPrime _
  have heq : Ideal.span {F1} = RingHom.ker (d.scaledSubstitution c) := by
    by_contra hne
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hle hne)
    have h2 := d.height_ker_scaledSubstitution_le_one hd c
    have h3 : (Ideal.span {F1}).height ≠ 0 := by
      rw [Ne, Ideal.height_eq_zero_iff_eq_bot, Ideal.span_singleton_eq_bot]
      exact hF1ne
    have h4 : 1 ≤ (Ideal.span {F1}).height := Order.one_le_iff_ne_zero.mpr h3
    have h5 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) (h1.trans h2)
    exact absurd h5 (by norm_num)
  have hdeF : 1 ≤ deF := by
    by_contra h0
    have h0' : deF = 0 := by omega
    exact hF1ne (d.eq_zero_of_xhom_zero c F1 (fun s hs => (hx s hs).trans h0') hF1)
  have hkey : ∀ (n : ℕ) (Q : MvPolynomial (UXVar d.D d.N) K), XHom n Q →
      (d.evc c Q = 0 ↔ F1 ∣ Q) := by
    intro n Q hQ
    rw [d.lineEval_eq_zero_iff hd c n Q hQ, ← Ideal.mem_span_singleton, heq, RingHom.mem_ker,
      d.scaledSubstitution_of_homogeneous c n Q hQ]
    constructor
    · intro h0
      rw [h0, map_zero, mul_zero]
    · intro h0
      rcases mul_eq_zero.mp h0 with h1 | h1
      · exact absurd (pow_eq_zero_iff'.mp h1).1 (MvPolynomial.X_ne_zero _)
      · exact MvPolynomial.rename_injective _ (Option.some_injective _) (by rw [h1, map_zero])
  have hFne : F c ≠ 0 := by
    intro h0
    rw [h0] at hpos
    simp [ReciprocityTheory.MultiplicativeHeights.h0, ReciprocityTheory.MultiplicativeHeights.gaussAbs, ReciprocityTheory.MultiplicativeHeights.blockSphereMean] at hpos
  have hh : ReciprocityTheory.MultiplicativeHeights.h0 (F c) ≤ m * hT F1 := by
    have e1 := logHeight_le_torusHeight_subst (F c) hFne _ hmh
    rw [hG, hTX5_C_mul_X_pow_mul_pow κ hκ _ a m F1 hF1ne] at e1
    exact e1
  exact ⟨F1, m, deF, hm, hdeF, hmd, hirr, hx, hu, hh, hkey⟩

end Data

end ReciprocityTheory.ChartRestriction.G.T0
