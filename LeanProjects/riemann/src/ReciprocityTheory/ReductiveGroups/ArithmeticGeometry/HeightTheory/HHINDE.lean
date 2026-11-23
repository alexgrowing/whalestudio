import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HHINDD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.IntNsg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.LogHeightGeneratorLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.IntegralLeOfAeLeAffine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.LogNormNonneg

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem exists_smul_eq (hd : d.AxH 𝒜) {c : ι} {G : WT} {f g : A c} (hf : f ∈ 𝒜 c G) (hf0 : f ≠ 0)
    (hg : g ∈ 𝒜 c G) (hg0 : g ≠ 0) : ∃ a : Ω c, a ≠ 0 ∧ a • f = g := by
  have h1 := hd.finrank_one c G
  have hne : (⟨f, hf⟩ : 𝒜 c G) ≠ 0 := by
    rwa [Ne, Submodule.mk_eq_zero]
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).1 h1 ⟨g, hg⟩
  have ha' : a • f = g := congrArg Subtype.val ha
  refine ⟨a, ?_, ha'⟩
  rintro rfl
  exact hg0 (by rw [← ha', zero_smul])

theorem Hgt_indep (hd : d.AxH 𝒜) (h : d.S1) (G : WT) (ta ta' : ∀ c, A c)
    (hta : ∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) (hta' : ∀ c, ta' c ∈ 𝒜 c G ∧ ta' c ≠ 0)
    (hI : d.IntOK G ta) (hI' : d.IntOK G ta') : d.Hgt h G ta = d.Hgt h G ta' := by
  choose a ha hae using fun c => d.exists_smul_eq hd (hta c).1 (hta c).2 (hta' c).1 (hta' c).2
  have he : ta' = fun c => a c • ta c := funext fun c => (hae c).symm
  subst he
  rw [d.Hgt_eq_AH, d.Hgt_eq_AH]
  refine (d.AH_smul hd h _ _ ta a ha (fun c v hv => hd.ord_smul c v hv (a c) (hta c).1 (hta c).2 (ha c))
    (fun c => hd.a3' c (hta c).1 (hta c).2) (fun c => hd.a3' c (hta' c).1 (hta' c).2)
    (fun c => (d.good_primes_properties hd h c).2.2.1 G (ta c) (hta c).1 (hta c).2)
    (fun c P => hd.nrm_smul c P (a c) (hta c).1 (hta c).2 (ha c))
    (fun c P => (hd.nrm_pos c P (hta c).1 (hta c).2).ne') hI hI').symm

theorem Hgt_pow (hd : d.AxH 𝒜) (h : d.S1) (G : WT) (f : ∀ c, A c)
    (hf : ∀ c, f c ∈ 𝒜 c G ∧ f c ≠ 0) (hI : d.IntOK G f) (n : ℕ) :
    (∀ c, (f ^ (n + 1)) c ∈ 𝒜 c ((n + 1) • G) ∧ (f ^ (n + 1)) c ≠ 0) ∧
      d.IntOK ((n + 1) • G) (f ^ (n + 1)) ∧
      d.Hgt h ((n + 1) • G) (f ^ (n + 1)) = ((n + 1 : ℕ) : ℝ) * d.Hgt h G f := by
  induction n with
  | zero =>
    refine ⟨fun c => ?_, ?_, ?_⟩ <;>
      simp only [zero_add, pow_one, one_smul, one_nsmul, Nat.cast_one, one_mul]
    · exact hf c
    · exact hI
  | succ n ih =>
    obtain ⟨hm, hI', hH⟩ := ih
    have hmem : ∀ c, (f ^ (n + 1 + 1)) c ∈ 𝒜 c ((n + 1 + 1) • G) ∧ (f ^ (n + 1 + 1)) c ≠ 0 := by
      intro c
      haveI := hd.graded c
      rw [pow_succ, succ_nsmul, Pi.mul_apply]
      exact ⟨SetLike.GradedMul.mul_mem (hm c).1 (hf c).1,
        hd.mul_ne_zero c (hm c).1 (hf c).1 (hm c).2 (hf c).2⟩
    obtain ⟨hI2, hH2⟩ := d.Hgt_mul hd h ((n + 1) • G) G (f ^ (n + 1)) f hm hf hI' hI
    rw [← pow_succ, ← succ_nsmul] at hI2 hH2
    refine ⟨hmem, hI2, ?_⟩
    rw [hH2, hH]
    push_cast
    ring

theorem Hgt_pow' (hd : d.AxH 𝒜) (h : d.S1) (G : WT) (f : ∀ c, A c)
    (hf : ∀ c, f c ∈ 𝒜 c G ∧ f c ≠ 0) (hI : d.IntOK G f) (n : ℕ) (hn : 0 < n) :
    (∀ c, (f ^ n) c ∈ 𝒜 c (n • G) ∧ (f ^ n) c ≠ 0) ∧ d.IntOK (n • G) (f ^ n) ∧
      d.Hgt h (n • G) (f ^ n) = (n : ℝ) * d.Hgt h G f := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact d.Hgt_pow hd h G f hf hI m

theorem wx_mem (hd : d.AxH 𝒜) (x : Fin (d.N + 1) → K) (c : ι) : d.wx x c ∈ 𝒜 c d.wL := by
  haveI := hd.tower c
  rw [Data.wx, Finset.sum_apply]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [Pi.smul_apply, ← algebraMap_smul (Ω c) (x j) (d.w j c)]
  exact Submodule.smul_mem _ _ (hd.w_mem j c)

theorem intOK_of (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) (G : WT)
    (hG : G ∈ ({d.wL, d.n1 • d.wde, (2 : ℕ) • d.G1, d.wF, d.G2} : Set WT)) (ta : ∀ c, A c)
    (hta : ∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) : d.IntOK G ta :=
  fun c sg => (d.int_Nsg hd h hI2be c sg).1 G (ta c) hG (hta c).1 (hta c).2

theorem weight_double_eq_scaled_line : d.n1 • ((2 : ℕ) • d.G1) + (2 : ℕ) • (d.n1 • d.wde) = (2 * d.n1) • d.wL := by
  simp only [Data.G1, smul_sub, smul_smul]
  rw [mul_comm d.n1 2]
  exact sub_add_cancel _ _

theorem weight_sum_eq_scaled_line : d.wF + d.G2 = (d.D + 4) • d.wL := by
  simp only [Data.G2]
  abel

theorem degree_multiplier_pos (hd : d.AxH 𝒜) : 0 < d.n1 := Nat.mul_pos hd.i_ge hd.g_zero_ge_ask_sum

theorem h_ind' (hd : d.AxH 𝒜) (h : d.S1) (hI2be : d.HeightIntegralBoundEstimate) :
    (∀ (G : WT) (ta ta' : ∀ c, A c),
      G ∈ ({d.wL, d.n1 • d.wde, (2 : ℕ) • d.G1, d.wF, d.G2} : Set WT) →
      (∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) → (∀ c, ta' c ∈ 𝒜 c G ∧ ta' c ≠ 0) →
      d.Hgt h G ta = d.Hgt h G ta') ∧
    (∀ f f' : ∀ c, A c, (∀ c, f c ∈ 𝒜 c d.wL ∧ f c ≠ 0) → (∀ c, f' c ∈ 𝒜 c d.wL ∧ f' c ≠ 0) →
      d.HgtMM h f = d.HgtMM h f') ∧
    (∀ x : Fin (d.N + 1) → K, (∀ c, d.wx x c ≠ 0) →
      (d.n1 : ℝ) * d.Hgt h ((2 : ℕ) • d.G1) d.ta1 + 2 * d.Hgt h (d.n1 • d.wde) d.et =
        2 * d.n1 * d.Hgt h d.wL (d.wx x)) ∧
    (∀ (x : Fin (d.N + 1) → K) (ta' : ∀ c, A c), (∀ c, d.wx x c ≠ 0) →
      (∀ c, ta' c ∈ 𝒜 c d.wF ∧ ta' c ≠ 0) →
      d.Hgt h d.wF ta' + d.Hgt h d.G2 d.ta2 = (d.D + 4) * d.Hgt h d.wL (d.wx x)) := by
  have hmemS : ∀ G, G ∈ ({d.wL, d.n1 • d.wde, (2 : ℕ) • d.G1, d.wF, d.G2} : Set WT) → True :=
    fun _ _ => trivial
  refine ⟨fun G ta ta' hG hta hta' => d.Hgt_indep hd h G ta ta' hta hta'
      (d.intOK_of hd h hI2be G hG ta hta) (d.intOK_of hd h hI2be G hG ta' hta'), ?_, ?_, ?_⟩
  · intro f f' hf hf'
    choose a ha hae using fun c => d.exists_smul_eq hd (hf c).1 (hf c).2 (hf' c).1 (hf' c).2
    have he : f' = fun c => a c • f c := funext fun c => (hae c).symm
    subst he
    have hbe : ∀ c P, d.be c P ≠ 0 := fun c P => by
      rw [d.hint_be_eq hd c P]
      exact (mul_pos (hd.nrm_pos c P (hd.w_mem (d.jc c) c) (hd.w_base c))
        (by linarith [d.hint_one_le_U hd c P])).ne'
    have hOs : ∀ c v, d.admitted c v →
        ((d.ordMM c v (a c • f c) : ℤ) : WithTop ℤ) = v (a c) + (d.ordMM c v (f c) : WithTop ℤ) := by
      intro c v hv
      have e := hd.ord_smul c v hv (a c) (hf c).1 (hf c).2 (ha c)
      have hvt : v (a c) ≠ ⊤ := by rw [Ne, AddValuation.top_iff]; exact ha c
      obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 hvt
      rw [← hk] at e ⊢
      unfold ordMM
      norm_cast at e ⊢
      omega
    have hOfin : ∀ c (g : A c), g ∈ 𝒜 c d.wL → g ≠ 0 →
        {v | d.admitted c v ∧ d.ordMM c v g ≠ 0}.Finite := by
      intro c g hg hg0
      refine ((hd.a3' c hg hg0).union (Set.finite_iUnion fun j : {j // d.w j c ≠ 0} =>
        hd.a3' c (hd.w_mem j.1 c) j.2)).subset ?_
      rintro v ⟨hv, hne⟩
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_exists, not_and,
        not_not] at hcon
      apply hne
      have hne' : Nonempty {j // d.w j c ≠ 0} := ⟨⟨d.jc c, hd.w_base c⟩⟩
      unfold ordMM
      rw [hcon.1 hv]
      have : (fun j : {j // d.w j c ≠ 0} => d.ord c v d.wL (d.w j c)) = fun _ => 0 :=
        funext fun j => hcon.2 j hv
      rw [this, ciInf_const]; rfl
    have hsm : ∀ c, a c • f c ∈ 𝒜 c d.wL ∧ a c • f c ≠ 0 := fun c =>
      ⟨Submodule.smul_mem _ _ (hf c).1, smul_ne_zero (ha c) (hf c).2⟩
    rw [d.HgtMM_eq_AH, d.HgtMM_eq_AH]
    refine (d.AH_smul hd h (fun c v g => d.ordMM c v g) (fun c g P => d.nrm c d.wL g P / d.be c P) f a ha hOs (fun c => hOfin c _ (hf c).1 (hf c).2)
      (fun c => hOfin c _ (hsm c).1 (hsm c).2)
      (fun c => (d.good_primes_properties hd h c).2.2.2 (f c) (hf c).1 (hf c).2)
      (fun c P => by
        rw [hd.nrm_smul c P (a c) (hf c).1 (hf c).2 (ha c), mul_div_assoc])
      (fun c P => div_ne_zero (hd.nrm_pos c P (hf c).1 (hf c).2).ne' (hbe c P))
      (fun c sg => (d.int_Nsg hd h hI2be c sg).2 (f c) (hf c).1 (hf c).2)
      (fun c sg => (d.int_Nsg hd h hI2be c sg).2 _ (hsm c).1 (hsm c).2)).symm
  · intro x hx
    have hw : ∀ c, d.wx x c ∈ 𝒜 c d.wL ∧ d.wx x c ≠ 0 := fun c => ⟨d.wx_mem hd x c, hx c⟩
    have hIw := d.intOK_of hd h hI2be d.wL (by simp) _ hw
    have hn1 := d.degree_multiplier_pos hd
    have ht1 : ∀ c, d.ta1 c ∈ 𝒜 c ((2 : ℕ) • d.G1) ∧ d.ta1 c ≠ 0 := fun c => ⟨hd.firstSectionMem c, hd.firstSectionNeZero c⟩
    have het : ∀ c, d.et c ∈ 𝒜 c (d.n1 • d.wde) ∧ d.et c ≠ 0 := fun c => ⟨hd.et_mem c, hd.et_ne c⟩
    obtain ⟨m1, I1, H1⟩ := d.Hgt_pow' hd h _ d.ta1 ht1 (d.intOK_of hd h hI2be _ (by simp) _ ht1) d.n1 hn1
    obtain ⟨m2, I2, H2⟩ := d.Hgt_pow' hd h _ d.et het (d.intOK_of hd h hI2be _ (by simp) _ het) 2 two_pos
    obtain ⟨m3, I3, H3⟩ := d.Hgt_pow' hd h _ _ hw hIw (2 * d.n1) (by omega)
    obtain ⟨I4, H4⟩ := d.Hgt_mul hd h _ _ _ _ m1 m2 I1 I2
    have m4 : ∀ c, (d.ta1 ^ d.n1 * d.et ^ 2) c ∈ 𝒜 c (d.n1 • ((2 : ℕ) • d.G1) + (2 : ℕ) • (d.n1 • d.wde)) ∧
        (d.ta1 ^ d.n1 * d.et ^ 2) c ≠ 0 := fun c => by
      have := hd.graded c
      rw [Pi.mul_apply]
      exact ⟨SetLike.mul_mem_graded (m1 c).1 (m2 c).1, hd.mul_ne_zero c (m1 c).1 (m2 c).1 (m1 c).2 (m2 c).2⟩
    rw [d.weight_double_eq_scaled_line] at I4 H4 m4
    have := d.Hgt_indep hd h _ _ _ m4 m3 I4 I3
    rw [H4, H1, H2, H3] at this
    push_cast at this
    linarith
  · intro x ta' hx hta'
    have hw : ∀ c, d.wx x c ∈ 𝒜 c d.wL ∧ d.wx x c ≠ 0 := fun c => ⟨d.wx_mem hd x c, hx c⟩
    have hIw := d.intOK_of hd h hI2be d.wL (by simp) _ hw
    have ht2 : ∀ c, d.ta2 c ∈ 𝒜 c d.G2 ∧ d.ta2 c ≠ 0 := fun c => ⟨hd.secondSectionMem c, hd.secondSectionNeZero c⟩
    obtain ⟨m3, I3, H3⟩ := d.Hgt_pow' hd h _ _ hw hIw (d.D + 4) (by omega)
    obtain ⟨I4, H4⟩ := d.Hgt_mul hd h _ _ _ _ hta' ht2 (d.intOK_of hd h hI2be _ (by simp) _ hta')
      (d.intOK_of hd h hI2be _ (by simp) _ ht2)
    have m4 : ∀ c, (ta' * d.ta2) c ∈ 𝒜 c (d.wF + d.G2) ∧ (ta' * d.ta2) c ≠ 0 := fun c => by
      have := hd.graded c
      rw [Pi.mul_apply]
      exact ⟨SetLike.mul_mem_graded (hta' c).1 (ht2 c).1,
        hd.mul_ne_zero c (hta' c).1 (ht2 c).1 (hta' c).2 (ht2 c).2⟩
    rw [d.weight_sum_eq_scaled_line] at I4 H4 m4
    have := d.Hgt_indep hd h _ _ _ m4 m3 I4 I3
    rw [H4, H3] at this
    push_cast at this
    linarith

end Data

end ReciprocityTheory.ChartRestriction.G.T0

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights MeasureTheory IsDedekindDomain

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem four_sg (hd : d.AxH 𝒜) (h : d.S1) (G : WT) (ta : ∀ c, A c)
    (hta : ∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0) (sg : K →+* ℂ)
    (hbdd : BddAbove (Set.range fun p : (Σ c, PT (Ω := Ω c) sg) => d.nrm p.1 G (ta p.1) p.2))
    (c : ι) (hint : Integrable (fun z : BlockSphere d.D (d.N + 1) =>
        ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => spherePoint (z i) j)),
          Real.log (d.nrm c G (ta c) P)) (blockSphereProb d.D (d.N + 1))) :
    -((d.delc c : ℝ) * Real.log (d.supN sg G ta)) ≤
      ∫ z, (∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => spherePoint (z i) j)),
        -Real.log (d.nrm c G (ta c) P)) ∂(blockSphereProb d.D (d.N + 1)) := by
  have := blockSphereMeasure_isProbability (B := d.D) (Nat.succ_pos d.N)
  have I2 := d.int_neg c sg (fun P => Real.log (d.nrm c G (ta c) P)) hint
  have k := integral_le_of_ae_le_affine (blockSphereProb d.D (d.N + 1)) (fun _ => (0 : ℝ)) _ _
    ((d.delc c : ℝ) * Real.log (d.supN sg G ta)) 0 (integrable_const 0) I2 I2 ?_
  · simp only [integral_zero, zero_mul, add_zero] at k
    linarith
  filter_upwards [d.norm_at_sg hd h c sg] with z hz
  obtain ⟨hfin0, hcard0, -, -⟩ := hz
  have hfin : (d.ST c sg (fun i j => spherePoint (z i) j)).Finite := hfin0
  have hcard : (d.ST c sg (fun i j => spherePoint (z i) j)).ncard = d.delc c := hcard0
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
  rw [Set.ncard_eq_toFinset_card _ hfin] at hcard
  have e : (d.delc c : ℝ) * Real.log (d.supN sg G ta) =
      ∑ P ∈ hfin.toFinset, Real.log (d.supN sg G ta) := by
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
  rw [e, zero_mul, add_zero, ← Finset.sum_add_distrib]
  refine Finset.sum_nonneg fun P hP => ?_
  rw [Set.Finite.mem_toFinset] at hP
  have hn := hd.nrm_pos c P (hta c).1 (hta c).2
  have hle : d.nrm c G (ta c) P ≤ d.supN sg G ta :=
    le_ciSup (f := fun p : (Σ c, PT (Ω := Ω c) sg) => d.nrm p.1 G (ta p.1) p.2) hbdd ⟨c, ⟨P, hP.1⟩⟩
  have := Real.log_le_log hn hle
  linarith

theorem sum_mult_logHeight_lower (hd : d.AxH 𝒜) (h : d.S1) (G : WT) (c : ι) (f : A c) (hf : f ∈ 𝒜 c G)
    (hf0 : f ≠ 0) (hord : ∀ v, d.admitted c v → 0 ≤ d.ord c v G f) :
    -((d.D : ℝ) * (((∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        d.nP h c G f p * (d.dg (d.gen p) : ℤ) : ℤ)) : ℝ) * (Real.log (d.N + 1 : ℕ) + 1 / 2)) ≤
      ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), (d.nP h c G f p : ℝ) * h0 (d.gen p) := by
  classical
  have hfin := (d.good_primes_properties hd h c).2.2.1 G f hf hf0
  set S := hfin.toFinset
  have mem : ∀ p, p ∈ d.HtOne → d.nP h c G f p ≠ 0 → p ∈ S := fun p hp h1 => by
    simp only [S, Set.Finite.mem_toFinset]; exact ⟨hp, h1⟩
  rw [fsum_eq_sum _ S (fun p => d.nP h c G f p * (d.dg (d.gen p) : ℤ))
      (fun p hp h0 => mem p hp fun e => h0 (by simp [e])),
    fsum_eq_sum _ S (fun p => (d.nP h c G f p : ℝ) * h0 (d.gen p))
      (fun p hp h0 => mem p hp fun e => h0 (by simp [e]))]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun p _ => ?_
  by_cases hp : p ∈ d.HtOne
  · simp only [Set.indicator_of_mem hp]
    by_cases hg : ∃ w, w ∈ d.GoodP c p
    · have hL := d.logHeight_generator_lower_bound hd h c hp hg
      have hn0 : (0 : ℝ) ≤ d.nP h c G f p := by exact_mod_cast d.nP_nonneg hd h c hp G f hord
      push_cast at hL ⊢
      nlinarith [mul_le_mul_of_nonneg_left hL hn0]
    · push_neg at hg
      have hG : d.GoodP c p = ∅ := Set.eq_empty_iff_forall_notMem.mpr hg
      have e2 : d.nP h c G f p = 0 := by unfold nP; rw [hG]; simp
      rw [e2]; simp
  · simp [Set.indicator_of_notMem hp]

theorem h_four' (hd : d.AxH 𝒜) (h : d.S1) (G : WT) (ta : ∀ c, A c)
    (hta : ∀ c, ta c ∈ 𝒜 c G ∧ ta c ≠ 0)
    (hord : ∀ c (v : AddValuation (Ω c) (WithTop ℤ)), d.admitted c v → 0 ≤ d.ord c v G (ta c))
    (hbdd : ∀ sg : K →+* ℂ, BddAbove (Set.range fun p : (Σ c, PT (Ω := Ω c) sg) => d.nrm p.1 G (ta p.1) p.2))
    (hint : ∀ (c : ι) (sg : K →+* ℂ), MeasureTheory.Integrable (fun z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) =>
        ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (fun i j => ReciprocityTheory.MultiplicativeHeights.spherePoint (z i) j)),
          Real.log (d.nrm c G (ta c) P)) (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1))) :
    -(d.del * meanK (fun sg => Real.log (d.supN sg G ta))) -
        d.D * d.aG h G ta * (Real.log (d.N + 1 : ℕ) + 1 / 2) ≤ d.Hgt h G ta ∧
      (∑ᶠ la, d.NlaG h G ta la * logNorm la) / (Module.finrank ℚ K : ℝ) ≤
        d.Hgt h G ta + d.del * meanK (fun sg => Real.log (d.supN sg G ta)) +
          d.D * d.aG h G ta * (Real.log (d.N + 1 : ℕ) + 1 / 2) := by

  have hA : 0 ≤ (∑ᶠ la, d.NlaG h G ta la * logNorm la) / (Module.finrank ℚ K : ℝ) := by
    refine div_nonneg (finsum_nonneg fun la => mul_nonneg ?_ (logNorm_nonneg la)) (Nat.cast_nonneg _)
    exact Finset.sum_nonneg fun c _ => finsum_nonneg fun w => finsum_nonneg fun hw =>
      mul_nonneg (Nat.cast_nonneg _) (by exact_mod_cast hord c _ (d.admissible_over_prime hd h la c w hw).1)

  have hB : -(d.del * meanK (fun sg => Real.log (d.supN sg G ta))) ≤ meanK (d.Nsg G ta) := by
    unfold meanK
    rw [← mul_div_assoc, ← neg_div, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun sg _ => ?_) (Nat.cast_nonneg _)
    unfold Nsg del
    push_cast
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun c _ => d.four_sg hd h G ta hta sg (hbdd sg) c (hint c sg)

  have hC : -((d.D : ℝ) * d.aG h G ta * (Real.log (d.N + 1 : ℕ) + 1 / 2)) ≤ d.h0f h G ta := by
    unfold aG h0f
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun c _ => ?_
    have k := d.sum_mult_logHeight_lower hd h G c (ta c) (hta c).1 (hta c).2 (fun v hv => hord c v hv)
    push_cast at k
    exact k
  have hH : d.Hgt h G ta = (∑ᶠ la, d.NlaG h G ta la * logNorm la) / (Module.finrank ℚ K : ℝ) +
      meanK (d.Nsg G ta) + d.h0f h G ta := rfl
  constructor
  · rw [hH]; linarith
  · rw [hH]; linarith

end Data

end ReciprocityTheory.ChartRestriction.G.T0
