import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GoodPrimesProperties
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.NormFactorizationClause
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ComponentFormProperties
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HNormPts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.KTFiniteDimensional
import ReciprocityTheory.SemistableReduction.AevalIsWeightedHomogeneous
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HintIntOfBounds

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField MeasureTheory ReciprocityTheory.MultiplicativeHeights

theorem hint_zpow_split {F : Type*} [Field F] (x : F) (e : ℤ) :
    x ^ e = x ^ e.toNat / x ^ (-e).toNat := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg e <;> simp [zpow_neg]

theorem hint_fp_split {R Fr ι : Type*} [CommRing R] [Field Fr] [Algebra R Fr] (S : Set ι)
    (g : ι → R) (e : ι → ℤ) :
    ∃ s : Finset ι, (∀ p ∈ s, p ∈ S ∧ e p ≠ 0) ∧
      ∏ᶠ (p : ι) (_ : p ∈ S), algebraMap R Fr (g p) ^ e p =
        algebraMap R Fr (∏ p ∈ s, g p ^ (e p).toNat) /
          algebraMap R Fr (∏ p ∈ s, g p ^ (-e p).toNat) := by
  classical
  by_cases hfin : (Function.mulSupport fun p => ∏ᶠ (_ : p ∈ S), algebraMap R Fr (g p) ^ e p).Finite
  · refine ⟨hfin.toFinset, fun p hp => ?_, ?_⟩
    · rw [Set.Finite.mem_toFinset, Function.mem_mulSupport] at hp
      by_cases hpS : p ∈ S
      · exact ⟨hpS, fun h0 => hp (by simp [hpS, h0])⟩
      · exact (hp (by simp [hpS])).elim
    · rw [finprod_eq_prod _ hfin, map_prod, map_prod, ← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [Set.Finite.mem_toFinset, Function.mem_mulSupport] at hp
      have hpS : p ∈ S := by
        by_contra h
        exact hp (by simp [h])
      rw [finprod_eq_if, if_pos hpS, map_pow, map_pow]
      exact hint_zpow_split _ _
  · refine ⟨∅, by simp, ?_⟩
    rw [finprod_of_infinite_mulSupport hfin]
    simp

def HintMH {R : Type*} [CommSemiring R] {D n : ℕ} (q : MvPolynomial (Fin (D + 1) × Fin n) R) :
    Prop :=
  ∃ α : Fin (D + 1) → ℕ, α 0 = 0 ∧ IsMultiHomogeneous α q

theorem hintMH_one {R : Type*} [CommSemiring R] {D n : ℕ} :
    HintMH (1 : MvPolynomial (Fin (D + 1) × Fin n) R) := by
  refine ⟨0, rfl, fun s hs b => ?_⟩
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hs
  split_ifs at hs with h
  · subst h
    simp
  · exact absurd rfl hs

theorem hintMH_C_mul {R : Type*} [CommSemiring R] {D n : ℕ} (k : R)
    {q : MvPolynomial (Fin (D + 1) × Fin n) R} (hq : HintMH q) :
    HintMH (MvPolynomial.C k * q) := by
  obtain ⟨α, h0, hα⟩ := hq
  refine ⟨α, h0, fun s hs b => hα s ?_ b⟩
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul] at hs
  exact MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hs)

theorem hintMH_mul {R : Type*} [CommSemiring R] {D n : ℕ}
    {q q' : MvPolynomial (Fin (D + 1) × Fin n) R} (hq : HintMH q) (hq' : HintMH q') :
    HintMH (q * q') := by
  classical
  obtain ⟨α, h0, hα⟩ := hq
  obtain ⟨α', h0', hα'⟩ := hq'
  refine ⟨α + α', by simp [h0, h0'], fun s hs b => ?_⟩
  open scoped Pointwise in
  have hsub : (q * q').support ⊆ q.support + q'.support := MvPolynomial.support_mul ..
  obtain ⟨a, ha, a', ha', rfl⟩ := Finset.mem_add.mp (hsub hs)
  simp [Finset.sum_add_distrib, hα a ha b, hα' a' ha' b]

theorem hintMH_pow {R : Type*} [CommSemiring R] {D n : ℕ}
    {q : MvPolynomial (Fin (D + 1) × Fin n) R} (hq : HintMH q) (m : ℕ) : HintMH (q ^ m) := by
  induction m with
  | zero =>
    rw [pow_zero]
    exact hintMH_one
  | succ k ih =>
    rw [pow_succ]
    exact hintMH_mul ih hq

theorem hintMH_prod {R ι : Type*} [CommSemiring R] {D n : ℕ} (s : Finset ι)
    (q : ι → MvPolynomial (Fin (D + 1) × Fin n) R) (m : ι → ℕ) (hq : ∀ p ∈ s, HintMH (q p)) :
    HintMH (∏ p ∈ s, q p ^ m p) := by
  exact Finset.prod_induction _ (fun x => HintMH x) (fun a b ha hb => hintMH_mul ha hb) hintMH_one
    (fun p hp => hintMH_pow (hq p hp) (m p))

theorem hintMH_map {K : Type*} [Field K] {D n : ℕ} {q : MvPolynomial (Fin (D + 1) × Fin n) K}
    (hq : HintMH q) (φ : K →+* ℂ) : HintMH (MvPolynomial.map φ q) := by
  obtain ⟨α, h0, hα⟩ := hq
  exact ⟨α, h0, fun s hs b => hα s (MvPolynomial.support_map_subset φ q hs) b⟩

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem hint_evT_eq (sg : K →+* ℂ) (t0 : Fin (d.N + 1) → ℂ)
    (z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1)) (q : KTp K d.D d.N) :
    d.evT sg t0 (d.tOf z) q = MvPolynomial.eval (hintPt t0 z) (MvPolynomial.map sg q) := by
  rw [MvPolynomial.eval_map]
  rfl

theorem hint_good_split (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (e : Ideal (KTp K d.D d.N) → ℤ)
    (he : ∀ p ∈ d.HtOne, e p ≠ 0 → ∃ w, w ∈ d.GoodP c p) :
    ∃ a b : KTp K d.D d.N, HintMH a ∧ HintMH b ∧
      ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ e p =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a / algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b := by
  obtain ⟨s, hs, heq⟩ := hint_fp_split (Fr := KTf K d.D d.N) d.HtOne d.gen e
  have hmh : ∀ p ∈ s, HintMH (d.gen p) := fun p hp => by
    obtain ⟨hp1, hp2⟩ := hs p hp
    exact ⟨_, by simp, (d.good_primes_properties hd h c).2.1 p hp1 (he p hp1 hp2)⟩
  exact ⟨_, _, hintMH_prod s _ _ hmh, hintMH_prod s _ _ hmh, heq⟩

theorem hint_good_of_ne (c : ι) (p : Ideal (KTp K d.D d.N)) {f : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ) → ℤ}
    (hp : (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.GoodP c p), f w) ≠ 0) :
    ∃ w, w ∈ d.GoodP c p := by
  by_contra hne
  push_neg at hne
  apply hp
  simp [hne]

theorem hint_log_finprod {α : Type*} (S : Set α) (hS : S.Finite) (f : α → ℂ)
    (hf : ∀ x ∈ S, f x ≠ 0) :
    ∑ᶠ (x : α) (_ : x ∈ S), Real.log ‖f x‖ = Real.log ‖∏ᶠ (x : α) (_ : x ∈ S), f x‖ := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, finprod_mem_eq_finite_toFinset_prod _ hS, norm_prod,
    Real.log_prod]
  intro x hx
  rw [Set.Finite.mem_toFinset] at hx
  exact norm_ne_zero_iff.mpr (hf x hx)

theorem hint_intNorm (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (sg : K →+* ℂ) (g : Ω c) (hg : g ≠ 0) :
    Integrable (fun z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) =>
      ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)), Real.log ‖P g‖)
      (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  haveI : FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.omS_finite hd h c).1
  obtain ⟨κ, hκ, hN⟩ := (d.norm_factorization hd h).1 c g hg
  obtain ⟨a, b, ha, hb, hsplit⟩ := d.hint_good_split hd h c _
    (fun p _ hp => d.hint_good_of_ne c p hp)
  rw [hsplit] at hN
  have hNm0 : Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g) ≠ 0 :=
    Algebra.norm_ne_zero_iff.2 ((map_ne_zero_iff _ (algebraMap (Ω c) _).injective).2 hg)
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero, div_zero, mul_zero] at hN
    exact hNm0 hN
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div, mul_zero] at hN
    exact hNm0 hN
  set a' : KTp K d.D d.N := MvPolynomial.C κ * a with ha'
  have hkey : Algebra.norm (KTf K d.D d.N) (algebraMap (Ω c) (OmS (Ω c) d.D d.N) g) *
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b = algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a' := by
    have hbne : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 hb0
    rw [hN, ha', map_mul, ← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
    field_simp
  have hmapb : MvPolynomial.map sg b ≠ 0 :=
    (map_ne_zero_iff _ (MvPolynomial.map_injective sg sg.injective)).2 hb0
  have hmapa : MvPolynomial.map sg a' ≠ 0 :=
    (map_ne_zero_iff _ (MvPolynomial.map_injective sg sg.injective)).2
      (mul_ne_zero (by simpa using hκ) ha0)
  have hn : 0 < d.N + 1 := Nat.succ_pos _
  obtain ⟨βb, hβb0, hβb⟩ := hintMH_map hb sg
  obtain ⟨βa, hβa0, hβa⟩ := hintMH_map (hintMH_C_mul κ ha) sg
  have hIa := hint_logInt_tail hn hmapa hβa hβa0 0
  have hIb := hint_logInt_tail hn hmapb hβb hβb0 0
  refine (hIa.sub hIb).congr ?_
  filter_upwards [d.norm_at_sg hd h c sg, hint_ae_tail hn hmapb hβb hβb0 0] with z hz hbz
  obtain ⟨hfin, -, hcl1, -⟩ := hz
  have hbz' : d.evT sg 0 (d.tOf z) b ≠ 0 := by rw [hint_evT_eq]; exact hbz
  have hprod := hcl1 g a' b 0 hg hb0 hkey hbz'
  have hPg : ∀ P ∈ d.ST c sg (d.tOf z), P g ≠ 0 := fun P _ =>
    (map_ne_zero_iff P P.injective).2 hg
  have hprod0 : (∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)), P g) ≠ 0 := by
    rw [finprod_mem_eq_finite_toFinset_prod _ hfin]
    exact Finset.prod_ne_zero_iff.2 fun P hP => hPg P (hfin.mem_toFinset.1 hP)
  have haz : d.evT sg 0 (d.tOf z) a' ≠ 0 := by
    intro h0; rw [h0, zero_div] at hprod; exact hprod0 hprod.symm
  simp only [Pi.sub_apply]
  rw [hint_log_finprod _ hfin _ hPg, ← hprod, norm_div, Real.log_div (norm_ne_zero_iff.2 haz)
    (norm_ne_zero_iff.2 hbz'), hint_evT_eq, hint_evT_eq]

variable {d} in
theorem hint_line (hd : d.AxH 𝒜) {c : ι} {G : WT} {f g : A c} (hg : g ∈ 𝒜 c G) (hg0 : g ≠ 0)
    (hf : f ∈ 𝒜 c G) : f = ratio (Ω := Ω c) f g • g := by
  have h1 := hd.finrank_one c G
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨g, hg⟩ : 𝒜 c G) (by simpa using hg0)).mp h1
    ⟨f, hf⟩
  have hex : ∃ a : Ω c, f = a • g := ⟨a, by simpa using (congrArg Subtype.val ha).symm⟩
  unfold ratio
  rw [dif_pos hex]
  exact hex.choose_spec

variable {d} in
theorem hint_ratio_self (hd : d.AxH 𝒜) {c : ι} {G : WT} {g : A c} (hg : g ∈ 𝒜 c G)
    (hg0 : g ≠ 0) : ratio (Ω := Ω c) g g = 1 := by
  have hex : ∃ a : Ω c, g = a • g := ⟨1, (one_smul _ _).symm⟩
  unfold ratio
  rw [dif_pos hex]
  have h := hex.choose_spec
  have h2 : (hex.choose - 1) • g = 0 := by rw [sub_smul, one_smul, ← h, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · exact sub_eq_zero.mp h3
  · exact absurd h3 hg0

noncomputable def hintU (c : ι) (P : Ω c →+* ℂ) : EuclideanSpace ℂ (Fin (d.N + 1)) :=
  WithLp.toLp 2 (fun j => P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)))

theorem hint_one_le_U (hd : d.AxH 𝒜) (c : ι) (P : Ω c →+* ℂ) : 1 ≤ ‖d.hintU c P‖ := by
  have hr : ratio (Ω := Ω c) (d.w (d.jc c) c) (d.w (d.jc c) c) = 1 :=
    hint_ratio_self hd (hd.w_mem _ c) (hd.w_base c)
  calc (1 : ℝ) = ‖(WithLp.ofLp (d.hintU c P)) (d.jc c)‖ := by simp [hintU, hr]
    _ ≤ ‖d.hintU c P‖ := PiLp.norm_apply_le _ _

theorem hint_nrm_w (hd : d.AxH 𝒜) (c : ι) (P : Ω c →+* ℂ) (j : Fin (d.N + 1)) :
    d.nrm c d.wL (d.w j c) P =
      ‖P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))‖ * d.nrm c d.wL (d.w (d.jc c) c) P := by
  have hl := hint_line hd (hd.w_mem (d.jc c) c) (hd.w_base c) (hd.w_mem j c)
  by_cases h0 : ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c) = 0
  · conv_lhs => rw [hl, h0, zero_smul, hd.nrm_zero]
    simp [h0]
  · conv_lhs => rw [hl]
    exact hd.nrm_smul c P _ (hd.w_mem _ c) (hd.w_base c) h0

theorem hint_be_eq (hd : d.AxH 𝒜) (c : ι) (P : Ω c →+* ℂ) :
    d.be c P = d.nrm c d.wL (d.w (d.jc c) c) P * ‖d.hintU c P‖ := by
  have hn : 0 ≤ d.nrm c d.wL (d.w (d.jc c) c) P := (hd.nrm_pos c P (hd.w_mem _ c) (hd.w_base c)).le
  have hs : ∑ j, d.nrm c d.wL (d.w j c) P ^ 2 =
      (∑ j, ‖P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))‖ ^ 2) *
        d.nrm c d.wL (d.w (d.jc c) c) P ^ 2 := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [hint_nrm_w d hd c P j, mul_pow]
  rw [Data.be, hs, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hn, mul_comm, EuclideanSpace.norm_eq]
  simp [hintU]

theorem hint_U_coord_ne (hd : d.AxH 𝒜) (c : ι) (P : Ω c →+* ℂ) :
    (WithLp.ofLp (d.hintU c P) : Fin (d.N + 1) → ℂ) ≠ 0 := by
  intro h
  have := congrFun h (d.jc c)
  simp [hintU, hint_ratio_self hd (hd.w_mem _ c) (hd.w_base c)] at this

theorem hint_intU (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (sg : K →+* ℂ) :
    Integrable (fun z : ReciprocityTheory.MultiplicativeHeights.BlockSphere d.D (d.N + 1) =>
      ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)), Real.log ‖d.hintU c P‖)
      (ReciprocityTheory.MultiplicativeHeights.blockSphereProb d.D (d.N + 1)) := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  obtain ⟨F, hF, hF0, hFmh, -, -⟩ := d.componentForm_properties hd h c
  obtain ⟨a, b, ha, hb, hsplit⟩ := d.hint_good_split hd h c
    (fun p => d.nPMM h c (d.w (d.jc c) c) p)
    (fun p _ hp => d.hint_good_of_ne c p
      (f := fun w => (d.fze h c w : ℤ) * d.ordMM c (d.Wres c w) (d.w (d.jc c) c)) hp)
  have hfZ : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) F =
      Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) *
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a /
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b) := by
    rw [hF, ← hsplit]; rfl
  have hinj := IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero, div_zero, mul_zero, ← map_zero (algebraMap (KTp K d.D d.N) (KTf K d.D d.N))]
      at hfZ
    exact hF0 (hinj hfZ)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div, mul_zero, ← map_zero (algebraMap (KTp K d.D d.N) (KTf K d.D d.N))]
      at hfZ
    exact hF0 (hinj hfZ)
  have hkey : Algebra.norm (KTf K d.D d.N) (d.rationalBaseRow c) *
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a =
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (F * b) := by
    have hbne : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) b ≠ 0 :=
      (map_ne_zero_iff _ hinj).2 hb0
    rw [map_mul, hfZ]
    field_simp
  have hmi := MvPolynomial.map_injective (σ := TVar d.D d.N) sg sg.injective
  have hFc0 : MvPolynomial.map sg F ≠ 0 := (map_ne_zero_iff _ hmi).2 hF0
  have hac0 : MvPolynomial.map sg a ≠ 0 := (map_ne_zero_iff _ hmi).2 ha0
  have hbc0 : MvPolynomial.map sg b ≠ 0 := (map_ne_zero_iff _ hmi).2 hb0
  have hFcmh := isMultiHomogeneous_map_ring _ F hFmh sg
  obtain ⟨αa, hαa0, hαa⟩ := hintMH_map ha sg
  obtain ⟨αb, hαb0, hαb⟩ := hintMH_map hb sg
  have hn : 0 < d.N + 1 := Nat.succ_pos _
  haveI := sphereMeasure_isProbability hn
  haveI := blockSphereMeasure_isProbability (B := d.D) hn
  have I1 := hint_fubini hn hFc0 hFcmh
  have I2 := hint_logInt_tail hn hac0 hαa hαa0 0
  have I3 := hint_logInt_tail hn hbc0 hαb hαb0 0
  refine (((I1.sub I2).add I3).add
    (integrable_const ((d.delc c : ℝ) * (harmonic d.N : ℝ) / 2))).congr ?_
  filter_upwards [d.norm_at_sg hd h c sg, hint_ae_tail hn hac0 hαa hαa0 0,
    hint_ae_tail hn hbc0 hαb hαb0 0] with z hz haz hbz
  obtain ⟨hfin, hcard, -, hcl2⟩ := hz
  set S := d.ST c sg (d.tOf z) with hS
  have hind : ∀ (q : MvPolynomial (Fin (d.D + 1) × Fin (d.N + 1)) ℂ) (α : Fin (d.D + 1) → ℕ),
      α 0 = 0 → IsMultiHomogeneous α q → ∀ t0 : Fin (d.N + 1) → ℂ,
      MvPolynomial.eval (hintPt t0 z) q = MvPolynomial.eval (hintPt 0 z) q := by
    intro q α h0 hq t0
    refine hint_eval_indep hq h0 _ _ ?_
    rintro ⟨i, j⟩ hi
    obtain ⟨k, rfl⟩ := Fin.exists_succ_eq.2 hi
    rfl
  have hlin : ∀ᵐ s ∂(sphereProb (d.N + 1)), ∀ P ∈ S,
      ∑ j, (WithLp.ofLp (d.hintU c P)) j * spherePoint s j ≠ 0 :=
    (Filter.eventually_all_finite hfin).2 fun P _ => hint_lin_ae _ (d.hint_U_coord_ne hd c P)
  have hpt : ∀ᵐ s ∂(sphereProb (d.N + 1)),
      Real.log ‖MvPolynomial.eval (hintPt (spherePoint s) z) (MvPolynomial.map sg F)‖ =
        Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a)‖ -
          Real.log ‖MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg b)‖ +
          ∑ P ∈ hfin.toFinset,
            Real.log ‖∑ j, (WithLp.ofLp (d.hintU c P)) j * spherePoint s j‖ := by
    filter_upwards [hlin] with s hs
    have haz' : d.evT sg (spherePoint s) (d.tOf z) a ≠ 0 := by
      rw [hint_evT_eq, hind _ _ hαa0 hαa]; exact haz
    have hq := hcl2 (F * b) a (spherePoint s) ha0 hkey haz'
    rw [hint_evT_eq, hint_evT_eq, map_mul, map_mul, hind _ _ hαa0 hαa,
      hind (MvPolynomial.map sg b) _ hαb0 hαb] at hq
    have hL : ∀ P ∈ S, (∑ j, spherePoint s j * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) ≠ 0 := by
      intro P hP
      have := hs P hP
      simpa [hintU, mul_comm] using this
    have hprod0 : (∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ S),
        ∑ j, spherePoint s j * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) ≠ 0 := by
      rw [finprod_mem_eq_finite_toFinset_prod _ hfin]
      exact Finset.prod_ne_zero_iff.2 fun P hP => hL P (hfin.mem_toFinset.1 hP)
    have hFz : MvPolynomial.eval (hintPt (spherePoint s) z) (MvPolynomial.map sg F) ≠ 0 := by
      intro h0; rw [h0, zero_mul, zero_div] at hq; exact hprod0 hq.symm
    have heq : MvPolynomial.eval (hintPt (spherePoint s) z) (MvPolynomial.map sg F) =
        MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg a) *
          (∏ᶠ (P : Ω c →+* ℂ) (_ : P ∈ S),
            ∑ j, spherePoint s j * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) /
          MvPolynomial.eval (hintPt 0 z) (MvPolynomial.map sg b) := by
      rw [← hq]; field_simp
    rw [heq, norm_div, norm_mul, Real.log_div (by simpa using mul_ne_zero haz hprod0)
      (norm_ne_zero_iff.2 hbz), Real.log_mul (norm_ne_zero_iff.2 haz)
      (norm_ne_zero_iff.2 hprod0), ← hint_log_finprod _ hfin _ hL,
      finsum_mem_eq_finite_toFinset_sum _ hfin]
    have : ∀ P ∈ hfin.toFinset, Real.log ‖∑ j, spherePoint s j *
        P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))‖ =
        Real.log ‖∑ j, (WithLp.ofLp (d.hintU c P)) j * spherePoint s j‖ := by
      intro P _; simp [hintU, mul_comm]
    rw [Finset.sum_congr rfl this]; ring
  have hInt : ∀ P ∈ hfin.toFinset, Integrable (fun s : UnitSphereC (d.N + 1) =>
      Real.log ‖∑ j, (WithLp.ofLp (d.hintU c P)) j * spherePoint s j‖) (sphereProb (d.N + 1)) :=
    fun P _ => (ReciprocityTheory.MultiplicativeHeights.Closed.sphereLinLog (d.N + 1) (d.hintU c P)
      (fun h0 => d.hint_U_coord_ne hd c P (by rw [h0]; rfl))).1
  simp only [Pi.add_apply, Pi.sub_apply]
  rw [integral_congr_ae hpt, integral_add (integrable_const _) (integrable_finset_sum _ hInt),
    integral_const, integral_finset_sum _ hInt, finsum_mem_eq_finite_toFinset_sum _ hfin]
  have hval : ∀ P ∈ hfin.toFinset, ∫ s, Real.log ‖∑ j, (WithLp.ofLp (d.hintU c P)) j *
      spherePoint s j‖ ∂(sphereProb (d.N + 1)) = Real.log ‖d.hintU c P‖ - (harmonic d.N : ℝ) / 2 := by
    intro P _
    have := (ReciprocityTheory.MultiplicativeHeights.Closed.sphereLinLog (d.N + 1) (d.hintU c P)
      (fun h0 => d.hint_U_coord_ne hd c P (by rw [h0]; rfl))).2
    simpa using this
  rw [Finset.sum_congr rfl hval, Finset.sum_sub_distrib, Finset.sum_const,
    ← Set.ncard_eq_toFinset_card _ hfin, hcard]
  simp only [probReal_univ, one_smul, nsmul_eq_mul]
  ring

end Data

end ReciprocityTheory.ChartRestriction.G.T0
