import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsIdealDenominator
import Formalism.PadicSubsetSums.CentralIdempotents.CentralIdempotentIntegral
import Formalism.PadicSubsetSums.StableGradedCounts.TWBoundedSeriesIntegral
import Formalism.PadicSubsetSums.StableGradedCounts.TWReuse
import Formalism.PadicSubsetSums.StableGradedCounts.TWUnitBallLattice

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions

namespace Formalism.MainNotions.ExistsIdealDenominator

open Formalism.IrreducibleCountingLemmas.TW

section Dense

variable (l : ℕ) [Fact l.Prime]

theorem norm_l : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  have h := PadicComplex.norm_extends' l (l : ℚ_[l])
  rw [Padic.norm_p, map_natCast, PadicComplex.coe_natCast] at h
  exact h

theorem norm_natCast_of_coprime {n : ℕ} (hn : Nat.Coprime n l) : ‖(n : ℂ_[l])‖ = 1 := by
  have h := PadicComplex.norm_extends' l (n : ℚ_[l])
  rw [(Padic.norm_natCast_eq_one_iff).2 hn.symm, map_natCast, PadicComplex.coe_natCast] at h
  exact h

theorem exists_norm_btwn (x y : ℝ) (hx : 0 ≤ x) (hxy : x < y) : ∃ a : ℂ_[l], x < ‖a‖ ∧ ‖a‖ < y := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := lt_trans one_pos hl1
  have hy : 0 < y := lt_of_le_of_lt hx hxy
  set x' := max x (y / 2) with hx'
  have hx'0 : 0 < x' := lt_of_lt_of_le (half_pos hy) (le_max_right _ _)
  have hx'y : x' < y := max_lt hxy (half_lt_self hy)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn ((Real.logb_lt_logb_iff hl1 hx'0 hy).2 hx'y)
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (l : ℂ_[l]) q.den_pos
  have hcn : ‖c‖ ^ q.den = (l : ℝ)⁻¹ := by rw [← norm_pow, hc, norm_l]
  have hc' : ‖c‖ = ((l : ℝ)⁻¹) ^ ((q.den : ℝ)⁻¹) := by
    rw [← hcn, Real.pow_rpow_inv_natCast (norm_nonneg _) q.den_ne_zero]
  have hval : ‖c ^ (-q.num)‖ = (l : ℝ) ^ (q : ℝ) := by
    rw [norm_zpow, ← Real.rpow_intCast, hc', ← Real.rpow_mul (inv_nonneg.2 hl0.le),
      Real.inv_rpow hl0.le, ← Real.rpow_neg hl0.le]
    congr 1
    have hq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
      exact_mod_cast (Rat.num_div_den q).symm
    rw [hq]
    push_cast
    field_simp
  refine ⟨c ^ (-q.num), ?_, ?_⟩
  · rw [hval]
    refine lt_of_le_of_lt (le_max_left x (y / 2)) ?_
    rw [← hx']
    calc x' = (l : ℝ) ^ Real.logb l x' := (Real.rpow_logb hl0 hl1.ne' hx'0).symm
      _ < (l : ℝ) ^ (q : ℝ) := (Real.rpow_lt_rpow_left_iff hl1).2 hq1
  · rw [hval]
    calc (l : ℝ) ^ (q : ℝ) < (l : ℝ) ^ Real.logb l y := (Real.rpow_lt_rpow_left_iff hl1).2 hq2
      _ = y := Real.rpow_logb hl0 hl1.ne' hy

@[reducible] def denseC : DenselyNormedField ℂ_[l] where
  __ := (inferInstance : NormedField ℂ_[l])
  lt_norm_lt := exists_norm_btwn l

attribute [local instance] denseC

variable {l}

end Dense

namespace PtGeo

variable {l : ℕ} [Fact l.Prime] {Λ : Type} [AddCommGroup Λ] {σ : Type} (X : PtGeo l Λ σ)

def InC (k : ℕ) (C : ℝ) (G : X.Gm k) : Prop := ∀ d : ℂ_[l], ‖d‖ * C ≤ 1 → d • G ∈ X.IntG k

def Vert (ρ : ℝ) : Set X.H := {n | n ∈ X.Fil ∧ ∀ d : ℂ_[l], ‖d‖ * ρ ≤ 1 → d • n ∈ X.HO}

def Cls (k : ℕ) (ρ : ℝ) : ℕ → ℝ → X.Gm k → Prop
  | 0, C, G => X.InC k C G ∧ ∀ n ∈ X.Vert ρ, X.nab k n G = 0
  | p + 1, C, G => X.InC k (C * ρ ^ ((p + 1) / 2)) G ∧ ∀ n ∈ X.Vert ρ, Cls k ρ p (C * ρ) (X.nab k n G)

variable {X} {k : ℕ} {ρ : ℝ}

end PtGeo

variable {D : Formalism.BasicNotions.D7}

theorem vdd_nonneg (l : ℕ) : 0 ≤ vdd D l :=
  Real.iSup_nonneg fun _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem norm_iO_le (i : D.ntw.Tw) (c : D.ntw.O i) : ‖iO i c‖ ≤ 1 := (D.nth.iC_int i _).2 ⟨c, rfl⟩

section Places

theorem exists_conj (D : Formalism.BasicNotions.D7) (y : 𝓞 D.host.E) :
    ∃ x : 𝓞 D.host.E, (y : D.host.E) = D.host.conj (x : D.host.E) :=
  ⟨RingOfIntegers.mapRingEquiv D.host.conj.symm.toRingEquiv y, by
    rw [RingOfIntegers.mapRingEquiv_apply]; simp⟩

theorem exists_conj' (D : Formalism.BasicNotions.D7) (x : 𝓞 D.host.E) :
    ∃ y : 𝓞 D.host.E, (y : D.host.E) = D.host.conj (x : D.host.E) :=
  ⟨RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv x, by
    rw [RingOfIntegers.mapRingEquiv_apply]; rfl⟩

theorem ConjPl.unique {P P' P'' : HeightOneSpectrum (𝓞 D.host.E)} (h : ConjPl D P P') (h' : ConjPl D P P'') :
    P' = P'' := by
  apply HeightOneSpectrum.ext
  ext y
  obtain ⟨x, hx⟩ := exists_conj D y
  rw [← h x y hx, ← h' x y hx]

theorem ConjPl.inj {P P' P'' : HeightOneSpectrum (𝓞 D.host.E)} (h : ConjPl D P P') (h' : ConjPl D P'' P') :
    P = P'' := by
  apply HeightOneSpectrum.ext
  ext x
  obtain ⟨y, hy⟩ := exists_conj' D x
  rw [h x y hy, h' x y hy]

theorem ConjPl.natCast_mem {P P' : HeightOneSpectrum (𝓞 D.host.E)} (h : ConjPl D P P') (n : ℕ) :
    (n : 𝓞 D.host.E) ∈ P.asIdeal ↔ (n : 𝓞 D.host.E) ∈ P'.asIdeal := h _ _ (by simp)

theorem Per.of_dvd {L V : Type} [AddCommGroup L] {a N : ℕ} {φ : L → V} (h : Per a φ) (hd : a ∣ N) :
    Per N φ := by
  obtain ⟨c, rfl⟩ := hd
  intro x z
  have e : ((a * c : ℕ) : ℤ) • z = (a : ℤ) • ((c : ℤ) • z) := by rw [smul_smul]; push_cast; rfl
  rw [e]; exact h x _

theorem Per.mul {L V : Type} [AddCommGroup L] [Mul V] {N : ℕ} {f g : L → V} (hf : Per N f) (hg : Per N g) :
    Per N (fun x => f x * g x) := fun x z => by
  show f _ * g _ = _
  rw [hf x z, hg x z]

theorem Per.prod {L V ι : Type} [AddCommGroup L] [CommMonoid V] {N : ℕ} (s : Finset ι) (f : ι → L → V)
    (h : ∀ i ∈ s, Per N (f i)) : Per N (fun x => ∏ i ∈ s, f i x) :=
  fun x z => Finset.prod_congr rfl fun i hi => h i hi x z

section

variable {E L V : Type} [Field E] [NumberField E] [AddCommGroup L] [Module (𝓞 E) L]

theorem natCast_smul_eq (N : ℕ) (z : L) : (N : 𝓞 E) • z = (N : ℤ) • z := by
  rw [natCast_zsmul, Nat.cast_smul_eq_nsmul]

theorem PerI.per {I : Ideal (𝓞 E)} {φ : L → V} (h : PerI I φ) {N : ℕ} (hN : (N : 𝓞 E) ∈ I) : Per N φ := by
  intro x z
  apply h
  rw [← natCast_smul_eq (E := E)]
  exact Submodule.smul_mem_smul hN trivial

theorem PerI.mono {I J : Ideal (𝓞 E)} {φ : L → V} (h : PerI J φ) (hIJ : I ≤ J) : PerI I φ :=
  fun x y hy => h x y (Submodule.smul_mono_left hIJ hy)

theorem PerI.mul [Mul V] {I : Ideal (𝓞 E)} {f g : L → V} (hf : PerI I f) (hg : PerI I g) :
    PerI I (fun x => f x * g x) := fun x y hy => by
  show f _ * g _ = _
  rw [hf x y hy, hg x y hy]

theorem PerI.prod {ι : Type} [CommMonoid V] {I : Ideal (𝓞 E)} (s : Finset ι) (f : ι → L → V)
    (h : ∀ i ∈ s, PerI I (f i)) : PerI I (fun x => ∏ i ∈ s, f i x) :=
  fun x y hy => Finset.prod_congr rfl fun i hi => h i hi x y hy

theorem isCoprime_of_ne {P P' : HeightOneSpectrum (𝓞 E)} (h : P ≠ P') : IsCoprime P.asIdeal P'.asIdeal := by
  rw [Ideal.isCoprime_iff_sup_eq]
  exact Ideal.IsMaximal.coprime_of_ne P.isMaximal P'.isMaximal fun e => h (HeightOneSpectrum.ext e)

end

end Places

section Gal

variable (X : Geo D)

def thG (i : D.ntw.Tw) (j : ℕ) (φ : D.nth.Lt i j → KK i) (P : MvPolynomial (D.nth.Let i j) (D.ntw.O i)) (n : ℕ)
    (y : D.nth.Pt i j) : ℂ_[D.ntw.l i] :=
  (X.pt i j y).PN (X.ord i j) (X.pt i j y).nabD (X.pt i j y).lf (P.map (iO i))
    ((X.pt i j y).fG (D.ntw.l i ^ D.nth.aL i * n) (2 * D.R.f * D.R.r * D.R.nV) (fun x => D.nth.iC i (φ x)))

end Gal

section U4

theorem norm_unif {K O : Type} [NormedField K] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra O K] [IsFractionRing O K]
    (hball : ∀ x : K, ‖x‖ ≤ 1 ↔ x ∈ (algebraMap O K).range) {ϖ : O} (hϖ : Irreducible ϖ) :
    0 < ‖algebraMap O K ϖ‖ ∧ ‖algebraMap O K ϖ‖ < 1 := by
  have h0 : algebraMap O K ϖ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective O K)]; exact hϖ.ne_zero
  refine ⟨norm_pos_iff.2 h0, lt_of_le_of_ne ((hball _).2 ⟨ϖ, rfl⟩) ?_⟩
  intro h1
  have h2 : ‖(algebraMap O K ϖ)⁻¹‖ ≤ 1 := by rw [norm_inv, h1, inv_one]
  obtain ⟨a, ha⟩ := (hball _).1 h2
  apply hϖ.not_isUnit
  refine IsUnit.of_mul_eq_one a ?_
  apply IsFractionRing.injective O K
  rw [map_mul, ha, map_one, mul_inv_cancel₀ h0]

theorem norm_unit_eq_one {K O : Type} [NormedField K] [CommRing O] [Algebra O K]
    (hball : ∀ x : K, ‖x‖ ≤ 1 ↔ x ∈ (algebraMap O K).range) (u : Oˣ) : ‖algebraMap O K (u : O)‖ = 1 := by
  apply le_antisymm ((hball _).2 ⟨_, rfl⟩)
  have h1 : ‖algebraMap O K ((u⁻¹ : Oˣ) : O)‖ ≤ 1 := (hball _).2 ⟨_, rfl⟩
  have h2 : algebraMap O K (u : O) * algebraMap O K ((u⁻¹ : Oˣ) : O) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have h3 : ‖algebraMap O K (u : O)‖ * ‖algebraMap O K ((u⁻¹ : Oˣ) : O)‖ = 1 := by
    rw [← norm_mul, h2, norm_one]
  nlinarith [norm_nonneg (algebraMap O K (u : O)), norm_nonneg (algebraMap O K ((u⁻¹ : Oˣ) : O))]

theorem norm_discrete {K O : Type} [NormedField K] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra O K] [IsFractionRing O K]
    (hball : ∀ x : K, ‖x‖ ≤ 1 ↔ x ∈ (algebraMap O K).range) {ϖ : O} (hϖ : Irreducible ϖ) (x : K)
    (hx : x ≠ 0) : ∃ n : ℤ, ‖x‖ = ‖algebraMap O K ϖ‖ ^ n := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by rintro rfl; simp at hx
  obtain ⟨s, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  obtain ⟨t, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  refine ⟨(s : ℤ) - t, ?_⟩
  have h0 := (norm_unif hball hϖ).1
  rw [norm_div, map_mul, map_mul, norm_mul, norm_mul, norm_unit_eq_one hball, norm_unit_eq_one hball, one_mul,
    one_mul, map_pow, map_pow, norm_pow, norm_pow, zpow_sub₀ h0.ne', zpow_natCast, zpow_natCast]

theorem complete_of_adic {K O : Type} [NormedField K] [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra O K] [IsFractionRing O K]
    (hball : ∀ x : K, ‖x‖ ≤ 1 ↔ x ∈ (algebraMap O K).range)
    (hc : IsAdicComplete (IsLocalRing.maximalIdeal O) O) : CompleteSpace K := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨hr0, hr1⟩ := norm_unif hball hϖ
  set r := ‖algebraMap O K ϖ‖ with hr
  have hπ0 : algebraMap O K ϖ ≠ 0 := norm_pos_iff.1 hr0
  have hmem : ∀ (a : O) (n : ℕ), ‖algebraMap O K a‖ ≤ r ^ n → a ∈ IsLocalRing.maximalIdeal O ^ n := by
    intro a n h
    have h1 : ‖algebraMap O K a / (algebraMap O K ϖ) ^ n‖ ≤ 1 := by
      rw [norm_div, norm_pow, div_le_one (pow_pos hr0 n)]; exact h
    obtain ⟨c, hc'⟩ := (hball _).1 h1
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    refine ⟨c, ?_⟩
    apply IsFractionRing.injective O K
    rw [map_mul, map_pow, hc', mul_div_cancel₀ _ (pow_ne_zero n hπ0)]
  have hnorm : ∀ (a : O) (n : ℕ), a ∈ IsLocalRing.maximalIdeal O ^ n → ‖algebraMap O K a‖ ≤ r ^ n := by
    intro a n h
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
    obtain ⟨c, rfl⟩ := h
    rw [map_mul, map_pow, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (pow_nonneg hr0.le n) ((hball _).2 ⟨c, rfl⟩)
  refine Metric.complete_of_convergent_controlled_sequences (fun n => r ^ n) (fun n => pow_pos hr0 n) ?_
  intro u hu
  have h1 : ∀ n, ∃ a : O, algebraMap O K a = u n - u 0 := by
    intro n
    have := hu 0 n 0 (Nat.zero_le _) le_rfl
    rw [pow_zero, dist_eq_norm] at this
    exact (hball _).1 this.le
  choose a ha using h1
  obtain ⟨L, hL⟩ := hc.toIsPrecomplete.prec (f := a) (by
    intro m n hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    apply hmem
    rw [map_sub, ha, ha, sub_sub_sub_cancel_right, ← dist_eq_norm]
    exact (hu m m n le_rfl hmn).le)
  refine ⟨u 0 + algebraMap O K L, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1)
  have h2 := hL n
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h2
  have h3 := hnorm _ n h2
  rw [map_sub, ha] at h3
  rwa [← sub_sub]

theorem supBall_lattice {K L V Pt : Type} [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K]
    [NormedField L] [IsUltrametricDist L] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (φ : K →+* L) (hφ : ∀ a, ‖φ a‖ = ‖a‖) (ev : V →+ (Pt → L))
    (hsm : ∀ (a : K) (f : V) (y : Pt), ev (a • f) y = φ a * ev f y) (hinj : Function.Injective ev)
    (ϖ : K) (hϖ : ‖ϖ‖ < 1) (hd : ∀ x : K, x ≠ 0 → ∃ n : ℤ, ‖x‖ = ‖ϖ‖ ^ n) :
    ∃ (n : ℕ) (w : Fin n → V), ∀ f : V, (∀ y, ‖ev f y‖ ≤ 1) ↔
      ∃ c : Fin n → K, (∀ t, ‖c t‖ ≤ 1) ∧ f = ∑ t, c t • w t := by
  classical
  let W : Submodule K V :=
    { carrier := {f | BddAbove (Set.range fun y => ‖ev f y‖)}
      zero_mem' := ⟨0, by rintro _ ⟨y, rfl⟩; simp⟩
      add_mem' := by
        rintro f g ⟨A, hA⟩ ⟨B, hB⟩
        refine ⟨max A B, ?_⟩
        rintro _ ⟨y, rfl⟩
        show ‖ev (f + g) y‖ ≤ _
        rw [map_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (hA ⟨y, rfl⟩) (hB ⟨y, rfl⟩))
      smul_mem' := by
        rintro a f ⟨A, hA⟩
        refine ⟨‖a‖ * A, ?_⟩
        rintro _ ⟨y, rfl⟩
        show ‖ev (a • f) y‖ ≤ _
        rw [hsm, norm_mul, hφ]
        exact mul_le_mul_of_nonneg_left (hA ⟨y, rfl⟩) (norm_nonneg _) }
  let sN : W → ℝ := fun f => ⨆ y, ‖ev (f : V) y‖
  have hle : ∀ (f : W) y, ‖ev (f : V) y‖ ≤ sN f := fun f y => le_ciSup f.2 y
  have hub : ∀ (f : W) (C : ℝ), 0 ≤ C → (∀ y, ‖ev (f : V) y‖ ≤ C) → sN f ≤ C :=
    fun f C hC h => Real.iSup_le h hC
  have hnn : ∀ f : W, 0 ≤ sN f := fun f => Real.iSup_nonneg fun y => norm_nonneg _
  have hmax : ∀ f g : W, sN (f + g) ≤ max (sN f) (sN g) := by
    intro f g
    refine hub _ _ (le_max_of_le_left (hnn f)) fun y => ?_
    rw [Submodule.coe_add, map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (hle f y) (hle g y))
  let nrm : AddGroupNorm W :=
    { toFun := sN
      map_zero' := le_antisymm (hub _ _ le_rfl fun y => by simp) (hnn _)
      add_le' := fun f g => (hmax f g).trans (max_le_add_of_nonneg (hnn f) (hnn g))
      neg' := fun f => by
        show (⨆ y, ‖ev ((-f : W) : V) y‖) = ⨆ y, ‖ev (f : V) y‖
        congr 1
        funext y
        rw [Submodule.coe_neg, map_neg, Pi.neg_apply, norm_neg]
      eq_zero_of_map_eq_zero' := fun f h0 => by
        apply Subtype.ext
        apply hinj
        rw [Submodule.coe_zero, map_zero]
        funext y
        have := hle f y
        rw [show sN f = 0 from h0] at this
        exact norm_le_zero_iff.1 this }
  let _ : NormedAddCommGroup W := nrm.toNormedAddCommGroup
  have hnorm : ∀ f : W, ‖f‖ = sN f := fun _ => rfl
  let _ : NormedSpace K W :=
    { norm_smul_le := fun a f => by
        rw [hnorm, hnorm]
        refine hub _ _ (mul_nonneg (norm_nonneg _) (hnn f)) fun y => ?_
        rw [Submodule.coe_smul, hsm, norm_mul, hφ]
        exact mul_le_mul_of_nonneg_left (hle f y) (norm_nonneg _) }
  have : IsUltrametricDist W :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm hmax
  obtain ⟨b, hb⟩ := unit_ball_is_lattice K W ϖ hϖ hd
  refine ⟨_, fun t => (b t : V), fun f => ⟨fun hf => ?_, ?_⟩⟩
  · have hfW : f ∈ W := ⟨1, by rintro _ ⟨y, rfl⟩; exact hf y⟩
    have h1 : ‖(⟨f, hfW⟩ : W)‖ ≤ 1 := hub _ _ zero_le_one hf
    refine ⟨fun t => b.repr ⟨f, hfW⟩ t, (hb _).1 h1, ?_⟩
    have h2 : ((∑ t, b.repr ⟨f, hfW⟩ t • b t : W) : V) = f := congrArg (Subtype.val) (b.sum_repr ⟨f, hfW⟩)
    refine h2.symm.trans ?_
    simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul]
  · rintro ⟨c, hc, rfl⟩ y
    have h1 : ‖∑ t, c t • b t‖ ≤ 1 := by
      rw [hb]
      intro t
      rw [b.repr_sum_self]
      exact hc t
    have h2 := hle (∑ t, c t • b t) y
    have h3 : ((∑ t, c t • b t : W) : V) = ∑ t, c t • (b t : V) := by
      simp only [AddSubmonoidClass.coe_finsetSum, Submodule.coe_smul]
    rw [h3] at h2
    exact h2.trans h1

end U4

section U4rec

variable {D : Formalism.BasicNotions.D7}

def BallS (i : D.ntw.Tw) (j : ℕ) (b : Bool) : Submodule (D.ntw.O i) (D.nexp.Fm i j b) where
  carrier := Ball i j b
  zero_mem' := fun y => by simp
  add_mem' := fun {f g} hf hg y => by
    rw [map_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hf y) (hg y))
  smul_mem' := fun a f hf y => by
    have : a • f = (algebraMap (D.ntw.O i) (KK i) a) • f := (algebraMap_smul _ _ _).symm
    rw [this, D.nth.ev_smul, norm_mul]
    exact mul_le_one₀ ((D.nth.iC_int i _).2 ⟨a, rfl⟩) (norm_nonneg _) (hf y)

theorem Ball_fg (i : D.ntw.Tw) (j : ℕ) (b : Bool) : (BallS i j b).FG := by
  classical
  let nf : NormedField (KK i) :=
    NormedField.induced (KK i) ℂ_[D.ntw.l i] (D.nth.iC i) (D.nth.iC i).injective
  have hball : ∀ x : KK i, ‖x‖ ≤ 1 ↔ x ∈ (algebraMap (D.ntw.O i) (KK i)).range := D.nth.iC_int i
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (D.ntw.O i)
  obtain ⟨h0, h1⟩ := norm_unif hball hϖ
  have hd := norm_discrete hball hϖ
  have hcs : CompleteSpace (KK i) := complete_of_adic hball (D.ntw.O_complete i)
  have hum : IsUltrametricDist (KK i) :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm (fun x y => by
      show ‖D.nth.iC i (x + y)‖ ≤ max ‖D.nth.iC i x‖ ‖D.nth.iC i y‖
      rw [map_add]
      exact IsUltrametricDist.norm_add_le_max _ _)
  let nnf : NontriviallyNormedField (KK i) :=
    { nf with
      non_trivial := ⟨(algebraMap (D.ntw.O i) (KK i) ϖ)⁻¹, by
        rw [norm_inv]; exact (one_lt_inv₀ h0).2 h1⟩ }
  obtain ⟨n, w, hw⟩ := @supBall_lattice (KK i) ℂ_[D.ntw.l i] (D.nexp.Fm i j b) (D.nth.Pt i j) nnf hcs hum _ _ _ _ _
    (D.nth.iC i) (fun _ => rfl) (D.nth.ev i j b) (D.nth.ev_smul i j b) (D.nth.ev_inj i j b)
    (algebraMap (D.ntw.O i) (KK i) ϖ) h1 hd
  refine ⟨Finset.univ.image w, ?_⟩
  rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    refine (hw (w t)).2 ⟨Pi.single t 1, fun s => ?_, by simp [Pi.single_apply]⟩
    by_cases hst : s = t
    · subst hst
      rw [Pi.single_eq_same]
      exact (hball 1).2 ⟨1, map_one _⟩
    · rw [Pi.single_eq_of_ne hst]
      exact (hball 0).2 ⟨0, map_zero _⟩
  · intro f hf
    obtain ⟨c, hc, rfl⟩ := (hw f).1 hf
    refine Submodule.sum_mem _ fun t _ => ?_
    obtain ⟨a, ha⟩ := (hball _).1 (hc t)
    rw [← ha, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)

theorem Bsup_le_BallS (i : D.ntw.Tw) (j : ℕ) (b : Bool) : D.nexp.Bsup i j b ≤ BallS i j b := by
  rw [D.nth.Bsup_def, Submodule.span_le]
  exact fun f hf => hf.2

theorem Bsup_fg (D : Formalism.BasicNotions.D7) (i : D.ntw.Tw) (j : ℕ) (b : Bool) : (D.nexp.Bsup i j b).FG := by
  have : IsNoetherian (D.ntw.O i) ↥(BallS i j b) := isNoetherian_of_fg_of_noetherian _ (Ball_fg i j b)
  exact (isNoetherian_submodule.1 this) _ (Bsup_le_BallS i j b)

end U4rec

section ConjPlaces

theorem conj_conj (D : Formalism.BasicNotions.D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  have h := D.host.conjE_apply D.host.φ₀
  show D.host.φ₀ (D.host.conj
    (D.host.conj x)) = _
  rw [h, h]
  simp

theorem ConjPl.symm {P P' : HeightOneSpectrum (𝓞 D.host.E)} (h : ConjPl D P P') : ConjPl D P' P := by
  intro x y hxy
  have : (x : D.host.E) = D.host.conj (y : D.host.E) := by rw [hxy, conj_conj]
  exact (h y x this).symm

theorem exists_conjPl (P : HeightOneSpectrum (𝓞 D.host.E)) : ∃ P' : HeightOneSpectrum (𝓞 D.host.E), ConjPl D P P' := by
  let e : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv
  have he : ∀ x : 𝓞 D.host.E, ((e x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := by
    intro x
    rw [RingOfIntegers.mapRingEquiv_apply]; rfl
  have := P.isPrime
  refine ⟨⟨P.asIdeal.comap (e.symm : 𝓞 D.host.E →+* 𝓞 D.host.E), Ideal.comap_isPrime _ _, ?_⟩, ?_⟩
  · intro hbot
    apply P.ne_bot
    rw [eq_bot_iff]
    intro x hx
    have h1 : e x ∈ P.asIdeal.comap (e.symm : 𝓞 D.host.E →+* 𝓞 D.host.E) := by
      rw [Ideal.mem_comap]
      simpa using hx
    rw [hbot, Ideal.mem_bot] at h1
    rw [Ideal.mem_bot]
    exact (map_eq_zero_iff e e.injective).1 h1
  · intro x y hxy
    have hy : y = e x := by
      apply RingOfIntegers.ext
      rw [hxy, he]
    subst hy
    show x ∈ P.asIdeal ↔ e.symm (e x) ∈ P.asIdeal
    rw [RingEquiv.symm_apply_apply]

theorem ConjPl.ne_of_split {P P' : HeightOneSpectrum (𝓞 D.host.E)} (h : ConjPl D P P')
    (hP : IsSplitPl D.host P) : P ≠ P' := by
  rintro rfl
  obtain ⟨x, hx, hy⟩ := hP
  obtain ⟨y, hxy⟩ := exists_conj' D x
  exact hy y hxy ((h x y hxy).1 hx)

end ConjPlaces

namespace SplitL

variable {R : Ranks} (H : Host R)

theorem bE_sq : (H.sqd) ^ 2 = -(H.d : H.E) := H.sqd_sq

def bO : 𝓞 H.E :=
  ⟨H.sqd, ⟨Polynomial.X ^ 2 + Polynomial.C (H.d : ℤ),
    Polynomial.monic_X_pow_add_C _ two_ne_zero, by simp [bE_sq]⟩⟩

end SplitL

section PartC

variable {i : D.ntw.Tw} {j : ℕ} {M : ℕ} {Q : Finset (HeightOneSpectrum (𝓞 D.host.E))}

def Psi (φ : D.nth.Lt i j → KK i) (Φ : ↥Q → ZMod (D.ntw.l i ^ M) → D.nth.Lt i j → KK i)
    (a : DelQM D.host (D.ntw.l i) Q M) : D.nth.Lt i j → KK i :=
  fun x => φ x * ∏ q : ↥Q, Φ q (a q) x

def nQ (Q : Finset (HeightOneSpectrum (𝓞 D.host.E))) : ℕ := ∏ q : ↥Q, (Ideal.absNorm q.1.asIdeal) ^ 2

def coefG (δ : G D.host.E D.nd.Om →* Multiplicative (DelQM D.host (D.ntw.l i) Q M))
    (Φ : ↥Q → ZMod (D.ntw.l i ^ M) → D.nth.Lt i j → KK i) (φ : D.nth.Lt i j → KK i)
    (P : MvPolynomial (D.nth.Let i j) (D.ntw.O i)) (a : DelQM D.host (D.ntw.l i) Q M) (y : D.nth.Pt i j) :
    ℂ_[D.ntw.l i] :=
  D.nth.thV i j (Psi φ Φ (a - delY i j δ y)) P y

variable {δ : G D.host.E D.nd.Om →* Multiplicative (DelQM D.host (D.ntw.l i) Q M)}
  {Φ : ↥Q → ZMod (D.ntw.l i ^ M) → D.nth.Lt i j → KK i} {φ : D.nth.Lt i j → KK i}

theorem QSet.not_over (hQ : QSet i M Q) {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : P ∈ Q) :
    P ∉ placesOver D.host.E (D.ntw.l i) := fun h => hQ.2.1 P hP (Finset.mem_coe.1 (D.ntw.twistExcludedPlaces_contains_residueChar i h))

variable (X : Geo D)

def coefH (δ : G D.host.E D.nd.Om →* Multiplicative (DelQM D.host (D.ntw.l i) Q M))
    (Φ : ↥Q → ZMod (D.ntw.l i ^ M) → D.nth.Lt i j → KK i) (φ : D.nth.Lt i j → KK i)
    (P : MvPolynomial (D.nth.Let i j) (D.ntw.O i)) (n : ℕ) (a : DelQM D.host (D.ntw.l i) Q M)
    (y : D.nth.Pt i j) : ℂ_[D.ntw.l i] :=
  thG X i j (Psi φ Φ (a - delY i j δ y)) P (n * nQ Q) y

end PartC

section U5

theorem norm_unit (i : D.ntw.Tw) (u : (D.ntw.O i)ˣ) : ‖iO i (u : D.ntw.O i)‖ = 1 := by
  have h1 : ‖iO i (u : D.ntw.O i)‖ ≤ 1 := norm_iO_le i _
  have h2 : ‖iO i ((u⁻¹ : (D.ntw.O i)ˣ) : D.ntw.O i)‖ ≤ 1 := norm_iO_le i _
  have h4 : ‖iO i (u : D.ntw.O i)‖ * ‖iO i ((u⁻¹ : (D.ntw.O i)ˣ) : D.ntw.O i)‖ = 1 := by
    rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  refine le_antisymm h1 ?_
  calc (1 : ℝ) = _ := h4.symm
    _ ≤ ‖iO i (u : D.ntw.O i)‖ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = _ := mul_one _

end U5

end Formalism.MainNotions.ExistsIdealDenominator

end
