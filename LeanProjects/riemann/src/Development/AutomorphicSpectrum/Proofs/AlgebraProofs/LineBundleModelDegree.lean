import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ClassListMapDomainPerm
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChernClassOnFlagPairStatement

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.LineCk

theorem exists_pow_mul_eq {R : Type*} [CommRing R] (w A B : R)
    (h : ∀ p : Ideal R, p.IsPrime → w ∉ p → ∃ U V : R, U ∉ p ∧ U * A = V * B) :
    ∃ (n : ℕ) (r : R), w ^ n * A = r * B := by
  let J : Ideal R :=
    { carrier := {s | ∃ r, s * A = r * B}
      add_mem' := by
        rintro a b ⟨r, hr⟩ ⟨t, ht⟩
        exact ⟨r + t, by rw [add_mul, add_mul, hr, ht]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c a ⟨r, hr⟩
        exact ⟨c * r, by rw [smul_eq_mul, mul_assoc, hr, mul_assoc]⟩ }
  have hw : w ∈ J.radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    rintro p ⟨hJp, hp⟩
    by_contra hwp
    obtain ⟨U, V, hU, hUV⟩ := h p hp hwp
    exact hU (hJp ⟨V, hUV⟩)
  obtain ⟨n, r, hr⟩ := hw
  exact ⟨n, r, hr⟩

section Forms

variable {O : Type*} [CommRing O] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem sum_block_eq {f : MRing ι O} {b : K → ℕ} (hf : IsMultiHomog f b) {m : (Σ k, ι k) →₀ ℕ}
    (hm : m ∈ f.support) (k : K) : ∑ i, m ⟨k, i⟩ = b k := by
  have h := congrFun (hf (mem_support_iff.mp hm)) k
  rw [← h, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, blockWeight, Pi.single_apply]
  rw [Fintype.sum_sigma]
  simp

theorem aeval_scale {A : Type*} [CommRing A] [Algebra O A] (y : (Σ k, ι k) → A) (t : K → A)
    {f : MRing ι O} {b : K → ℕ} (hf : IsMultiHomog f b) :
    aeval (fun p : Σ k, ι k => y p * t p.1) f = aeval y f * ∏ k, t k ^ b k := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hX : ∏ p : Σ k, ι k, t p.1 ^ m p = ∏ k, t k ^ b k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    change ∏ i, t k ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, sum_block_eq hf hm k]
  simp only [mul_pow, Finset.prod_mul_distrib, hX, mul_assoc]

theorem map_aeval_of {A B : Type*} [CommRing A] [CommRing B] [Algebra O A] [Algebra O B] (π : A →+* B)
    (hπ : ∀ c : O, π (algebraMap O A c) = algebraMap O B c) (w : (Σ k, ι k) → A) (f : MRing ι O) :
    π (aeval w f) = aeval (fun p => π (w p)) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [hπ]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

end Forms

section Chart

variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
  {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem aeval_ne_zero (x : (Σ k, ι k) → Ω) {f : MRing ι O} {b : K → ℕ} (hf : IsMultiHomog f b)
    (hP : f ∉ pointIdeal O x) : aeval x f ≠ 0 := by
  intro h0
  apply hP
  show f ∈ RingHom.ker (pointConeMap O x)
  rw [RingHom.mem_ker]
  have h1 := aeval_scale (fun p => (C (x p) : MvPolynomial K Ω)) (fun k => (X k : MvPolynomial K Ω)) hf
  have h2 := map_aeval_of (O := O) (C : Ω →+* MvPolynomial K Ω)
    (fun c => by simp [MvPolynomial.algebraMap_apply]) x f
  rw [h0, map_zero] at h2
  rw [← h2, zero_mul] at h1
  exact h1

theorem coord_ne_zero (x : (Σ k, ι k) → Ω) {s : ∀ k, ι k} (hs : mseg x s ≠ 0) (k : K) :
    x ⟨k, s k⟩ ≠ 0 :=
  Finset.prod_ne_zero_iff.mp hs k (Finset.mem_univ k)

theorem ratio_mem (x : (Σ k, ι k) → Ω) {s : ∀ k, ι k} (hs : mseg x s ≠ 0) (p : Σ k, ι k) :
    x p / x ⟨p.1, s p.1⟩ ∈ chartRing O (mseg x) s := by
  have h1 : mseg x (Function.update s p.1 p.2) / mseg x s ∈ chartRing O (mseg x) s :=
    ReciprocityTheory.ChartRestriction.G.Geo.div_mem_chartRing (mseg x) s (Function.update s p.1 p.2)
  have h2 : mseg x (Function.update s p.1 p.2) / mseg x s = x p / x ⟨p.1, s p.1⟩ := by
    have hc := coord_ne_zero x hs p.1
    rw [div_eq_div_iff hs hc]
    unfold mseg
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ p.1),
      ← Finset.mul_prod_erase Finset.univ (fun k => x ⟨k, s k⟩) (Finset.mem_univ p.1)]
    have h3 : ∏ k ∈ Finset.univ.erase p.1, x ⟨k, Function.update s p.1 p.2 k⟩ =
        ∏ k ∈ Finset.univ.erase p.1, x ⟨k, s k⟩ := by
      refine Finset.prod_congr rfl fun k hk => ?_
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
    rw [h3, Function.update_self]
    ring
  rwa [h2] at h1

def chartHom (x : (Σ k, ι k) → Ω) {s : ∀ k, ι k} (hs : mseg x s ≠ 0) :
    MRing ι O →ₐ[O] chartRing O (mseg x) s :=
  aeval fun p => ⟨x p / x ⟨p.1, s p.1⟩, ratio_mem x hs p⟩

theorem chartHom_coe (x : (Σ k, ι k) → Ω) {s : ∀ k, ι k} (hs : mseg x s ≠ 0) (h : MRing ι O) :
    ((chartHom (O := O) x hs h : chartRing O (mseg x) s) : Ω) =
      aeval (fun p : Σ k, ι k => x p / x ⟨p.1, s p.1⟩) h := by
  have := map_aeval_of (O := O) (chartRing O (mseg x) s).val.toRingHom (fun c => rfl)
    (fun p => (⟨x p / x ⟨p.1, s p.1⟩, ratio_mem x hs p⟩ : chartRing O (mseg x) s)) h
  exact this

theorem chartHom_form (x : (Σ k, ι k) → Ω) {s : ∀ k, ι k} (hs : mseg x s ≠ 0) {f : MRing ι O}
    {b : K → ℕ} (hf : IsMultiHomog f b) :
    ((chartHom (O := O) x hs f : chartRing O (mseg x) s) : Ω) =
      aeval x f * ∏ k, (x ⟨k, s k⟩)⁻¹ ^ b k := by
  rw [chartHom_coe, ← aeval_scale x (fun k => (x ⟨k, s k⟩)⁻¹) hf]
  simp only [div_eq_mul_inv]

theorem chartHom_eq_zero (x : (Σ k, ι k) → Ω) {s : ∀ k, ι k} (hs : mseg x s ≠ 0) {h : MRing ι O}
    (hP : h ∈ pointIdeal O x) : chartHom (O := O) x hs h = 0 := by
  have h0 : pointConeMap O x h = 0 := RingHom.mem_ker.mp hP
  have h1 := map_aeval_of (O := O) (eval fun k : K => (x ⟨k, s k⟩)⁻¹)
    (fun c => by simp [MvPolynomial.algebraMap_apply]) (fun p => C (x p) * X p.1) h
  have h2 : (aeval (fun p : Σ k, ι k => C (x p) * X p.1) h : MvPolynomial K Ω) = 0 := h0
  rw [h2, map_zero] at h1
  apply Subtype.ext
  rw [chartHom_coe]
  simpa [div_eq_mul_inv] using h1.symm

end Chart

section Lines

variable {O : Type*} [CommRing O] {Ω : Type*} [Field Ω] [Algebra O Ω]
  {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem chartMon_relation (x : (Σ k, ι k) → Ω) {s : ∀ k, ι k} (hs : mseg x s ≠ 0) {a a' : K → ℤ}
    {bf bg : K → ℕ} (hb : ∀ k, (bf k : ℤ) - bg k = a k - a' k) :
    chartMon x s a * ∏ k, (x ⟨k, s k⟩)⁻¹ ^ bf k = chartMon x s a' * ∏ k, (x ⟨k, s k⟩)⁻¹ ^ bg k := by
  unfold chartMon
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have hx := coord_ne_zero x hs k
  rw [inv_pow, inv_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_neg, ← zpow_add₀ hx,
    ← zpow_add₀ hx]
  congr 1
  have := hb k
  linarith

theorem line_step (ϖ : O) (x : (Σ k, ι k) → Ω) {u u' : Ω} {a a' : K → ℤ} {f g : MRing ι O}
    {bf bg : K → ℕ} (hf : IsMultiHomog f bf) (hg : IsMultiHomog g bg)
    (hb : ∀ k, (bf k : ℤ) - bg k = a k - a' k) (hG : aeval x g ≠ 0)
    (hgen : aeval x f * u = aeval x g * u')
    (hU : ∀ W : Ideal (MRing ι O), W.IsPrime → pointIdeal O x ≤ W → IsRelevant W →
      (C ϖ : MRing ι O) ∉ W → ∃ c e : MRing ι O, e ∉ W ∧ c * f - e * g ∈ pointIdeal O x)
    {L L' : (∀ k, ι k) → AddSubgroup Ω} (hL : IsLine O x u a L) (hL' : IsLine O x u' a' L')
    {s : ∀ k, ι k} (hs : mseg x s ≠ 0) {v : Ω} (hv : v ∈ L s) :
    ∃ n : ℕ, algebraMap O Ω ϖ ^ n • v ∈ L' s := by
  obtain ⟨n, r, hr⟩ := exists_pow_mul_eq (algebraMap O (chartRing O (mseg x) s) ϖ)
    (chartHom (O := O) x hs g) (chartHom (O := O) x hs f) (fun p hp hw => by
      have hWp : (p.comap (chartHom (O := O) x hs)).IsPrime := Ideal.comap_isPrime _ p
      obtain ⟨c, e, he, hce⟩ := hU (p.comap (chartHom (O := O) x hs)) hWp
        (fun h hh => by
          rw [Ideal.mem_comap, chartHom_eq_zero x hs hh]
          exact p.zero_mem)
        (fun k => ⟨s k, by
          have h1 : chartHom (O := O) x hs (X ⟨k, s k⟩ : MRing ι O) = 1 := by
            apply Subtype.ext
            rw [chartHom_coe]
            simp [div_self (coord_ne_zero x hs k)]
          rw [Ideal.mem_comap, h1]
          exact (Ideal.ne_top_iff_one p).mp hp.ne_top⟩)
        (fun h => hw (by
          rw [Ideal.mem_comap] at h
          have h1 : chartHom (O := O) x hs (C ϖ : MRing ι O) =
              algebraMap O (chartRing O (mseg x) s) ϖ := (chartHom (O := O) x hs).commutes ϖ
          rwa [h1] at h))
      refine ⟨chartHom (O := O) x hs e, chartHom (O := O) x hs c, he, ?_⟩
      have h2 := chartHom_eq_zero x hs hce
      rw [map_sub, map_mul, map_mul, sub_eq_zero] at h2
      exact h2.symm)
  obtain ⟨r₀, hr₀, rfl⟩ := (hL s hs v).1 hv
  refine ⟨n, (hL' s hs _).2 ⟨r₀ * r, mul_mem hr₀ r.2, ?_⟩⟩
  have h1 : algebraMap O Ω ϖ ^ n * ((chartHom (O := O) x hs g : chartRing O (mseg x) s) : Ω) =
      (r : Ω) * ((chartHom (O := O) x hs f : chartRing O (mseg x) s) : Ω) := by
    have := congrArg (chartRing O (mseg x) s).val hr
    simpa only [map_mul, map_pow, AlgHom.commutes, Subalgebra.coe_val] using this
  rw [chartHom_form x hs hg, chartHom_form x hs hf] at h1
  have hM := chartMon_relation x hs hb
  have hIf : ∏ k, (x ⟨k, s k⟩)⁻¹ ^ bf k ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (inv_ne_zero (coord_ne_zero x hs k))
  rw [smul_eq_mul]
  apply mul_right_cancel₀ (mul_ne_zero hG hIf)
  generalize (∏ k, (x ⟨k, s k⟩)⁻¹ ^ bf k) = If at *
  generalize (∏ k, (x ⟨k, s k⟩)⁻¹ ^ bg k) = Ig at *
  generalize chartMon x s a = Ma at *
  generalize chartMon x s a' = Ma' at *
  generalize aeval x f = F at *
  generalize aeval x g = G at *
  generalize algebraMap O Ω ϖ ^ n = Wn at *
  linear_combination (r₀ : Ω) * ((Wn * u * G) * hM + (u * Ma') * h1 + ((r : Ω) * Ma' * If) * hgen)

theorem line_ne_zero (x : (Σ k, ι k) → Ω) (A : ChartBundle O (mseg x) 1 Ω) {u : Ω} {a : K → ℤ}
    (hA : IsLine O x u a A.lat) {s : ∀ k, ι k} (hs : mseg x s ≠ 0) : u ≠ 0 := by
  obtain ⟨m, e, c, he, hc, hsum, hl⟩ := A.frame s hs
  rintro rfl
  have hnz : ∃ l, e l ≠ 0 := by
    by_contra hn
    push_neg at hn
    simp [hn] at hsum
  obtain ⟨l, hl0⟩ := hnz
  obtain ⟨b, hb, -, hiff⟩ := hl l
  obtain ⟨n, hn⟩ := (hiff (b 0)).2 ⟨fun _ => 1, fun q => ⟨1, by simpa using he l⟩, by simp⟩
  obtain ⟨r, -, hr⟩ := (hA s hs _).1 hn
  have h0 : e l ^ n • b 0 = 0 := by rw [hr]; simp
  exact (smul_ne_zero (pow_ne_zero _ hl0) (hb.ne_zero 0)) h0

def lineBasis {u : Ω} (hu : u ≠ 0) : Module.Basis (Fin 1) Ω Ω :=
  (Module.Basis.singleton (Fin 1) Ω).unitsSMul fun _ => Units.mk0 u hu

theorem lineBasis_repr {u : Ω} (hu : u ≠ 0) (v : Ω) (i : Fin 1) : (lineBasis hu).repr v i = u⁻¹ * v := by
  simp [lineBasis, Units.smul_def]

theorem lineBasis_apply {u : Ω} (hu : u ≠ 0) (i : Fin 1) : lineBasis hu i = u := by
  simp [lineBasis, Module.Basis.unitsSMul_apply, Units.smul_def]

theorem isFlagFrame_line (x : (Σ k, ι k) → Ω) (A : ChartBundle O (mseg x) 1 Ω) {u : Ω} (hu : u ≠ 0)
    {a : K → ℤ} (hA : IsLine O x u a A.lat) : IsFlagFrame x A (lineBasis hu) (fun _ => a) := by
  refine ⟨fun c hc i => ?_⟩
  ext t
  constructor
  · rintro ⟨v, hv, -, rfl⟩
    obtain ⟨r, hr, rfl⟩ := (hA c hc _).1 hv
    refine ⟨r, hr, ?_⟩
    rw [lineBasis_repr]
    show _ = r * chartMon x c a
    field_simp
  · rintro ⟨r, hr, rfl⟩
    refine ⟨r * (u * chartMon x c a), (hA c hc _).2 ⟨r, hr, rfl⟩, fun j hij => ?_, ?_⟩
    · exact absurd hij (by rw [Subsingleton.elim i j]; exact lt_irrefl j)
    · rw [lineBasis_repr]
      show _ = r * chartMon x c a
      field_simp

end Lines

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ d : ℕ, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ (A A' : ChartBundle O (mseg x) 1 Ω) (u u' : Ω) (a a' : K → ℤ), IsLine O x u a A.lat → IsLine O x u' a' A'.lat → ∀ f g : MRing ι O, IsVerticalDivisor (pointIdeal O x) ϖ (a - a') f g → aeval x f * u = aeval x g * u' → SameGeneric O x A A' ∧ ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d 1 A A' k L Q = ∑ μ ∈ Q.support, Q.coeff μ * pairNum (pointIdeal O x) (fun _ : Fin 1 => a) (fun _ => a') (fun _ => f) (fun _ => g) (psumExpansion 1 k) (classList L μ) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x ϖ hϖ d hM A A' u u' a a' hA hA' f g hD hgen
  obtain ⟨hK, hModel⟩ := (BundleExamples.isModelOver_iff O (mcIdeal O x) d).1 hM
  obtain ⟨bf, bg, hf, hg, hb⟩ := hD.degrees
  have hb' : ∀ k, (bf k : ℤ) - bg k = a k - a' k := fun k => congrFun hb k
  have hF : aeval x f ≠ 0 := aeval_ne_zero x hf hD.num_not_mem
  have hG : aeval x g ≠ 0 := aeval_ne_zero x hg hD.den_not_mem
  have hSF : SameGenericFibre ϖ A A' := by
    intro c hc
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · exact line_step ϖ x hf hg hb' hG hgen (fun W h1 h2 h3 h4 => by
        obtain ⟨c', e, hc', he, hce⟩ := hD.unit_off_special W h1 h2 h3 h4
        exact ⟨c', e, he, hce⟩) hA hA' hc hv
    · exact line_step ϖ x hg hf (fun k => by have := hb' k; linarith) hF hgen.symm
        (fun W h1 h2 h3 h4 => by
          obtain ⟨c', e, hc', he, hce⟩ := hD.unit_off_special W h1 h2 h3 h4
          refine ⟨e, c', hc', ?_⟩
          have := (pointIdeal O x).neg_mem hce
          rwa [neg_sub] at this) hA' hA hc hv
  have hRel := hModel.multiProj.relevant
  choose s hs using hRel
  have hs0 : mseg x s ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun k _ => fun h0 => hs k ?_
    show _ ∈ RingHom.ker (pointConeMap O x)
    rw [RingHom.mem_ker]
    simp [pointConeMap, h0]
  have hu : u ≠ 0 := line_ne_zero x A hA hs0
  have hu' : u' ≠ 0 := line_ne_zero x A' hA' hs0
  have hFP : IsFlagPair ϖ x A A' (lineBasis hu) (lineBasis hu') (fun _ => a) (fun _ => a')
      (fun _ => f) (fun _ => g) :=
    { flag := isFlagFrame_line x A hu hA
      flag' := isFlagFrame_line x A' hu' hA'
      sameFlag := fun i j hij => absurd hij (by rw [Subsingleton.elim i j]; exact lt_irrefl j)
      vertical := fun _ => hD
      generic := fun i => by
        rw [lineBasis_repr, lineBasis_apply]
        field_simp
        linear_combination hgen }
  refine ⟨(BundleExamples.sameGeneric_iff hϖ x A A').2 hSF, fun k hk1 hk2 q L Q hQ => ?_⟩
  exact (GlobalTheory.T.chern_class_on_flag_pair O ϖ hϖ Ω K ι x d hK hModel 1 Ω A A' hSF (lineBasis hu) (lineBasis hu')
    (fun _ => a) (fun _ => a') (fun _ => f) (fun _ => g) hFP).1 k hk1 hk2 (psumExpansion 1 k)
    (isPairExpansion_psum 1 k) q L Q hQ

end GlobalTheory.CompanionTheory.Ar.Num.LineCk
