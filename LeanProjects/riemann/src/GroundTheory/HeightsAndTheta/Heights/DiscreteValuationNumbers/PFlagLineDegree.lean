import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagLineDegree
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PSplitRelDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace FlagLineDegreeProof

theorem weight_blockWeight_apply {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*}
    [∀ k, Fintype (ι k)] (μ : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blockWeight ι) μ k = ∑ i : ι k, μ ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    Fintype.sum_sigma]
  simp [blockWeight, Pi.single_apply]

theorem cone_of_isMultiHomog {K Kt : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*}
    [∀ k, Fintype (ι k)] {R S : Type*} [CommRing R] [CommRing S] (r : R →+* S)
    (x : (Σ k, ι k) → S) (τ : K → Kt) {h : MRing ι R} {D : K → ℕ} (hh : IsMultiHomog h D) :
    eval₂Hom (C.comp r) (fun p => C (x p) * X (τ p.1)) h =
      C (eval₂ r x h) * ∏ k, (X (τ k) : MvPolynomial Kt S) ^ D k := by
  conv_lhs => rw [h.as_sum]
  conv_rhs => rw [h.as_sum]
  rw [map_sum, eval₂_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [eval₂Hom_monomial, eval₂_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [mul_pow, Finset.prod_mul_distrib, map_mul, map_prod, map_pow, mul_assoc,
    RingHom.comp_apply]
  have hB : ∏ p : (Σ k, ι k), (X (τ p.1) : MvPolynomial Kt S) ^ μ p = ∏ k, X (τ k) ^ D k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i : ι k, (X (τ k) : MvPolynomial Kt S) ^ μ ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, ← weight_blockWeight_apply, hh (mem_support_iff.mp hμ)]
  rw [hB]

theorem segreForm_homog {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {R : Type*}
    [CommRing R] (c : ∀ k, ι k) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι R)) (fun _ => 1) := by
  have h := IsWeightedHomogeneous.prod Finset.univ (fun k => (X ⟨k, c k⟩ : MRing ι R))
    (fun k => Pi.single k 1) (w := blockWeight ι) (fun k _ => isWeightedHomogeneous_X R _ _)
  rwa [Finset.univ_sum_single (fun _ : K => (1 : ℕ))] at h

theorem chart_form {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} {F Ω : Type*} [Field F]
    [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : segreVec y c ≠ 0) {α : Ω}
    (hα : α ∈ chartRing F (segreVec y) c) :
    ∃ (m : ℕ) (A : MRing ι F), IsMultiHomog A (fun _ => m) ∧ α * segreVec y c ^ m = aeval y A := by
  have hσ : aeval y (∏ k, (X ⟨k, c k⟩ : MRing ι F)) = segreVec y c := by
    simp [segreVec, map_prod]
  have hdeg : ∀ m n : ℕ, ((fun _ : K => m) + fun _ : K => n) = fun _ => m + n := fun _ _ => rfl
  have hpow : ∀ n : ℕ, IsMultiHomog ((∏ k, (X ⟨k, c k⟩ : MRing ι F)) ^ n) (fun _ => n) := by
    intro n
    have h := (segreForm_homog (R := F) c).pow n
    have e : (n • fun _ : K => (1 : ℕ)) = fun _ => n := by funext k; simp
    rw [e] at h
    exact h
  induction hα using Algebra.adjoin_induction with
  | mem z hz =>
    obtain ⟨c', rfl⟩ := hz
    refine ⟨1, ∏ k, X ⟨k, c' k⟩, segreForm_homog c', ?_⟩
    rw [pow_one, div_mul_cancel₀ _ hc]
    simp [segreVec, map_prod]
  | algebraMap q =>
    exact ⟨0, C q, isWeightedHomogeneous_C _ _, by simp⟩
  | add z z' _ _ hz hz' =>
    obtain ⟨m, A, hA, hAe⟩ := hz
    obtain ⟨n, B, hB, hBe⟩ := hz'
    refine ⟨m + n, A * (∏ k, X ⟨k, c k⟩) ^ n + B * (∏ k, X ⟨k, c k⟩) ^ m, ?_, ?_⟩
    · have h1 := hA.mul (hpow n)
      have h2 := hB.mul (hpow m)
      rw [hdeg] at h1 h2
      rw [add_comm n m] at h2
      exact h1.add h2
    · rw [map_add, map_mul, map_mul, map_pow, map_pow, hσ, ← hAe, ← hBe]
      ring
  | mul z z' _ _ hz hz' =>
    obtain ⟨m, A, hA, hAe⟩ := hz
    obtain ⟨n, B, hB, hBe⟩ := hz'
    refine ⟨m + n, A * B, ?_, ?_⟩
    · have h1 := hA.mul hB
      rwa [hdeg] at h1
    · rw [map_mul, ← hAe, ← hBe]
      ring

def substVar {K : Type*} {ι : K → Type} {M : ℕ} {F : Type*} [CommRing F] (A : Fin M → MRing ι F) :
    (Σ o, bundleIdx ι M o) → MRing ι F
  | ⟨none, l⟩ => A l
  | ⟨some k, i⟩ => X ⟨k, i⟩

theorem subst_homog {K : Type*} [DecidableEq K] {ι : K → Type} {M : ℕ} {F : Type*} [CommRing F]
    (m : ℕ) (A : Fin M → MRing ι F) (hA : ∀ l, IsMultiHomog (A l) (fun _ => m))
    {h : MRing (bundleIdx ι M) F} {D : Option K → ℕ} (hh : IsMultiHomog h D) :
    IsMultiHomog (aeval (substVar A) h) (fun k => D (some k) + D none * m) := by
  let L : (Option K → ℕ) →+ (K → ℕ) :=
    { toFun := fun d k => d (some k) + d none * m
      map_zero' := by funext k; simp
      map_add' := by intro d d'; funext k; simp only [Pi.add_apply]; ring }
  have hω : ∀ p, IsMultiHomog (substVar A p) (L (blockWeight (bundleIdx ι M) p)) := by
    rintro ⟨o, i⟩
    cases o with
    | none =>
      have : L (blockWeight (bundleIdx ι M) ⟨none, i⟩) = fun _ => m := by
        funext k; simp [L, blockWeight]
      rw [this]; exact hA i
    | some k =>
      have : L (blockWeight (bundleIdx ι M) ⟨some k, i⟩) = blockWeight ι ⟨k, i⟩ := by
        funext k'; simp [L, blockWeight, Pi.single_apply]
      rw [this]; exact isWeightedHomogeneous_X F _ _
  have hD : (fun k => D (some k) + D none * m) = L D := rfl
  rw [hD, h.as_sum, map_sum]
  apply IsWeightedHomogeneous.sum
  intro μ hμ
  rw [aeval_monomial, algebraMap_eq, Finsupp.prod]
  have := (isWeightedHomogeneous_C (blockWeight ι) (coeff μ h)).mul (IsWeightedHomogeneous.prod
    μ.support (fun v => substVar A v ^ μ v) (fun v => μ v • L (blockWeight _ v))
    (fun v _ => (hω v).pow (μ v)))
  rw [zero_add] at this
  have e : L D = ∑ i ∈ μ.support, μ i • L (blockWeight _ i) := by
    rw [← hh (mem_support_iff.mp hμ), Finsupp.weight_apply, Finsupp.sum, map_sum]
    simp only [map_nsmul]
  rw [e]
  exact this

end FlagLineDegreeProof

open FlagLineDegreeProof in

theorem FlagLineDegree.proof : FlagLineDegree.Statement := by
  intro F _ Ω _ _ K _ _ ι _ y e hV _ N E _ _ B w b hflag M a φ hφ Φ _ _ t ht h0
  classical

  have hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hV.relevant k
    refine ⟨i, fun h => hi ?_⟩
    show pointConeMap F y (X ⟨k, i⟩) = 0
    simp [pointConeMap, h]
  choose c hc using hy
  have hS : segreVec y c ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  let i0 : Fin N := ⟨0, h0⟩
  let s : Ω := ∏ k, y ⟨k, c k⟩ ^ b i0 k
  have hs : s ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)

  obtain ⟨v, hv, hv0, hvs⟩ : ∃ v ∈ B.lat c, (∀ j, i0 < j → w.repr v j = 0) ∧ w.repr v i0 = s := by
    have hmem : s ∈ degLat F y (b i0) c := ⟨1, Subalgebra.one_mem _, by simp [s]⟩
    rw [← hflag.graded c hS i0] at hmem
    exact hmem
  have hφv : ∀ l, φ l v = s * φ l (w i0) := by
    intro l
    conv_lhs => rw [← w.sum_repr v]
    rw [map_sum, Finset.sum_eq_single i0]
    · rw [map_smul, smul_eq_mul, hvs]
    · intro j _ hj
      have hj' : i0 < j := by
        rw [Fin.lt_def]
        have : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
        show 0 < (j : ℕ)
        omega
      rw [hv0 j hj', zero_smul, map_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hsec : ∀ l, ∃ α ∈ chartRing F (segreVec y) c, s * φ l (w i0) = α * ∏ k, y ⟨k, c k⟩ ^ a k := by
    intro l
    rw [← hφv l]
    exact hφ.sections c hS l v hv
  choose α hα hαe using hsec
  choose m A hA hAe using fun l => chart_form y c hS (hα l)

  let m0 : ℕ := Finset.univ.sup m
  have hm : ∀ l, m l ≤ m0 := fun l => Finset.le_sup (Finset.mem_univ l)
  let σ : MRing ι F := ∏ k, X ⟨k, c k⟩
  have hσ : aeval y σ = segreVec y c := by simp [σ, segreVec, map_prod]
  let A' : Fin M → MRing ι F := fun l => A l * σ ^ (m0 - m l)
  have hA' : ∀ l, IsMultiHomog (A' l) (fun _ => m0) := by
    intro l
    have h1 := (hA l).mul ((segreForm_homog (R := F) c).pow (m0 - m l))
    have e : ((fun _ : K => m l) + (m0 - m l) • fun _ : K => (1 : ℕ)) = fun _ => m0 := by
      funext k; simp; have := hm l; omega
    rw [e] at h1
    exact h1
  have hA'e : ∀ l, α l * segreVec y c ^ m0 = aeval y (A' l) := by
    intro l
    rw [map_mul, map_pow, hσ, ← hAe l, mul_assoc, ← pow_add, Nat.add_sub_cancel' (hm l)]

  let ρ : Ω := (∏ k, y ⟨k, c k⟩ ^ a k) / (segreVec y c ^ m0 * s)
  have hρ : ρ ≠ 0 := div_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k))
    (mul_ne_zero (pow_ne_zero _ hS) hs)
  have hu : ∀ l, φ l (w i0) = ρ * aeval y (A' l) := by
    intro l
    rw [← hA'e l]
    have h1 := hαe l
    simp only [ρ]
    field_simp
    linear_combination h1

  let x := projCoord y w φ (truncCoord t 1)
  let lam : Φ := t i0 * algebraMap Ω Φ ρ
  have hlam : lam ≠ 0 := mul_ne_zero (ht.ne_zero i0) ((map_ne_zero _).mpr hρ)
  have hxn : ∀ l, x ⟨none, l⟩ = lam * algebraMap Ω Φ (aeval y (A' l)) := by
    intro l
    show ∑ i, truncCoord t 1 i * algebraMap Ω Φ (φ l (w i)) = _
    rw [Finset.sum_eq_single i0]
    · simp only [truncCoord, i0, hu l, lam, map_mul]
      simp
      ring
    · intro j _ hj
      have : ¬ (j : ℕ) < 1 := fun h => hj (Fin.ext (by simp [i0]; omega))
      simp [truncCoord, this]
    · intro h; exact absurd (Finset.mem_univ _) h
  let r : F →+* Φ := (algebraMap Ω Φ).comp (algebraMap F Ω)
  let cone := eval₂Hom (C.comp r) (fun p : (Σ o, bundleIdx ι M o) => C (x p) * X p.1)
  have hmemP : ∀ q, q ∈ projIdeal F y w φ (truncCoord t 1) ↔ cone q = 0 := fun q => Iff.rfl
  let θ : MRing (bundleIdx ι M) F →ₐ[F] MRing ι F := aeval (substVar A')
  let E' : MRing ι F →+* Φ := eval₂Hom r (fun p => algebraMap Ω Φ (y p))
  have hE' : ∀ q, E' q = algebraMap Ω Φ (aeval y q) := by
    intro q
    rw [aeval_def, eval₂_comp_left]
    rfl

  have key : ∀ (D : Option K → ℕ) (f : MRing (bundleIdx ι M) F), IsMultiHomog f D →
      eval₂ r x f = lam ^ D none * E' (θ f) := by
    intro D f hf
    let x0 : (Σ o, bundleIdx ι M o) → Φ := fun p => E' (θ (X p))
    let sc : MvPolynomial (Option K) Φ →+* Φ :=
      eval₂Hom (RingHom.id Φ) (fun o => Option.elim o lam (fun _ => 1))
    have h1 : (eval₂Hom r x : MRing (bundleIdx ι M) F →+* Φ) =
        sc.comp (eval₂Hom (C.comp r) (fun p => C (x0 p) * X p.1)) := by
      apply MvPolynomial.ringHom_ext
      · intro q; simp [sc]
      · rintro ⟨o, i⟩
        cases o with
        | none =>
          simp only [RingHom.comp_apply, eval₂Hom_X', sc, x0, θ, aeval_X, substVar]
          simp [hxn i, hE', mul_comm]
        | some k =>
          simp only [RingHom.comp_apply, eval₂Hom_X', sc, x0, θ, aeval_X, substVar]
          simp [E', x, projCoord]
    have h2 : (eval₂Hom r x0 : MRing (bundleIdx ι M) F →+* Φ) = E'.comp θ.toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro q; simp [E', θ]
      · intro p; simp [x0]
    have h3 := congrArg (fun g => g f) h1
    simp only [RingHom.comp_apply, coe_eval₂Hom] at h3
    have hc : eval₂ (C.comp r) (fun p => C (x0 p) * X p.1) f =
        C (eval₂ r x0 f) * ∏ o, (X o : MvPolynomial (Option K) Φ) ^ D o :=
      cone_of_isMultiHomog r x0 id hf
    rw [h3, hc, map_mul]
    have hsc : sc (∏ o, (X o : MvPolynomial (Option K) Φ) ^ D o) = lam ^ D none := by
      simp [sc, Fintype.prod_option]
    have hsc2 : sc (C (eval₂ r x0 f)) = eval₂ r x0 f := by simp [sc]
    rw [hsc, hsc2]
    have h4 := congrArg (fun g => g f) h2
    simp only [RingHom.comp_apply, coe_eval₂Hom] at h4
    rw [h4, mul_comm]
    rfl

  have hren : ∀ (D : K → ℕ) (q : MRing (fun k => bundleIdx ι M (Function.Embedding.some k)) F),
      IsMultiHomog q D →
      cone (rename (FieldNumbers.blockIncl (Function.Embedding.some : K ↪ Option K)
        (bundleIdx ι M)) q) = C (E' q) * ∏ k, (X (some k) : MvPolynomial (Option K) Φ) ^ D k := by
    intro D q hq
    simp only [cone, coe_eval₂Hom]
    rw [eval₂_rename]
    exact cone_of_isMultiHomog (ι := fun k => bundleIdx ι M (Function.Embedding.some k)) r
      (fun p => algebraMap Ω Φ (y p)) some hq
  have hcone : ∀ (D : Option K → ℕ) (f : MRing (bundleIdx ι M) F), IsMultiHomog f D →
      cone f = C (lam ^ D none * E' (θ f)) * ∏ o, (X o : MvPolynomial (Option K) Φ) ^ D o := by
    intro D f hf
    rw [← key D f hf]
    exact cone_of_isMultiHomog r x id hf
  have hmon : ∀ (D : K → ℕ), (∏ k, (X (some k) : MvPolynomial (Option K) Φ) ^ D k) ≠ 0 :=
    fun D => Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (X_ne_zero _)

  unfold FieldNumbers.relDeg
  rw [IntermediateField.relfinrank_eq_one_iff]
  conv_lhs => unfold FieldNumbers.homFracDegZero
  rw [IntermediateField.adjoin_le_iff]
  rintro _ ⟨D, f, g, hf, hg, hgP, rfl⟩
  have hEg : E' (θ g) ≠ 0 := by
    intro h0'
    apply hgP
    rw [hmemP, hcone D g hg, h0', mul_zero, map_zero, zero_mul]
  have hgren : rename (FieldNumbers.blockIncl (Function.Embedding.some : K ↪ Option K)
      (bundleIdx ι M)) (θ g) ∉ projIdeal F y w φ (truncCoord t 1) := by
    rw [hmemP, hren _ _ (subst_homog m0 A' hA' hg)]
    exact mul_ne_zero (C_ne_zero.mpr hEg) (hmon _)
  have hne : ∀ q ∉ projIdeal F y w φ (truncCoord t 1),
      algebraMap (MRing (bundleIdx ι M) F ⧸ projIdeal F y w φ (truncCoord t 1))
        (FractionRing (MRing (bundleIdx ι M) F ⧸ projIdeal F y w φ (truncCoord t 1)))
        (Ideal.Quotient.mk _ q) ≠ 0 := by
    intro q hq
    rw [map_ne_zero_iff _ (IsFractionRing.injective _ _)]
    exact fun h => hq (Ideal.Quotient.eq_zero_iff_mem.mp h)
  rw [SetLike.mem_coe, IntermediateField.mem_map]
  refine ⟨_, IntermediateField.subset_adjoin _ _
    ⟨fun k => D (some k) + D none * m0, θ f, θ g, subst_homog m0 A' hA' hf,
      subst_homog m0 A' hA' hg, hgren, rfl⟩, ?_⟩
  rw [map_div₀]
  erw [FieldNumbers.contractFracMap_mk Function.Embedding.some (projIdeal F y w φ (truncCoord t 1)),
    FieldNumbers.contractFracMap_mk Function.Embedding.some (projIdeal F y w φ (truncCoord t 1))]
  rw [
    div_eq_div_iff (hne _ hgren) (hne _ hgP), ← map_mul, ← map_mul, ← map_mul, ← map_mul]
  congr 1
  rw [Ideal.Quotient.eq, hmemP, map_sub, map_mul, map_mul, hren _ _ (subst_homog m0 A' hA' hf),
    hren _ _ (subst_homog m0 A' hA' hg), hcone D f hf, hcone D g hg]
  simp only [map_mul, map_pow]
  ring

end

end GroundTheory.Heights₂.Heights.NumbersDVR
