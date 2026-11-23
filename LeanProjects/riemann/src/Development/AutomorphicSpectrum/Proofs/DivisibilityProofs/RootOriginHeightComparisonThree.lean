import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsLatFlagPair
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SplitComps
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArMonoReline
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCompareSecondStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginCompareFirstStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginPointCompareStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootModelFlagCompareStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinModelPointsProjectStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsDenseNonvanishingStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinCoordsUnitValues
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BadExists
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm blockFnField)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)
open GlobalTheory.CompanionTheory.Ar.Num

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.OrIso

section Poly

variable {K' K : Type} [Fintype K'] [Fintype K] {ι : K' → Type} [∀ k, Fintype (ι k)]
  {J : K → Type} [∀ k, Fintype (J k)]

def pushDeg (κ : K' → K) [DecidableEq K] (d : K' → ℕ) : K → ℕ :=
  fun k => ∑ k', if κ k' = k then d k' else 0

theorem sum_single_block [DecidableEq K] (q : Σ k, J k) (n : ℕ) (k : K) :
    ∑ i, (Finsupp.single q n : (Σ k, J k) →₀ ℕ) ⟨k, i⟩ = if q.1 = k then n else 0 := by
  classical
  obtain ⟨k₀, i₀⟩ := q
  by_cases h : k₀ = k
  · subst h
    simp [Finsupp.single_apply]
  · have : ∀ i : J k, (Finsupp.single (⟨k₀, i₀⟩ : Σ k, J k) n) ⟨k, i⟩ = 0 := by
      intro i
      rw [Finsupp.single_apply, if_neg]
      intro e
      exact h (congrArg Sigma.fst e)
    simp [this, h]

theorem sum_mapDomain_block [DecidableEq K] {κ : K' → K} {u : (Σ k, ι k) → Σ k, J k}
    (hu : ∀ p, (u p).1 = κ p.1) (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    ∑ i, (Finsupp.mapDomain u m) ⟨k, i⟩ = ∑ k', if κ k' = k then ∑ i, m ⟨k', i⟩ else 0 := by
  classical
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb =>
    rw [Finsupp.mapDomain_add]
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, ha, hb]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k' _ => ?_
    split_ifs <;> simp
  | single p n =>
    rw [Finsupp.mapDomain_single, sum_single_block, hu]
    simp only [sum_single_block]
    by_cases h : κ p.1 = k
    · rw [if_pos h, Finset.sum_eq_single p.1]
      · simp [h]
      · intro b _ hb
        split_ifs with h1 h2
        · exact absurd h2.symm hb
        · rfl
        · rfl
      · simp
    · rw [if_neg h]
      symm
      refine Finset.sum_eq_zero fun k' _ => ?_
      split_ifs with h1 h2
      · exact absurd (h2 ▸ h1) h
      · rfl
      · rfl

theorem isMultiHomog_rename [DecidableEq K] {κ : K' → K} {u : (Σ k, ι k) → Σ k, J k}
    (hu : ∀ p, (u p).1 = κ p.1) {G : MRing ι} {d : K' → ℕ} (hG : IsMultiHomog G d) :
    IsMultiHomog (rename u G : MRing J) (pushDeg κ d) := by
  classical
  intro m hm k
  have e : (rename u G : MRing J) = ∑ m' ∈ G.support, monomial (m'.mapDomain u) (coeff m' G) := by
    conv_lhs => rw [G.as_sum]
    rw [map_sum]
    simp only [rename_monomial]
  have hm' : m ∈ (rename u G : MRing J).support := hm
  rw [e] at hm'
  obtain ⟨m', hm'', h2⟩ := Finset.mem_biUnion.1 (MvPolynomial.support_sum hm')
  have h3 := Finset.mem_singleton.1 (support_monomial_subset h2)
  subst h3
  rw [sum_mapDomain_block hu]
  refine Finset.sum_congr rfl fun k' _ => ?_
  rw [hG m' hm'' k']

theorem aeval_comp_hom {Ω' Ω : Type} [Field Ω'] [Field Ω] (i : Ω' →+* Ω) (y : (Σ k, ι k) → Ω') (g : MRing ι) :
    aeval (fun p => i (y p)) g = i (aeval y g) := by
  have e : (aeval (fun p => i (y p)) : MRing ι →ₐ[ℤ] Ω) = (i.toIntAlgHom).comp (aeval y) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp
  rw [e]
  rfl

theorem rename_mem {Ω' Ω : Type} [Field Ω'] [Field Ω] {κ : K' → K} {u : (Σ k, ι k) → Σ k, J k}
    (hu : ∀ p, (u p).1 = κ p.1) {y' : (Σ k, ι k) → Ω'} {y : (Σ k, J k) → Ω} (i : Ω' →+* Ω)
    (hy : ∀ p, y (u p) = i (y' p)) {q : MRing ι} (hq : q ∈ mCoordIdeal y') :
    rename u q ∈ mCoordIdeal y := by
  have key : ((mConeMap y).toRingHom.comp (rename u : MRing ι →ₐ[ℤ] MRing J).toRingHom) =
      (eval₂Hom ((C : Ω →+* MvPolynomial K Ω).comp i) (fun k => X (κ k))).comp
        (mConeMap y').toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro p
      simp [mConeMap, hy, hu]
  have h0 : mConeMap y' q = 0 := (RingHom.mem_ker).1 hq
  refine (RingHom.mem_ker).2 ?_
  have := congrArg (fun φ => φ q) key
  simp only [RingHom.comp_apply] at this
  have h1 : (mConeMap y') q = 0 := h0
  simpa [h1] using this

theorem eval_mConeMap {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (x : K' → Ω) (f : MRing ι) :
    eval x (mConeMap y f) = aeval (fun p => x p.1 * y p) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add p q hp hq => simp [hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, hp]
    simp [mConeMap, mul_comm]

def scaleForm (c : K' → ℕ) (f : MRing ι) : MRing ι :=
  bind₁ (fun p => C (c p.1 : ℤ) * X p) f

theorem aeval_scaleForm {A : Type} [CommRing A] (c : K' → ℕ) (f : MRing ι) (z : (Σ k, ι k) → A) :
    aeval z (scaleForm c f) = aeval (fun p => (c p.1 : A) * z p) f := by
  rw [scaleForm, aeval_bind₁]
  congr 2
  funext p
  simp

theorem exists_scale {Ω : Type} [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) {f : MRing ι}
    (hf : f ∉ mCoordIdeal y) : ∃ c : K' → ℕ, (∀ k, c k ≠ 0) ∧ aeval y (scaleForm c f) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  apply hf
  refine (RingHom.mem_ker).2 ?_
  have hinf : ((fun n : ℕ => ((n + 1 : ℕ) : Ω)) '' Set.univ).Infinite :=
    Set.infinite_univ.image (fun a _ b _ h => by
      have : ((a + 1 : ℕ) : Ω) = ((b + 1 : ℕ) : Ω) := h
      have := Nat.cast_injective this
      omega)
  refine MvPolynomial.funext_set (fun _ => (fun n : ℕ => ((n + 1 : ℕ) : Ω)) '' Set.univ) (fun _ => hinf) ?_
  intro x hx
  have hx' : ∀ k, ∃ n : ℕ, ((n + 1 : ℕ) : Ω) = x k := by
    intro k
    obtain ⟨n, -, hn⟩ := hx k (Set.mem_univ k)
    exact ⟨n, hn⟩
  choose n hn using hx'
  have h0 := hcon (fun k => n k + 1) (fun k => Nat.succ_ne_zero _)
  rw [aeval_scaleForm] at h0
  have e : (fun p : Σ k, ι k => x p.1 * y p) = fun p => ((n p.1 + 1 : ℕ) : Ω) * y p := by
    funext p
    rw [hn]
  rw [eval_mConeMap, map_zero, e]
  exact h0

theorem aeval_smul_of_homog {A : Type} [CommRing A] {g : MRing ι} {d : K' → ℕ} (hg : IsMultiHomog g d)
    (c : K' → A) (z : (Σ k, ι k) → A) :
    aeval (fun p => c p.1 * z p) g = (∏ k, c k ^ d k) * aeval z g := by
  classical
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have h1 : ∏ p : (Σ k, ι k), c p.1 ^ m p = ∏ k, c k ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, c k ^ m ⟨k, i⟩ = c k ^ d k
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  simp only [mul_pow, Finset.prod_mul_distrib, h1]
  ring

theorem hasVal_smul {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {a : K' → ℤ} {s : Ω} {z : (Σ k, ι k) → ℂ} {w : ℂ}
    (h : Small.HasVal y a s z w) {c : K' → ℂ} (hc : ∀ k, c k ≠ 0) :
    Small.HasVal y a s (fun p => c p.1 * z p) ((∏ k, c k ^ a k) * w) := by
  obtain ⟨dg, dh, g, h', hg, hh, hd, e, n, v⟩ := h
  have hP : ∀ d : K' → ℕ, (∏ k, c k ^ d k) ≠ 0 := fun d =>
    Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
  refine ⟨dg, dh, g, h', hg, hh, hd, e, ?_, ?_⟩
  · rw [aeval_smul_of_homog hh]
    exact mul_ne_zero (hP _) n
  · rw [aeval_smul_of_homog hg, aeval_smul_of_homog hh, v]
    have : (∏ k, c k ^ dg k) = (∏ k, c k ^ a k) * ∏ k, c k ^ dh k := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_natCast, hd k, zpow_add₀ (hc k), zpow_natCast, mul_comm]
    rw [this]
    ring

end Poly

section Rel

variable {K₀ K₁ K : Type} [Fintype K₀] [Fintype K₁] [Fintype K] [DecidableEq K]
  {ι₀ : K₀ → Type} [∀ k, Fintype (ι₀ k)] {ι₁ : K₁ → Type} [∀ k, Fintype (ι₁ k)]
  {J : K → Type} [∀ k, Fintype (J k)]

theorem val_rel {Ω₀ Ω₁ Ω : Type} [Field Ω₀] [Field Ω₁] [Field Ω] {κ₀ : K₀ → K} {κ₁ : K₁ → K}
    {u₀ : (Σ k, ι₀ k) → Σ k, J k} {u₁ : (Σ k, ι₁ k) → Σ k, J k}
    (hu₀ : ∀ p, (u₀ p).1 = κ₀ p.1) (hu₁ : ∀ p, (u₁ p).1 = κ₁ p.1)
    {y₀ : (Σ k, ι₀ k) → Ω₀} {y₁ : (Σ k, ι₁ k) → Ω₁} {y : (Σ k, J k) → Ω} (i₀ : Ω₀ →+* Ω) (i₁ : Ω₁ →+* Ω)
    (hy₀ : ∀ p, y (u₀ p) = i₀ (y₀ p)) (hy₁ : ∀ p, y (u₁ p) = i₁ (y₁ p))
    {a₀ : K₀ → ℤ} {a₁ : K₁ → ℤ} {s₀ : Ω₀} {s₁ : Ω₁} {f g : MRing J} {bf bg : K → ℕ}
    (hf : IsMultiHomog f bf) (hg : IsMultiHomog g bg)
    (hb : ∀ k, (bf k : ℤ) - bg k =
      (∑ k', if κ₀ k' = k then a₀ k' else 0) - ∑ k', if κ₁ k' = k then a₁ k' else 0)
    (hval : aeval y f * i₁ s₁ = aeval y g * i₀ s₀)
    {z : (Σ k, J k) → ℂ} (hz : ∀ q ∈ mCoordIdeal y, aeval z q = 0) {w₀ w₁ : ℂ}
    (h₀ : Small.HasVal y₀ a₀ s₀ (fun p => z (u₀ p)) w₀) (h₁ : Small.HasVal y₁ a₁ s₁ (fun p => z (u₁ p)) w₁) :
    aeval z f * w₁ = aeval z g * w₀ := by
  obtain ⟨dg₀, dh₀, G₀, H₀, hG₀, hH₀, hd₀, e₀, n₀, v₀⟩ := h₀
  obtain ⟨dg₁, dh₁, G₁, H₁, hG₁, hH₁, hd₁, e₁, n₁, v₁⟩ := h₁
  have rn₀ : ∀ q : MRing ι₀, aeval y (rename u₀ q) = i₀ (aeval y₀ q) := fun q => by
    rw [aeval_rename]
    have : y ∘ u₀ = fun p => i₀ (y₀ p) := funext hy₀
    rw [this]
    exact aeval_comp_hom i₀ y₀ q
  have rn₁ : ∀ q : MRing ι₁, aeval y (rename u₁ q) = i₁ (aeval y₁ q) := fun q => by
    rw [aeval_rename]
    have : y ∘ u₁ = fun p => i₁ (y₁ p) := funext hy₁
    rw [this]
    exact aeval_comp_hom i₁ y₁ q
  have hdeg : bf + pushDeg κ₁ dg₁ + pushDeg κ₀ dh₀ = bg + pushDeg κ₀ dg₀ + pushDeg κ₁ dh₁ := by
    funext k
    have h1 : ((pushDeg κ₀ dg₀ k : ℕ) : ℤ) = pushDeg κ₀ dh₀ k + ∑ k', if κ₀ k' = k then a₀ k' else 0 := by
      simp only [pushDeg, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k' _ => ?_
      split_ifs
      · exact hd₀ k'
      · simp
    have h2 : ((pushDeg κ₁ dg₁ k : ℕ) : ℤ) = pushDeg κ₁ dh₁ k + ∑ k', if κ₁ k' = k then a₁ k' else 0 := by
      simp only [pushDeg, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k' _ => ?_
      split_ifs
      · exact hd₁ k'
      · simp
    have h3 := hb k
    simp only [Pi.add_apply]
    omega
  have hA : IsMultiHomog (f * rename u₁ G₁ * rename u₀ H₀ + -(g * rename u₀ G₀ * rename u₁ H₁))
      (bf + pushDeg κ₁ dg₁ + pushDeg κ₀ dh₀) :=
    GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.mhAdd (GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.mhMul (GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.mhMul hf (isMultiHomog_rename hu₁ hG₁)) (isMultiHomog_rename hu₀ hH₀))
      (GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.mhNeg (hdeg ▸ GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.mhMul (GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine.mhMul hg (isMultiHomog_rename hu₀ hG₀))
        (isMultiHomog_rename hu₁ hH₁)))
  have hmem := hz _ (Small.LineModel.mem_of_aeval y hA (by
    simp only [map_add, map_neg, map_mul, rn₀, rn₁, e₀, e₁]
    linear_combination (i₀ (aeval y₀ H₀) * i₁ (aeval y₁ H₁)) * hval))
  simp only [map_add, map_neg, map_mul, aeval_rename] at hmem
  have c₀ : z ∘ u₀ = fun p => z (u₀ p) := rfl
  have c₁ : z ∘ u₁ = fun p => z (u₁ p) := rfl
  rw [c₀, c₁, v₀, v₁] at hmem
  have : (aeval z f * w₁ - aeval z g * w₀) * ((aeval (fun p => z (u₀ p)) H₀) * (aeval (fun p => z (u₁ p)) H₁)) = 0 := by
    linear_combination hmem
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right (mul_ne_zero n₀ n₁))

end Rel

theorem zero_of_sum_Iic {n : ℕ} (d : Fin n → ℝ) (h : ∀ p, ∑ k ∈ Finset.Iic p, d k = 0) : ∀ p, d p = 0 := by
  intro p
  induction' hp : (p : ℕ) using Nat.strong_induction_on with m ih generalizing p
  have hs : Finset.Iic p = insert p (Finset.Iio p) := by
    ext k
    simp [le_iff_lt_or_eq, or_comm]
  have h1 := h p
  rw [hs, Finset.sum_insert (by simp)] at h1
  have h2 : ∑ k ∈ Finset.Iio p, d k = 0 :=
    Finset.sum_eq_zero fun k hk => ih k (by rw [← hp]; exact Fin.lt_def.1 (Finset.mem_Iio.1 hk)) k rfl
  linarith

theorem isMultiHomog_of_dvr {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {f : MRing ι} {b : K → ℕ} (h : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f b) : IsMultiHomog f b := by
  intro m hm k
  have h1 := h (mem_support_iff.mp hm)
  rw [← h1, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, GroundTheory.Heights₂.Heights.NumbersDVR.blockWeight,
    Pi.single_apply]
  rw [Fintype.sum_sigma]
  simp

theorem aeval_zero_of_mem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) {g : MRing ι} (h : g ∈ mCoordIdeal y) : aeval y g = 0 := by
  have h0 : mConeMap y g = 0 := (RingHom.mem_ker).1 h
  have e : ((aeval (fun _ : K => (1 : Ω)) : MvPolynomial K Ω →ₐ[Ω] Ω).restrictScalars ℤ).comp (mConeMap y) =
      aeval y := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMap]
  rw [← e, AlgHom.comp_apply, h0, map_zero]

theorem scaleForm_mem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (c : K → ℕ) (y : (Σ k, ι k) → Ω) {q : MRing ι} (hq : q ∈ mCoordIdeal y) : scaleForm c q ∈ mCoordIdeal y := by
  have e : (mConeMap y).comp (bind₁ (fun p : Σ k, ι k => C (c p.1 : ℤ) * X p)) =
      ((aeval (fun k => C (c k : Ω) * X k) : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K Ω).restrictScalars ℤ).comp
        (mConeMap y) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMap]
    ring
  have h0 : mConeMap y q = 0 := (RingHom.mem_ker).1 hq
  refine (RingHom.mem_ker).2 ?_
  have := congrArg (fun φ => φ q) e
  simp only [AlgHom.comp_apply] at this
  rw [h0, map_zero] at this
  exact this

theorem block_ne {K₁ K : Type} [Fintype K] {ι : K₁ → Type} {J : K → Type} {κ : K₁ → K}
    {v : (Σ k, ι k) → Σ k, J k} (hv : IsBlockMap κ v) {z : (Σ k, J k) → ℂ} (hz : ∀ k, ∃ a, z ⟨k, a⟩ ≠ 0) (k : K₁) :
    ∃ a, z (v ⟨k, a⟩) ≠ 0 := by
  obtain ⟨a, ha⟩ := hz (κ k)
  obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, a⟩ ⟨k, rfl⟩
  obtain ⟨k', b⟩ := p
  have h1 : κ k' = κ k := by
    have := hv.2.2.1 ⟨k', b⟩
    rw [hp] at this
    exact this.symm
  obtain rfl := hv.1 h1
  exact ⟨b, by rw [hp]; exact ha⟩

theorem orbit_trans {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {a b c : (Σ k, ι k) → ℂ}
    (h1 : SameOrbit a b) (h2 : SameOrbit b c) : SameOrbit a c := by
  obtain ⟨c1, hc1, rfl⟩ := h1
  obtain ⟨c2, hc2, rfl⟩ := h2
  exact ⟨fun k => c1 k * c2 k, fun k => mul_ne_zero (hc1 k) (hc2 k), by funext q; simp [mul_assoc]⟩

theorem sum_ite_pull {K₁ K : Type} [Fintype K₁] [DecidableEq K] {κ : K₁ → K} (hκ : Function.Injective κ)
    (a : K₁ → ℤ) (k : K) : (∑ k', if κ k' = k then a k' else 0) = pullDeg κ a k := by
  classical
  by_cases h : k ∈ Set.range κ
  · obtain ⟨k₀, rfl⟩ := h
    rw [pullDeg, hκ.extend_apply, Finset.sum_eq_single k₀]
    · simp
    · intro b _ hb
      rw [if_neg fun e => hb (hκ e)]
    · simp
  · rw [pullDeg, Function.extend_apply' _ _ _ (by simpa using h)]
    refine Finset.sum_eq_zero fun k' _ => ?_
    rw [if_neg fun e => h ⟨k', e⟩]

section Origin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S S₀ : Finset ℕ}
  {M R : RootModel (CMType H) (D.p + D.q)}
  {Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))} {Fx : FixedData Y Sys}

theorem side [CharZero M.Ω] (o : RootOrigin Y S M Fx) (o₀ : RootOrigin Y S₀ R Fx) (i : R.Ω →+* M.Ω)
    (hi : i.comp o₀.g = o.g) (hJ : o.Re.J = ⊤) (hJ₀ : o₀.Re.J = ⊤) :
    ∃ F : MRing (Cmp.joinIdx M.ι R.ι), aeval (Ht.joinOf M R i) F ≠ 0 ∧
      ∀ w ∈ Small.ptsOver ℂ (mCoordIdeal (Ht.joinOf M R i)), aeval w F ≠ 0 →
        ∃ (x : o.Re.R.X) (x' : o₀.Re.R.X),
          SameOrbit (o.Re.R.lift x x) (fun p => w (Cmp.joinInl M.ι R.ι p)) ∧
          SameOrbit (o₀.Re.R.lift x' x') (fun p => w (Cmp.joinInr M.ι R.ι p)) ∧
          o.Re.π x = o₀.Re.π x' ∧ o.Re.π x ∈ Sys.open' ∧
          ∀ (r : RootIx D) (v : ℂ),
            Small.HasVal (Ht.joinOf M R i) (Ht.joinDeg M R (some r)) (i (o₀.e r) / o.e r) w v →
            ‖v‖ * (o₀.sing r).h (fun p => w (Cmp.joinInr M.ι R.ι p)) =
              (o.sing r).h (fun p => w (Cmp.joinInl M.ι R.ι p)) := by
  obtain ⟨f, hf, hfp⟩ := GlobalTheory.T.root_origin_compare_second E H D l Xo c Y S S₀ M R Sys Fx o o₀ i hi hJ hJ₀
  obtain ⟨cc, hcc, hne⟩ := exists_scale (Ht.joinOf M R i) hf
  refine ⟨scaleForm cc f, hne, fun w hw hwF => ?_⟩
  have hwF' := hwF
  rw [aeval_scaleForm] at hwF'
  have hc : ∀ k, (cc k : ℂ) ≠ 0 := fun k => Nat.cast_ne_zero.2 (hcc k)
  have hw' : (fun p => (cc p.1 : ℂ) * w p) ∈ Small.ptsOver ℂ (mCoordIdeal (Ht.joinOf M R i)) := by
    refine ⟨fun k => ?_, fun q hq => ?_⟩
    · obtain ⟨a, ha⟩ := hw.1 k
      exact ⟨a, mul_ne_zero (hc k) ha⟩
    · rw [← aeval_scaleForm]
      exact hw.2 _ (scaleForm_mem cc _ hq)
  have hwf : Cmp.evC (fun p => (cc p.1 : ℂ) * w p) f ≠ 0 := by
    rw [Cmp.evC, Small.LineModel.eval_map_eq]
    exact hwF'
  obtain ⟨x, x', z₁, z₂, ho₁, ho₂, hπ, hop, hc₁, hc₂, hi₁, hi₂⟩ := hfp _ hw' hwf
  refine ⟨x, x', orbit_trans ho₁ ⟨fun k => (cc (Sum.inl k) : ℂ), fun k => hc _, rfl⟩,
    orbit_trans ho₂ ⟨fun k => (cc (Sum.inr k) : ℂ), fun k => hc _, rfl⟩, hπ, hop, ?_⟩
  intro r v hv
  have h1 := GlobalTheory.T.root_origin_compare_first E H D l Xo c Y S S₀ M R Sys Fx o o₀ i hi z₁ z₂ _ hw' hc₁ hc₂ hi₁ hi₂ r _
    (hasVal_smul hv (c := fun k => (cc k : ℂ)) hc)
  have e₁ : (fun p => (cc (Cmp.joinInl M.ι R.ι p).1 : ℂ) * w (Cmp.joinInl M.ι R.ι p)) =
      fun p => (fun k => (cc (Sum.inl k) : ℂ)) p.1 * w (Cmp.joinInl M.ι R.ι p) := rfl
  have e₂ : (fun p => (cc (Cmp.joinInr M.ι R.ι p).1 : ℂ) * w (Cmp.joinInr M.ι R.ι p)) =
      fun p => (fun k => (cc (Sum.inr k) : ℂ)) p.1 * w (Cmp.joinInr M.ι R.ι p) := rfl
  rw [e₁, e₂, (o₀.sing r).smul _ _ (fun k => hc _), (o.sing r).smul _ _ (fun k => hc _), o.sing_deg, o₀.sing_deg,
    norm_mul, norm_prod, Fintype.prod_sum_type] at h1
  have hA : (∏ k, ‖(cc (Sum.inl k : M.K ⊕ R.K) : ℂ)‖ ^ M.xdeg r k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc _))
  have hB : (∏ k, ‖(cc (Sum.inr k : M.K ⊕ R.K) : ℂ)‖ ^ R.xdeg r k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc _))
  have l₁ : (∏ k : M.K, ‖(cc (Sum.inl k) : ℂ) ^ Ht.joinDeg M R (some r) (Sum.inl k)‖) =
      ∏ k, ‖(cc (Sum.inl k : M.K ⊕ R.K) : ℂ)‖ ^ M.xdeg r k := by
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [norm_zpow]
    show _ ^ (M.x 1 r).a k = _
    rw [M.x_deg]
  have l₂ : (∏ k : R.K, ‖(cc (Sum.inr k) : ℂ) ^ Ht.joinDeg M R (some r) (Sum.inr k)‖) =
      (∏ k, ‖(cc (Sum.inr k : M.K ⊕ R.K) : ℂ)‖ ^ R.xdeg r k)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [norm_zpow]
    show _ ^ (-(R.x 1 r).a) k = _
    rw [R.x_deg, Pi.neg_apply, zpow_neg]
  rw [l₁, l₂] at h1
  have : (∏ k, ‖(cc (Sum.inl k : M.K ⊕ R.K) : ℂ)‖ ^ M.xdeg r k) *
      (‖v‖ * (o₀.sing r).h (fun p => w (Cmp.joinInr M.ι R.ι p))) =
      (∏ k, ‖(cc (Sum.inl k : M.K ⊕ R.K) : ℂ)‖ ^ M.xdeg r k) *
        (o.sing r).h (fun p => w (Cmp.joinInl M.ι R.ι p)) := by
    rw [← h1]
    field_simp
  exact mul_left_cancel₀ hA this

theorem join_pt {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
    {y : (Σ k, J k) → Ω} {κ : M.K → K} {v : (Σ k, M.ι k) → Σ k, J k} {κR : R.K → K}
    {vR : (Σ k, R.ι k) → Σ k, J k} (hv : IsBlockMap κ v) (hvR : IsBlockMap κR vR) (i : R.Ω →+* M.Ω)
    (j : M.Ω →+* Ω) (hy : ∀ p, y (v p) = j (M.y p)) (hyR : ∀ p, y (vR p) = j (i (R.y p)))
    {z : (Σ k, J k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) :
    (fun q => z (Cmp.joinVec v vR q)) ∈ Small.ptsOver ℂ (mCoordIdeal (Ht.joinOf M R i)) := by
  refine ⟨?_, fun q hq => ?_⟩
  · rintro (k | k)
    · exact block_ne hv hz.1 k
    · exact block_ne hvR hz.1 k
  · have hu : ∀ p, (Cmp.joinVec v vR p).1 = Sum.elim κ κR p.1 := by
      rintro ⟨k | k, a⟩
      · exact hv.2.2.1 ⟨k, a⟩
      · exact hvR.2.2.1 ⟨k, a⟩
    have hyJ : ∀ p, y (Cmp.joinVec v vR p) = j (Ht.joinOf M R i p) := by
      rintro ⟨k | k, a⟩
      · exact hy ⟨k, a⟩
      · exact hyR ⟨k, a⟩
    have h1 := hz.2 _ (rename_mem hu j hyJ hq)
    rw [Small.LineModel.eval_map_eq, aeval_rename] at h1
    exact h1

theorem side_pt {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [CharZero Ω]
    {y : (Σ k, J k) → Ω} {κ : M.K → K} {v : (Σ k, M.ι k) → Σ k, J k} {κR : R.K → K}
    {vR : (Σ k, R.ι k) → Σ k, J k} (hv : IsBlockMap κ v) (hvR : IsBlockMap κR vR)
    (o : RootOrigin Y S M Fx) (o₀ : RootOrigin Y S₀ R Fx) (i : R.Ω →+* M.Ω)
    (hi : i.comp o₀.g = o.g) (hJ : o.Re.J = ⊤) (hJ₀ : o₀.Re.J = ⊤)
    (j : M.Ω →+* Ω) (hy : ∀ p, y (v p) = j (M.y p)) (hyR : ∀ p, y (vR p) = j (i (R.y p))) :
    ∃ F : MRing J, aeval y F ≠ 0 ∧ ∀ z ∈ mcPts (mCoordIdeal y), aeval z F ≠ 0 →
      ∃ (x' : o₀.Re.R.X) (val : RootIx D → ℂ),
        SameOrbit (o₀.Re.R.lift x' x') (fun p => z (vR p)) ∧ (∀ r, val r ≠ 0) ∧
        (∀ r, Small.HasVal (Ht.joinOf M R i) (Ht.joinDeg M R (some r)) (i (o₀.e r) / o.e r)
          (fun q => z (Cmp.joinVec v vR q)) (val r)) ∧
        ∀ t, 0 < t → t ≤ Sys.t₀ → ∀ (τ : CMType H) (p : Fin (D.p + D.q)),
          -∑ k ∈ Finset.Iic p, (Real.log ((M.x t (τ, k)).h fun q => z (v q)) -
            Real.log ((R.x 1 (τ, k)).h fun q => z (vR q)) - Real.log ‖val (τ, k)‖) =
          Sys.phT (some (τ, p)) t (o₀.Re.π x') + (Real.log ((o₀.Re.ref (some (τ, p))).h fun q => z (vR q)) +
            ∑ k ∈ Finset.Iic p, Real.log ((R.x 1 (τ, k)).h fun q => z (vR q))) := by
  classical
  haveI : CharZero M.Ω := j.charZero
  obtain ⟨F, hF, hFp⟩ := side o o₀ i hi hJ hJ₀
  have hyJ : y ∘ Cmp.joinVec v vR = fun p => j (Ht.joinOf M R i p) := by
    funext p
    obtain ⟨k | k, a⟩ := p
    · exact hy ⟨k, a⟩
    · exact hyR ⟨k, a⟩
  refine ⟨rename (Cmp.joinVec v vR) F, ?_, fun z hz hzF => ?_⟩
  · rw [aeval_rename, hyJ, aeval_comp_hom]
    exact (map_ne_zero j).2 hF
  · have hw := join_pt hv hvR i j hy hyR hz
    rw [aeval_rename] at hzF
    obtain ⟨x, x', ho₁, ho₂, hπ, hop, hs⟩ := hFp _ hw hzF
    have hunit : ∀ r, Ht.GenUnit (Ht.joinOf M R i) (Ht.joinDeg M R (some r)) (i (o₀.e r) / o.e r) := by
      intro r
      refine GlobalTheory.T.root_model_flag_compare E H D l Xo c Y S S₀ M R o.𝔐 o₀.𝔐 o.Fl o₀.Fl i o.e o₀.e ?_ ?_ o.lines o₀.lines r
      · rw [o.g_over, o₀.g_over, ← hi, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
      · intro s' k
        have hd : dualMap o.g = (dualMap i).comp (dualMap o₀.g) := by
          rw [← hi]
          ext a <;> simp [dualMap]
        rw [o.g_flag, o₀.g_flag, hd, ← Category.assoc, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
    have hex := fun r => hunit r ℂ _ hw
    choose val hval0 hval using hex
    obtain ⟨hw₁, hw₂⟩ := (GlobalTheory.T.join_model_points_project _ _ M R i).2.2.1 ℂ _ hw
    rw [Small.LineModel.ptsOver_complex] at hw₁ hw₂
    refine ⟨x', val, ho₂, hval0, hval, fun t ht0 ht τ p => ?_⟩
    have hid := GlobalTheory.T.root_origin_point_compare E H D l Xo c Y S S₀ M R Sys Fx o o₀ x x' _ _ (fun r => ‖val r‖) t ht0 ht hw₁ hw₂ ho₁ ho₂
      hπ hop (fun r => ⟨norm_pos_iff.2 (hval0 r), hs r _ (hval r)⟩) τ p
    rw [hπ] at hid
    exact hid

theorem pi_eq (o₀ : RootOrigin Y S₀ R Fx) {x₁ x₂ : o₀.Re.R.X} {w : (Σ k, R.ι k) → ℂ}
    (h₁ : SameOrbit (o₀.Re.R.lift x₁ x₁) w) (h₂ : SameOrbit (o₀.Re.R.lift x₂ x₂) w) :
    o₀.Re.π x₁ = o₀.Re.π x₂ := by
  obtain ⟨c₁, hc₁, e₁⟩ := h₁
  obtain ⟨c₂, hc₂, e₂⟩ := h₂
  obtain ⟨a₁, ha₁, f₁⟩ := TowerOriginModel.pi_pt_ne o₀ x₁
  obtain ⟨a₂, ha₂, f₂⟩ := TowerOriginModel.pi_pt_ne o₀ x₂
  refine Fx.pt_inj _ _ (a₁⁻¹ * c₁ o₀.k₀ * (c₂ o₀.k₀)⁻¹ * a₂) (funext fun b => ?_)
  have g₁ := congrFun f₁ b
  have g₂ := congrFun f₂ b
  simp only [e₁, e₂, Pi.smul_apply, smul_eq_mul] at g₁ g₂
  have h₀ := hc₂ o₀.k₀
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination (-c₂ o₀.k₀) * g₁ + c₁ o₀.k₀ * g₂

end Origin

theorem root_isometric : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S₀ S : Finset ℕ) (M₀ M₁ Rf : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (o₀ : RootOrigin Y S₀ M₀ Fx) (o₁ : RootOrigin Y S M₁ Fx) (oR : RootOrigin Y ∅ Rf Fx) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (κ₀ : M₀.K → K) (v₀ : (Σ k, M₀.ι k) → Σ k, J k) (κ₁ : M₁.K → K) (v₁ : (Σ k, M₁.ι k) → Σ k, J k) (κR : Rf.K → K) (vR : (Σ k, Rf.ι k) → Σ k, J k) (i₀ : M₀.Ω →+* Ω) (i₁ : M₁.Ω →+* Ω) (iR : Rf.Ω →+* Ω), IsBlockMap κ₀ v₀ → IsBlockMap κ₁ v₁ → IsBlockMap κR vR → (∀ p, y (v₀ p) = i₀ (M₀.y p)) → (∀ p, y (v₁ p) = i₁ (M₁.y p)) → (∀ p, y (vR p) = iR (Rf.y p)) → i₀.comp o₀.g = iR.comp oR.g → i₁.comp o₁.g = iR.comp oR.g → o₀.Re.J = ⊤ → o₁.Re.J = ⊤ → oR.Re.J = ⊤ → oR.Fl.deg = 1 → ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (dimFl (CMType H) (D.p + D.q) + 1) → ∀ (r : CMType H × Fin (D.p + D.q)) (f g : MvPolynomial (Σ k, J k) ℤ) (bf bg : K → ℕ), GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog f bf → GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog g bg → (fun k => (bf k : ℤ) - bg k) = pullDeg κ₀ (M₀.xdeg r) - pullDeg κ₁ (M₁.xdeg r) → f ∉ mCoordIdeal y → g ∉ mCoordIdeal y → aeval y f = i₁ (o₁.e r) / i₀ (o₀.e r) * aeval y g → ∀ t, 0 < t → t ≤ Sys.t₀ → ∀ z ∈ mcPts (mCoordIdeal y), ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) f)‖ * (M₁.x t r).h (fun p => z (v₁ p)) = ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) g)‖ * (M₀.x t r).h (fun p => z (v₀ p)) := by
  intro E _ _ _ H D l Xo c Y S₀ S M₀ M₁ Rf Sys Fx o₀ o₁ oR Ω _ _ K _ _ J _ y κ₀ v₀ κ₁ v₁ κR vR i₀ i₁ iR hv₀ hv₁ hvR
    hy₀ hy₁ hyR hc₀ hc₁ hJ₀ hJ₁ hJR hdeg hA r f g bf bg hf hg hb hfn hgn hfg t ht0 ht z hz
  have hf' := isMultiHomog_of_dvr hf
  have hg' := isMultiHomog_of_dvr hg

  have hbij : Function.Bijective oR.g := by
    refine ⟨oR.g.injective, ?_⟩
    letI := oR.g.toAlgebra
    have h1 : Module.finrank Fx.Ωf Rf.Ω = 1 := oR.g_deg.trans hdeg
    obtain ⟨u, hu0, hu⟩ := finrank_eq_one_iff'.1 h1
    intro w
    obtain ⟨a, ha⟩ := hu 1
    obtain ⟨b, hb'⟩ := hu w
    have ha' : oR.g a * u = 1 := ha
    have hb'' : oR.g b * u = w := hb'
    have hga : oR.g a ≠ 0 := left_ne_zero_of_mul_eq_one ha'
    refine ⟨b * a⁻¹, ?_⟩
    rw [map_mul, map_inv₀, ← hb'']
    field_simp
    linear_combination (-oR.g b) * ha'
  let e := RingEquiv.ofBijective oR.g hbij
  have he : ∀ a, oR.g (e.symm a) = a := fun a => e.apply_symm_apply a
  have he' : ∀ a, e.symm (oR.g a) = a := fun a => e.symm_apply_apply a
  let a₀ : Rf.Ω →+* M₀.Ω := o₀.g.comp e.symm.toRingHom
  let a₁ : Rf.Ω →+* M₁.Ω := o₁.g.comp e.symm.toRingHom
  have ha₀ : a₀.comp oR.g = o₀.g := by
    ext u
    simp [a₀, he']
  have ha₁ : a₁.comp oR.g = o₁.g := by
    ext u
    simp [a₁, he']
  have hi₀ : ∀ u, i₀ (a₀ u) = iR u := fun u => by
    have := congrArg (fun φ : Fx.Ωf →+* Ω => φ (e.symm u)) hc₀
    simpa [a₀, he] using this
  have hi₁ : ∀ u, i₁ (a₁ u) = iR u := fun u => by
    have := congrArg (fun φ : Fx.Ωf →+* Ω => φ (e.symm u)) hc₁
    simpa [a₁, he] using this
  obtain ⟨F₀, hF₀, hp₀⟩ := side_pt hv₀ hvR o₀ oR a₀ ha₀ hJ₀ hJR i₀ hy₀ (fun p => by rw [hi₀]; exact hyR p)
  obtain ⟨F₁, hF₁, hp₁⟩ := side_pt hv₁ hvR o₁ oR a₁ ha₁ hJ₁ hJR i₁ hy₁ (fun p => by rw [hi₁]; exact hyR p)

  have hfy : aeval y f ≠ 0 := fun h => hfn (Small.LineModel.mem_of_aeval y hf' h)
  have hgy : aeval y g ≠ 0 := fun h => hgn (Small.LineModel.mem_of_aeval y hg' h)
  have he₁ : i₁ (o₁.e r) ≠ 0 := by
    intro h
    rw [h] at hfg
    simp at hfg
    exact hfy hfg
  have he₀ : i₀ (o₀.e r) ≠ 0 := by
    intro h
    rw [h] at hfg
    simp at hfg
    exact hfy hfg
  have hrel : aeval y f * i₁ (a₁ (oR.e r) / o₁.e r) = aeval y g * i₀ (a₀ (oR.e r) / o₀.e r) := by
    rw [map_div₀, map_div₀, hi₀, hi₁, hfg]
    field_simp
  have hdegs : ∀ k, (bf k : ℤ) - bg k =
      (∑ k', if Sum.elim κ₀ κR k' = k then Ht.joinDeg M₀ Rf (some r) k' else 0) -
        ∑ k', if Sum.elim κ₁ κR k' = k then Ht.joinDeg M₁ Rf (some r) k' else 0 := by
    intro k
    have h1 := congrFun hb k
    have hs : ∀ (M : RootModel (CMType H) (D.p + D.q)) (κ : M.K → K), Function.Injective κ →
        (∑ k', if Sum.elim κ κR k' = k then Ht.joinDeg M Rf (some r) k' else 0) =
          pullDeg κ (M.xdeg r) k - pullDeg κR (Rf.xdeg r) k := by
      intro M κ hκ
      rw [Fintype.sum_sum_type, ← sum_ite_pull hκ, ← sum_ite_pull hvR.1, sub_eq_add_neg, ← Finset.sum_neg_distrib]
      congr 1
      · refine Finset.sum_congr rfl fun k' _ => ?_
        show (if κ k' = k then (M.x 1 r).a k' else 0) = _
        rw [M.x_deg]
      · refine Finset.sum_congr rfl fun k' _ => ?_
        show (if κR k' = k then (-(Rf.x 1 r).a) k' else 0) = _
        rw [Rf.x_deg]
        split_ifs <;> simp
    rw [hs M₀ κ₀ hv₀.1, hs M₁ κ₁ hv₁.1]
    simp only [Pi.sub_apply] at h1
    rw [h1]
    ring

  have hS : ∀ z' ∈ mcPts (mCoordIdeal y), aeval z' F₀ ≠ 0 → aeval z' F₁ ≠ 0 →
      ‖aeval z' f‖ * (M₁.x t r).h (fun p => z' (v₁ p)) = ‖aeval z' g‖ * (M₀.x t r).h (fun p => z' (v₀ p)) := by
    intro z' hz' h₀ h₁
    obtain ⟨x₀, val₀, ho₀, hn₀, hval₀, hid₀⟩ := hp₀ z' hz' h₀
    obtain ⟨x₁, val₁, ho₁, hn₁, hval₁, hid₁⟩ := hp₁ z' hz' h₁
    have hπ := pi_eq oR ho₀ ho₁
    have hu₀ : ∀ p, (Cmp.joinVec v₀ vR p).1 = Sum.elim κ₀ κR p.1 := by
      rintro ⟨k | k, a⟩
      · exact hv₀.2.2.1 ⟨k, a⟩
      · exact hvR.2.2.1 ⟨k, a⟩
    have hu₁ : ∀ p, (Cmp.joinVec v₁ vR p).1 = Sum.elim κ₁ κR p.1 := by
      rintro ⟨k | k, a⟩
      · exact hv₁.2.2.1 ⟨k, a⟩
      · exact hvR.2.2.1 ⟨k, a⟩
    have hyJ₀ : ∀ p, y (Cmp.joinVec v₀ vR p) = i₀ (Ht.joinOf M₀ Rf a₀ p) := by
      rintro ⟨k | k, a⟩
      · exact hy₀ ⟨k, a⟩
      · exact (hyR ⟨k, a⟩).trans (hi₀ _).symm
    have hyJ₁ : ∀ p, y (Cmp.joinVec v₁ vR p) = i₁ (Ht.joinOf M₁ Rf a₁ p) := by
      rintro ⟨k | k, a⟩
      · exact hy₁ ⟨k, a⟩
      · exact (hyR ⟨k, a⟩).trans (hi₁ _).symm
    have hz2 : ∀ q ∈ mCoordIdeal y, aeval z' q = 0 := fun q hq => by
      have := hz'.2 q hq
      rwa [Small.LineModel.eval_map_eq] at this
    have hrelz := val_rel hu₀ hu₁ i₀ i₁ hyJ₀ hyJ₁ hf' hg' hdegs hrel hz2 (hval₀ r) (hval₁ r)

    obtain ⟨τ, p⟩ := r
    have hD := zero_of_sum_Iic (fun k => (Real.log ((M₀.x t (τ, k)).h fun q => z' (v₀ q)) - Real.log ‖val₀ (τ, k)‖) -
      (Real.log ((M₁.x t (τ, k)).h fun q => z' (v₁ q)) - Real.log ‖val₁ (τ, k)‖)) (fun p' => by
        have h1 := hid₀ t ht0 ht τ p'
        have h2 := hid₁ t ht0 ht τ p'
        rw [hπ, ← h2] at h1
        simp only [Finset.sum_sub_distrib, neg_inj] at h1 ⊢
        linarith) p
    beta_reduce at hD
    have hP₀ := (M₀.x t (τ, p)).pos (fun q => z' (v₀ q)) (block_ne hv₀ hz'.1)
    have hP₁ := (M₁.x t (τ, p)).pos (fun q => z' (v₁ q)) (block_ne hv₁ hz'.1)
    have hN₀ : 0 < ‖val₀ (τ, p)‖ := norm_pos_iff.2 (hn₀ _)
    have hN₁ : 0 < ‖val₁ (τ, p)‖ := norm_pos_iff.2 (hn₁ _)
    have hL : (M₀.x t (τ, p)).h (fun q => z' (v₀ q)) * ‖val₁ (τ, p)‖ =
        (M₁.x t (τ, p)).h (fun q => z' (v₁ q)) * ‖val₀ (τ, p)‖ := by
      apply Real.log_injOn_pos (Set.mem_Ioi.2 (mul_pos hP₀ hN₁)) (Set.mem_Ioi.2 (mul_pos hP₁ hN₀))
      rw [Real.log_mul hP₀.ne' hN₁.ne', Real.log_mul hP₁.ne' hN₀.ne']
      linarith
    have hR := congrArg norm hrelz
    rw [norm_mul, norm_mul] at hR
    apply mul_right_cancel₀ hN₀.ne'
    calc _ = ‖aeval z' f‖ * ((M₁.x t (τ, p)).h (fun q => z' (v₁ q)) * ‖val₀ (τ, p)‖) := by ring
      _ = ‖aeval z' f‖ * ((M₀.x t (τ, p)).h (fun q => z' (v₀ q)) * ‖val₁ (τ, p)‖) := by rw [hL]
      _ = (‖aeval z' f‖ * ‖val₁ (τ, p)‖) * (M₀.x t (τ, p)).h (fun q => z' (v₀ q)) := by ring
      _ = _ := by rw [hR]; ring

  have hFne : F₀ * F₁ ∉ mCoordIdeal y := fun h => by
    have := aeval_zero_of_mem y h
    rw [map_mul] at this
    exact (mul_ne_zero hF₀ hF₁) this
  have hzc := GlobalTheory.T.complex_points_dense_nonvanishing K J (mCoordIdeal y) _ (F₀ * F₁) hA hFne hz
  haveI hnb := mem_closure_iff_nhdsWithin_neBot.1 hzc
  have cont : ∀ {K₁ : Type} [Fintype K₁] {ι : K₁ → Type} [∀ k, Fintype (ι k)] (A : HermLine ι) (_ : IsSmoothHerm A)
      (u : (Σ k, ι k) → Σ k, J k), (∀ k, ∃ a, z (u ⟨k, a⟩) ≠ 0) →
      ContinuousAt (fun w : (Σ k, J k) → ℂ => A.h fun p => w (u p)) z := by
    intro K₁ _ ι _ A hAs u hu
    exact ContinuousAt.comp (g := A.h) (f := fun (w : (Σ k, J k) → ℂ) p => w (u p))
      (GlobalTheory.CompanionTheory.Ar.OrArch.Ext.continuousAt_metric A hAs hu) (continuous_pi fun p => continuous_apply _).continuousAt
  have c₁ : ContinuousAt (fun w : (Σ k, J k) → ℂ =>
      ‖eval w (MvPolynomial.map (Int.castRingHom ℂ) f)‖ * (M₁.x t r).h (fun p => w (v₁ p))) z :=
    ((MvPolynomial.continuous_eval _).norm.continuousAt).mul (cont _ (M₁.x_smooth t r) v₁ (block_ne hv₁ hz.1))
  have c₀ : ContinuousAt (fun w : (Σ k, J k) → ℂ =>
      ‖eval w (MvPolynomial.map (Int.castRingHom ℂ) g)‖ * (M₀.x t r).h (fun p => w (v₀ p))) z :=
    ((MvPolynomial.continuous_eval _).norm.continuousAt).mul (cont _ (M₀.x_smooth t r) v₀ (block_ne hv₀ hz.1))
  refine tendsto_nhds_unique_of_eventuallyEq
    (l := 𝓝[{z | z ∈ mcPts (mCoordIdeal y) ∧ Flat.evC z (F₀ * F₁) ≠ 0}] z) (c₁.tendsto.mono_left nhdsWithin_le_nhds)
    (c₀.tendsto.mono_left nhdsWithin_le_nhds) (eventually_nhdsWithin_of_forall fun w hw => ?_)
  obtain ⟨hw₁, hw₂⟩ := hw
  have hw₂' : aeval w (F₀ * F₁) ≠ 0 := by
    rwa [Flat.evC, Small.LineModel.eval_map_eq] at hw₂
  rw [map_mul] at hw₂'
  beta_reduce
  rw [Small.LineModel.eval_map_eq, Small.LineModel.eval_map_eq]
  exact hS w hw₁ (left_ne_zero_of_mul hw₂') (right_ne_zero_of_mul hw₂')

end GlobalTheory.CompanionTheory.Ar.OrIso
