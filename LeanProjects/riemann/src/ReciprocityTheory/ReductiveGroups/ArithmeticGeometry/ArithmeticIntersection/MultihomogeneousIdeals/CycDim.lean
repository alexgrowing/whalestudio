import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSuppAC
import Lemmata.GeneralBFactBis.Imports
import Lemmata.FirstBlockLemmaB.Imports

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AI.I1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

section CycBlocks

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]

def cycBlockWt [DecidableEq K] (k : K) : (Σ k, ι k) → ℕ := fun p => if p.1 = k then 1 else 0

theorem weight_cycBlockWt [DecidableEq K] (k : K) (m : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (cycBlockWt (ι := ι) k) m = ∑ i, m ⟨k, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp), Fintype.sum_sigma,
    Finset.sum_eq_single k]
  · simp [cycBlockWt]
  · intro b _ hb
    simp [cycBlockWt, hb]
  · simp

theorem isWeightedHomogeneous_cycBlockWt [DecidableEq K] {s : MRingOver R ι} {a : K → ℕ}
    (h : IsMultiHomog s a) (k : K) : IsWeightedHomogeneous (cycBlockWt (ι := ι) k) s (a k) := by
  intro d hd
  rw [weight_cycBlockWt]
  exact h d (mem_support_iff.mpr hd) k

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem cyc_isHomogeneous_of_isMultiHomogIdeal [DecidableEq K] {P : Ideal (MRingOver R ι)}
    (h : IsMultiHomogIdeal P) (k : K) :
    P.IsHomogeneous (weightedHomogeneousSubmodule R (cycBlockWt (ι := ι) k)) := by
  obtain ⟨S, hS, rfl⟩ := h
  refine Ideal.homogeneous_span _ S fun x hx => ?_
  obtain ⟨a, ha⟩ := hS x hx
  exact ⟨a k, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr
    (isWeightedHomogeneous_cycBlockWt ha k)⟩

theorem cyc_isHomogeneous_of_mem_minimalPrimes {A : Type*} [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedRing 𝒜] {I W : Ideal A} (hI : I.IsHomogeneous 𝒜)
    (hW : W ∈ I.minimalPrimes) : W.IsHomogeneous 𝒜 := by
  have hWp : W.IsPrime := hW.1.1
  have h1 : (W.homogeneousCore 𝒜).toIdeal.IsPrime := hWp.homogeneousCore
  have h2 : I ≤ (W.homogeneousCore 𝒜).toIdeal :=
    hI.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ hW.1.2)
  have h3 := hW.2 ⟨h1, h2⟩ (Ideal.toIdeal_homogeneousCore_le _ _)
  have e : (W.homogeneousCore 𝒜).toIdeal = W :=
    le_antisymm (Ideal.toIdeal_homogeneousCore_le _ _) h3
  exact e ▸ (W.homogeneousCore 𝒜).isHomogeneous

theorem cyc_exists_blockComponent [DecidableEq K] {W : Ideal (MRingOver R ι)}
    (hW : ∀ k, W.IsHomogeneous (weightedHomogeneousSubmodule R (cycBlockWt (ι := ι) k)))
    (a : K → ℕ) (T : Finset K) {f : MRingOver R ι} (hf : f ∈ W) :
    ∃ g ∈ W, ∀ m, coeff m g = if (∀ k ∈ T, ∑ i, m ⟨k, i⟩ = a k) then coeff m f else 0 := by
  induction T using Finset.induction_on with
  | empty => exact ⟨f, hf, fun m => by simp⟩
  | @insert k T hk ih =>
    obtain ⟨g, hgW, hg⟩ := ih
    refine ⟨weightedHomogeneousComponent (cycBlockWt k) (a k) g,
      weightedHomogeneousComponent_mem_of_mem R (cycBlockWt k) (hW k) hgW (a k), fun m => ?_⟩
    rw [coeff_weightedHomogeneousComponent, weight_cycBlockWt, hg]
    by_cases h1 : ∑ i, m ⟨k, i⟩ = a k <;> by_cases h2 : ∀ k' ∈ T, ∑ i, m ⟨k', i⟩ = a k' <;>
      simp [h1, h2]

theorem cyc_isMultiHomogIdeal_of_isHomogeneous [DecidableEq K] {W : Ideal (MRingOver R ι)}
    (hW : ∀ k, W.IsHomogeneous (weightedHomogeneousSubmodule R (cycBlockWt (ι := ι) k))) :
    IsMultiHomogIdeal W := by
  refine ⟨{f | f ∈ W ∧ ∃ a, IsMultiHomog f a}, fun f hf => hf.2, le_antisymm (fun f hf => ?_)
    (Ideal.span_le.mpr fun f hf => hf.1)⟩
  choose g hgW hg using fun a : K → ℕ => cyc_exists_blockComponent hW a Finset.univ hf
  have hsum : f = ∑ a ∈ f.support.image (fun m k => ∑ i, m ⟨k, i⟩), g a := by
    ext m
    rw [coeff_sum]
    have e : ∀ a : K → ℕ,
        coeff m (g a) = if (fun k => ∑ i, m ⟨k, i⟩) = a then coeff m f else 0 := by
      intro a
      rw [hg a]
      by_cases h : (fun k => ∑ i, m ⟨k, i⟩) = a
      · subst h
        simp
      · rw [if_neg h, if_neg]
        intro h'
        exact h (funext fun k => h' k (Finset.mem_univ k))
    simp_rw [e]
    rw [Finset.sum_ite_eq]
    split_ifs with hm
    · rfl
    · by_contra hne
      exact hm (Finset.mem_image_of_mem _ (mem_support_iff.mpr hne))
  rw [hsum]
  refine Ideal.sum_mem _ fun a _ => Ideal.subset_span ⟨hgW a, a, fun m hm k => ?_⟩
  rw [mem_support_iff, hg a] at hm
  by_contra hk
  exact hm (if_neg fun h => hk (h k (Finset.mem_univ k)))

theorem cyc_isMultiHomogIdeal_of_mem_minimalPrimes {P W : Ideal (MRingOver R ι)} {s : MRingOver R ι}
    {a : K → ℕ} (hP : IsMultiHomogIdeal P) (hs : IsMultiHomog s a)
    (hW : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes) : IsMultiHomogIdeal W := by
  classical
  refine cyc_isMultiHomogIdeal_of_isHomogeneous fun k => cyc_isHomogeneous_of_mem_minimalPrimes _
    ((cyc_isHomogeneous_of_isMultiHomogIdeal hP k).sup (Ideal.homogeneous_span _ _ ?_)) hW
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨a k, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr
    (isWeightedHomogeneous_cycBlockWt hs k)⟩

end CycBlocks

section CycDim

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]

theorem cyc_withBot_eq_of_add_one {x : WithBot ℕ∞} {m : ℕ} (h : x + 1 = ((m + 1 : ℕ) : WithBot ℕ∞)) :
    x = (m : WithBot ℕ∞) := by
  first | exact Bl.general_b_fact_bis.goal1 .. | (apply Bl.general_b_fact_bis.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_bis.goal1 <;> assumption)

theorem cyc_dim_quot_minimal_add_one {V W : Ideal (MRingOver F ι)} [hVp : V.IsPrime]
    {f : MRingOver F ι} (hf : f ∉ V) (hW : W ∈ (V ⊔ Ideal.span {f}).minimalPrimes)
    (hfin : ringKrullDim (MRingOver F ι ⧸ V) ≠ ⊤) :
    ringKrullDim (MRingOver F ι ⧸ W) + 1 = ringKrullDim (MRingOver F ι ⧸ V) := by
  have hPW : V ≤ W := le_sup_left.trans hW.1.2
  have hfW : f ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  have hq : W.map (Ideal.Quotient.mk V) ∈ (Ideal.span {Ideal.Quotient.mk V f}).minimalPrimes := by
    have e : Ideal.span {Ideal.Quotient.mk V f} = (Ideal.span {f}).map (Ideal.Quotient.mk V) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [e, Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_comm]
    exact ⟨W, hW, rfl⟩
  have : (W.map (Ideal.Quotient.mk V)).IsPrime := hq.1.1
  have : (Ideal.span {Ideal.Quotient.mk V f}).IsPrincipal := ⟨⟨_, rfl⟩⟩
  have hh : (W.map (Ideal.Quotient.mk V)).height = 1 := by
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hq) ?_
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    intro h0
    have : Ideal.Quotient.mk V f ∈ W.map (Ideal.Quotient.mk V) := Ideal.mem_map_of_mem _ hfW
    rw [h0, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
    exact hf this
  have : IsDomain (MRingOver F ι ⧸ V) := Ideal.Quotient.isDomain V
  have : Algebra.FiniteType F (MRingOver F ι ⧸ V) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F V)
      (Ideal.Quotient.mkₐ_surjective F V)
  have : IsNoetherianRing (MRingOver F ι ⧸ V) := Algebra.FiniteType.isNoetherianRing F _
  have : FiniteRingKrullDim (MRingOver F ι ⧸ V) :=
    finiteRingKrullDim_iff_ne_bot_and_top.mpr ⟨fun h => by
      have h0 := ringKrullDim_nonneg_of_nontrivial (R := MRingOver F ι ⧸ V)
      rw [h] at h0
      exact absurd h0 (by simp), hfin⟩
  obtain ⟨s, hs⟩ := DimF.exists_height_of_isMaximal_of_field F (MRingOver F ι ⧸ V)
  have key := DimF.dim_quot_add_height (A := MRingOver F ι ⧸ V)
    (fun M N hM hN => (hs M hM).trans (hs N hN).symm) (W.map (Ideal.Quotient.mk V))
  rw [hh, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPW)] at key
  exact_mod_cast key

end CycDim

section CycChart

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]

theorem aeval_blockScale {A : Type*} [CommRing A] [Algebra F A] {g : MRingOver F ι} {a : K → ℕ}
    (hg : IsMultiHomog g a) (c : K → A) (z : (Σ k, ι k) → A) :
    aeval (fun p => c p.1 * z p) g = (∏ k, c k ^ a k) * aeval z g := by
  simp only [aeval_def, eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have h1 : ∏ p, (c p.1 * z p) ^ d p = (∏ p, c p.1 ^ d p) * ∏ p, z p ^ d p := by
    rw [← Finset.prod_mul_distrib]
    simp_rw [mul_pow]
  have h2 : ∏ p : (Σ k, ι k), c p.1 ^ d p = ∏ k, c k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ y, c k ^ d ⟨k, y⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hg d hd k]
  rw [h1, h2]
  ring

theorem aeval_blockScale_eq_zero {A : Type*} [CommRing A] [Algebra F A] {V : Ideal (MRingOver F ι)}
    (hV : IsMultiHomogIdeal V) (c : K → A) (θ : MRingOver F ι →ₐ[F] A) (hθ : ∀ g ∈ V, θ g = 0)
    {g : MRingOver F ι} (hg : g ∈ V) : aeval (fun p => c p.1 * θ (X p)) g = 0 := by
  have e : (aeval fun p => θ (X p) : MRingOver F ι →ₐ[F] A) = θ :=
    MvPolynomial.algHom_ext fun p => aeval_X _ _
  obtain ⟨S, hS, rfl⟩ := hV
  have h : Ideal.span S ≤ RingHom.ker (aeval (fun p => c p.1 * θ (X p)) : MRingOver F ι →ₐ[F] A) := by
    refine Ideal.span_le.mpr fun f hfS => ?_
    obtain ⟨a, ha⟩ := hS f hfS
    rw [SetLike.mem_coe, RingHom.mem_ker, aeval_blockScale ha, DFunLike.congr_fun e f,
      hθ f (Ideal.subset_span hfS), mul_zero]
  exact RingHom.mem_ker.mp (h hg)

theorem cyc_dim_add_one_le {R : Type*} [CommRing R] {P Q : Ideal R} [P.IsPrime] (hPQ : P ≤ Q)
    {x : R} (hxQ : x ∈ Q) (hxP : x ∉ P) : ringKrullDim (R ⧸ Q) + 1 ≤ ringKrullDim (R ⧸ P) := by
  first | exact Bl.FirstBlockLemmaB.goal1 .. | (apply Bl.FirstBlockLemmaB.goal1 <;> assumption) | (intros; apply Bl.FirstBlockLemmaB.goal1 <;> assumption)

theorem mk_chartIdeal_X_self (V : Ideal (MRingOver F ι)) (j : ∀ k, ι k) (k : K) :
    Ideal.Quotient.mk (chartIdeal V j) (X ⟨k, j k⟩) = 1 := by
  rw [← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq]
  exact Ideal.mem_sup_right (Ideal.subset_span ⟨k, rfl⟩)

theorem mkₐ_chartIdeal_X_self (V : Ideal (MRingOver F ι)) (j : ∀ k, ι k) (k : K) :
    Ideal.Quotient.mkₐ F (chartIdeal V j) (X ⟨k, j k⟩) = 1 :=
  mk_chartIdeal_X_self V j k

theorem isUnit_mk_chartIdeal_X {V : Ideal (MRingOver F ι)} (hV : IsProjVarF V 0) (j : ∀ k, ι k)
    (p : Σ k, ι k) (hp : (X p : MRingOver F ι) ∉ V) :
    IsUnit (Ideal.Quotient.mk (chartIdeal V j) (X p)) := by
  classical
  by_contra hu
  obtain ⟨M, hM, hpM⟩ := exists_max_ideal_of_mem_nonunits hu
  have hVp : V.IsPrime := hV.1.1
  letI : Field (((MRingOver F ι ⧸ chartIdeal V j) ⧸ M)) := Ideal.Quotient.field M
  let θ : MRingOver F ι →ₐ[F] MvPolynomial K (((MRingOver F ι ⧸ chartIdeal V j) ⧸ M)) :=
    (IsScalarTower.toAlgHom F (((MRingOver F ι ⧸ chartIdeal V j) ⧸ M)) (MvPolynomial K (((MRingOver F ι ⧸ chartIdeal V j) ⧸ M)))).comp
      ((Ideal.Quotient.mkₐ F M).comp (Ideal.Quotient.mkₐ F (chartIdeal V j)))
  have hθ : ∀ g, θ g = MvPolynomial.C (Ideal.Quotient.mk M (Ideal.Quotient.mk (chartIdeal V j) g)) := fun g => rfl
  let c : Finset K → K → MvPolynomial K (((MRingOver F ι ⧸ chartIdeal V j) ⧸ M)) :=
    fun S k => if k ∈ S then 0 else MvPolynomial.X k
  let φ : Finset K → MRingOver F ι →ₐ[F] MvPolynomial K (((MRingOver F ι ⧸ chartIdeal V j) ⧸ M)) :=
    fun S => aeval fun q => c S q.1 * θ (X q)
  have hφX : ∀ S q, φ S (X q) = c S q.1 * θ (X q) := fun S q => aeval_X _ _
  let Q : Finset K → Ideal (MRingOver F ι) := fun S => RingHom.ker (φ S)
  have hQp : ∀ S, (Q S).IsPrime := fun S => RingHom.ker_isPrime (φ S).toRingHom
  have hVQ : ∀ S, V ≤ Q S := fun S g hg => RingHom.mem_ker.mpr
    (aeval_blockScale_eq_zero hV.1.2.1 (c S) θ (fun g hg => by
      rw [hθ, Ideal.Quotient.eq_zero_iff_mem.mpr (show g ∈ chartIdeal V j from Ideal.mem_sup_left hg),
        map_zero, map_zero]) hg)

  have hmono : ∀ S k, Q S ≤ Q (insert k S) := by
    intro S k g hg
    let ρ : MvPolynomial K (((MRingOver F ι ⧸ chartIdeal V j) ⧸ M)) →ₐ[F] MvPolynomial K (((MRingOver F ι ⧸ chartIdeal V j) ⧸ M)) :=
      (aeval fun k' => if k' = k then 0 else MvPolynomial.X k').restrictScalars F
    have e : ρ.comp (φ S) = φ (insert k S) := by
      refine MvPolynomial.algHom_ext fun q => ?_
      rw [AlgHom.comp_apply, hφX, hφX, map_mul]
      congr 1
      · by_cases h1 : q.1 ∈ S
        · simp [ρ, c, h1]
        · by_cases h2 : q.1 = k
          · subst h2
            simp [ρ, c, h1]
          · simp [ρ, c, h1, h2]
      · rw [hθ]
        simp [ρ, MvPolynomial.algebraMap_eq]
    have hg' : φ S g = 0 := RingHom.mem_ker.mp hg
    show φ (insert k S) g = 0
    rw [← e, AlgHom.comp_apply, hg', map_zero]
  have hin : ∀ S k, (X ⟨k, j k⟩ : MRingOver F ι) ∈ Q (insert k S) := by
    intro S k
    show φ (insert k S) (X ⟨k, j k⟩) = 0
    rw [hφX]
    simp [c]
  have hout : ∀ S k, k ∉ S → (X ⟨k, j k⟩ : MRingOver F ι) ∉ Q S := by
    intro S k hk h
    have h' : φ S (X ⟨k, j k⟩) = 0 := RingHom.mem_ker.mp h
    rw [hφX, hθ, mk_chartIdeal_X_self, map_one, map_one, mul_one] at h'
    simp only [c, if_neg hk] at h'
    exact MvPolynomial.X_ne_zero k h'
  have hbase : (X p : MRingOver F ι) ∈ Q ∅ := by
    show φ ∅ (X p) = 0
    rw [hφX, hθ, Ideal.Quotient.eq_zero_iff_mem.mpr hpM, map_zero, mul_zero]
  have chain : ∀ S : Finset K, ((S.card : ℕ) : WithBot ℕ∞) + 1 + ringKrullDim (MRingOver F ι ⧸ Q S) ≤
      ringKrullDim (MRingOver F ι ⧸ V) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have := cyc_dim_add_one_le (hVQ ∅) hbase hp
      rw [Finset.card_empty, Nat.cast_zero, zero_add, add_comm]
      exact this
    | @insert k S hk ih =>
      have : (Q S).IsPrime := hQp S
      have h1 := cyc_dim_add_one_le (hmono S k) (hin S k) (hout S k hk)
      rw [Finset.card_insert_of_notMem hk]
      calc (((S.card + 1 : ℕ)) : WithBot ℕ∞) + 1 + ringKrullDim (MRingOver F ι ⧸ Q (insert k S))
          = (S.card : WithBot ℕ∞) + 1 + (ringKrullDim (MRingOver F ι ⧸ Q (insert k S)) + 1) := by
            push_cast; abel
        _ ≤ (S.card : WithBot ℕ∞) + 1 + ringKrullDim (MRingOver F ι ⧸ Q S) := add_le_add_right h1 _
        _ ≤ _ := ih
  have h := chain Finset.univ
  have : (Q Finset.univ).IsPrime := hQp _
  have : IsDomain (MRingOver F ι ⧸ Q Finset.univ) := Ideal.Quotient.isDomain _
  have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MRingOver F ι ⧸ Q Finset.univ) :=
    ringKrullDim_nonneg_of_nontrivial
  rw [hV.2, Finset.card_univ] at h
  have h2 : (((Fintype.card K + 1 : ℕ)) : WithBot ℕ∞) ≤ ((0 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    calc (((Fintype.card K + 1 : ℕ)) : WithBot ℕ∞) = (Fintype.card K : WithBot ℕ∞) + 1 + 0 := by
          push_cast; simp
      _ ≤ _ := add_le_add_right h0 _
      _ ≤ _ := h
  have h3 : Fintype.card K + 1 ≤ 0 + Fintype.card K := by exact_mod_cast h2
  omega

def chartSwap {V : Ideal (MRingOver F ι)} (hV : IsMultiHomogIdeal V) (i j : ∀ k, ι k)
    (hu : ∀ k, IsUnit (Ideal.Quotient.mkₐ F (chartIdeal V j) (X ⟨k, i k⟩))) :
    (MRingOver F ι ⧸ chartIdeal V i) →ₐ[F] (MRingOver F ι ⧸ chartIdeal V j) :=
  Ideal.Quotient.liftₐ (chartIdeal V i)
    (aeval fun p => ↑(hu p.1).unit⁻¹ * Ideal.Quotient.mkₐ F (chartIdeal V j) (X p)) (by
      intro a ha
      have h : chartIdeal V i ≤ RingHom.ker
          (aeval fun p => ↑(hu p.1).unit⁻¹ * Ideal.Quotient.mkₐ F (chartIdeal V j) (X p) :
            MRingOver F ι →ₐ[F] _) := by
        refine sup_le (fun g hg => RingHom.mem_ker.mpr (aeval_blockScale_eq_zero
          (A := MRingOver F ι ⧸ chartIdeal V j) hV (fun k => ↑(hu k).unit⁻¹)
          (Ideal.Quotient.mkₐ F (chartIdeal V j)) (fun g hg => ?_) hg)) (Ideal.span_le.mpr ?_)
        · rw [Ideal.Quotient.mkₐ_eq_mk]
          exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left hg)
        · rintro _ ⟨k, rfl⟩
          rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_one, aeval_X, IsUnit.val_inv_mul,
            sub_self]
      exact RingHom.mem_ker.mp (h ha))

theorem chartSwap_mkₐ {V : Ideal (MRingOver F ι)} (hV : IsMultiHomogIdeal V) (i j : ∀ k, ι k)
    (hu : ∀ k, IsUnit (Ideal.Quotient.mkₐ F (chartIdeal V j) (X ⟨k, i k⟩))) (p : Σ k, ι k) :
    chartSwap hV i j hu (Ideal.Quotient.mkₐ F (chartIdeal V i) (X p)) =
      ↑(hu p.1).unit⁻¹ * Ideal.Quotient.mkₐ F (chartIdeal V j) (X p) := by
  unfold chartSwap
  exact (Ideal.Quotient.liftₐ_apply _ _ _ _).trans ((Ideal.Quotient.lift_mk _ _ _).trans (aeval_X _ _))

theorem chartSwap_comp {V : Ideal (MRingOver F ι)} (hV : IsMultiHomogIdeal V) (i j : ∀ k, ι k)
    (hu : ∀ k, IsUnit (Ideal.Quotient.mkₐ F (chartIdeal V j) (X ⟨k, i k⟩)))
    (hv : ∀ k, IsUnit (Ideal.Quotient.mkₐ F (chartIdeal V i) (X ⟨k, j k⟩))) :
    (chartSwap hV j i hv).comp (chartSwap hV i j hu) = AlgHom.id F _ := by
  refine Ideal.Quotient.algHom_ext F (MvPolynomial.algHom_ext fun p => ?_)
  simp only [AlgHom.comp_apply, AlgHom.id_apply]
  rw [chartSwap_mkₐ, map_mul, chartSwap_mkₐ]
  have hui : chartSwap hV j i hv (↑(hu p.1).unit) = ↑(hv p.1).unit⁻¹ := by
    rw [(hu p.1).unit_spec, chartSwap_mkₐ, mkₐ_chartIdeal_X_self, mul_one]
  have hinv : chartSwap hV j i hv (↑(hu p.1).unit⁻¹) = ↑(hv p.1).unit := by
    have h1 : chartSwap hV j i hv (↑(hu p.1).unit⁻¹) * chartSwap hV j i hv (↑(hu p.1).unit) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [hui] at h1
    exact Units.mul_inv_eq_one.mp h1
  rw [hinv, Units.mul_inv_cancel_left]

end CycChart

end ReciprocityTheory.ChartRestriction.G.AI.I1
