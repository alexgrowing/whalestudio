import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ThickFrames
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.MatchProd
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SplitLoc

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Global GroundTheory.Global.SemiLocal PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.L1
open scoped ENNReal

namespace UpperTheory.ConvolutionTheory.L1.CosetQuotientIntegrals

section Grp

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

omit [MeasurableSpace G] [BorelSpace G] in
private theorem relIndex_ne (I K : Subgroup G) (hIo : IsOpen (I : Set G)) (hK : IsCompact (K : Set G)) :
    I.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hopen : IsOpen ((I.subgroupOf K : Subgroup K) : Set K) := hIo.preimage continuous_subtype_val
  haveI : Finite (K ⧸ I.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hopen
  rw [Subgroup.relIndex, Subgroup.index_eq_card]
  exact Nat.card_pos.ne'

private theorem vol_sub (I K : Subgroup G) (hIK : I ≤ K) (hIo : IsOpen (I : Set G)) (hK : IsCompact (K : Set G))
    (μ : Measure G) [μ.IsMulLeftInvariant] (h1 : μ (K : Set G) = 1) :
    I.relIndex K ≠ 0 ∧ μ.real (I : Set G) = ((I.relIndex K : ℕ) : ℝ)⁻¹ := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hopen : IsOpen ((I.subgroupOf K : Subgroup K) : Set K) := hIo.preimage continuous_subtype_val
  haveI : Finite (K ⧸ I.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hopen
  letI : Fintype (K ⧸ I.subgroupOf K) := Fintype.ofFinite _
  let r : (K ⧸ I.subgroupOf K) → G := fun q => ((q.out : K) : G)
  let S : (K ⧸ I.subgroupOf K) → Set G := fun q => (fun x => r q * x) '' (I : Set G)
  have hcov : (K : Set G) = ⋃ q, S q := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · intro hx
      refine ⟨QuotientGroup.mk ⟨x, hx⟩, ?_⟩
      have h := QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk ⟨x, hx⟩ : K ⧸ I.subgroupOf K))
      refine ⟨_, Subgroup.mem_subgroupOf.1 h, ?_⟩
      simp [r]
    · rintro ⟨q, y, hy, rfl⟩
      exact K.mul_mem (q.out).2 (hIK hy)
  have hdis : Pairwise (Function.onFun Disjoint S) := by
    intro p q hpq
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
    apply hpq
    rw [← QuotientGroup.out_eq' p, ← QuotientGroup.out_eq' q]
    refine QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 ?_)
    have : ((p.out : K) : G)⁻¹ * ((q.out : K) : G) = a * b⁻¹ := by
      have hab' : r q * b = r p * a := hab
      simp only [r] at hab'
      rw [eq_mul_inv_iff_mul_eq, mul_assoc, hab', inv_mul_cancel_left]
    simpa using this ▸ I.mul_mem ha (I.inv_mem hb)
  have hmeas : ∀ q, MeasurableSet (S q) := fun q => (isOpenMap_mul_left (r q) _ hIo).measurableSet
  have hvol : ∀ q, μ (S q) = μ (I : Set G) := fun q => by
    simp only [S]
    rw [Set.image_mul_left]
    exact measure_preimage_mul μ _ _
  have hsum : (1 : ℝ≥0∞) = (Fintype.card (K ⧸ I.subgroupOf K) : ℝ≥0∞) * μ (I : Set G) := by
    rw [← h1, hcov, measure_iUnion hdis hmeas, tsum_fintype]
    simp [hvol]
  have hreal : (1 : ℝ) = (Fintype.card (K ⧸ I.subgroupOf K) : ℝ) * μ.real (I : Set G) := by
    have := congrArg ENNReal.toReal hsum
    simpa [Measure.real, ENNReal.toReal_mul] using this
  have hidx : I.relIndex K = Fintype.card (K ⧸ I.subgroupOf K) := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  have hne : I.relIndex K ≠ 0 := by
    rw [hidx]; exact Fintype.card_ne_zero
  refine ⟨hne, ?_⟩
  rw [hidx]
  have hc : (Fintype.card (K ⧸ I.subgroupOf K) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp
  linarith

private theorem cv_ind (μ : Measure G) [μ.IsMulLeftInvariant] (I : Subgroup G) (hI : IsOpen (I : Set G)) (A : Set G)
    (hA : ∀ a ∈ A, ∀ u ∈ I, a * u ∈ A) (c : ℂ) (x : G) :
    cv μ (A.indicator 1) (fun g => c * (I : Set G).indicator 1 g) x =
      c * (μ.real (I : Set G) : ℂ) * A.indicator 1 x := by
  unfold cv
  by_cases hx : x ∈ A
  · have e : ∀ y, A.indicator (1 : G → ℂ) y * (c * (I : Set G).indicator 1 (y⁻¹ * x)) =
        c * (I : Set G).indicator (fun _ => (1 : ℂ)) (x⁻¹ * y) := by
      intro y
      by_cases hy : x⁻¹ * y ∈ I
      · have hy' : y⁻¹ * x ∈ I := by simpa using I.inv_mem hy
        have hyA : y ∈ A := by simpa using hA x hx _ hy
        rw [Set.indicator_of_mem hyA, Set.indicator_of_mem (show y⁻¹ * x ∈ (I : Set G) from hy'),
          Set.indicator_of_mem (show x⁻¹ * y ∈ (I : Set G) from hy)]
        simp
      · have hy' : y⁻¹ * x ∉ I := fun h => hy (by simpa using I.inv_mem h)
        rw [Set.indicator_of_notMem (show y⁻¹ * x ∉ (I : Set G) from hy'),
          Set.indicator_of_notMem (show x⁻¹ * y ∉ (I : Set G) from hy)]
        simp
    simp_rw [e]
    rw [integral_const_mul, integral_mul_left_eq_self (fun z => (I : Set G).indicator (fun _ => (1 : ℂ)) z) x⁻¹,
      integral_indicator_const (1 : ℂ) hI.measurableSet, Set.indicator_of_mem hx]
    simp
  · have e : ∀ y, A.indicator (1 : G → ℂ) y * (c * (I : Set G).indicator 1 (y⁻¹ * x)) = 0 := by
      intro y
      by_cases hy : y ∈ A
      · have : y⁻¹ * x ∉ I := fun h => hx (by simpa using hA y hy _ h)
        rw [Set.indicator_of_notMem (show y⁻¹ * x ∉ (I : Set G) from this)]
        simp
      · rw [Set.indicator_of_notMem hy]
        simp
    simp_rw [e]
    simp [Set.indicator_of_notMem hx]

private theorem cvAll_ind (μ : Measure G) [μ.IsMulLeftInvariant] (I : Subgroup G) (hI : IsOpen (I : Set G)) (m : ℕ) :
    ∀ (A : Set G), (∀ a ∈ A, ∀ u ∈ I, a * u ∈ A) → ∀ φ : Fin (m + 1) → G → ℂ, φ 0 = A.indicator 1 →
      (∀ i, i ≠ 0 → φ i = (I : Set G).indicator 1) →
      ∀ x, cvAll μ m φ x = (μ.real (I : Set G) : ℂ) ^ m * A.indicator 1 x := by
  induction m with
  | zero =>
    intro A _ φ h0 _ x
    simp [cvAll, h0]
  | succ m ih =>
    intro A hA φ h0 hi x
    have ht : cvAll μ m (Fin.tail φ) =
        fun g => (μ.real (I : Set G) : ℂ) ^ m * (I : Set G).indicator 1 g := by
      funext g
      refine ih (I : Set G) (fun a ha u hu => I.mul_mem ha hu) _ ?_ ?_ g
      · exact hi _ (Fin.succ_ne_zero _)
      · intro i _
        exact hi _ (Fin.succ_ne_zero _)
    change cv μ (φ 0) (cvAll μ m (Fin.tail φ)) x = _
    rw [ht, h0, cv_ind μ I hI A hA, pow_succ]

end Grp

section Quot

private theorem quotInt_mul {G T X : Type*} [Group G] [MeasurableSpace G] [MeasurableSpace T] [MeasurableSpace X]
    (μ : Measure X) (u : X → G) (j : T → G) (ν : Measure T) (c : ℂ) (Φ : X → ℂ) :
    quotInt μ u j ν (fun x => c * Φ x) = c * quotInt μ u j ν Φ := by
  unfold quotInt
  split_ifs with h
  · simp_rw [mul_assoc]
    exact integral_const_mul _ _
  · simp

private theorem match_of_scale {n : ℕ} {R S : Type*} [CommRing R] [CommRing S] [TopologicalSpace R]
    [MeasurableSpace (GL (Fin n) R)] [MeasurableSpace (GL (Fin n) S)] {ι : R →+* S} {s : S →+* S} {l : ℕ}
    {μS : Measure (GL (Fin n) S)} {μR : Measure (GL (Fin n) R)} {c : ℂ} (hc : c ≠ 0)
    {φ : GL (Fin n) S → ℂ} {f : GL (Fin n) R → ℂ}
    (h : Match ι s l μS μR 1 φ (fun g => c * f g)) : Match ι s l μS μR c φ f := by
  intro γ hγ ν hν
  obtain ⟨h1, h2⟩ := h γ hγ ν hν
  have e : orb μR γ ν (fun g => c * f g) = c * orb μR γ ν f := by
    unfold orb
    exact quotInt_mul _ _ _ _ _ _
  refine ⟨fun δ hδ => ?_, fun hn => ?_⟩
  · rw [h1 δ hδ, e, one_mul]
  · have := h2 hn
    rw [e] at this
    exact (mul_eq_zero.1 this).resolve_left hc

end Quot

section Coset

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private theorem iwCoset_zero (w : Pl K) :
    GM.iwCoset w (0 : Fin n → ℤ) = (GLnLocal.iwahori (w.adicCompletion K) n : Set _) := by
  have h1 : Cartan.diagPow (w.adicCompletion K) n (0 : Fin n → ℤ) = 1 := by
    refine Units.ext ?_
    simp [Cartan.coe_diagPow]
  ext g
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [h1, mul_one]
    exact mul_mem ha hb
  · intro hg
    exact ⟨g, hg, 1, one_mem _, by rw [h1]; simp⟩

private theorem iwCoset_right (w : Pl K) (ν : Fin n → ℤ) :
    ∀ a ∈ GM.iwCoset w ν, ∀ u ∈ GLnLocal.iwahori (w.adicCompletion K) n, a * u ∈ GM.iwCoset w ν := by
  rintro _ ⟨a, ha, b, hb, rfl⟩ u hu
  exact ⟨a, ha, b * u, mul_mem hb hu, by simp [mul_assoc]⟩

open scoped Pointwise in
private theorem iwCoset_test (w : Pl K) (ν : Fin n → ℤ) :
    Continuous ((GM.iwCoset w ν).indicator (1 : GL (Fin n) (w.adicCompletion K) → ℂ)) ∧
      HasCompactSupport ((GM.iwCoset w ν).indicator (1 : GL (Fin n) (w.adicCompletion K) → ℂ)) := by
  have e : GM.iwCoset w ν = (GLnLocal.iwahori (w.adicCompletion K) n : Set _) *
      {Cartan.diagPow (w.adicCompletion K) n ν} * (GLnLocal.iwahori (w.adicCompletion K) n : Set _) := by
    ext g
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact Set.mul_mem_mul (Set.mul_mem_mul ha rfl) hb
    · rintro ⟨_, ⟨a, ha, _, rfl, rfl⟩, b, hb, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩
  have hc : IsCompact (GM.iwCoset w ν) := by
    rw [e]
    exact ((GLnLocal.isCompact_iwahori _ _).mul isCompact_singleton).mul (GLnLocal.isCompact_iwahori _ _)
  have ho : IsOpen (GM.iwCoset w ν) := by
    rw [e]
    exact (GLnLocal.isOpen_iwahori _ _).mul_left
  exact ⟨IsClopen.continuous_indicator ⟨hc.isClosed, ho⟩ continuous_const,
    HasCompactSupport.intro hc fun g hg => Set.indicator_of_notMem hg _⟩

end Coset

end UpperTheory.ConvolutionTheory.L1.CosetQuotientIntegrals

open UpperTheory.ConvolutionTheory.L1.CosetQuotientIntegrals in
open Classical in
theorem UpperTheory.ConvolutionTheory.L1.locQ :
    UpperTheory.ConvolutionTheory.GM.LocQ := by
  intro F E _ _ _ _ _ _ σ hσ hp n hn q hq
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank F E = m + 1 := ⟨Module.finrank F E - 1, by have := hp.pos; omega⟩
  set I := GLnLocal.iwahori (q.adicCompletion F) n with hIdef
  set K := GLnLocal.integralGL (q.adicCompletion F) n with hKdef
  have hIK : I ≤ K := GLnLocal.iwahori_le_integralGL _ _
  have hIo : IsOpen (I : Set (GL (Fin n) (q.adicCompletion F))) := GLnLocal.isOpen_iwahori _ _
  have hKc : IsCompact (K : Set (GL (Fin n) (q.adicCompletion F))) := GLnLocal.isCompact_integralGL _ _
  have hidx : I.relIndex K ≠ 0 := relIndex_ne I K hIo hKc
  have hpos : (0 : ℝ) < (I.relIndex K : ℝ)⁻¹ := by
    have : (0 : ℝ) < (I.relIndex K : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hidx
    positivity
  refine ⟨((I.relIndex K : ℝ)⁻¹) ^ m, pow_pos hpos m, fun w₀ ν => ?_⟩
  obtain ⟨w, hw0, hw⟩ := UpperTheory.ConvolutionTheory.L1.matchProd F E σ hσ m hm n q w₀ hq
  intro _ _ _ _ mE mF hE hF hE1 hF1
  set h : ∀ u : PlacesOver E q, GL (Fin n) (u.1.adicCompletion E) → ℂ :=
    fun u => (GM.iwCoset u.1 (if u = w₀ then ν else 0)).indicator 1 with hh
  have hM := hw h (fun u => iwCoset_test u.1 _) mF hF hF1 mE mF hE hF hE1 hF1
  have hvol := (vol_sub I K hIK hIo hKc mF hF1).2
  have hconv : (cvAll mF m fun i g => h (w i) (mapGL n (completionMap q (w i).1) g)) =
      fun g => (((((I.relIndex K : ℝ)⁻¹) ^ m : ℝ)) : ℂ) * (GM.iwCoset q ν).indicator 1 g := by
    funext g
    have hloc : ∀ (i : Fin (m + 1)) (ν' : Fin n → ℤ) (g : GL (Fin n) (q.adicCompletion F)),
        mapGL n (completionMap q (w i).1) g ∈ GM.iwCoset (w i).1 ν' ↔ g ∈ GM.iwCoset q ν' := fun i ν' g =>
      (UpperTheory.ConvolutionTheory.L1.splitLoc F E q (w i) (hq (w i)) n).2.2.2.1 ν' g
    have hind : ∀ (i : Fin (m + 1)) (ν' : Fin n → ℤ),
        (fun g => (GM.iwCoset (w i).1 ν').indicator (1 : GL (Fin n) ((w i).1.adicCompletion E) → ℂ) (mapGL n (completionMap q (w i).1) g)) =
          (GM.iwCoset q ν').indicator 1 := by
      intro i ν'
      funext g
      by_cases hg : g ∈ GM.iwCoset q ν'
      · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((hloc i ν' g).2 hg)]
        rfl
      · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem (fun h' => hg ((hloc i ν' g).1 h'))]
    rw [cvAll_ind mF I hIo m (GM.iwCoset q ν) (iwCoset_right q ν) _ ?_ ?_ g, hvol]
    · push_cast
      rfl
    · have := hind 0 ν
      simpa [hh, hw0] using this
    · intro i hi
      have hne : w i ≠ w₀ := fun e => hi (w.injective (e.trans hw0.symm))
      have := hind i 0
      rw [iwCoset_zero q] at this
      simpa [hh, hne] using this
  rw [hconv] at hM
  have hcne : (((((I.relIndex K : ℝ)⁻¹) ^ m : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast (pow_pos hpos m).ne'
  exact match_of_scale hcne hM
