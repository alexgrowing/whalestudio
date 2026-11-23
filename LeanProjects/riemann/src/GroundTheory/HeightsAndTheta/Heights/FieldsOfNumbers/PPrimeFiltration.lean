import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

namespace PrimeFiltration

section Lex

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]

abbrev lexDecEq (n : ℕ) : DecidableEq (Lex (Fin n → ℕ)) := LinearOrder.toDecidableEq

attribute [local instance 2000] lexDecEq

@[irreducible] def blockIdx (K : Type) [Fintype K] : K ≃ Fin (Fintype.card K) :=
  Fintype.equivFin K

def lexEmb (K : Type) [Fintype K] : (K → ℕ) →+ Lex (Fin (Fintype.card K) → ℕ) where
  toFun b := toLex (fun i => b ((blockIdx K).symm i))
  map_zero' := rfl
  map_add' _ _ := rfl

omit [DecidableEq K] in
theorem ofLex_lexEmb (b : K → ℕ) (i : Fin (Fintype.card K)) :
    ofLex (lexEmb K b) i = b ((blockIdx K).symm i) := rfl

omit [DecidableEq K] in
theorem lexEmb_injective : Function.Injective (lexEmb K) := by
  intro b b' h
  funext k
  have := congrFun (congrArg ofLex h) (blockIdx K k)
  rwa [ofLex_lexEmb, ofLex_lexEmb, Equiv.symm_apply_apply] at this

def lexWeight : (Σ k, ι k) → Lex (Fin (Fintype.card K) → ℕ) :=
  fun v => lexEmb K (blockWeight ι v)

theorem weight_lexWeight (d : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (lexWeight (ι := ι)) d = lexEmb K (Finsupp.weight (blockWeight ι) d) := by
  simp only [Finsupp.weight_apply, map_finsuppSum, map_nsmul, lexWeight]

abbrev lexGrading (ι : K → Type) (F : Type u) [Field F] :
    Lex (Fin (Fintype.card K) → ℕ) → Submodule F (MRing ι F) :=
  weightedHomogeneousSubmodule F (lexWeight (ι := ι))

open Classical in
theorem component_lex (f : MRing ι F) (b : K → ℕ) :
    weightedHomogeneousComponent (lexWeight (ι := ι)) (lexEmb K b) f =
      weightedHomogeneousComponent (blockWeight ι) b f := by
  ext d
  simp only [coeff_weightedHomogeneousComponent, weight_lexWeight, lexEmb_injective.eq_iff]

open Classical in
theorem component_lex_of_ne (f : MRing ι F) (m : Lex (Fin (Fintype.card K) → ℕ))
    (hm : ∀ b, lexEmb K b ≠ m) :
    weightedHomogeneousComponent (lexWeight (ι := ι)) m f = 0 := by
  ext d
  simp [coeff_weightedHomogeneousComponent, weight_lexWeight, hm]

theorem component_lex_mem {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I) {f : MRing ι F}
    (hf : f ∈ I) (m : Lex (Fin (Fintype.card K) → ℕ)) :
    weightedHomogeneousComponent (lexWeight (ι := ι)) m f ∈ I := by
  by_cases h : ∃ b, lexEmb K b = m
  · obtain ⟨b, rfl⟩ := h
    rw [component_lex]
    exact hI f hf b
  · push Not at h
    rw [component_lex_of_ne f m h]
    exact I.zero_mem

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem isHomogeneous_of_multiHomog {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I) :
    I.IsHomogeneous (lexGrading ι F) := by
  classical
  have e : I = Ideal.span
      {g | ∃ f ∈ I, ∃ m, g = weightedHomogeneousComponent (lexWeight (ι := ι)) m f} := by
    apply le_antisymm
    · intro f hf
      rw [← sum_weightedHomogeneousComponent (lexWeight (ι := ι)) f,
        finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
      exact Ideal.sum_mem _ fun m _ => Ideal.subset_span ⟨f, hf, m, rfl⟩
    · rw [Ideal.span_le]
      rintro g ⟨f, hf, m, rfl⟩
      exact component_lex_mem hI hf m
  rw [e]
  refine Ideal.homogeneous_span _ _ fun x hx => ?_
  obtain ⟨f, -, m, rfl⟩ := hx
  exact ⟨m, weightedHomogeneousComponent_isWeightedHomogeneous m f⟩

theorem multiHomog_of_isHomogeneous {I : Ideal (MRing ι F)}
    (h : I.IsHomogeneous (lexGrading ι F)) : IsMultiHomogIdeal I := by
  classical
  intro f hf b
  rw [← component_lex]
  exact weightedHomogeneousComponent_mem_of_mem (h := h) (hp := hf) (m := lexEmb K b)

theorem mem_lexGrading {s : MRing ι F} {c : K → ℕ} (hs : IsMultiHomog s c) :
    s ∈ lexGrading ι F (lexEmb K c) := by
  rw [mem_weightedHomogeneousSubmodule]
  intro d hd
  rw [weight_lexWeight, hs hd]

theorem exists_multiHomog_of_mem {s : MRing ι F} {m : Lex (Fin (Fintype.card K) → ℕ)}
    (hs : s ∈ lexGrading ι F m) (h0 : s ≠ 0) : ∃ c : K → ℕ, IsMultiHomog s c := by
  rw [mem_weightedHomogeneousSubmodule] at hs
  obtain ⟨d, hd⟩ := MvPolynomial.ne_zero_iff.mp h0
  refine ⟨Finsupp.weight (blockWeight ι) d, fun {d'} hd' => ?_⟩
  apply lexEmb_injective
  rw [← weight_lexWeight, ← weight_lexWeight, hs hd', hs hd]

theorem component_mul_form {c : K → ℕ} {s : MRing ι F} (hs : IsMultiHomog s c)
    (t : MRing ι F) (b : K → ℕ) :
    weightedHomogeneousComponent (blockWeight ι) (b + c) (t * s) =
      weightedHomogeneousComponent (blockWeight ι) b t * s := by
  have hs' : s ∈ weightedHomogeneousSubmodule F (blockWeight ι) c :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mpr hs
  have := DirectSum.coe_decompose_mul_add_of_right_mem
    (𝒜 := weightedHomogeneousSubmodule F (blockWeight ι)) (i := b) (a := t) hs'
  rw [← weightedDecomposition.decompose'_apply, ← weightedDecomposition.decompose'_apply]
  exact this

omit [Fintype K] [DecidableEq K] in
theorem mem_colon_iff {J : Ideal (MRing ι F)} {s f : MRing ι F} :
    f ∈ J.colon (Ideal.span {s}) ↔ f * s ∈ J := by
  rw [Submodule.mem_colon_span_singleton, smul_eq_mul]

theorem multiHomog_colon {J : Ideal (MRing ι F)} (hJ : IsMultiHomogIdeal J) {s : MRing ι F}
    {c : K → ℕ} (hs : IsMultiHomog s c) : IsMultiHomogIdeal (J.colon (Ideal.span {s})) := by
  intro f hf b
  rw [mem_colon_iff] at hf ⊢
  rw [← component_mul_form hs]
  exact hJ _ hf _

theorem exists_colon_isPrime [∀ k, Fintype (ι k)] {J : Ideal (MRing ι F)}
    (hJ : IsMultiHomogIdeal J) (hJt : J ≠ ⊤) :
    ∃ (c : K → ℕ) (s : MRing ι F), IsMultiHomog s c ∧ s ∉ J ∧
      (J.colon (Ideal.span {s})).IsPrime ∧ IsMultiHomogIdeal (J.colon (Ideal.span {s})) := by
  let 𝒮 : Set (Ideal (MRing ι F)) :=
    {P | ∃ s, (∃ i, s ∈ lexGrading ι F i) ∧ s ∉ J ∧ P = J.colon (Ideal.span {s})}
  have hne : 𝒮.Nonempty :=
    ⟨_, 1, ⟨0, SetLike.GradedOne.one_mem⟩, (Ideal.ne_top_iff_one J).mp hJt, rfl⟩
  have hnoeth : IsNoetherian (MRing ι F) (MRing ι F) := inferInstance
  obtain ⟨P, hP, hmax⟩ := set_has_maximal_iff_noetherian.mpr hnoeth 𝒮 hne
  obtain ⟨s, ⟨i, hsi⟩, hsJ, hPs⟩ := hP
  subst hPs
  have hs0 : s ≠ 0 := fun h => hsJ (h ▸ J.zero_mem)
  obtain ⟨c, hc⟩ := exists_multiHomog_of_mem hsi hs0
  have hmh := multiHomog_colon hJ hc
  have hcolon := isHomogeneous_of_multiHomog hmh
  have hprime : (J.colon (Ideal.span {s})).IsPrime := by
    refine hcolon.isPrime_of_homogeneous_mem_or_mem ?_ ?_
    · rw [Ne, Ideal.eq_top_iff_one, mem_colon_iff, one_mul]
      exact hsJ
    · intro x y hx _ hxy
      by_cases hxP : x ∈ J.colon (Ideal.span {s})
      · exact Or.inl hxP
      right
      obtain ⟨i', hxi⟩ := hx
      have hxs : x * s ∉ J := fun h => hxP (mem_colon_iff.mpr h)
      have hle : J.colon (Ideal.span {s}) ≤ J.colon (Ideal.span {x * s}) := by
        intro f hf
        rw [mem_colon_iff] at hf ⊢
        rw [show f * (x * s) = x * (f * s) by ring]
        exact J.mul_mem_left x hf
      have heq : J.colon (Ideal.span {s}) = J.colon (Ideal.span {x * s}) := by
        by_contra hne'
        exact hmax _ ⟨x * s, ⟨i' + i, SetLike.mul_mem_graded hxi hsi⟩, hxs, rfl⟩
          (lt_of_le_of_ne hle hne')
      rw [heq, mem_colon_iff, show y * (x * s) = x * y * s by ring]
      exact mem_colon_iff.mp hxy
  exact ⟨c, s, hc, hsJ, hprime, hmh⟩

theorem multiHomog_sup_span {J : Ideal (MRing ι F)} (hJ : IsMultiHomogIdeal J) {s : MRing ι F}
    {c : K → ℕ} (hs : IsMultiHomog s c) : IsMultiHomogIdeal (J ⊔ Ideal.span {s}) := by
  refine multiHomog_of_isHomogeneous ((isHomogeneous_of_multiHomog hJ).sup ?_)
  refine Ideal.homogeneous_span _ _ ?_
  rintro x rfl
  exact ⟨_, mem_lexGrading hs⟩

end Lex

section Length

variable {K : Type} {ι : K → Type} {F : Type u} [Field F]

theorem smul_quot_mk (I : Ideal (MRing ι F)) (r x : MRing ι F) :
    r • Ideal.Quotient.mk I x = Ideal.Quotient.mk I (r * x) := by
  exact (Submodule.Quotient.mk_smul I r x).symm

theorem multAt_eq_zero {A W : Ideal (MRing ι F)} [W.IsPrime] (h : ¬ A ≤ W) : multAt A W = 0 := by
  obtain ⟨q, hqA, hqW⟩ := Set.not_subset.mp h
  have hz : ∀ z : LocalizedModule W.primeCompl (MRing ι F ⧸ A), z = 0 := by
    intro z
    induction z using LocalizedModule.induction_on with
    | h m t =>
      obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m
      rw [← LocalizedModule.zero_mk t, LocalizedModule.mk_eq]
      refine ⟨⟨q, Ideal.mem_primeCompl_iff.mpr hqW⟩, ?_⟩
      rw [smul_zero, smul_zero, Submonoid.smul_def, Submonoid.smul_def, smul_smul,
        smul_quot_mk, Ideal.Quotient.eq_zero_iff_mem]
      exact A.mul_mem_right _ (A.mul_mem_right _ hqA)
  have : Subsingleton (LocalizedModule W.primeCompl (MRing ι F ⧸ A)) :=
    ⟨fun x y => by rw [hz x, hz y]⟩
  exact Module.length_eq_zero

theorem multAt_self (W : Ideal (MRing ι F)) [hW : W.IsPrime] : multAt W W = 1 := by
  unfold multAt
  have hφ : ∀ x : Localization.AtPrime W,
      LinearMap.toSpanSingleton (Localization.AtPrime W)
        (LocalizedModule W.primeCompl (MRing ι F ⧸ W))
        (LocalizedModule.mk 1 1) x = x • LocalizedModule.mk 1 1 := fun x => rfl
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton (Localization.AtPrime W)
      (LocalizedModule W.primeCompl (MRing ι F ⧸ W)) (LocalizedModule.mk 1 1)) := by
    intro z
    induction z using LocalizedModule.induction_on with
    | h m t =>
      obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m
      refine ⟨Localization.mk m t, ?_⟩
      rw [hφ, LocalizedModule.mk_smul_mk, mul_one, ← map_one (Ideal.Quotient.mk W),
        smul_quot_mk, mul_one]
  have hle : IsLocalRing.maximalIdeal (Localization.AtPrime W) ≤ LinearMap.ker
      (LinearMap.toSpanSingleton (Localization.AtPrime W)
        (LocalizedModule W.primeCompl (MRing ι F ⧸ W)) (LocalizedModule.mk 1 1)) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
    intro w hw
    rw [Ideal.mem_comap, LinearMap.mem_ker, hφ, algebraMap_smul, LocalizedModule.smul'_mk,
      ← map_one (Ideal.Quotient.mk W), smul_quot_mk, mul_one,
      (Ideal.Quotient.eq_zero_iff_mem).mpr hw, LocalizedModule.zero_mk]
  have hne : LinearMap.ker (LinearMap.toSpanSingleton (Localization.AtPrime W)
      (LocalizedModule W.primeCompl (MRing ι F ⧸ W)) (LocalizedModule.mk 1 1)) ≠ ⊤ := by
    intro h
    have h1 := (LinearMap.mem_ker).mp (h ▸ Submodule.mem_top : (1 : Localization.AtPrime W) ∈ _)
    rw [hφ, one_smul, ← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq] at h1
    obtain ⟨u, hu⟩ := h1
    rw [smul_zero, smul_zero, Submonoid.smul_def, Submonoid.smul_def, Submonoid.coe_one,
      one_smul, ← map_one (Ideal.Quotient.mk W), smul_quot_mk, mul_one,
      Ideal.Quotient.eq_zero_iff_mem] at hu
    exact u.2 hu
  have hker := ((IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime W)).eq_of_le hne hle).symm
  rw [← (LinearMap.quotKerEquivOfSurjective _ hsurj).length_eq]
  have : IsSimpleModule (Localization.AtPrime W) (Localization.AtPrime W ⧸ LinearMap.ker
      (LinearMap.toSpanSingleton (Localization.AtPrime W)
        (LocalizedModule W.primeCompl (MRing ι F ⧸ W)) (LocalizedModule.mk 1 1))) := by
    rw [isSimpleModule_iff_isCoatom, hker]
    exact Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal _)
  exact Module.length_eq_one _ _

theorem multAt_colon_add (J W : Ideal (MRing ι F)) [W.IsPrime] (s : MRing ι F) :
    multAt J W = multAt (J.colon (Ideal.span {s})) W + multAt (J ⊔ Ideal.span {s}) W := by
  let f : (MRing ι F ⧸ J.colon (Ideal.span {s})) →ₗ[MRing ι F] (MRing ι F ⧸ J) :=
    Submodule.liftQ _ (J.mkQ ∘ₗ LinearMap.mulRight (MRing ι F) s) (by
      intro x hx
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero, LinearMap.mulRight_apply]
      exact (PrimeFiltration.mem_colon_iff).mp hx)
  let g : (MRing ι F ⧸ J) →ₗ[MRing ι F] (MRing ι F ⧸ (J ⊔ Ideal.span {s})) :=
    Submodule.factor le_sup_left
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    refine Submodule.ker_liftQ_eq_bot _ _ _ ?_
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, LinearMap.mulRight_apply] at hx
    exact (PrimeFiltration.mem_colon_iff).mpr hx
  have hg : Function.Surjective g := Submodule.factor_surjective _
  have hex : Function.Exact f g := by
    intro y
    induction y using Submodule.Quotient.induction_on with
    | H y =>
    constructor
    · intro hy
      have hy' : y ∈ J ⊔ Ideal.span {s} := by
        have := hy
        simp only [g] at this
        rwa [← Submodule.mkQ_apply, Submodule.factor_mk, Submodule.mkQ_apply,
          Submodule.Quotient.mk_eq_zero] at this
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy'
      obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hb
      refine ⟨Submodule.Quotient.mk t, ?_⟩
      simp only [f, Submodule.liftQ_apply, LinearMap.comp_apply, LinearMap.mulRight_apply,
        Submodule.mkQ_apply]
      rw [Submodule.Quotient.eq]
      simpa using J.neg_mem ha
    · rintro ⟨x, hx⟩
      rw [← hx]
      induction x using Submodule.Quotient.induction_on with
      | H t =>
      simp only [f, g, Submodule.liftQ_apply, LinearMap.comp_apply, LinearMap.mulRight_apply]
      rw [Submodule.factor_mk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨t, rfl⟩)
  let p := W.primeCompl
  let R' := Localization.AtPrime W
  let fL := (IsLocalizedModule.map p (LocalizedModule.mkLinearMap p _)
    (LocalizedModule.mkLinearMap p _) f).extendScalarsOfIsLocalization p R'
  let gL := (IsLocalizedModule.map p (LocalizedModule.mkLinearMap p _)
    (LocalizedModule.mkLinearMap p _) g).extendScalarsOfIsLocalization p R'
  exact Module.length_eq_add_of_exact fL gL
    (IsLocalizedModule.map_injective p _ _ f hf) (IsLocalizedModule.map_surjective p _ _ g hg)
    (LocalizedModule.map_exact p f g hex)

end Length

section Dim

theorem ringKrullDim_mvPolynomial_le (F : Type u) [Field F] (σ : Type) [Finite σ] :
    ringKrullDim (MvPolynomial σ F) ≤ Nat.card σ := by
  induction σ using Finite.induction_empty_option with
  | of_equiv e H =>
    rw [← ringKrullDim_eq_of_ringEquiv (renameEquiv F e).toRingEquiv, ← Nat.card_congr e]
    exact H
  | h_empty =>
    simp [ringKrullDim_eq_zero_of_field]
  | h_option IH =>
    rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.optionEquivLeft F _).toRingEquiv,
      Polynomial.ringKrullDim_of_isNoetherianRing, Finite.card_option, Nat.cast_add, Nat.cast_one]
    exact add_le_add IH le_rfl

theorem ringKrullDim_quotient_prime {R : Type*} [CommRing R] (Q : Ideal R) [hQ : Q.IsPrime] :
    ringKrullDim (R ⧸ Q) = (Order.coheight (⟨Q, hQ⟩ : PrimeSpectrum R) : WithBot ℕ∞) := by
  have hset : PrimeSpectrum.zeroLocus (Q : Set R) = Set.Ici ⟨Q, hQ⟩ := by
    ext x
    rw [PrimeSpectrum.mem_zeroLocus, Set.mem_Ici, ← PrimeSpectrum.asIdeal_le_asIdeal]
    exact SetLike.coe_subset_coe
  rw [ringKrullDim_quotient, hset, Order.coheight_eq_krullDim_Ici]

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {F : Type u} [Field F]

omit [DecidableEq K] in

theorem relDim_cases {I Q : Ideal (MRing ι F)} [hQ : Q.IsPrime] (hIQ : I ≤ Q) :
    relDim Q < relDim I ∨ (Q ∈ I.minimalPrimes ∧ relDim Q = relDim I) := by
  have hmono : StrictMono (fun x : WithBot ℕ∞ =>
      WithBot.map (fun d : ℕ∞ => WithTop.map (fun e : ℕ => (e : ℤ) - Fintype.card K) d) x) :=
    WithBot.strictMono_map_iff.2 (WithTop.strictMono_map_iff.2 (fun a b h =>
      Int.sub_lt_sub_right (by exact_mod_cast h) _))
  have hle : ringKrullDim (MRing ι F ⧸ Q) ≤ ringKrullDim (MRing ι F ⧸ I) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hIQ) (Ideal.Quotient.factor_surjective hIQ)
  by_cases hmin : Q ∈ I.minimalPrimes
  · rcases hle.lt_or_eq with h | h
    · exact Or.inl (hmono h)
    · exact Or.inr ⟨hmin, by simp only [relDim, h]⟩
  · left
    apply hmono
    obtain ⟨W', hW', hW'Q⟩ := Ideal.exists_minimalPrimes_le hIQ
    have hW'p : W'.IsPrime := hW'.1.1
    have hlt : (⟨W', hW'p⟩ : PrimeSpectrum (MRing ι F)) < ⟨Q, hQ⟩ :=
      lt_of_le_of_ne hW'Q (fun h => hmin (by
        have : W' = Q := congrArg PrimeSpectrum.asIdeal h
        exact this ▸ hW'))
    have h1 := Order.coheight_add_one_le hlt
    have h2 : ringKrullDim (MRing ι F ⧸ W') ≤ ringKrullDim (MRing ι F ⧸ I) :=
      ringKrullDim_le_of_surjective (Ideal.Quotient.factor hW'.1.2)
        (Ideal.Quotient.factor_surjective hW'.1.2)
    have h3 : ringKrullDim (MRing ι F ⧸ W') ≤ Nat.card (Σ k, ι k) :=
      (ringKrullDim_quotient_le W').trans (ringKrullDim_mvPolynomial_le F _)
    rw [ringKrullDim_quotient_prime W'] at h2 h3
    rw [ringKrullDim_quotient_prime Q]
    have h3' : Order.coheight (⟨W', hW'p⟩ : PrimeSpectrum (MRing ι F)) ≤
        (Nat.card (Σ k, ι k) : ℕ∞) := by
      exact_mod_cast h3
    have hfin : Order.coheight (⟨Q, hQ⟩ : PrimeSpectrum (MRing ι F)) ≠ ⊤ := by
      intro htop
      rw [htop, top_add] at h1
      exact absurd (h1.trans h3') (not_le.mpr (ENat.natCast_lt_top _))
    have h4 := (ENat.add_one_le_iff hfin).1 h1
    exact lt_of_lt_of_le (by exact_mod_cast h4) h2

end Dim

section Main

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {F : Type u} [Field F]

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem hilbFn_top (m : K → ℤ) : hilbFn (⊤ : Ideal (MRing ι F)) m = 0 := by
  have : Subsingleton (MRing ι F ⧸ (⊤ : Ideal (MRing ι F))) :=
    Ideal.Quotient.subsingleton_iff.mpr rfl
  unfold hilbFn
  split_ifs
  · simp [Module.finrank_zero_of_subsingleton]
  · rfl

open Classical in

theorem filtration (h1 : HilbExactDivide.Statement.{u}) (J : Ideal (MRing ι F))
    (hJ : IsMultiHomogIdeal J) :
    ∃ (r : ℕ) (Q : Fin r → Ideal (MRing ι F)) (c : Fin r → K → ℕ),
      (∀ j, (Q j).IsPrime ∧ IsMultiHomogIdeal (Q j) ∧ J ≤ Q j) ∧
      (∀ m, hilbFn J m = ∑ j, hilbFn (Q j) (m - fun k => (c j k : ℤ))) ∧
      (∀ W (hW : W ∈ J.minimalPrimes),
        haveI : W.IsPrime := hW.1.1
        (((∑ j, if Q j = W then 1 else 0 : ℕ)) : ℕ∞) = multAt J W) := by
  induction J using IsNoetherian.induction with
  | hgt J IH =>
  by_cases hJt : J = ⊤
  · subst hJt
    refine ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun m => ?_, fun W hW => ?_⟩
    · simp [hilbFn_top]
    · exact absurd (top_le_iff.mp hW.1.2) hW.1.1.ne_top
  obtain ⟨c, s, hs, hsJ, hQp, hQh⟩ := exists_colon_isPrime hJ hJt
  have hJQ : J ≤ J.colon (Ideal.span {s}) := fun x hx =>
    mem_colon_iff.mpr (Ideal.mul_mem_right s J hx)
  have hgt : J < J ⊔ Ideal.span {s} :=
    lt_of_le_of_ne le_sup_left (fun h => hsJ (h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self s)))
  obtain ⟨r, Q', c', hQ', hh', hcount'⟩ := IH _ hgt (multiHomog_sup_span hJ hs)
  refine ⟨r + 1, Fin.cons (J.colon (Ideal.span {s})) Q', Fin.cons c c', ?_, ?_, ?_⟩
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [Fin.cons_zero]
      exact ⟨hQp, hQh, hJQ⟩
    · simp only [Fin.cons_succ]
      exact ⟨(hQ' j).1, (hQ' j).2.1, le_sup_left.trans (hQ' j).2.2⟩
  · intro m
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← hh' m]
    have := h1 F K ι J hJ c s hs m
    linarith
  · intro W hW
    have : W.IsPrime := hW.1.1
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [multAt_colon_add J W s, Nat.cast_add]
    congr 1
    · by_cases hle : J.colon (Ideal.span {s}) ≤ W
      · have heq : J.colon (Ideal.span {s}) = W := le_antisymm hle (hW.2 ⟨hQp, hJQ⟩ hle)
        rw [if_pos heq]
        simp only [heq]
        rw [multAt_self]
        rfl
      · rw [if_neg (fun h => hle h.le), multAt_eq_zero hle]
        rfl
    · by_cases hJ'W : J ⊔ Ideal.span {s} ≤ W
      · have hW' : W ∈ Ideal.minimalPrimes (J ⊔ Ideal.span {s}) :=
          ⟨⟨hW.1.1, hJ'W⟩, fun q hq hqW => hW.2 ⟨hq.1, le_sup_left.trans hq.2⟩ hqW⟩
        exact hcount' W hW'
      · rw [multAt_eq_zero hJ'W]
        have : ∀ j, Q' j ≠ W := fun j h => hJ'W (h ▸ (hQ' j).2.2)
        simp [this]

end Main

theorem proof (h1 : HilbExactDivide.Statement.{u}) : PrimeFiltration.Statement.{u} := by
  intro F _ K _ _ ι _ I hI
  obtain ⟨r, Q, c, hQ, hhilb, hcount⟩ := filtration h1 I hI
  refine ⟨r, Q, c, hQ, Filter.Eventually.of_forall hhilb, ?_, ?_⟩
  · intro W hW _ _
    rw [← hcount W hW, Finset.card_filter]
  · intro j
    have := (hQ j).1
    rcases relDim_cases (hQ j).2.2 with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

end PrimeFiltration

end

end GroundTheory.Heights₂.Heights.FieldNumbers
