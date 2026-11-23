import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.SwapLoc
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ExistsUnique
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

namespace ExistsUniqueRelabel

section RingEquiv

variable {R R' : Type*} [CommRing R] [CommRing R'] (φ : R ≃+* R')

theorem mem_map_iff (I : Ideal R) (x : R) : φ x ∈ I.map (φ : R →+* R') ↔ x ∈ I := by
  rw [Ideal.map_comap_of_equiv, Ideal.mem_comap, RingEquiv.symm_apply_apply]

theorem map_mem_minimalPrimes {J W : Ideal R} (h : W ∈ J.minimalPrimes) :
    W.map (φ : R →+* R') ∈ (J.map (φ : R →+* R')).minimalPrimes := by
  rw [Ideal.map_comap_of_equiv, Ideal.map_comap_of_equiv]
  exact Ideal.minimalPrimes_comap_of_surjective (f := (φ.symm : R' →+* R)) φ.symm.surjective h

theorem map_mem_minimalPrimes_iff {J W : Ideal R} :
    W.map (φ : R →+* R') ∈ (J.map (φ : R →+* R')).minimalPrimes ↔ W ∈ J.minimalPrimes := by
  refine ⟨fun h => ?_, map_mem_minimalPrimes φ⟩
  have := map_mem_minimalPrimes φ.symm h
  rwa [Ideal.map_of_equiv, Ideal.map_of_equiv] at this

theorem isPrime_map (W : Ideal R) [W.IsPrime] : (W.map (φ : R →+* R')).IsPrime := by
  rw [Ideal.map_comap_of_equiv]
  exact Ideal.comap_isPrime _ _

theorem ringKrullDim_quot_map (V : Ideal R) :
    ringKrullDim (R' ⧸ V.map (φ : R →+* R')) = ringKrullDim (R ⧸ V) :=
  (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv V _ φ rfl)).symm

theorem length_map (V W : Ideal R) [W.IsPrime] [(W.map (φ : R →+* R')).IsPrime] (hVW : V ≤ W)
    (x : R) :
    Module.length (Localization.AtPrime (W.map (φ : R →+* R')))
        (LocalizedModule (W.map (φ : R →+* R')).primeCompl
          (R' ⧸ (V.map (φ : R →+* R') ⊔ Ideal.span {φ x}))) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ (V ⊔ Ideal.span {x}))) := by
  set V' := V.map (φ : R →+* R')
  set W' := W.map (φ : R →+* R')
  have hVW' : V' ≤ W' := Ideal.map_mono hVW
  have : (W'.map (Ideal.Quotient.mk V')).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hVW')
  have h' := ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.isLocData_atPrime_quot V' W' hVW'
  letI : Algebra R (Localization.AtPrime (W'.map (Ideal.Quotient.mk V'))) :=
    ((algebraMap R' (Localization.AtPrime (W'.map (Ideal.Quotient.mk V')))).comp
      (φ : R →+* R')).toAlgebra
  have hal : ∀ r, algebraMap R (Localization.AtPrime (W'.map (Ideal.Quotient.mk V'))) r =
      algebraMap R' (Localization.AtPrime (W'.map (Ideal.Quotient.mk V'))) (φ r) := fun r => rfl
  have hS : ∀ s : R', s ∈ W'.primeCompl → φ.symm s ∈ W.primeCompl := by
    intro s hs h
    apply hs
    rw [← φ.apply_symm_apply s]
    exact (mem_map_iff φ W _).2 h
  have h : ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.IsLocData R
      (Localization.AtPrime (W'.map (Ideal.Quotient.mk V'))) W.primeCompl V := by
    refine ⟨fun s hs => ?_, fun y => ?_, fun r hr => ?_, fun v hv => ?_⟩
    · rw [hal]
      exact h'.1 _ (fun h => hs ((mem_map_iff φ W s).1 h))
    · obtain ⟨r, s, hs, e⟩ := h'.2.1 y
      refine ⟨φ.symm r, φ.symm s, hS s hs, ?_⟩
      rw [hal, hal, φ.apply_symm_apply, φ.apply_symm_apply]
      exact e
    · rw [hal] at hr
      obtain ⟨s, hs, e⟩ := h'.2.2.1 _ hr
      refine ⟨φ.symm s, hS s hs, ?_⟩
      rw [← mem_map_iff φ V, map_mul, φ.apply_symm_apply]
      exact e
    · rw [hal]
      exact h'.2.2.2 _ ((mem_map_iff φ V v).2 hv)
  exact (h'.length_eq (φ x)).trans (h.length_eq x).symm

end RingEquiv

section MRing

variable {F : Type*} [Field F] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]

theorem multAt_map (φ : MRingOver F ι ≃+* MRingOver F ι') (V W : Ideal (MRingOver F ι))
    [hW : W.IsPrime] (hVW : V ≤ W) (f : MRingOver F ι) :
    multAt (V.map (φ : MRingOver F ι →+* MRingOver F ι') ⊔ Ideal.span {φ f})
        (W.map (φ : MRingOver F ι →+* MRingOver F ι')) =
      multAt (V ⊔ Ideal.span {f}) W := by
  have hW' : (W.map (φ : MRingOver F ι →+* MRingOver F ι')).IsPrime := isPrime_map φ W
  rw [multAt, multAt, dif_pos hW, dif_pos hW']
  exact congrArg ENat.toNat (length_map φ V W hVW f)

theorem isRelevant_iff (W : Ideal (MRingOver F ι)) :
    IsRelevant W ↔ ∀ k, ∃ p : Σ k, ι k, p.1 = k ∧ (X p : MRingOver F ι) ∉ W := by
  refine ⟨fun h k => ?_, fun h k => ?_⟩
  · obtain ⟨i, hi⟩ := h k
    exact ⟨⟨k, i⟩, rfl, hi⟩
  · obtain ⟨⟨a, b⟩, rfl, hp⟩ := h k
    exact ⟨b, hp⟩

theorem sum_fiber {M : Type*} [AddCommMonoid M] [DecidableEq K] (g : (Σ k, ι k) → M) (k : K) :
    ∑ i, g ⟨k, i⟩ = ∑ p : Σ k, ι k, if p.1 = k then g p else 0 := by
  rw [Fintype.sum_sigma, Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

variable (e : K ≃ K') (σ : (Σ k, ι k) ≃ (Σ k', ι' k')) (hσ : ∀ p, (σ p).1 = e p.1)

abbrev ren : MRingOver F ι ≃+* MRingOver F ι' := (renameEquiv F σ).toRingEquiv

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem ren_apply (f : MRingOver F ι) : ren σ f = rename σ f := rfl

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem ren_X (p : Σ k, ι k) : ren (F := F) σ (X p) = X (σ p) := by
  rw [ren_apply, rename_X]

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem map_ren_symm_map (V : Ideal (MRingOver F ι)) :
    (V.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι')).map
      (ren (F := F) σ.symm : MRingOver F ι' →+* MRingOver F ι) = V := by
  rw [Ideal.map_map]
  convert Ideal.map_id V
  refine RingHom.ext fun p => ?_
  simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom, ren_apply, rename_rename,
    Equiv.symm_comp_self, rename_id, AlgHom.id_apply, RingHom.id_apply]

include hσ

theorem isMultiHomog_ren {f : MRingOver F ι} {a : K → ℕ} (h : IsMultiHomog f a) :
    IsMultiHomog (ren σ f) (a ∘ e.symm) := by
  classical
  intro m hm k'
  rw [ren_apply, support_rename_of_injective σ.injective, Finset.mem_image] at hm
  obtain ⟨m₀, hm₀, rfl⟩ := hm
  rw [sum_fiber, Function.comp_apply, ← h m₀ hm₀ (e.symm k'), sum_fiber]
  refine (Equiv.sum_comp σ _).symm.trans (Finset.sum_congr rfl fun p _ => ?_)
  rw [Finsupp.mapDomain_equiv_apply, Equiv.symm_apply_apply, hσ, Equiv.apply_eq_iff_eq_symm_apply]

theorem isMultiHomogIdeal_map {V : Ideal (MRingOver F ι)} (h : IsMultiHomogIdeal V) :
    IsMultiHomogIdeal (V.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι')) := by
  obtain ⟨S, hS, rfl⟩ := h
  refine ⟨(ren (F := F) σ : MRingOver F ι →+* MRingOver F ι') '' S, ?_, Ideal.map_span _ _⟩
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨a, ha⟩ := hS f hf
  exact ⟨a ∘ e.symm, isMultiHomog_ren e σ hσ ha⟩

theorem isRelevant_map_iff (W : Ideal (MRingOver F ι)) :
    IsRelevant (W.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι')) ↔ IsRelevant W := by
  have hX : ∀ q : Σ k', ι' k', (X q : MRingOver F ι') = ren σ (X (σ.symm q)) := fun q => by
    rw [ren_X, Equiv.apply_symm_apply]
  rw [isRelevant_iff, isRelevant_iff]
  constructor
  · intro h k
    obtain ⟨q, hq, hX'⟩ := h (e k)
    refine ⟨σ.symm q, e.injective ?_, ?_⟩
    · rw [← hσ, Equiv.apply_symm_apply, hq]
    · rwa [hX, mem_map_iff] at hX'
  · intro h k'
    obtain ⟨p, hp, hX'⟩ := h (e.symm k')
    refine ⟨σ p, by rw [hσ, hp, Equiv.apply_symm_apply], ?_⟩
    rwa [← ren_X, mem_map_iff]

theorem isMultiProjPrime_map {V : Ideal (MRingOver F ι)} (h : IsMultiProjPrime V) :
    IsMultiProjPrime (V.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι')) := by
  obtain ⟨hp, hh, hr⟩ := h
  exact ⟨isPrime_map _ V, isMultiHomogIdeal_map e σ hσ hh,
    (isRelevant_map_iff e σ hσ V).2 hr⟩

theorem isProjVarF_map {V : Ideal (MRingOver F ι)} {n : ℕ} (h : IsProjVarF V n) :
    IsProjVarF (V.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι')) n := by
  refine ⟨isMultiProjPrime_map e σ hσ h.1, ?_⟩
  rw [ringKrullDim_quot_map, h.2, Fintype.card_congr e]

theorem isRatSection_map {V : Ideal (MRingOver F ι)} {A : K → ℤ} {f g : MRingOver F ι}
    (h : IsRatSection V A f g) :
    IsRatSection (V.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι')) (A ∘ e.symm) (ren σ f)
      (ren σ g) := by
  obtain ⟨α, β, hf, hg, hfV, hgV, hd⟩ := h
  refine ⟨α ∘ e.symm, β ∘ e.symm, isMultiHomog_ren e σ hσ hf, isMultiHomog_ren e σ hσ hg,
    fun h => hfV ((mem_map_iff _ _ _).1 h), fun h => hgV ((mem_map_iff _ _ _).1 h),
    fun k' => hd (e.symm k')⟩

omit hσ in
omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem sup_span_map (V : Ideal (MRingOver F ι)) (f : MRingOver F ι) :
    (V ⊔ Ideal.span {f}).map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι') =
      V.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι') ⊔ Ideal.span {ren σ f} := by
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  rfl

theorem mem_divSupp_map_iff (V W : Ideal (MRingOver F ι)) (f : MRingOver F ι) :
    W.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι') ∈
        divSupp (V.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι')) (ren σ f) ↔
      W ∈ divSupp V f := by
  have h1 : W.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι') ∈
        (V.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι') ⊔
          Ideal.span {ren σ f}).minimalPrimes ↔ W ∈ (V ⊔ Ideal.span {f}).minimalPrimes := by
    rw [← sup_span_map]
    exact map_mem_minimalPrimes_iff _
  exact and_congr h1 (isRelevant_map_iff e σ hσ W)

theorem divCycle_map_apply (V W : Ideal (MRingOver F ι)) (f : MRingOver F ι) :
    divCycle (V.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι')) (ren σ f)
        (W.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι')) = divCycle V f W := by
  classical
  simp only [divCycle, Finsupp.ofSupportFinite_coe]
  by_cases hW : W ∈ divSupp V f
  · have hW' := (mem_divSupp_map_iff e σ hσ V W f).2 hW
    rw [if_pos hW, if_pos hW']
    haveI : W.IsPrime := hW.1.1.1
    exact multAt_map (ren σ) V W (le_sup_left.trans hW.1.1.2) f
  · have hW' := mt (mem_divSupp_map_iff e σ hσ V W f).1 hW
    rw [if_neg hW, if_neg hW']

omit hσ in

def idealEquiv : Ideal (MRingOver F ι) ≃ Ideal (MRingOver F ι') where
  toFun W := W.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι')
  invFun W := W.map ((ren (F := F) σ).symm : MRingOver F ι' →+* MRingOver F ι)
  left_inv W := Ideal.map_of_equiv (I := W) (ren (F := F) σ)
  right_inv W := by
    have := Ideal.map_of_equiv (I := W) (ren (F := F) σ).symm
    rwa [RingEquiv.symm_symm] at this

omit hσ in
omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem idealEquiv_apply (W : Ideal (MRingOver F ι)) :
    idealEquiv σ W = W.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι') := rfl

theorem ratDiv_map (V : Ideal (MRingOver F ι)) (f g : MRingOver F ι) :
    ratDiv (V.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι')) (ren σ f) (ren σ g) =
      Finsupp.equivMapDomain (idealEquiv σ) (ratDiv V f g) := by
  ext W'
  obtain ⟨W, rfl⟩ := (idealEquiv σ).surjective W'
  rw [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply]
  simp only [ratDiv, Finsupp.coe_sub, Pi.sub_apply, Finsupp.mapRange_apply, idealEquiv_apply,
    divCycle_map_apply e σ hσ]

omit hσ in
omit [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in
theorem cycEval_map (J : Ideal (MRingOver F ι') → ℤ) (D : Ideal (MRingOver F ι) →₀ ℤ) :
    cycEval J (Finsupp.equivMapDomain (idealEquiv σ) D) = cycEval (fun W => J (idealEquiv σ W)) D := by
  classical
  unfold cycEval
  rw [Finsupp.equivMapDomain_eq_mapDomain,
    Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]

omit hσ in

def fiberElt (q : Σ k', ι' k') (k' : K') (h : q.1 = k') : ι' k' := h ▸ q.2

omit hσ in
omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem sigma_mk_fiberElt (q : Σ k', ι' k') (k' : K') (h : q.1 = k') :
    (⟨k', fiberElt q k' h⟩ : Σ k', ι' k') = q := by
  obtain ⟨a, b⟩ := q
  dsimp only at h
  subst h
  rfl

def chartMap (i : ∀ k, ι k) (k' : K') : ι' k' :=
  fiberElt (σ ⟨e.symm k', i (e.symm k')⟩) k' (by rw [hσ, Equiv.apply_symm_apply])

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem X_chartMap (i : ∀ k, ι k) (k' : K') :
    (X ⟨k', chartMap e σ hσ i k'⟩ : MRingOver F ι') = ren σ (X ⟨e.symm k', i (e.symm k')⟩) := by
  rw [chartMap, sigma_mk_fiberElt, ren_X]

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem isChart_map {V : Ideal (MRingOver F ι)} {i : ∀ k, ι k} (h : IsChart V i) :
    IsChart (V.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι')) (chartMap e σ hσ i) := by
  intro k' hk'
  rw [X_chartMap, mem_map_iff] at hk'
  exact h _ hk'

omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem chartIdeal_map (V : Ideal (MRingOver F ι)) (i : ∀ k, ι k) :
    chartIdeal (V.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι')) (chartMap e σ hσ i) =
      (chartIdeal V i).map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι') := by
  rw [chartIdeal, chartIdeal, Ideal.map_sup, Ideal.map_span, ← Set.range_comp]
  congr 2
  have : (fun k' => (X ⟨k', chartMap e σ hσ i k'⟩ : MRingOver F ι') - 1) =
      ((ren (F := F) σ : MRingOver F ι →+* MRingOver F ι') ∘ fun k => (X ⟨k, i k⟩ : MRingOver F ι) - 1) ∘
        e.symm := by
    funext k'
    simp only [Function.comp_apply, X_chartMap, map_sub, map_one, RingEquiv.coe_toRingHom]
  rw [this, e.symm.surjective.range_comp]

theorem ptDeg_map (V : Ideal (MRingOver F ι)) (i : ∀ k, ι k) :
    ptDeg (V.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι')) (chartMap e σ hσ i) = ptDeg V i := by
  rw [ptDeg, ptDeg]
  exact (Ideal.quotientEquivAlg (chartIdeal V i) _ (renameEquiv F σ)
    (chartIdeal_map e σ hσ V i)).toLinearEquiv.finrank_eq.symm

omit hσ in

def pullFamily (I' : IFamily F ι') : IFamily F ι :=
  fun V n L => I' (V.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι')) n (fun j => L j ∘ e.symm)

omit hσ in
omit [Fintype K] [∀ k, Fintype (ι k)] [Fintype K'] [∀ k, Fintype (ι' k)] in
theorem snoc_comp {n : ℕ} (L : Fin n → K → ℤ) (A : K → ℤ) :
    (fun j => Fin.snoc (α := fun _ => K → ℤ) L A j ∘ e.symm) =
      Fin.snoc (α := fun _ => K' → ℤ) (fun j => L j ∘ e.symm) (A ∘ e.symm) := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp only [Fin.snoc_last]
  · simp only [Fin.snoc_castSucc]

theorem isFieldIntersection_pull {I' : IFamily F ι'} (hI' : IsFieldIntersection I') :
    IsFieldIntersection (pullFamily e σ I') := by
  refine ⟨fun V L i hV hi => ?_, fun V n L A f g hV hs => ?_⟩
  · have := hI'.1 (V.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι')) (fun j => L j ∘ e.symm)
      (chartMap e σ hσ i) (isProjVarF_map e σ hσ hV) (isChart_map e σ hσ hi)
    rw [pullFamily, this, ptDeg_map]
  · have := hI'.2 (V.map (ren (F := F) σ : MRingOver F ι →+* MRingOver F ι')) n (fun j => L j ∘ e.symm)
      (A ∘ e.symm) (ren σ f) (ren σ g) (isProjVarF_map e σ hσ hV) (isRatSection_map e σ hσ hs)
    simp only [pullFamily]
    rw [snoc_comp, this, ratDiv_map e σ hσ, cycEval_map]
    rfl

end MRing

end ExistsUniqueRelabel

universe u v w v' w'

theorem ExistsUniqueRelabel.proof : ExistsUniqueRelabel.Statement.{u, v, w, v', w'} := by
  intro F _ K _ ι _ K' _ ι' _ e hι hE
  obtain ⟨I', hI', huniq⟩ := hE
  let σ : (Σ k, ι k) ≃ (Σ k', ι' k') := Equiv.sigmaCongr e hι
  have hσ : ∀ p, (σ p).1 = e p.1 := fun p => rfl
  have hσ' : ∀ q, (σ.symm q).1 = e.symm q.1 := fun q => by
    rw [Equiv.eq_symm_apply, ← hσ, Equiv.apply_symm_apply]
  refine ⟨ExistsUniqueRelabel.pullFamily e σ I',
    ExistsUniqueRelabel.isFieldIntersection_pull e σ hσ hI', fun J hJ V n L hV => ?_⟩
  have hJ' := ExistsUniqueRelabel.isFieldIntersection_pull e.symm σ.symm hσ' hJ
  have := huniq _ hJ' _ n (fun j => L j ∘ e.symm) (ExistsUniqueRelabel.isProjVarF_map e σ hσ hV)
  simp only [ExistsUniqueRelabel.pullFamily, Equiv.symm_symm,
    ExistsUniqueRelabel.map_ren_symm_map] at this ⊢
  convert this using 2
  funext j k
  simp

end GroundTheory.Heights₂.Heights.Targets
