import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsArithVarOfBlockAlgebraic
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValuationCoordsComplexPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsValuationSubringExtension
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullFormsGeneric

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace GlobalTheory.CompanionTheory.Ar.Ht.JoinFacts

open GlobalTheory.CompanionTheory.Ar.LocVal (homog_one homog_zero homog_mul homog_add homog_neg homog_X aeval_scale
  mem_mCoordIdeal_of_aeval_eq_zero)

section Local

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω L : Type} [Field Ω] [Field L]

def IsVal (y : (Σ k, ι k) → Ω) (w : (Σ k, ι k) → L) (a : Ω) (v : L) : Prop :=
  ∃ (d : K → ℕ) (g h : MRing ι), IsMultiHomog g d ∧ IsMultiHomog h d ∧ aeval w h ≠ 0 ∧
    aeval y g = a * aeval y h ∧ aeval w g = v * aeval w h

variable {y : (Σ k, ι k) → Ω} {w : (Σ k, ι k) → L}

theorem aeval_eq_zero_of (hw : w ∈ ptsOver L (mCoordIdeal y)) {f : MRing ι} {d : K → ℕ}
    (hf : IsMultiHomog f d) (h0 : aeval y f = 0) : aeval w f = 0 :=
  hw.2 f (mem_mCoordIdeal_of_aeval_eq_zero y hf h0)

theorem aeval_ne_zero_of (hw : w ∈ ptsOver L (mCoordIdeal y)) {f : MRing ι} {d : K → ℕ}
    (hf : IsMultiHomog f d) (h0 : aeval w f ≠ 0) : aeval y f ≠ 0 :=
  fun h => h0 (aeval_eq_zero_of hw hf h)

theorem IsVal.unique (hw : w ∈ ptsOver L (mCoordIdeal y)) {a : Ω} {v v' : L}
    (h1 : IsVal y w a v) (h2 : IsVal y w a v') : v = v' := by
  obtain ⟨d, g, h, hg, hh, hn, hy, hv⟩ := h1
  obtain ⟨d', g', h', hg', hh', hn', hy', hv'⟩ := h2
  have hF : IsMultiHomog (g * h' + -(g' * h)) (d + d') :=
    homog_add (homog_mul hg hh') (by
      have := homog_neg (homog_mul hg' hh)
      rwa [add_comm d' d] at this)
  have h0 := aeval_eq_zero_of hw hF (by
    simp only [map_add, map_neg, map_mul, hy, hy']
    ring)
  simp only [map_add, map_neg, map_mul, hv, hv'] at h0
  have : (v - v') * (aeval w h * aeval w h') = 0 := by linear_combination h0
  rcases mul_eq_zero.mp this with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h (mul_ne_zero hn hn')

theorem IsVal.add {a b : Ω} {v u : L} (h1 : IsVal y w a v) (h2 : IsVal y w b u) :
    IsVal y w (a + b) (v + u) := by
  obtain ⟨d, g, h, hg, hh, hn, hy, hv⟩ := h1
  obtain ⟨d', g', h', hg', hh', hn', hy', hv'⟩ := h2
  refine ⟨d + d', g * h' + g' * h, h * h', homog_add (homog_mul hg hh') ?_, homog_mul hh hh',
    ?_, ?_, ?_⟩
  · have := homog_mul hg' hh
    rwa [add_comm d' d] at this
  · rw [map_mul]; exact mul_ne_zero hn hn'
  · simp only [map_add, map_mul, hy, hy']; ring
  · simp only [map_add, map_mul, hv, hv']; ring

theorem IsVal.mul {a b : Ω} {v u : L} (h1 : IsVal y w a v) (h2 : IsVal y w b u) :
    IsVal y w (a * b) (v * u) := by
  obtain ⟨d, g, h, hg, hh, hn, hy, hv⟩ := h1
  obtain ⟨d', g', h', hg', hh', hn', hy', hv'⟩ := h2
  refine ⟨d + d', g * g', h * h', homog_mul hg hg', homog_mul hh hh', ?_, ?_, ?_⟩
  · rw [map_mul]; exact mul_ne_zero hn hn'
  · simp only [map_mul, hy, hy']; ring
  · simp only [map_mul, hv, hv']; ring

theorem IsVal.neg {a : Ω} {v : L} (h1 : IsVal y w a v) : IsVal y w (-a) (-v) := by
  obtain ⟨d, g, h, hg, hh, hn, hy, hv⟩ := h1
  refine ⟨d, -g, h, homog_neg hg, hh, hn, ?_, ?_⟩
  · simp only [map_neg, hy]; ring
  · simp only [map_neg, hv]; ring

theorem isVal_one : IsVal y w 1 1 :=
  ⟨0, 1, 1, homog_one, homog_one, by simp, by simp, by simp⟩

theorem isVal_zero : IsVal y w 0 0 :=
  ⟨0, 0, 1, homog_zero 0, homog_one, by simp, by simp, by simp⟩

variable (y w) in

def locRing : Subring Ω where
  carrier := {a | ∃ v, IsVal y w a v}
  mul_mem' := fun ⟨_, hv⟩ ⟨_, hu⟩ => ⟨_, hv.mul hu⟩
  one_mem' := ⟨1, isVal_one⟩
  add_mem' := fun ⟨_, hv⟩ ⟨_, hu⟩ => ⟨_, hv.add hu⟩
  zero_mem' := ⟨0, isVal_zero⟩
  neg_mem' := fun ⟨_, hv⟩ => ⟨_, hv.neg⟩

def locVal (a : locRing y w) : L := Classical.choose a.2

theorem isVal_locVal (a : locRing y w) : IsVal y w a (locVal a) := Classical.choose_spec a.2

theorem locVal_eq (hw : w ∈ ptsOver L (mCoordIdeal y)) {a : locRing y w} {v : L}
    (h : IsVal y w a v) : locVal a = v :=
  (isVal_locVal a).unique hw h

def locHom (hw : w ∈ ptsOver L (mCoordIdeal y)) : locRing y w →+* L where
  toFun := locVal
  map_one' := locVal_eq hw isVal_one
  map_mul' a b := locVal_eq hw ((isVal_locVal a).mul (isVal_locVal b))
  map_zero' := locVal_eq hw isVal_zero
  map_add' a b := locVal_eq hw ((isVal_locVal a).add (isVal_locVal b))

theorem coord_ne_zero (hw : w ∈ ptsOver L (mCoordIdeal y)) {k : K} {c : ι k} (hc : w ⟨k, c⟩ ≠ 0) :
    y ⟨k, c⟩ ≠ 0 := by
  classical
  have hXw : aeval w (X ⟨k, c⟩ : MRing ι) ≠ 0 := by simpa using hc
  simpa using aeval_ne_zero_of hw (homog_X k c) hXw

theorem isVal_ratio (hw : w ∈ ptsOver L (mCoordIdeal y)) (k : K) (c e : ι k) (hc : w ⟨k, c⟩ ≠ 0) :
    IsVal y w (y ⟨k, e⟩ / y ⟨k, c⟩) (w ⟨k, e⟩ / w ⟨k, c⟩) := by
  classical
  have hyc := coord_ne_zero hw hc
  refine ⟨Pi.single k 1, X ⟨k, e⟩, X ⟨k, c⟩, homog_X k e, homog_X k c, by simpa using hc, ?_, ?_⟩
  · simp only [aeval_X]; field_simp
  · simp only [aeval_X]; field_simp

end Local

theorem exists_pivot {I Ω : Type} [Finite I] [Field Ω] (V : ValuationSubring Ω) (f : I → Ω) (h : ∃ i, f i ≠ 0) :
    ∃ e, f e ≠ 0 ∧ ∀ q, f q / f e ∈ V := by
  obtain ⟨i, hi⟩ := h
  haveI : Nonempty I := ⟨i⟩
  obtain ⟨e, he⟩ := Finite.exists_max fun q => V.valuation (f q)
  have hne : f e ≠ 0 := by
    intro h0
    have h1 := he i
    rw [h0, map_zero, le_zero_iff, map_eq_zero] at h1
    exact hi h1
  refine ⟨e, hne, fun q => ?_⟩
  rw [← ValuationSubring.valuation_le_one_iff, map_div₀]
  exact div_le_one_of_le₀ (he q) zero_le'

section Lift

variable {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] {ι₁ : K₁ → Type} {ι₂ : K₂ → Type} [∀ k, Fintype (ι₁ k)]
  [∀ k, Fintype (ι₂ k)] {Ω L : Type} [Field Ω] [Field L]

theorem aeval_eq_zero_of_mem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {y : (Σ k, ι k) → Ω}
    {f : MRing ι} (hf : f ∈ mCoordIdeal y) : aeval y f = 0 := by
  let φ : MvPolynomial K Ω →ₐ[ℤ] Ω :=
    (aeval (fun _ : K => (1 : Ω)) : MvPolynomial K Ω →ₐ[Ω] Ω).restrictScalars ℤ
  have e : φ.comp (mConeMap y) = aeval y := by
    refine MvPolynomial.algHom_ext fun p => ?_
    simp [φ, mConeMap]
  have h0 : mConeMap y f = 0 := hf
  rw [← e, AlgHom.comp_apply, h0, map_zero]

theorem exists_join_lift [IsAlgClosed L] (y : (Σ k, ι₁ k) → Ω) (b : (Σ k, ι₂ k) → Ω) (hb : ∀ k, ∃ i, b ⟨k, i⟩ ≠ 0)
    (w : (Σ k, ι₁ k) → L) (hw : w ∈ ptsOver L (mCoordIdeal y)) :
    ∃ z ∈ ptsOver L (mCoordIdeal (joinVec y b)), (fun p => z (joinInl ι₁ ι₂ p)) = w := by
  classical
  choose c hc using hw.1
  obtain ⟨V, hAV, ψ, hψ⟩ := GlobalTheory.CompanionTheory.Chevalley.chevalley_extension Ω L (locRing y w) (locHom hw)
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => coord_ne_zero hw (hc k)
  have hval : ∀ k i, IsVal y w (y ⟨k, i⟩ / y ⟨k, c k⟩) (w ⟨k, i⟩ / w ⟨k, c k⟩) := fun k i =>
    isVal_ratio hw k (c k) i (hc k)
  have hr : ∀ k i, y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ V := fun k i => hAV _ ⟨_, hval k i⟩
  have hrv : ∀ k i, ψ ⟨_, hr k i⟩ = w ⟨k, i⟩ / w ⟨k, c k⟩ := fun k i =>
    (hψ ⟨_, ⟨_, hval k i⟩⟩).trans (locVal_eq hw (hval k i))
  choose e he hq using fun k => exists_pivot V (fun q : ι₂ k => b ⟨k, q⟩) (hb k)

  let Y : (Σ k, joinIdx ι₁ ι₂ k) → V := joinVec (fun p => ⟨_, hr p.1 p.2⟩) (fun p => ⟨_, hq p.1 p.2⟩)
  let t : K₁ ⊕ K₂ → Ω := Sum.elim (fun k => y ⟨k, c k⟩) (fun k => b ⟨k, e k⟩)
  let s : K₁ ⊕ K₂ → L := Sum.elim (fun k => w ⟨k, c k⟩) (fun _ => 1)
  let z : (Σ k, joinIdx ι₁ ι₂ k) → L := joinVec w (fun p => ψ ⟨_, hq p.1 p.2⟩)
  have hJ : joinVec y b = fun p => t p.1 * (Y p : Ω) := by
    funext ⟨k, i⟩
    cases k with
    | inl k => exact (mul_div_cancel₀ _ (hyc k)).symm
    | inr k => exact (mul_div_cancel₀ _ (he k)).symm
  have hZ : z = fun p => s p.1 * ψ (Y p) := by
    funext ⟨k, i⟩
    cases k with
    | inl k =>
      show w ⟨k, i⟩ = w ⟨k, c k⟩ * ψ ⟨_, hr k i⟩
      exact (mul_div_cancel₀ _ (hc k)).symm.trans (congrArg _ (hrv k i).symm)
    | inr k =>
      show ψ _ = 1 * ψ _
      rw [one_mul]
      rfl
  refine ⟨z, ⟨?_, ?_⟩, by funext ⟨k, i⟩; rfl⟩
  · intro k
    cases k with
    | inl k => exact ⟨c k, hc k⟩
    | inr k =>
      refine ⟨e k, ?_⟩
      have h1 : (⟨_, hq k (e k)⟩ : V) = 1 := Subtype.ext (div_self (he k))
      show ψ ⟨_, hq k (e k)⟩ ≠ 0
      rw [h1, map_one]
      exact one_ne_zero
  · obtain ⟨S, hS, hspan⟩ := GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal (joinVec y b)
    have hle : mCoordIdeal (joinVec y b) ≤ RingHom.ker (aeval z : MRing (joinIdx ι₁ ι₂) →ₐ[ℤ] L).toRingHom := by
      rw [hspan, Ideal.span_le]
      intro g hg
      obtain ⟨d, hd⟩ := hS g hg
      have hgP : g ∈ mCoordIdeal (joinVec y b) := hspan ▸ Ideal.subset_span hg
      have h0 : aeval (joinVec y b) g = 0 := aeval_eq_zero_of_mem hgP
      rw [hJ, aeval_scale hd] at h0
      have ht : ∏ k, t k ^ d k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (by
        cases k with
        | inl k => exact hyc k
        | inr k => exact he k)
      have h1 : aeval (fun p => (Y p : Ω)) g = 0 := (mul_eq_zero.mp h0).resolve_left ht
      have h2 : aeval Y g = 0 := by
        apply Subtype.val_injective
        have := comp_aeval_apply (R := ℤ) Y (V.subtype.toIntAlgHom) g
        exact this.trans h1
      have h3 : aeval (fun p => ψ (Y p)) g = 0 := by
        have h' : ψ (aeval Y g) = aeval (fun p => ψ (Y p)) g := comp_aeval_apply (R := ℤ) Y (ψ.toIntAlgHom) g
        rw [← h', h2, map_zero]
      show aeval z g = 0
      rw [hZ, aeval_scale hd, h3, mul_zero]
    exact fun f hf => hle hf

end Lift

section Maps

variable {K K' : Type} {ι : K → Type} {ι' : K' → Type} {Ω Ω' : Type} [Field Ω] [Field Ω']

theorem rename_mem {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hv : ∀ p, (v p).1 = κ p.1) (Y : (Σ k, ι' k) → Ω)
    {f : MRing ι} (hf : f ∈ mCoordIdeal fun p => Y (v p)) : rename v f ∈ mCoordIdeal Y := by
  have h0 : mConeMap (fun p => Y (v p)) f = 0 := hf
  have e : (mConeMap Y).comp (rename v) =
      ((rename κ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K' Ω).restrictScalars ℤ).comp
        (mConeMap fun p => Y (v p)) := by
    refine MvPolynomial.algHom_ext fun p => ?_
    simp [mConeMap, hv]
  have h1 := DFunLike.congr_fun e f
  simp only [AlgHom.comp_apply, h0, map_zero] at h1
  exact h1

theorem mem_map (i : Ω →+* Ω') (y : (Σ k, ι k) → Ω) {f : MRing ι} (hf : f ∈ mCoordIdeal y) :
    f ∈ mCoordIdeal fun p => i (y p) := by
  have h0 : mConeMap y f = 0 := hf
  have e : mConeMap (fun p => i (y p)) =
      (MvPolynomial.map i : MvPolynomial K Ω →+* MvPolynomial K Ω').toIntAlgHom.comp (mConeMap y) := by
    refine MvPolynomial.algHom_ext fun p => ?_
    show _ = MvPolynomial.map i (mConeMap y (X p))
    simp [mConeMap]
  show mConeMap (fun p => i (y p)) f = 0
  rw [e]
  show MvPolynomial.map i (mConeMap y f) = 0
  rw [h0, map_zero]

theorem charZero_of {y : (Σ k, ι k) → Ω} (h : IsHorizontal (mCoordIdeal y)) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn => ?_
  have h1 : (n : ℤ) ∈ Ideal.comap (C : ℤ →+* MRing ι) (mCoordIdeal y) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker, ← algebraMap_eq, AlgHom.commutes]
    have e : algebraMap ℤ (MvPolynomial K Ω) (n : ℤ) = C (n : Ω) := by simp
    rw [e, hn, map_zero]
  rw [h] at h1
  simpa using h1

variable [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]

theorem joinInl_injective : Function.Injective (joinInl ι ι') := by
  rintro ⟨k, i⟩ ⟨k', i'⟩ h
  have h1 : k = k' := Sum.inl_injective (congrArg Sigma.fst h)
  subst h1
  have h' : (⟨Sum.inl k, i⟩ : Σ k, joinIdx ι ι' k) = ⟨Sum.inl k, i'⟩ := h
  have h2 : i = i' := eq_of_heq (Sigma.mk.inj h').2
  rw [h2]

theorem isMultiHomog_rename_inl {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) [Fintype K] [Fintype K'] :
    IsMultiHomog (rename (joinInl ι ι') g) (Sum.elim d 0) := by
  classical
  intro m hm k
  rw [support_rename_of_injective joinInl_injective] at hm
  obtain ⟨m₀, hm₀, rfl⟩ := Finset.mem_image.mp hm
  cases k with
  | inl k =>
    have h1 : ∀ i : joinIdx ι ι' (Sum.inl k), Finsupp.mapDomain (joinInl ι ι') m₀ ⟨Sum.inl k, i⟩ = m₀ ⟨k, i⟩ :=
      fun i => Finsupp.mapDomain_apply joinInl_injective m₀ ⟨k, i⟩
    simp only [h1]
    exact hg m₀ hm₀ k
  | inr k =>
    have h1 : ∀ i : joinIdx ι ι' (Sum.inr k), Finsupp.mapDomain (joinInl ι ι') m₀ ⟨Sum.inr k, i⟩ = 0 := fun i =>
      Finsupp.mapDomain_notin_range _ _ (by
        rintro ⟨p, hp⟩
        have := congrArg Sigma.fst hp
        simp [joinInl] at this)
    simp [h1]

end Maps

theorem main : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M R : RootModel Ψ N) (i : R.Ω →+* M.Ω),
    IsArithVar (mCoordIdeal (joinOf M R i)) (dimFl Ψ N + 1) ∧ Birational (joinOf M R i) ∧
    (∀ (L : Type) [Field L], ∀ z ∈ ptsOver L (mCoordIdeal (joinOf M R i)),
      (fun p => z (joinInl M.ι R.ι p)) ∈ ptsOver L M.P ∧ (fun p => z (joinInr M.ι R.ι p)) ∈ ptsOver L R.P) ∧
    ∀ (L : Type) [Field L] [IsAlgClosed L], ∀ w ∈ ptsOver L M.P,
      ∃ z ∈ ptsOver L (mCoordIdeal (joinOf M R i)), (fun p => z (joinInl M.ι R.ι p)) = w := by
  intro Ψ _ _ N M R i
  obtain ⟨cM, hcM⟩ := GroundTheory.Heights₂.Heights.HilbertSamuel.CoordArithOfFnField.nonzero_of_relevant M.y M.arith.2.1.2.2
  obtain ⟨cR, hcR⟩ := GroundTheory.Heights₂.Heights.HilbertSamuel.CoordArithOfFnField.nonzero_of_relevant R.y R.arith.2.1.2.2
  have hb : ∀ k, ∃ q, (fun p => i (R.y p)) ⟨k, q⟩ ≠ 0 := fun k =>
    ⟨cR k, (map_ne_zero i).mpr (hcR k)⟩
  haveI : CharZero M.Ω := charZero_of M.arith.2.2.1
  have eL : joinOf M R i ∘ joinInl M.ι R.ι = M.y := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hblock : ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap (Sum.inl : M.K → M.K ⊕ R.K) (joinInl M.ι R.ι) := by
      refine ⟨Sum.inl_injective, joinInl_injective, fun _ => rfl, ?_⟩
      rintro ⟨_, q⟩ ⟨k, rfl⟩
      exact ⟨⟨k, q⟩, rfl⟩
    have hnz : ∀ k, ∃ q, joinOf M R i ⟨k, q⟩ ≠ 0 := by
      intro k
      cases k with
      | inl k => exact ⟨cM k, hcM k⟩
      | inr k => exact hb k
    have htop := GroundTheory.Heights₂.Heights.HilbertSamuel.PullFormsGeneric.blockFnField_eq_top cM hcM M.birational
    refine isArithVar_of_isAlgebraic_image _ _ _ _ Sum.inl (joinInl M.ι R.ι) M.Ω (joinOf M R i) _ hblock hnz
      (by rw [eL]; exact M.arith) fun t _ => ?_
    rw [eL]
    exact isAlgebraic_algebraMap (⟨t, htop ▸ IntermediateField.mem_top⟩ : ReciprocityTheory.ChartRestriction.G.AI.I4.blockFnField M.y)
  · intro s
    obtain ⟨d, g, h, hg, hh, hn, he⟩ := M.birational s
    refine ⟨Sum.elim d 0, rename (joinInl M.ι R.ι) g, rename (joinInl M.ι R.ι) h, isMultiHomog_rename_inl hg,
      isMultiHomog_rename_inl hh, ?_, ?_⟩
    · rw [aeval_rename, eL]
      exact hn
    · rw [aeval_rename, aeval_rename, eL]
      exact he
  · intro L _ z hz
    refine ⟨⟨fun k => hz.1 (Sum.inl k), fun f hf => ?_⟩, ⟨fun k => hz.1 (Sum.inr k), fun f hf => ?_⟩⟩
    · have h1 := hz.2 _ (rename_mem (κ := Sum.inl) (v := joinInl M.ι R.ι) (fun _ => rfl) (joinOf M R i) (f := f) hf)
      rw [aeval_rename] at h1
      exact h1
    · have h1 := hz.2 _ (rename_mem (κ := Sum.inr) (v := joinInr M.ι R.ι) (fun _ => rfl) (joinOf M R i) (f := f)
        (mem_map i R.y hf))
      rw [aeval_rename] at h1
      exact h1
  · intro L _ _ w hw
    exact exists_join_lift M.y (fun p => i (R.y p)) hb w hw

end GlobalTheory.CompanionTheory.Ar.Ht.JoinFacts
