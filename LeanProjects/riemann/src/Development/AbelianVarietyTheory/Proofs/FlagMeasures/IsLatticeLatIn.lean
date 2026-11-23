import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLatticeDiscriminantOrderNeZeroUnimodula
import Formalism.SizeWindowBrackets.ChainSlopeWindows.TruncatedLatticeHolds

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S IsDedekindDomain
open scoped ENNReal Classical

namespace GlobalTheory.Mass.DetAgree

section
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]

theorem genIdxH_eq_idxN {A B : Submodule (𝓞 K) V} (hBA : B ≤ A) (h0 : idxN A B ≠ 0) :
    Lat.genIdxH A B = (idxN A B : ℝ) := by
  obtain ⟨k, hk, hc⟩ := Formalism.LFunctionChainParameters.LLcv.card_pLen _ A B hBA rfl h0
  let e : HeightOneSpectrum (𝓞 K) ≃ {p : Ideal (𝓞 K) // p.IsMaximal} :=
    { toFun := fun P => ⟨P.asIdeal, P.isMaximal⟩
      invFun := fun p => ⟨p.1, p.2.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField p.2 (RingOfIntegers.not_isField K)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hl : ∀ P : HeightOneSpectrum (𝓞 K), (haveI := P.isPrime; lidx P.asIdeal A B) = (k (e P) : ℤ) := by
    intro P
    have a := hk (e P)
    unfold Formalism.LFunctionChainParameters.LLcv.pLen at a
    unfold lidx
    rw [inf_eq_right.mpr hBA, indexBasic_locLen_self]
    unfold locLen
    erw [a]
    simp
  unfold Lat.genIdxH
  simp only [hl, zpow_natCast]
  have := finprod_comp_equiv (f := fun w : {p : Ideal (𝓞 K) // p.IsMaximal} =>
    ((Ideal.absNorm w.1 : ℕ) : ℝ) ^ k w) e
  refine this.trans ?_
  rw [idxN, hc, finprod_eq_prod_of_mulSupport_subset (s := k.support), Finsupp.prod, Nat.cast_prod]
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [Nat.cast_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  · intro w hw
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro h
    apply hw
    simp [h]

variable [Module K V] [IsScalarTower (𝓞 K) K V]

theorem span_inf_eq (L : Submodule (𝓞 K) V) (hL : Submodule.IsLattice K L) (U : Submodule K V) :
    Submodule.span K ((L ⊓ U.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) = U := by
  refine le_antisymm (Submodule.span_le.2 fun x hx => hx.2) fun u hu => ?_
  obtain ⟨r, hr, hru⟩ := Formalism.LFunctionChainParameters.LLcv.span_le_locS (K := K) L (x := u) (by rw [hL.span_eq_top]; trivial)
  have h1 : algebraMap (𝓞 K) K r ≠ 0 := by simpa using nonZeroDivisors.ne_zero hr
  have h2 : r • u ∈ Submodule.span K ((L ⊓ U.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) :=
    Submodule.subset_span ⟨hru, (U.restrictScalars (𝓞 K)).smul_mem r hu⟩
  rw [← algebraMap_smul K r] at h2
  exact (Submodule.smul_mem_iff _ h1).1 h2

theorem isLattice_latIn (L : Submodule (𝓞 K) V) (hL : Submodule.IsLattice K L) (U : Submodule K V) :
    Submodule.IsLattice K (latIn U L) := by
  refine ⟨?_, ?_⟩
  · refine Submodule.fg_of_fg_map_injective (U.subtype.restrictScalars (𝓞 K)) U.injective_subtype ?_
    exact Submodule.FG.of_le hL.fg (Submodule.map_comap_le _ _)
  · rw [eq_top_iff]
    intro u _
    obtain ⟨r, hr, hru⟩ := Formalism.LFunctionChainParameters.LLcv.span_le_locS (K := K) L (x := u) (by rw [hL.span_eq_top]; trivial)
    have h1 : algebraMap (𝓞 K) K r ≠ 0 := by simpa using nonZeroDivisors.ne_zero hr
    have h2 : r • u ∈ Submodule.span K (latIn U L : Set U) := Submodule.subset_span hru
    rw [← algebraMap_smul K r] at h2
    exact (Submodule.smul_mem_iff _ h1).1 h2

variable [StarRing K]

theorem nondeg_of_pd {h : V →ₗ⋆[K] V →ₗ[K] K} (hp : PD h) : h.Nondegenerate := by
  obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
  have key : ∀ x, h x x = 0 → x = 0 := fun x hx => by
    by_contra h0
    have := hp τ x h0
    rw [hx] at this
    simp at this
  exact ⟨fun x hx => key x (hx x), fun x hx => key x (hx x)⟩

theorem idxN_dualInH (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (hL : Submodule.IsLattice K L)
    (U : Submodule K V) :
    idxN (Lat.dualInH h (L ⊓ U.restrictScalars (𝓞 K))) (L ⊓ U.restrictScalars (𝓞 K)) =
      discN (hRes h U) (latIn U L) := by
  have e1 : (L ⊓ U.restrictScalars (𝓞 K)).toAddSubgroup =
      (latIn U L).toAddSubgroup.map U.subtype.toAddMonoidHom := by
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, h2⟩, h1, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.2⟩
  have e2 : (Lat.dualInH h (L ⊓ U.restrictScalars (𝓞 K))).toAddSubgroup =
      (dual (hRes h U) (latIn U L)).toAddSubgroup.map U.subtype.toAddMonoidHom := by
    unfold Lat.dualInH
    rw [span_inf_eq L hL U]
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨x, h2⟩, (dualBasic_mem_dual _ _ _).2 fun y hy => ?_, rfl⟩
      exact (dualBasic_mem_dual _ _ _).1 h1 y ⟨hy, y.2⟩
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(dualBasic_mem_dual _ _ _).2 fun z hz => ?_, y.2⟩
      exact (dualBasic_mem_dual _ _ _).1 hy ⟨z, hz.2⟩ hz.1
  rw [discN, idxN, idxN, e1, e2, AddSubgroup.relIndex_map_map_of_injective _ _ U.injective_subtype]

theorem discGen_iff (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (hle : L ≤ dual h L) (e : ℕ) :
    Cnt.DiscGen h L e ↔ ∃ t : Finset V, t.card ≤ e ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set V) := by
  set D := dual h L with hD
  set q : D →ₗ[𝓞 K] Cnt.discMod h L := (L.comap D.subtype).mkQ with hq
  have key : ∀ s : Finset D, Submodule.span (𝓞 K) ((s.image q : Finset _) : Set (Cnt.discMod h L)) = ⊤ ↔
      D = L ⊔ Submodule.span (𝓞 K) ((s.image D.subtype : Finset V) : Set V) := by
    intro s
    rw [Finset.coe_image, Finset.coe_image, ← Submodule.map_span, ← Submodule.map_span, hq,
      Submodule.map_mkQ_eq_top, ← (Submodule.map_injective_of_injective D.injective_subtype).eq_iff,
      Submodule.map_sup, Submodule.map_comap_subtype, inf_eq_right.2 hle, Submodule.map_top,
      Submodule.range_subtype, eq_comm]
  constructor
  · rintro ⟨s, hs, hsp⟩
    have hsurj : Function.Surjective q := Submodule.mkQ_surjective _
    refine ⟨(s.image (Function.surjInv hsurj)).image D.subtype,
      Finset.card_image_le.trans (Finset.card_image_le.trans hs), (key _).1 ?_⟩
    rw [Finset.image_image, (Function.rightInverse_surjInv hsurj).comp_eq_id, Finset.image_id, hsp]
  · rintro ⟨t, ht, hsp⟩
    have htD : ∀ x ∈ t, x ∈ D := fun x hx => by
      rw [hsp]; exact Submodule.mem_sup_right (Submodule.subset_span hx)
    have ee : (t.subtype (· ∈ D)).image D.subtype = t := by
      ext x
      simp only [Finset.mem_image, Finset.mem_subtype]
      exact ⟨fun ⟨y, hy, e⟩ => e ▸ hy, fun hx => ⟨⟨x, htD x hx⟩, hx, rfl⟩⟩
    refine ⟨(t.subtype (· ∈ D)).image q, Finset.card_image_le.trans ?_, (key _).2 (by rw [ee]; exact hsp)⟩
    rw [Finset.card_subtype]
    exact (Finset.card_filter_le _ _).trans ht

end

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → ∀ L : Submodule (𝓞 K) V, IsIntLat h L → Lat.latDetH h L ^ 2 = (discN h L : ℝ) ∧ 0 < Lat.latDetH h L ∧ (∀ j de : ℕ, Cnt.cntPrim h L j de = (primSp h L j (de ^ 2)).encard) ∧ (∀ e : ℕ, Cnt.DiscGen h L e ↔ (∃ t : Finset V, t.card ≤ e ∧ dual h L = L ⊔ Submodule.span (𝓞 K) (t : Set V))) ∧ ∀ (U : Submodule K V), Lat.latDetH h (L ⊓ U.restrictScalars (𝓞 K)) ^ 2 = (discN (hRes h U) (latIn U L) : ℝ) := by
  intro K V _ _ _ _ _ _ _ _ h hK hs hp L hL
  have hle : L ≤ dual h L := fun x hx => (dualBasic_mem_dual _ _ _).2 fun y hy => hL.2 y hy x hx
  have hn := nondeg_of_pd hp
  have h0 := (DiscOrder.main K V h hK hs hn L hL).1
  have hd : Lat.dualInH h L = dual h L := by
    unfold Lat.dualInH
    rw [hL.1.span_eq_top]
    simp
  have h1 : Lat.latDetH h L = Real.sqrt (discN h L : ℝ) := by
    rw [Lat.latDetH, hd, genIdxH_eq_idxN hle h0, discN]
  have hU : ∀ U : Submodule K V, Lat.latDetH h (L ⊓ U.restrictScalars (𝓞 K)) =
      Real.sqrt (discN (hRes h U) (latIn U L) : ℝ) := by
    intro U
    have hsU : (hRes h U).IsSymm := ⟨fun x y => hs.eq x y⟩
    have hpU : PD (hRes h U) := fun τ x hx => hp τ x fun e => hx (Subtype.ext e)
    have hI : IsIntLat (hRes h U) (latIn U L) :=
      ⟨isLattice_latIn L hL.1 U, fun x hx y hy => hL.2 x hx y hy⟩
    have n0 := (DiscOrder.main K U _ hK hsU (nondeg_of_pd hpU) _ hI).1
    rw [← idxN_dualInH h L hL.1 U] at n0 ⊢
    rw [Lat.latDetH, genIdxH_eq_idxN _ n0]
    intro x hx
    exact ⟨(dualBasic_mem_dual _ _ _).2 fun y hy => hL.2 y hy.1 x hx.1, Submodule.subset_span hx⟩
  refine ⟨by rw [h1, Real.sq_sqrt (Nat.cast_nonneg _)], ?_, fun j de => ?_, discGen_iff h L hle,
    fun U => by rw [hU, Real.sq_sqrt (Nat.cast_nonneg _)]⟩
  · rw [h1]
    exact Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero h0)
  · have hinj : Function.Injective fun U : Submodule K V => L ⊓ U.restrictScalars (𝓞 K) :=
      Function.LeftInverse.injective (g := fun M : Submodule (𝓞 K) V => Submodule.span K (M : Set V))
        (span_inf_eq L hL.1)
    have hsq : ∀ n : ℕ, Real.sqrt (n : ℝ) = de ↔ n = de ^ 2 := fun n => by
      rw [Real.sqrt_eq_iff_eq_sq (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      exact_mod_cast Iff.rfl
    rw [Cnt.cntPrim, ← hinj.encard_image]
    congr 1
    ext M
    constructor
    · rintro ⟨⟨-, a⟩, b, c⟩
      refine ⟨Submodule.span K (M : Set V), ⟨b, ?_⟩, a.symm⟩
      rw [← hsq, ← hU, ← a, c]
    · rintro ⟨U, ⟨a, b⟩, rfl⟩
      refine ⟨⟨inf_le_left, ?_⟩, ?_, ?_⟩
      · simp only
        rw [span_inf_eq L hL.1]
      · simp only
        rw [span_inf_eq L hL.1, a]
      · simp only
        rw [hU, hsq, b]

end GlobalTheory.Mass.DetAgree
