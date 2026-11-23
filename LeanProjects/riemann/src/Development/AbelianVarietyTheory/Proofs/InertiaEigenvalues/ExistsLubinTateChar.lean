import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.LTCrys
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ConradLocalTied
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRootOfUnityFixedDvdWeilGroupDegree
import CompanionTheory.AutomorphicTheory.PadicUnitaryWeights.CrystallineUnitParts.UnitPart
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapTop

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.LocLanglands GlobalTheory.WeilDeligne TensorProduct CompanionTheory.PRW.ACWD
open Topology

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LTExt

theorem ext_dense {W D B : Type} [Group W] [Group D] [TopologicalSpace D] [IsTopologicalGroup D]
    [CompactSpace D] [T2Space D] [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [T2Space B]
    (i : W →* D) (hi : DenseRange i) (χ : W →* B) (C : Set B) (hC : IsCompact C) (hχ : ∀ σ, χ σ ∈ C)
    (h1 : ∀ V ∈ 𝓝 (1 : B), ∃ U ∈ 𝓝 (1 : D), ∀ σ, i σ ∈ U → χ σ ∈ V) :
    ∃! κ : D →* B, Continuous κ ∧ ∀ σ, κ (i σ) = χ σ := by
  let Γ : Subgroup (D × B) := (i.prod χ).range.topologicalClosure
  have hΓ : IsCompact (Γ : Set (D × B)) := by
    refine (isCompact_univ.prod hC).of_isClosed_subset (Subgroup.isClosed_topologicalClosure _) ?_
    refine closure_minimal ?_ (isCompact_univ.prod hC).isClosed
    rintro _ ⟨σ, rfl⟩
    exact ⟨trivial, hχ σ⟩
  haveI : CompactSpace Γ := isCompact_iff_compactSpace.1 hΓ
  let p : Γ →* D := (MonoidHom.fst D B).comp Γ.subtype
  have hp : Continuous p := continuous_fst.comp continuous_subtype_val
  have hmem : ∀ σ, (i σ, χ σ) ∈ Γ := fun σ => Subgroup.le_topologicalClosure _ ⟨σ, rfl⟩
  have hinj : Function.Injective p := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨d, k⟩, hk⟩ hd
    obtain rfl : d = 1 := hd
    by_contra hne
    have hk1 : (1 : B) ≠ k := by
      rintro rfl
      exact hne rfl
    obtain ⟨V, V', hV, hV', hVV⟩ := t2_separation_nhds hk1
    obtain ⟨U, hU, H⟩ := h1 V hV
    obtain ⟨_, ⟨h2, h3⟩, σ, rfl⟩ := mem_closure_iff_nhds.1 hk _ (prod_mem_nhds hU hV')
    exact Set.disjoint_left.1 hVV (H σ h2) h3
  have hsurj : Function.Surjective p := by
    have h2 : IsClosed (Set.range p) := (isCompact_range hp).isClosed
    have h3 : Set.range i ⊆ Set.range p := by
      rintro _ ⟨σ, rfl⟩
      exact ⟨⟨_, hmem σ⟩, rfl⟩
    intro d
    exact closure_minimal h3 h2 (hi d)
  let e : Γ ≃* D := MulEquiv.ofBijective p ⟨hinj, hsurj⟩
  have he : Continuous e.symm := Continuous.continuous_symm_of_equiv_compact_to_t2 (f := e.toEquiv) hp
  refine ⟨((MonoidHom.snd D B).comp Γ.subtype).comp e.symm.toMonoidHom,
    ⟨continuous_snd.comp (continuous_subtype_val.comp he), fun σ => ?_⟩, ?_⟩
  · have : e.symm (i σ) = ⟨_, hmem σ⟩ := e.symm_apply_eq.2 rfl
    show (e.symm (i σ)).1.2 = _
    rw [this]
  · rintro κ ⟨hκ, H⟩
    refine DFunLike.coe_injective (hi.equalizer hκ (continuous_snd.comp (continuous_subtype_val.comp he)) ?_)
    funext σ
    have : e.symm (i σ) = ⟨_, hmem σ⟩ := e.symm_apply_eq.2 rfl
    show κ (i σ) = (e.symm (i σ)).1.2
    rw [this, H]

variable {E : Type} [Field E] [NumberField E]

def unitSub (w : HeightOneSpectrum (𝓞 E)) : Subgroup (w.adicCompletion E)ˣ where
  carrier := {x | IsUnitAt w x}
  one_mem' := by simp [IsUnitAt]
  mul_mem' := by
    intro x y hx hy
    simp only [IsUnitAt, Set.mem_setOf_eq] at *
    simp [hx, hy]
  inv_mem' := by
    intro x hx
    simp only [IsUnitAt, Set.mem_setOf_eq] at *
    simp [hx]

theorem compactSpace_unitSub (w : HeightOneSpectrum (𝓞 E)) : CompactSpace (unitSub w) := by
  refine isCompact_iff_compactSpace.1 (?_ : IsCompact (unitSub w : Set (w.adicCompletion E)ˣ))
  rw [Units.isEmbedding_val₀.isCompact_iff]
  have h1 : IsCompact (w.adicCompletionIntegers E : Set (w.adicCompletion E)) :=
    isCompact_iff_compactSpace.2 (Formalism.MainNotions.Gaps.LevGap.compact_Ov w)
  have h2 : Units.val '' (unitSub w : Set (w.adicCompletion E)ˣ) = {x | Valued.v x = 1} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      have hx' : Valued.v x = 1 := hx
      have h0 : x ≠ 0 := fun h => by simp [h] at hx'
      exact ⟨Units.mk0 x h0, hx', rfl⟩
  rw [h2]
  refine h1.of_isClosed_subset ?_ fun x hx => le_of_eq hx
  have h3 : IsOpen {x : w.adicCompletion E | Valued.v x < 1} := by
    simpa using Valued.isOpen_ball (w.adicCompletion E) 1
  have h4 : {x : w.adicCompletion E | Valued.v x = 1} =
      (w.adicCompletionIntegers E : Set (w.adicCompletion E)) \ {x | Valued.v x < 1} := by
    ext x
    exact ⟨fun hx => ⟨le_of_eq hx, fun h => (ne_of_lt h) hx⟩, fun hx => le_antisymm hx.1 (not_lt.1 hx.2)⟩
  rw [h4]
  exact h1.isClosed.sdiff h3

variable {Ω : Type} [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}

theorem ext_profinite (h : IsPlaceOver A w) {B : Type} [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
    [CompactSpace B] [T2Space B] [TotallyDisconnectedSpace B] (χ : Weil h →* B)
    (hI : Continuous fun τ : Ine (F := E) A => χ (ineIncl h τ)) :
    DenseRange (Subgroup.inclusion (Weil_le_Dec h)) ∧
    ∃ κ : ↥(Dec (F := E) A) →* B, Continuous κ ∧ ∀ σ : Weil h, κ (Subgroup.inclusion (Weil_le_Dec h) σ) = χ σ := by
  haveI : IsGalois E Ω := IsAlgClosure.isGalois E Ω
  haveI : CompactSpace (Dec (F := E) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  have hd : DenseRange (Subgroup.inclusion (Weil_le_Dec h)) := by
    have h1 := GlobalTheory.TameQuot.closure_frob_sup_Ine E Ω A w h
      (Subgroup.inclusion (Weil_le_Dec h) (frob h)) (isFrob_frob (h := h))
    have h2 : Subgroup.zpowers (Subgroup.inclusion (Weil_le_Dec h) (frob h)) ⊔
        (Ine (F := E) A).subgroupOf (Dec (F := E) A) ≤ (Subgroup.inclusion (Weil_le_Dec h)).range := by
      refine sup_le ?_ fun σ hσ => ⟨⟨σ, Ine_le_Weil h hσ⟩, rfl⟩
      rw [Subgroup.zpowers_le]
      exact ⟨_, rfl⟩
    intro d
    have h3 : d ∈ (⊤ : Subgroup (Dec (F := E) A)) := trivial
    rw [← h1] at h3
    exact closure_mono h2 h3
  refine ⟨hd, (ext_dense (Subgroup.inclusion (Weil_le_Dec h)) hd χ Set.univ isCompact_univ (fun _ => trivial)
    fun V hV => ?_).exists⟩
  obtain ⟨V', hVV, hV', h1V⟩ := mem_nhds_iff.1 hV
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hV' h1V
  haveI := H.toSubgroup.quotient_finite_of_isOpen H.isOpen
  obtain ⟨N, hN, -, hNH⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.index_ne_zero_of_finite (H := H.toSubgroup)) (χ (frob h))
  have hM := (H.isOpen.preimage hI).mem_nhds (x := 1) (by simpa using H.toSubgroup.one_mem)
  rw [nhds_subtype_eq_comap, Filter.mem_comap] at hM
  obtain ⟨U, hU, hUM⟩ := hM
  obtain ⟨L, hL, hLU⟩ := (krullTopology_mem_nhds_one_iff E Ω U).1 hU
  have hLo : IsOpen (L.fixingSubgroup : Set (G E Ω)) := L.fixingSubgroup_isOpen
  haveI := L.fixingSubgroup.quotient_finite_of_isOpen hLo
  obtain ⟨m, hm, -, hmL⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (Subgroup.index_ne_zero_of_finite (H := L.fixingSubgroup)) (frob h : G E Ω)
  obtain ⟨ζ, hζ⟩ := GlobalTheory.exists_fixed_dvd_deg E Ω A w h (m * N) (Nat.mul_pos hm hN)
  have hζo : IsOpen (MulAction.stabilizer (G E Ω) ζ : Set (G E Ω)) := stabilizer_isOpen_of_isIntegral ζ
  refine ⟨_, continuous_subtype_val.continuousAt.preimage_mem_nhds
    ((hLo.inter hζo).mem_nhds ⟨L.fixingSubgroup.one_mem, (MulAction.stabilizer (G E Ω) ζ).one_mem⟩),
    fun σ hσ => hVV (hH ?_)⟩
  obtain ⟨k, hk⟩ := hζ σ hσ.2
  obtain ⟨τ, hτ⟩ := exists_eq_zpow_mul deg_frob σ
  have h1 : ((frob h ^ deg σ : Weil h) : G E Ω) ∈ L.fixingSubgroup := by
    rw [hk, Subgroup.coe_zpow, Nat.cast_mul, mul_assoc, zpow_mul, zpow_natCast]
    exact L.fixingSubgroup.zpow_mem hmL _
  have h2 : (τ : G E Ω) ∈ L.fixingSubgroup := by
    have h3 : (σ : G E Ω) ∈ L.fixingSubgroup := hσ.1
    rw [hτ, Subgroup.coe_mul] at h3
    exact (L.fixingSubgroup.mul_mem_cancel_left h1).1 h3
  show χ σ ∈ H.toSubgroup
  rw [hτ, map_mul, map_zpow]
  refine H.toSubgroup.mul_mem ?_ (hUM (hLU h2))
  rw [hk, Nat.cast_mul, mul_comm (m : ℤ), mul_assoc, zpow_mul, zpow_natCast]
  exact H.toSubgroup.zpow_mem hNH _

theorem exists_lubinTate_char : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (a : Weil h →* (w.adicCompletion E)ˣ), IsLocalArtin h a → ∀ (π : (w.adicCompletion E)ˣ), IsUnifAt w π →
    ∃ c : ↥(Dec (F := E) A) →* (w.adicCompletion E)ˣ,
      Continuous (fun g => ((c g : (w.adicCompletion E)ˣ) : w.adicCompletion E)) ∧
      (∀ σ : Weil h, c ⟨σ, Weil_le_Dec h σ.2⟩ = a σ * π ^ deg σ) ∧ (∀ g, IsUnitAt w (c g)) ∧
      ∀ c' : ↥(Dec (F := E) A) →* (w.adicCompletion E)ˣ,
        Continuous (fun g => ((c' g : (w.adicCompletion E)ˣ) : w.adicCompletion E)) →
        (∀ σ : Weil h, c' ⟨σ, Weil_le_Dec h σ.2⟩ = a σ * π ^ deg σ) → c' = c := by
  intro E Ω _ _ _ _ _ w A h a ha π hπ
  let u : Weil h →* (w.adicCompletion E)ˣ := a * (zpowersHom _ π).comp (degHom h)
  have hu : ∀ σ, u σ = a σ * π ^ deg σ := fun _ => rfl
  have hunit : ∀ σ, u σ ∈ unitSub w := by
    intro σ
    have h1 := ha.ord_eq σ
    rw [GlobalTheory.SmGL.SphCompletion.ord_completion, neg_inj] at h1
    have h0 : Valued.v ((a σ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≠ 0 := by simp
    show Valued.v ((a σ * π ^ deg σ : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1
    unfold IsUnifAt at hπ
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hπ, ← WithZero.exp_log h0, h1,
      ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp
  haveI := compactSpace_unitSub w
  haveI : TotallyDisconnectedSpace (w.adicCompletion E)ˣ :=
    Units.isEmbedding_val₀.isTotallyDisconnected_range.1 (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  obtain ⟨hd, κ, hκ, hκu⟩ := ext_profinite h (u.codRestrict _ hunit) (by
    refine Continuous.subtype_mk ?_ _
    simpa [hu] using ha.cont)
  have hc : Continuous fun g => (((unitSub w).subtype.comp κ g : (w.adicCompletion E)ˣ) : w.adicCompletion E) :=
    Units.continuous_val.comp (continuous_subtype_val.comp hκ)
  have hv : ∀ σ : Weil h, (unitSub w).subtype.comp κ ⟨σ, Weil_le_Dec h σ.2⟩ = a σ * π ^ deg σ :=
    fun σ => congrArg Subtype.val (hκu σ)
  refine ⟨(unitSub w).subtype.comp κ, hc, hv, fun g => (κ g).2, fun c' hc' H => ?_⟩
  have := hd.equalizer hc' hc (funext fun σ => congrArg Units.val ((H σ).trans (hv σ).symm))
  exact MonoidHom.ext fun g => Units.ext (congrFun this g)

end GlobalTheory.LTExt

end
