import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

scoped instance isGalois_GB : IsGalois K (PadicAlgCl p) := by
  have : IsGalois ℚ_[p] (PadicAlgCl p) := inferInstance
  infer_instance

scoped instance : CompactSpace (GK p K) := inferInstance

scoped instance : T2Space (GK p K) := inferInstance

scoped instance : TotallyDisconnectedSpace (GK p K) := inferInstance

variable {p K L}

theorem subG_anti {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : L ≤ L') : subG p K L' ≤ subG p K L :=
  fun _ hσ x hx => hσ x (h hx)

theorem subG_eq_fixingSubgroup (h : K ≤ L) :
    subG p K L = (IntermediateField.extendScalars h).fixingSubgroup := by
  ext σ
  rw [IntermediateField.mem_fixingSubgroup_iff]
  rfl

variable (p K L) in
theorem subG_sup : subG p K (K ⊔ L) = subG p K L := by
  refine le_antisymm (subG_anti le_sup_right) fun σ hσ => ?_
  have hle : K ⊔ L ≤ (IntermediateField.fixedField (Subgroup.zpowers σ)).restrictScalars ℚ_[p] := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · exact (IntermediateField.fixedField (Subgroup.zpowers σ)).algebraMap_mem ⟨x, hx⟩
    · rw [IntermediateField.mem_restrictScalars, IntermediateField.mem_fixedField_iff]
      intro τ hτ
      exact (Subgroup.zpowers_le.2 hσ : Subgroup.zpowers σ ≤ subG p K L) hτ x hx
  intro x hx
  have := hle hx
  rw [IntermediateField.mem_restrictScalars, IntermediateField.mem_fixedField_iff] at this
  exact this σ (Subgroup.mem_zpowers σ)

theorem mem_iff_fixed (h : K ≤ L) (x : PadicAlgCl p) : x ∈ L ↔ ∀ σ ∈ subG p K L, σ x = x := by
  rw [subG_eq_fixingSubgroup h, ← IntermediateField.mem_fixedField_iff,
    InfiniteGalois.fixedField_fixingSubgroup]
  rfl

theorem subG_le_iff {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ L) :
    subG p K L' ≤ subG p K L ↔ L ≤ K ⊔ L' := by
  constructor
  · intro hle x hx
    rw [mem_iff_fixed (le_sup_left : K ≤ K ⊔ L'), subG_sup]
    exact fun σ hσ => hle hσ x hx
  · intro hle
    rw [← subG_sup p K L']
    exact subG_anti hle

variable (p K L) in
theorem isClosed_subG : IsClosed (subG p K L : Set (GK p K)) := by
  rw [← subG_sup, subG_eq_fixingSubgroup le_sup_left]
  exact InfiniteGalois.fixingSubgroup_isClosed _

theorem isOpen_subG (hL : FiniteDimensional ℚ_[p] L) : IsOpen (subG p K L : Set (GK p K)) := by
  have hint : Algebra.IsIntegral K (PadicAlgCl p) := Algebra.IsIntegral.tower_top (R := ℚ_[p])
  let b := Module.finBasis ℚ_[p] L
  have hopen : IsOpen (⋂ i, {σ : GK p K | σ (b i : PadicAlgCl p) = b i}) :=
    isOpen_iInter_of_finite fun i => stabilizer_isOpen_of_isIntegral (K := K) (b i : PadicAlgCl p)
  have heq : (subG p K L : Set (GK p K)) = ⋂ i, {σ : GK p K | σ (b i : PadicAlgCl p) = b i} := by
    ext σ
    rw [Set.mem_iInter]
    constructor
    · intro hσ i
      exact hσ _ (b i).2
    · intro hσ x hx
      have hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : PadicAlgCl p) := by
        have := congrArg L.val (b.sum_repr ⟨x, hx⟩)
        rw [map_sum] at this
        exact this.symm
      rw [hx', map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul]
      exact congrArg₂ _ ((σ.restrictScalars ℚ_[p]).commutes _) (hσ i)
  rw [heq]
  exact hopen

theorem finiteIndex_subG (hL : FiniteDimensional ℚ_[p] L) : (subG p K L).FiniteIndex := by
  have : Finite (GK p K ⧸ subG p K L) := Subgroup.quotient_finite_of_isOpen _ (isOpen_subG hL)
  exact Subgroup.finiteIndex_of_finite_quotient

theorem degLK_eq_finrank (h : K ≤ L) :
    degLK p K L = Module.finrank K (IntermediateField.extendScalars h) := by
  rw [IntermediateField.finrank_eq_fixingSubgroup_index, ← subG_eq_fixingSubgroup h]
  rfl

theorem finrank_eq_degLK_mul (h : K ≤ L) (hL : FiniteDimensional ℚ_[p] L) :
    Module.finrank ℚ_[p] L = degLK p K L * Module.finrank ℚ_[p] K := by
  rw [degLK_eq_finrank h, mul_comm]
  exact (Module.finrank_mul_finrank ℚ_[p] K (IntermediateField.extendScalars h)).symm

theorem degLK_pos (hL : FiniteDimensional ℚ_[p] L) : 0 < degLK p K L :=
  Nat.pos_of_ne_zero (finiteIndex_subG hL).index_ne_zero

theorem range_galois_restriction (h : K ≤ L) : (resGK h).range = subG p K L := by
  ext σ
  constructor
  · rintro ⟨τ, rfl⟩ x hx
    exact τ.commutes ⟨x, hx⟩
  · intro hσ
    exact ⟨{ σ.toRingEquiv with commutes' := fun x => hσ x.1 x.2 }, rfl⟩

theorem degLK_mul {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ L) (h' : L ≤ L') :
    degLK p K L' = degLK p K L * degLK p L L' := by
  have hc : (subG p K L').comap (resGK h) = subG p L L' := rfl
  show (subG p K L').index = (subG p K L).index * (subG p L L').index
  rw [← hc, Subgroup.index_comap, range_galois_restriction, mul_comm,
    Subgroup.relIndex_mul_index (subG_anti h')]

theorem exists_subG_eq (U : Subgroup (GK p K)) (hU : IsClosed (U : Set (GK p K))) :
    ∃ L : IntermediateField ℚ_[p] (PadicAlgCl p), K ≤ L ∧ subG p K L = U := by
  have h : K ≤ (IntermediateField.fixedField U).restrictScalars ℚ_[p] :=
    fun x hx => (IntermediateField.fixedField U).algebraMap_mem ⟨x, hx⟩
  refine ⟨_, h, ?_⟩
  rw [subG_eq_fixingSubgroup h]
  exact InfiniteGalois.fixingSubgroup_fixedField ⟨U, hU⟩

theorem exists_subG_eq_of_isOpen (hK : FiniteDimensional ℚ_[p] K) (U : Subgroup (GK p K))
    (hU : IsOpen (U : Set (GK p K))) :
    ∃ L : IntermediateField ℚ_[p] (PadicAlgCl p), K ≤ L ∧ FiniteDimensional ℚ_[p] L ∧ subG p K L = U := by
  obtain ⟨L, h, hL⟩ := exists_subG_eq U (Subgroup.isClosed_of_isOpen U hU)
  refine ⟨L, h, ?_, hL⟩
  have hfd : FiniteDimensional K (IntermediateField.extendScalars h) := by
    rw [← InfiniteGalois.isOpen_iff_finite, ← subG_eq_fixingSubgroup h, hL]
    exact hU
  exact FiniteDimensional.trans ℚ_[p] K (IntermediateField.extendScalars h)

theorem subG_normal_iff (h : K ≤ L) : (subG p K L).Normal ↔ ∀ (σ : GK p K), ∀ x ∈ L, σ x ∈ L := by
  refine ⟨fun hn σ x hx => ?_, subG_normal_of_stable⟩
  rw [mem_iff_fixed h]
  intro τ hτ
  have h1 : (σ⁻¹ * τ * σ⁻¹⁻¹) x = x := hn.conj_mem τ hτ σ⁻¹ x hx
  rw [inv_inv] at h1
  have h2 : σ ((σ⁻¹ * τ * σ) x) = τ (σ x) := by
    show (σ * (σ⁻¹ * τ * σ)) x = (τ * σ) x
    rw [mul_assoc, mul_inv_cancel_left]
  rw [← h2, h1]

theorem subG_normal_of_le {K' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ K') (hL : K ≤ L)
    (hn : (subG p K L).Normal) : (subG p K' L).Normal :=
  subG_normal_of_stable fun σ x hx => (subG_normal_iff hL).1 hn (resGK h σ) x hx

theorem resGK_injective (h : K ≤ L) : Injective (resGK h) :=
  fun _ _ hστ => AlgEquiv.ext fun x => DFunLike.congr_fun hστ x

theorem range_resGK (h : K ≤ L) : (resGK h).range = subG p K L := by
  ext σ
  constructor
  · rintro ⟨τ, rfl⟩ x hx
    exact τ.commutes ⟨x, hx⟩
  · intro hσ
    exact ⟨{ σ.toRingEquiv with commutes' := fun x => hσ x.1 x.2 }, AlgEquiv.ext fun _ => rfl⟩

theorem isClosedEmbedding_resGK (h : K ≤ L) : Topology.IsClosedEmbedding (resGK h) :=
  (resGK_continuous h).isClosedEmbedding (resGK_injective h)

theorem comap_resGK_subG (h : K ≤ L) (L' : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    (subG p K L').comap (resGK h) = subG p L L' := by
  ext σ
  exact Iff.rfl

theorem exists_equiv_subG (h : K ≤ L) : ∃ e : GK p L ≃* subG p K L, (∀ σ, (e σ : GK p K) = resGK h σ) ∧
    Continuous e ∧ Continuous e.symm := by
  have hmem : ∀ σ, resGK h σ ∈ subG p K L := fun σ => by
    rw [← range_resGK h]; exact ⟨σ, rfl⟩
  let f : GK p L →* subG p K L := (resGK h).codRestrict (subG p K L) hmem
  have hf : Bijective f := by
    refine ⟨fun a b hab => resGK_injective h (congrArg Subtype.val hab), fun τ => ?_⟩
    have hτ : τ.1 ∈ (resGK h).range := by rw [range_resGK h]; exact τ.2
    obtain ⟨σ, hσ⟩ := hτ
    exact ⟨σ, Subtype.ext hσ⟩
  have hc : Continuous (MulEquiv.ofBijective f hf) := (resGK_continuous h).subtype_mk hmem
  refine ⟨MulEquiv.ofBijective f hf, fun _ => rfl, hc, ?_⟩
  exact Continuous.continuous_symm_of_equiv_compact_to_t2 (f := (MulEquiv.ofBijective f hf).toEquiv) hc

variable (p K L) in
theorem totallySeparatedSpace_GalLK : TotallySeparatedSpace (GalLK p K L) := by
  have hint : Algebra.IsIntegral K (PadicAlgCl p) := Algebra.IsIntegral.tower_top (R := ℚ_[p])
  rw [totallySeparatedSpace_iff_exists_isClopen]
  intro x y hxy
  induction x using QuotientGroup.induction_on with
  | H a =>
  induction y using QuotientGroup.induction_on with
  | H b =>
  have hab : a⁻¹ * b ∉ subG p K L := fun hh => hxy (QuotientGroup.eq.2 hh)
  rw [mem_subG_iff] at hab
  push Not at hab
  obtain ⟨z, hz, hne⟩ := hab
  have hpre : (QuotientGroup.mk : GK p K → GalLK p K L) ⁻¹' (QuotientGroup.mk '' {g : GK p K | g z = a z}) =
      (fun g : GK p K => a⁻¹ * g) ⁻¹' (MulAction.stabilizer (GK p K) z : Set (GK p K)) := by
    ext g
    have key : ∀ g : GK p K, (a⁻¹ * g) z = z ↔ g z = a z := fun g => by
      rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq]
    constructor
    · rintro ⟨g', hg', he⟩
      have hn : g'⁻¹ * g ∈ subG p K L := QuotientGroup.eq.1 he
      have h1 : (g'⁻¹ * g) z = z := hn z hz
      rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] at h1
      exact (key g).2 (h1.trans hg')
    · intro hg
      exact ⟨g, (key g).1 hg, rfl⟩
  have hop : IsOpen (MulAction.stabilizer (GK p K) z : Set (GK p K)) :=
    stabilizer_isOpen_of_isIntegral (K := K) z
  have hcl : IsClopen (MulAction.stabilizer (GK p K) z : Set (GK p K)) :=
    ⟨Subgroup.isClosed_of_isOpen _ hop, hop⟩
  refine ⟨QuotientGroup.mk '' {g : GK p K | g z = a z}, ?_, ⟨a, rfl, rfl⟩, ?_⟩
  · rw [← QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.isClopen_preimage, hpre]
    exact hcl.preimage (continuous_const.mul continuous_id)
  · rintro ⟨g', hg', he⟩
    have hn : g'⁻¹ * b ∈ subG p K L := QuotientGroup.eq.1 he
    have h1 : (g'⁻¹ * b) z = z := hn z hz
    rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq] at h1
    apply hne
    rw [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq]
    exact h1.trans hg'

scoped instance [(subG p K L).Normal] : T2Space (GalLK p K L) :=
  have := totallySeparatedSpace_GalLK p K L
  TotallySeparatedSpace.t2Space

scoped instance [(subG p K L).Normal] : TotallyDisconnectedSpace (GalLK p K L) :=
  have := totallySeparatedSpace_GalLK p K L
  TotallySeparatedSpace.totallyDisconnectedSpace _

theorem discreteTopology_GalLK (hL : FiniteDimensional ℚ_[p] L) : DiscreteTopology (GalLK p K L) :=
  QuotientGroup.discreteTopology (isOpen_subG hL)

theorem finite_GalLK (hL : FiniteDimensional ℚ_[p] L) : Finite (GalLK p K L) :=
  have := finiteIndex_subG (K := K) hL
  Subgroup.finite_quotient_of_finiteIndex

theorem card_GalLK : Nat.card (GalLK p K L) = degLK p K L := rfl

theorem mem_multOf_iff_fixed (h : K ≤ L) (x : KbarMult p) :
    x ∈ multOf p L ↔ ∀ σ ∈ subG p K L, kbarRep p K σ x = x := by
  have h1 : x ∈ multOf p L ↔ ((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p) ∈ L := Iff.rfl
  rw [h1, mem_iff_fixed h]
  refine forall₂_congr fun σ _ => ⟨fun hx => Units.ext hx, fun hx => ?_⟩
  exact congrArg (fun y : KbarMult p => ((Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p)) hx

theorem layer_val_mem [(subG p K L).Normal] (h : K ≤ L) (x : (layer p K L).V) : x.1 ∈ multOf p L :=
  (mem_multOf_iff_fixed h x.1).2 fun σ hσ => x.2 ⟨σ, hσ⟩

theorem layer_invariant_iff [(subG p K L).Normal] (x : (layer p K L).V) :
    (∀ g, (layer p K L).rho g x = x) ↔ x.1 ∈ multOf p K := by
  refine Iff.trans ?_ (mem_multOf_iff_fixed (le_refl K) x.1).symm
  constructor
  · intro hx σ _
    exact congrArg Subtype.val (hx (QuotientGroup.mk σ))
  · intro hx g
    induction g using QuotientGroup.induction_on with
    | H σ => exact Subtype.ext (hx σ fun y hy => σ.commutes ⟨y, hy⟩)

theorem exists_resPair_factor (h : K ≤ L) :
    ∃ e : Pair ((kbarT p K).resSub (subG p K L)) (kbarT p L), (∀ n, Bijective (e.hom.H n)) ∧
      ∀ n x, (resPair h).hom.H n x =
        e.hom.H n ((Pair.res (kbarT p K) (subG p K L).subtype continuous_subtype_val).hom.H n x) := by
  obtain ⟨e, he, hc, hc'⟩ := exists_equiv_subG h
  let P : Pair ((kbarT p K).resSub (subG p K L)) (kbarT p L) :=
    { φ := e.toMonoidHom
      u := LinearMap.id
      φ_cont := hc
      u_cont := continuous_id
      equiv := fun g m => by
        show kbarRep p K (e g : GK p K) m = kbarRep p L g m
        rw [he]; rfl }
  let Q : Pair (kbarT p L) ((kbarT p K).resSub (subG p K L)) :=
    { φ := e.symm.toMonoidHom
      u := LinearMap.id
      φ_cont := hc'
      u_cont := continuous_id
      equiv := fun g m => by
        show kbarRep p L (e.symm g) m = kbarRep p K (g : GK p K) m
        have : (g : GK p K) = resGK h (e.symm g) := by rw [← he, e.apply_symm_apply]
        rw [this]; rfl }
  have hPQ : ∀ n x, P.hom.H n (Q.hom.H n x) = x := fun n x => by
    induction x using Cx.H_ind with
    | h x hx =>
      refine Cx.cls_congr _ _ (Subtype.ext (funext fun g => ?_))
      show x.1 (fun i => e.symm (e (g i))) = x.1 g
      simp
  have hQP : ∀ n x, Q.hom.H n (P.hom.H n x) = x := fun n x => by
    induction x using Cx.H_ind with
    | h x hx =>
      refine Cx.cls_congr _ _ (Subtype.ext (funext fun g => ?_))
      show x.1 (fun i => e (e.symm (g i))) = x.1 g
      simp
  refine ⟨P, fun n => ⟨LeftInverse.injective (hQP n), RightInverse.surjective (hPQ n)⟩, fun n x => ?_⟩
  induction x using Cx.H_ind with
  | h x hx =>
    refine Cx.cls_congr _ _ (Subtype.ext (funext fun g => ?_))
    show x.1 (fun i => resGK h (g i)) = x.1 (fun i => (e (g i) : GK p K))
    simp only [he]

theorem resPair_trans {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : K ≤ L) (h' : L ≤ L') (n : ℕ)
    (x : (kbarT p K).H n) :
    (resPair (h.trans h')).hom.H n x = (resPair h').hom.H n ((resPair h).hom.H n x) := by
  induction x using Cx.H_ind with
  | h x hx => rfl

end ReciprocityTheory.DiscreteGroups.LocalClassField
