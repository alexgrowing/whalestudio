import Development.EtaleCohomology.EtaleSheaves.AICAcycPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.CovPf

theorem aic_equiv {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (h : AIC A) : AIC B := by
  intro p hp hd
  obtain ⟨a, ha⟩ := h (p.map (e.symm : B →+* A)) (hp.map _) (by
    rwa [Polynomial.natDegree_map_eq_of_injective e.symm.injective])
  refine ⟨e a, ?_⟩
  rw [Polynomial.eval_map] at ha
  have h2 := congrArg (e : A →+* B) ha
  rw [Polynomial.hom_eval₂, map_zero] at h2
  have h3 : ((e : A →+* B).comp (e.symm : B →+* A)) = RingHom.id B := by ext x; simp
  rw [h3] at h2
  exact h2

theorem aicsch_of_imm {W Z : Scheme.{0}} (i : W ⟶ Z) [IsOpenImmersion i] [Nonempty W] (hZ : AICSch Z) :
    AICSch W := by
  have : IsIntegral Z := hZ.1
  refine ⟨isIntegral_of_isOpenImmersion i, fun V hV hne => ?_⟩
  have h1 := hZ.2 (i ''ᵁ V) (hV.image_of_isOpenImmersion i) (by
    obtain ⟨x, hx⟩ := hne; exact ⟨i.base x, x, hx, rfl⟩)
  exact aic_equiv (i.appIso V).commRingCatIsoToRingEquiv h1

theorem unit_of_hom {W Z : Scheme.{0}} (i : W ⟶ Z) (q : ℕ) (hq : IsUnit (q : Γ(Z, ⊤))) :
    IsUnit (q : Γ(W, ⊤)) := by
  have := hq.map (i.appTop).hom
  simpa using this

def R (P : Scheme.{0} → Prop) {Z : Scheme.{0}} (s : Set Z) : Prop :=
  ∀ (W : Scheme.{0}) (i : W ⟶ Z) [IsOpenImmersion i], Set.range i = s → Nonempty W → P W

def StepP (q : ℕ) (P : Scheme.{0} → Prop) : Prop :=
  ∀ {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) [IsOpenImmersion f] [IsOpenImmersion g],
    Set.range f ∪ Set.range g = Set.univ → AICSch X → AICSch U → AICSch V → IsUnit (q : Γ(X, ⊤)) →
    P U → P V → (Nonempty ↥(pullback f g : Scheme.{0}) → P (pullback f g)) → P X

theorem R_empty (P : Scheme.{0} → Prop) {Z : Scheme.{0}} : R P (∅ : Set Z) := by
  intro W i _ hr hW
  obtain ⟨w⟩ := hW
  have : i.base w ∈ Set.range i := ⟨w, rfl⟩
  rw [hr] at this; exact this.elim

theorem R_aff (q : ℕ) (P : Scheme.{0} → Prop) (haff : ∀ Z : Scheme.{0}, IsAffine Z → AICSch Z → IsUnit (q : Γ(Z, ⊤)) → P Z)
    {Z : Scheme.{0}} (hZ : AICSch Z) (hq : IsUnit (q : Γ(Z, ⊤))) (A : Z.Opens) (hA : IsAffineOpen A) :
    R P (A : Set Z) := by
  intro W i _ hr hW
  have e : Set.range i = Set.range A.ι := by rw [hr]; simp
  have hWa : IsAffine W := (IsAffine.iff_of_isIso (IsOpenImmersion.isoOfRangeEq i A.ι e).hom).mpr hA
  exact haff W hWa (aicsch_of_imm i hZ) (unit_of_hom i q hq)

theorem R_step (q : ℕ) (P : Scheme.{0} → Prop) (hstep : StepP q P) {Z : Scheme.{0}} (hZ : AICSch Z)
    (hq : IsUnit (q : Γ(Z, ⊤))) {s t : Set Z} (hs : IsOpen s) (ht : IsOpen t)
    (Rs : R P s) (Rt : R P t) (Rst : R P (s ∩ t)) : R P (s ∪ t) := by
  intro W i _ hr hW
  rcases s.eq_empty_or_nonempty with hs0 | ⟨x, hx⟩
  · subst hs0; exact Rt W i (by simpa using hr) hW
  rcases t.eq_empty_or_nonempty with ht0 | ⟨y, hy⟩
  · subst ht0; exact Rs W i (by simpa using hr) hW
  have subs : s ⊆ Set.range i := hr ▸ Set.subset_union_left
  have subt : t ⊆ Set.range i := hr ▸ Set.subset_union_right
  let U' : W.Opens := i ⁻¹ᵁ ⟨s, hs⟩
  let V' : W.Opens := i ⁻¹ᵁ ⟨t, ht⟩
  have rU : Set.range (U'.ι ≫ i) = s := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    exact Set.image_preimage_eq_of_subset subs
  have rV : Set.range (V'.ι ≫ i) = t := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    exact Set.image_preimage_eq_of_subset subt
  obtain ⟨w, hw⟩ := subs hx
  obtain ⟨v, hv⟩ := subt hy
  have neU : Nonempty U'.toScheme := ⟨⟨w, show i.base w ∈ s from hw ▸ hx⟩⟩
  have neV : Nonempty V'.toScheme := ⟨⟨v, show i.base v ∈ t from hv ▸ hy⟩⟩
  have hZW : AICSch W := aicsch_of_imm i hZ
  refine hstep U'.ι V'.ι ?_ hZW (aicsch_of_imm U'.ι hZW) (aicsch_of_imm V'.ι hZW) (unit_of_hom i q hq)
    (Rs _ (U'.ι ≫ i) rU neU) (Rt _ (V'.ι ≫ i) rV neV) (fun hne => Rst _ (pullback.fst U'.ι V'.ι ≫ U'.ι ≫ i) ?_ hne)
  · ext w'
    simp only [Scheme.Opens.range_ι, Set.mem_union, Set.mem_univ, iff_true]
    have : i.base w' ∈ s ∪ t := hr ▸ ⟨w', rfl⟩
    exact this
  · rw [← Category.assoc, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      IsOpenImmersion.range_pullback_to_base_of_left, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    exact Set.image_preimage_eq_of_subset (Set.inter_subset_left.trans subs)

section Topo
variable {Z : Scheme.{0}} (Q : Set Z → Prop) (hE : Q ∅) (hB : ∀ A : Z.Opens, IsAffineOpen A → Q A)
  (hS : ∀ {s t : Set Z}, IsOpen s → IsOpen t → Q s → Q t → Q (s ∩ t) → Q (s ∪ t))
include hE hB hS

theorem stage1 (A : Z.Opens) (hA : IsAffineOpen A) {ι : Type} (t : Finset ι) :
    ∀ f : ι → Γ(Z, A), Q (⋃ i ∈ t, (Z.basicOpen (f i) : Set Z)) := by
  classical
  induction t using Finset.induction_on with
  | empty => intro f; simpa using hE
  | insert a t ha ih =>
    intro f
    rw [Finset.set_biUnion_insert]
    have hI : (Z.basicOpen (f a) : Set Z) ∩ ⋃ i ∈ t, (Z.basicOpen (f i) : Set Z)
        = ⋃ i ∈ t, (Z.basicOpen (f a * f i) : Set Z) := by
      simp [Scheme.basicOpen_mul, Set.inter_iUnion₂]
    refine hS (Z.basicOpen (f a)).isOpen (isOpen_biUnion fun i _ => (Z.basicOpen (f i)).isOpen)
      (hB _ (hA.basicOpen _)) (ih f) ?_
    rw [hI]; exact ih _

theorem stage1' (A : Z.Opens) (hA : IsAffineOpen A) (S : Set Z) (hSo : IsOpen S) (hSc : IsCompact S)
    (hSA : S ⊆ A) : Q S := by
  have hch : ∀ x : S, ∃ f : Γ(Z, A), Z.basicOpen f ≤ ⟨S, hSo⟩ ∧ (x : Z) ∈ Z.basicOpen f :=
    fun x => hA.exists_basicOpen_le (V := ⟨S, hSo⟩) ⟨x.1, x.2⟩ (hSA x.2)
  choose f hf1 hf2 using hch
  obtain ⟨t, ht⟩ := hSc.elim_finite_subcover (fun x : S => (Z.basicOpen (f x) : Set Z))
    (fun x => (Z.basicOpen _).isOpen) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hf2 _⟩)
  have : S = ⋃ i ∈ t, (Z.basicOpen (f i) : Set Z) :=
    subset_antisymm ht (Set.iUnion₂_subset fun i _ => hf1 i)
  rw [this]; exact stage1 Q hE hB hS A hA t f

theorem stage2 [QuasiSeparatedSpace Z] (t : Finset Z.affineOpens) :
    Q (⋃ i ∈ t, ((i : Z.Opens) : Set Z)) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using hE
  | insert a t ha ih =>
    rw [Finset.set_biUnion_insert]
    have hTo : IsOpen (⋃ i ∈ t, ((i : Z.Opens) : Set Z)) := isOpen_biUnion fun i _ => (i : Z.Opens).isOpen
    have hTc : IsCompact (⋃ i ∈ t, ((i : Z.Opens) : Set Z)) := t.isCompact_biUnion fun i _ => i.2.isCompact
    refine hS (a : Z.Opens).isOpen hTo (hB _ a.2) ih ?_
    exact stage1' Q hE hB hS a a.2 _ ((a : Z.Opens).isOpen.inter hTo)
      (QuasiSeparatedSpace.inter_isCompact _ _ (a : Z.Opens).isOpen a.2.isCompact hTo hTc) Set.inter_subset_left

theorem stage3 [CompactSpace Z] [QuasiSeparatedSpace Z] : Q Set.univ := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun U : Z.affineOpens => ((U : Z.Opens) : Set Z))
    (fun U => (U : Z.Opens).isOpen) (fun x _ => by
      have : x ∈ (⨆ i : Z.affineOpens, (i : Z.Opens)) := by rw [iSup_affineOpens_eq_top]; trivial
      simpa [TopologicalSpace.Opens.mem_iSup] using this)
  have : (Set.univ : Set Z) = ⋃ i ∈ t, ((i : Z.Opens) : Set Z) := subset_antisymm ht (Set.subset_univ _)
  rw [this]; exact stage2 Q hE hB hS t

end Topo

theorem Cov_of : LateralTheory.E.AICAcycPf.Cov := by
  intro q P hiso haff hstep Z _ _ hZ hq
  have h := stage3 (R P (Z := Z)) (R_empty P) (fun A hA => R_aff q P haff hZ hq A hA)
    (fun hs ht Rs Rt Rst => R_step q P hstep hZ hq hs ht Rs Rt Rst)
  have : IsIntegral Z := hZ.1
  exact h Z (𝟙 Z) (by simp) inferInstance

end LateralTheory.E.CovPf
