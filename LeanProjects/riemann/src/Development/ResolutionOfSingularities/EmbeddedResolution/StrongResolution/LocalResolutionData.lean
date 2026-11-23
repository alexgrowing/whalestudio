import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.StrongResolution
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

section

variable {X : Scheme.{u}}

def SequenceOfBlowups.schemeAtIsoOfEq (s : SequenceOfBlowups X) {i j : ℕ} (h : i = j) : s.schemeAt i ≅ s.schemeAt j :=
  eqToIso (congrArg s.schemeAt h)

theorem SequenceOfBlowups.schemeAtIsoOfEq_hom_projectionToBase (s : SequenceOfBlowups X) {i j : ℕ} (h : i = j) :
    (s.schemeAtIsoOfEq h).hom ≫ s.projectionToBase j = s.projectionToBase i := by
  subst h
  simp [SequenceOfBlowups.schemeAtIsoOfEq]

end

structure BlowupSequencePullbackComparison {S T : Scheme.{u}} (φ : T ⟶ S) (s' : SequenceOfBlowups T)
    (s : SequenceOfBlowups S) where
  reindex : ℕ → ℕ
  iso : ∀ i : ℕ, i ≤ s'.length →
    (s'.schemeAt i ≅ (pullback φ (s.projectionToBase (reindex i)) : Scheme.{u}))
  reindex_length : reindex s'.length = s.length
  retention : ∀ i : ℕ, i < s.length →
    ((∃ j : ℕ, ∃ _ : j < s'.length, reindex j = i) ↔
      ∃ x, x ∈ ((s.center i).comap (pullback.snd φ (s.projectionToBase i))).support)
  iso_hom_fst : ∀ (i : ℕ) (h : i ≤ s'.length),
    (iso i h).hom ≫ pullback.fst φ (s.projectionToBase (reindex i)) = s'.projectionToBase i
  center_eq : ∀ (i : ℕ) (h : i < s'.length),
    s'.center i =
      (s.center (reindex i)).comap
        ((iso i h.le).hom ≫ pullback.snd φ (s.projectionToBase (reindex i)))

theorem nonempty_pullbackComparison_of_isPullback {S T : Scheme.{u}} (φ : T ⟶ S) (s' : SequenceOfBlowups T)
    (s : SequenceOfBlowups S) (h : IsPullbackBlowupSequence φ s' s) : Nonempty (BlowupSequencePullbackComparison φ s' s) := by
  unfold IsPullbackBlowupSequence at h
  obtain ⟨r, e, hlt, hmono, hlen, hret, hfst, hblow, hcen⟩ := h
  have hret' : ∀ i : ℕ, i < s.length →
      ((∃ j : ℕ, ∃ _ : j < s'.length, r j = i) ↔
        ∃ x, x ∈ ((s.center i).comap (pullback.snd φ (s.projectionToBase i))).support) := by
    intro i hi
    refine ⟨fun hj => (hret i hi).2 ?_, fun hx => ?_⟩
    · obtain ⟨j, hj1, hj2⟩ := hj
      exact ⟨j, hj1, hj2⟩
    · obtain ⟨j, hj1, hj2⟩ := (hret i hi).1 hx
      exact ⟨j, hj1, hj2⟩
  exact ⟨⟨r, e, hlen, hret', hfst, hcen⟩⟩

structure LocalResolutionData (k : Type u) [instFieldk : Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f] (s : SequenceOfBlowups X) where
  cover : Scheme.OpenCover.{u, u} X
  seq : ∀ i : cover.I₀, SequenceOfBlowups (cover.X i)
  isPullback : ∀ i : cover.I₀, IsPullbackBlowupSequence (cover.f i) (seq i) s
  finiteType : ∀ i : cover.I₀, LocallyOfFiniteType (cover.f i ≫ f)
  isResolution : ∀ i : cover.I₀,
    @IsStrongResolution k instFieldk (cover.X i) (cover.f i ≫ f) (finiteType i) (seq i)

attribute [instance] LocalResolutionData.finiteType

namespace LocalResolutionData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

def comparison (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    BlowupSequencePullbackComparison (d.cover.f i) (d.seq i) s :=
  (nonempty_pullbackComparison_of_isPullback (d.cover.f i) (d.seq i) s (d.isPullback i)).some

def reindex (d : LocalResolutionData k f s) (i : d.cover.I₀) : ℕ → ℕ := (d.comparison i).reindex

def schemeAtIsoPullback (d : LocalResolutionData k f s) (i : d.cover.I₀) (j : ℕ) (hj : j ≤ (d.seq i).length) :
    ((d.seq i).schemeAt j ≅ (pullback (d.cover.f i) (s.projectionToBase (d.reindex i j)) : Scheme.{u})) :=
  (d.comparison i).iso j hj

theorem reindex_length (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    d.reindex i (d.seq i).length = s.length :=
  (d.comparison i).reindex_length

theorem schemeAtIsoPullback_hom_fst (d : LocalResolutionData k f s) (i : d.cover.I₀) (j : ℕ)
    (hj : j ≤ (d.seq i).length) :
    (d.schemeAtIsoPullback i j hj).hom ≫ pullback.fst (d.cover.f i) (s.projectionToBase (d.reindex i j))
      = (d.seq i).projectionToBase j :=
  (d.comparison i).iso_hom_fst j hj

theorem localSequence_center_eq_comap (d : LocalResolutionData k f s) (i : d.cover.I₀) (j : ℕ)
    (hj : j < (d.seq i).length) :
    (d.seq i).center j =
      (s.center (d.reindex i j)).comap
        ((d.schemeAtIsoPullback i j hj.le).hom ≫
          pullback.snd (d.cover.f i) (s.projectionToBase (d.reindex i j))) :=
  (d.comparison i).center_eq j hj

theorem exists_reindex_eq_iff_exists_mem_support (d : LocalResolutionData k f s) (i : d.cover.I₀) (j : ℕ) (hj : j < s.length) :
    ((∃ l : ℕ, ∃ _ : l < (d.seq i).length, d.reindex i l = j) ↔
      ∃ x, x ∈ ((s.center j).comap (pullback.snd (d.cover.f i) (s.projectionToBase j))).support) :=
  (d.comparison i).retention j hj

theorem pullback_projectionToBase_eq_pullback_lastStructMap (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    (pullback (d.cover.f i) (s.projectionToBase (d.reindex i (d.seq i).length)) : Scheme.{u})
      = (pullback (d.cover.f i) s.lastStructMap : Scheme.{u}) := by
  have h1 : (pullback (d.cover.f i) (s.projectionToBase (d.reindex i (d.seq i).length)) : Scheme.{u})
      = (pullback (d.cover.f i) (s.projectionToBase s.length) : Scheme.{u}) :=
    congrArg (fun n : ℕ => (pullback (d.cover.f i) (s.projectionToBase n) : Scheme.{u}))
      (d.reindex_length i)
  have h2 : (pullback (d.cover.f i) (s.projectionToBase s.length) : Scheme.{u})
      = (pullback (d.cover.f i) s.lastStructMap : Scheme.{u}) :=
    congrArg (fun g : s.lastObj ⟶ X => (pullback (d.cover.f i) g : Scheme.{u}))
      s.lastStructMap_eq_projectionToBase.symm
  exact h1.trans h2

def lastObjIsoPullback (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    ((d.seq i).lastObj ≅ (pullback (d.cover.f i) s.lastStructMap : Scheme.{u})) :=
  (d.schemeAtIsoPullback i (d.seq i).length le_rfl).trans (eqToIso (d.pullback_projectionToBase_eq_pullback_lastStructMap i))

private theorem eqToHom_comp_pullback_fst {X₀ X₁ Y₀ Y₁ : Scheme.{u}} (φ : X₁ ⟶ X₀)
    {g : Y₀ ⟶ X₀} {g' : Y₁ ⟶ X₀} (hY : Y₀ = Y₁) (hg : eqToHom hY ≫ g' = g)
    (e : (pullback φ g : Scheme.{u}) = (pullback φ g' : Scheme.{u})) :
    eqToHom e ≫ pullback.fst φ g' = pullback.fst φ g := by
  subst hY
  simp only [eqToHom_refl, Category.id_comp] at hg
  subst hg
  simp

private theorem base_comp_apply {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (t : ↥A) :
    (a ≫ b).base t = b.base (a.base t) := by
  simp

theorem lastObjIsoPullback_hom_fst (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    (d.lastObjIsoPullback i).hom ≫ pullback.fst (d.cover.f i) s.lastStructMap = (d.seq i).lastStructMap := by
  have hg : eqToHom (congrArg s.schemeAt (d.reindex_length i)) ≫ s.lastStructMap
      = s.projectionToBase (d.reindex i (d.seq i).length) := by
    rw [s.lastStructMap_eq_projectionToBase]
    exact s.schemeAtIsoOfEq_hom_projectionToBase (d.reindex_length i)
  have key := eqToHom_comp_pullback_fst (d.cover.f i)
    (congrArg s.schemeAt (d.reindex_length i)) hg (d.pullback_projectionToBase_eq_pullback_lastStructMap i)
  have e1 : (d.lastObjIsoPullback i).hom
      = (d.schemeAtIsoPullback i (d.seq i).length le_rfl).hom ≫ eqToHom (d.pullback_projectionToBase_eq_pullback_lastStructMap i) := rfl
  rw [e1, Category.assoc, key, d.schemeAtIsoPullback_hom_fst i (d.seq i).length le_rfl,
    (d.seq i).lastStructMap_eq_projectionToBase]

def chartToLastObj (d : LocalResolutionData k f s) (i : d.cover.I₀) : (d.seq i).lastObj ⟶ s.lastObj :=
  (d.lastObjIsoPullback i).hom ≫ pullback.snd (d.cover.f i) s.lastStructMap

theorem chartToLastObj_eq (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    d.chartToLastObj i = (d.lastObjIsoPullback i).hom ≫ pullback.snd (d.cover.f i) s.lastStructMap :=
  rfl

theorem isOpenImmersion_chartToLastObj (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    IsOpenImmersion (d.chartToLastObj i) := by
  have : IsOpenImmersion (d.cover.f i) := d.cover.map_prop i
  rw [d.chartToLastObj_eq i]
  infer_instance

instance instIsOpenImmersionChartEmbedding (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    IsOpenImmersion (d.chartToLastObj i) :=
  d.isOpenImmersion_chartToLastObj i

theorem chartToLastObj_comp_lastStructMap (d : LocalResolutionData k f s) (i : d.cover.I₀) :
    d.chartToLastObj i ≫ s.lastStructMap = (d.seq i).lastStructMap ≫ d.cover.f i := by
  rw [d.chartToLastObj_eq i, Category.assoc, ← pullback.condition, ← Category.assoc,
    d.lastObjIsoPullback_hom_fst i]

theorem exists_chartToLastObj_eq (d : LocalResolutionData k f s) (x : ↥(s.lastObj)) :
    ∃ (i : d.cover.I₀) (y : ↥((d.seq i).lastObj)), (d.chartToLastObj i).base y = x := by
  obtain ⟨w, hw⟩ := d.cover.covers (s.lastStructMap.base x)
  obtain ⟨p, hp1, hp2⟩ := Scheme.Pullback.exists_preimage_pullback w x hw
  refine ⟨d.cover.idx (s.lastStructMap.base x), (d.lastObjIsoPullback _).inv.base p, ?_⟩
  have h2 : (d.lastObjIsoPullback (d.cover.idx (s.lastStructMap.base x))).inv ≫
      d.chartToLastObj (d.cover.idx (s.lastStructMap.base x))
      = pullback.snd (d.cover.f (d.cover.idx (s.lastStructMap.base x))) s.lastStructMap := by
    rw [d.chartToLastObj_eq, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have h3 := congrArg
    (fun m : (pullback (d.cover.f (d.cover.idx (s.lastStructMap.base x))) s.lastStructMap : Scheme.{u}) ⟶ s.lastObj
      => m.base p) h2
  simp only [base_comp_apply] at h3
  exact h3.trans hp2

private theorem exists_chartToLastObj_apply_eq (d : LocalResolutionData k f s) :
    ∀ x : ↥(s.lastObj), ∃ (i : d.cover.I₀) (y : ↥((d.seq i).lastObj)), (d.chartToLastObj i) y = x :=
  fun x => d.exists_chartToLastObj_eq x

def lastObjCover (d : LocalResolutionData k f s) : Scheme.OpenCover.{u, u} s.lastObj :=
  Scheme.Cover.mkOfCovers d.cover.I₀ (fun i => (d.seq i).lastObj)
    (fun i => d.chartToLastObj i) d.exists_chartToLastObj_apply_eq
    (fun i => d.isOpenImmersion_chartToLastObj i)

theorem preimage_smoothLocus_cover_map (d : LocalResolutionData k f s) (i : d.cover.I₀)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation (d.cover.f i ≫ f)] :
    (d.cover.f i) ⁻¹ᵁ f.smoothLocus = (d.cover.f i ≫ f).smoothLocus := by
  have : IsOpenImmersion (d.cover.f i) := d.cover.map_prop i
  exact Scheme.Hom.preimage_smoothLocus_eq _ _

theorem preimage_smoothLocusComplement_cover_map (d : LocalResolutionData k f s) (i : d.cover.I₀)
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation (d.cover.f i ≫ f)] :
    (d.cover.f i).base ⁻¹' ((smoothLocusComplement f : TopologicalSpace.Closeds ↥X) : Set ↥X)
      = ((smoothLocusComplement (d.cover.f i ≫ f) :
          TopologicalSpace.Closeds ↥(d.cover.X i)) : Set ↥(d.cover.X i)) := by
  have h : ((d.cover.f i).base ⁻¹' (f.smoothLocus : Set ↥X))
      = ((d.cover.f i ≫ f).smoothLocus : Set ↥(d.cover.X i)) :=
    congrArg (fun U : TopologicalSpace.Opens ↥(d.cover.X i) => (U : Set ↥(d.cover.X i)))
      (d.preimage_smoothLocus_cover_map i)
  show (d.cover.f i).base ⁻¹' ((f.smoothLocus : Set ↥X))ᶜ
      = ((d.cover.f i ≫ f).smoothLocus : Set ↥(d.cover.X i))ᶜ
  rw [Set.preimage_compl, h]

end LocalResolutionData

end FunctorialResolution.EmbeddedResolution

end
