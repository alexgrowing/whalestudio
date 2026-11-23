import Mathlib

open Complex Filter Topology Set

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

variable (L : PeriodPair)

instance isClosed_lattice_toAddSubgroup : IsClosed (L.lattice.toAddSubgroup : Set ℂ) :=
  L.isClosed_lattice

abbrev Torus : Type := ℂ ⧸ L.lattice.toAddSubgroup

abbrev Torus.mk (z : ℂ) : Torus L := QuotientAddGroup.mk z

lemma Torus.mk_add {z l : ℂ} (hl : l ∈ L.lattice) : Torus.mk L (z + l) = Torus.mk L z :=
  QuotientAddGroup.mk_add_of_mem z hl

lemma Torus.mk_eq_mk_iff {z w : ℂ} : Torus.mk L z = Torus.mk L w ↔ z - w ∈ L.lattice := by
  rw [Torus.mk, Torus.mk, QuotientAddGroup.eq_iff_sub_mem]
  rfl

lemma Torus.mk_surjective : Function.Surjective (Torus.mk L) :=
  QuotientAddGroup.mk_surjective

lemma Torus.continuous_mk : Continuous (Torus.mk L) :=
  continuous_quot_mk

def IsPeriodic {E : Type*} (f : ℂ → E) : Prop :=
  ∀ z : ℂ, ∀ l ∈ L.lattice, f (z + l) = f z

def IsEllipticFunction (f : ℂ → ℂ) : Prop :=
  Meromorphic f ∧ IsPeriodic L f

variable {L}

lemma IsPeriodic.sub {E : Type*} {f : ℂ → E} (hf : IsPeriodic L f) (z : ℂ) {l : ℂ}
    (hl : l ∈ L.lattice) : f (z - l) = f z := by
  simpa using (hf (z - l) l hl).symm

lemma IsPeriodic.comp_add {E : Type*} {f : ℂ → E} (hf : IsPeriodic L f) {l : ℂ}
    (hl : l ∈ L.lattice) : (fun z ↦ f (z + l)) = f :=
  funext fun z ↦ hf z l hl

lemma IsPeriodic.eq_of_mk_eq {E : Type*} {f : ℂ → E} (hf : IsPeriodic L f) {z w : ℂ}
    (h : Torus.mk L z = Torus.mk L w) : f z = f w := by
  have hzw := (Torus.mk_eq_mk_iff L).1 h
  simpa using hf w (z - w) hzw

variable (L)

instance : CompactSpace (Torus L) := by
  have h := IsZLattice.isCompact_range_of_periodic L.lattice (Torus.mk L) (Torus.continuous_mk L)
    (fun z w hw ↦ Torus.mk_add L hw)
  rw [(Torus.mk_surjective L).range_eq] at h
  exact isCompact_univ_iff.mp h

instance : T2Space (Torus L) := inferInstance

instance : IsTopologicalAddGroup (Torus L) := inferInstance

def fundamentalCompact : Set ℂ := closure (ZSpan.fundamentalDomain L.basis)

lemma isCompact_fundamentalCompact : IsCompact (fundamentalCompact L) :=
  (ZSpan.fundamentalDomain_isBounded L.basis).isCompact_closure

lemma exists_sub_mem_fundamentalCompact (z : ℂ) :
    ∃ l ∈ L.lattice, z - l ∈ fundamentalCompact L := by
  refine ⟨ZSpan.floor L.basis z, ?_, subset_closure ?_⟩
  · rw [L.lattice_eq_span_range_basis]
    exact (ZSpan.floor L.basis z).2
  · rw [← ZSpan.fract_apply]
    exact ZSpan.fract_mem_fundamentalDomain _ _

theorem isCompact_range_of_isPeriodic {E : Type*} [TopologicalSpace E] {f : ℂ → E}
    (hc : Continuous f) (hf : IsPeriodic L f) : IsCompact (range f) :=
  IsZLattice.isCompact_range_of_periodic L.lattice f hc fun z w hw ↦ hf z w hw

theorem eq_of_differentiable_of_isPeriodic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} (hd : Differentiable ℂ f) (hf : IsPeriodic L f) (z w : ℂ) : f z = f w :=
  hd.apply_eq_apply_of_bounded (isCompact_range_of_isPeriodic L hd.continuous hf).isBounded z w

variable {L}

lemma IsPeriodic.analyticAt_add_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} (hf : IsPeriodic L f) {l : ℂ} (hl : l ∈ L.lattice) (z : ℂ) :
    AnalyticAt ℂ f (z + l) ↔ AnalyticAt ℂ f z := by
  constructor
  · intro h
    have : AnalyticAt ℂ (f ∘ fun w ↦ w + l) z := AnalyticAt.comp (g := f) h (by fun_prop)
    rwa [Function.comp_def, hf.comp_add hl] at this
  · intro h
    have h' : AnalyticAt ℂ f ((z + l) - l) := by simpa using h
    have : AnalyticAt ℂ (f ∘ fun w ↦ w - l) (z + l) := AnalyticAt.comp (g := f) h' (by fun_prop)
    have e : (fun w ↦ f (w - l)) = f := funext fun w ↦ hf.sub w hl
    rwa [Function.comp_def, e] at this

lemma IsPeriodic.meromorphicOrderAt_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} (hf : IsPeriodic L f) {l : ℂ} (hl : l ∈ L.lattice) (z : ℂ) :
    meromorphicOrderAt f (z + l) = meromorphicOrderAt f z := by
  have := meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt (f := f) (x := z) (c := l)
  rw [hf.comp_add hl] at this
  exact this.symm

def singularSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : ℂ → E) : Set ℂ :=
  {z | ¬ AnalyticAt ℂ f z}

def poles {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : ℂ → E) : Set ℂ :=
  {z | meromorphicOrderAt f z < 0}

theorem finite_inter_singularSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} (hf : Meromorphic f) {K : Set ℂ} (hK : IsCompact K) :
    (K ∩ singularSet f).Finite := by
  have h := hK.finite_sdiff_of_mem_codiscreteWithin
    ((hf.meromorphicOn (s := K)).analyticAt_mem_codiscreteWithin)
  exact h.subset fun z hz ↦ ⟨hz.1, hz.2⟩

variable (L)

theorem finite_image_singularSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {f : ℂ → E} (hf : Meromorphic f) (hp : IsPeriodic L f) :
    (Torus.mk L '' singularSet f).Finite := by
  refine ((finite_inter_singularSet hf (isCompact_fundamentalCompact L)).image
    (Torus.mk L)).subset ?_
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨l, hl, hzl⟩ := exists_sub_mem_fundamentalCompact L z
  refine ⟨z - l, ⟨hzl, fun h ↦ hz ?_⟩, ?_⟩
  · have := (hp.analyticAt_add_iff hl (z - l)).2 h
    simpa using this
  · exact (Torus.mk_eq_mk_iff L).2 (by simpa using L.lattice.neg_mem hl)

end Elliptic
end GroundTheory.Global
