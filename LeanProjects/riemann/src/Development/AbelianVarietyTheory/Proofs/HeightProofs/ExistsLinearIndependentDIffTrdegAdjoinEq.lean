import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.TrdegPf
import ReciprocityTheory.SemistableReduction.AlgAll
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent

namespace GlobalTheory

open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

open NumberField in
open scoped TensorProduct in
open scoped IntermediateField.algebraAdjoinAdjoin in

theorem _root_.GlobalTheory.exists_linearIndependent_D_iff_trdeg_adjoin_eq {K Ω κ : Type} [Field K] [CharZero K]
    [Field Ω] [Algebra K Ω] {D : ℕ} (hD : Algebra.trdeg K Ω = D) (x : κ → Ω) :
    (∃ J : Fin D → κ, LinearIndependent Ω fun k => KaehlerDifferential.D K Ω (x (J k))) ↔
      Algebra.trdeg K (IntermediateField.adjoin K (Set.range x)) = D := by
  constructor
  · rintro ⟨J, hJ⟩
    have hind : AlgebraicIndependent K fun k => x (J k) := _root_.ReciprocityTheory.ChartRestriction.G.AR.differentialIndependence K Ω D (fun k => x (J k)) hJ
    let y : Fin D → IntermediateField.adjoin K (Set.range x) :=
      fun k => ⟨x (J k), IntermediateField.subset_adjoin K _ ⟨J k, rfl⟩⟩
    have hy : AlgebraicIndependent K y :=
      AlgebraicIndependent.of_comp (IntermediateField.adjoin K (Set.range x)).val hind
    apply le_antisymm
    · rw [← hD]
      exact trdeg_le_of_injective _ (IntermediateField.adjoin K (Set.range x)).val.injective
    · simpa using hy.cardinalMk_le_trdeg
  · intro h
    set L := IntermediateField.adjoin K (Set.range x) with hL
    set s : Set L := Subtype.val ⁻¹' Set.range x with hs
    have hmem : ∀ z : L, z ∈ IntermediateField.adjoin K s := by
      intro z
      have hle : L ≤ (IntermediateField.adjoin K s).map L.val := by
        refine IntermediateField.adjoin_le_iff.mpr ?_
        rintro _ ⟨i, rfl⟩
        exact ⟨⟨x i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩,
          IntermediateField.subset_adjoin K _ ⟨i, rfl⟩, rfl⟩
      obtain ⟨m, hm, hmz⟩ := hle z.2
      rwa [show m = z from Subtype.ext hmz] at hm
    haveI : Algebra.IsAlgebraic (Algebra.adjoin K s) L := ⟨fun z => by
      have hz := isAlgebraic_algebraMap (R := IntermediateField.adjoin K s) (A := L) ⟨z, hmem z⟩
      exact IntermediateField.isAlgebraic_adjoin_iff.mp hz⟩
    obtain ⟨t, hts, ht⟩ := exists_isTranscendenceBasis_subset (R := K) (A := L) s
    have hcard : Cardinal.mk t = D := by rw [ht.cardinalMk_eq_trdeg, h]
    obtain ⟨e⟩ := Cardinal.mk_eq_nat_iff.mp hcard
    let v : t → Ω := fun z => ((z : L) : Ω)
    have hv : AlgebraicIndependent K v := ht.1.map' (f := L.val) Subtype.val_injective
    haveI : Finite t := Finite.of_equiv _ e.symm
    have hvb : IsTranscendenceBasis K v := by
      refine hv.isTranscendenceBasis_of_lift_trdeg_le ?_ ?_
      · rw [hD]; exact Cardinal.nat_lt_aleph0 D
      · rw [hD, hcard]
    haveI := hvb.isAlgebraic_field
    haveI : Algebra.IsSeparable (IntermediateField.adjoin K (Set.range v)) Ω :=
      Algebra.IsAlgebraic.isSeparable_of_perfectField
    obtain ⟨b, hb⟩ := _root_.GlobalTheory.exists_basis_kaehler_of_algebraicIndependent hv
    have hex : ∀ k : Fin D, ∃ i, x i = (((e.symm k : t) : L) : Ω) := fun k => hts (e.symm k).2
    choose J hJ using hex
    refine ⟨J, ?_⟩
    have hfun : (fun k => KaehlerDifferential.D K Ω (x (J k))) = b ∘ e.symm := by
      funext k
      rw [Function.comp_apply, hb, hJ k]
    rw [hfun]
    exact b.linearIndependent.comp _ e.symm.injective

section Ratios

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]

end Ratios

open NumberField in
private theorem sImg_eq_sImage_finSuccEquiv_reindex {Ω : Type} [Field Ω] {D N : ℕ} (j : Fin (N + 1))
    (x : Fin N → Ω) (p : _root_.ReciprocityTheory.ChartRestriction.G.T0.TVar D N) :
    _root_.ReciprocityTheory.ChartRestriction.G.T0.sImg j x p = _root_.ReciprocityTheory.MultiplicativeHeights.sImage x (p.1, ((finSuccEquiv' j).trans (finSuccEquiv N).symm) p.2) := by
  rcases p with ⟨a, i⟩
  unfold _root_.ReciprocityTheory.ChartRestriction.G.T0.sImg _root_.ReciprocityTheory.MultiplicativeHeights.sImage
  rcases Fin.eq_self_or_eq_succAbove j i with rfl | ⟨k, rfl⟩
  · simp only [Equiv.trans_apply, finSuccEquiv'_at, finSuccEquiv_symm_none, Fin.cases_zero]
    exact congrArg _ (Fin.insertNth_apply_same i _ _)
  · simp only [Equiv.trans_apply, finSuccEquiv'_succAbove, finSuccEquiv_symm_some, Fin.cases_succ]
    exact congrArg _ (Fin.insertNth_apply_succAbove j _ _ k)

open NumberField in

theorem _root_.GlobalTheory.differentials_iff_trdegD_and_genericSection : ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] (WT : Type) [AddCommGroup WT] (A : ι → Type) [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)] [∀ c, Algebra (𝓞 K) (A c)] (_𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : _root_.ReciprocityTheory.ChartRestriction.G.T0.Data K ι Ω WT A), ∀ c : ι, (⊤ : IntermediateField K (Ω c)).FG → Algebra.trdeg K (Ω c) = d.D → d.w (d.jc c) c ≠ 0 → ((∃ J : Fin d.D → Fin d.N, LinearIndependent (Ω c) fun k => KaehlerDifferential.D K (Ω c) (d.x c (J k))) ↔ _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.TrdegD d c) ∧ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.TrdegD d c → Function.Injective (d.sH c) ∧ FiniteDimensional (d.KT c) (_root_.ReciprocityTheory.ChartRestriction.G.T0.OmS (Ω c) d.D d.N)) := by
  intro K _ _ ι _ Ω _ _ WT _ A _ _ _ _ _𝒜 d c hfg hD hw
  have hadj : IntermediateField.adjoin K
      (Set.range fun j => _root_.ReciprocityTheory.ChartRestriction.G.T0.ratio (d.w j c) (d.w (d.jc c) c)) =
      IntermediateField.adjoin K (Set.range (d.x c)) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨j, rfl⟩
      rcases Fin.eq_self_or_eq_succAbove (d.jc c) j with rfl | ⟨k, rfl⟩
      · show _root_.ReciprocityTheory.ChartRestriction.G.T0.ratio (d.w (d.jc c) c) (d.w (d.jc c) c) ∈ _
        rw [_root_.ReciprocityTheory.ChartRestriction.G.T0.ValuationResidueLemmas.ratio_eq hw (one_smul _ _).symm]
        exact one_mem _
      · exact IntermediateField.subset_adjoin K _ ⟨k, rfl⟩
    · apply IntermediateField.adjoin.mono
      rintro _ ⟨k, rfl⟩
      exact ⟨(d.jc c).succAbove k, rfl⟩
  have htr : _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.TrdegD d c ↔ Algebra.trdeg K (IntermediateField.adjoin K (Set.range (d.x c))) = d.D := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.TrdegD
    rw [hadj]
  have key := _root_.GlobalTheory.exists_linearIndependent_D_iff_trdeg_adjoin_eq hD (d.x c)
  refine ⟨key.trans htr.symm, fun hT => ?_⟩
  obtain ⟨hind, hfin⟩ := _root_.ReciprocityTheory.MultiplicativeHeights.Closed.fieldOfS K (Ω c) d.D d.N (d.x c) hfg hD (key.mpr (htr.mp hT))
  let e := (finSuccEquiv' (d.jc c)).trans (finSuccEquiv d.N).symm
  let σ : _root_.ReciprocityTheory.ChartRestriction.G.T0.TVar d.D d.N → Fin (d.D + 1) × Fin (d.N + 1) := fun p => (p.1, e p.2)
  have hσ : Function.Bijective σ := ((Equiv.refl (Fin (d.D + 1))).prodCongr e).bijective
  have hcomp : _root_.ReciprocityTheory.ChartRestriction.G.T0.sImg (d.jc c) (d.x c) = _root_.ReciprocityTheory.MultiplicativeHeights.sImage (d.x c) ∘ σ :=
    funext fun p => sImg_eq_sImage_finSuccEquiv_reindex _ _ p
  constructor
  · unfold _root_.ReciprocityTheory.ChartRestriction.G.T0.Data.sH _root_.ReciprocityTheory.ChartRestriction.G.T0.sHom
    rw [hcomp]
    exact hind.comp σ hσ.1
  · have hrange : Set.range (_root_.ReciprocityTheory.ChartRestriction.G.T0.sImg (d.jc c) (d.x c)) = Set.range (_root_.ReciprocityTheory.MultiplicativeHeights.sImage (D := d.D) (d.x c)) := by
      rw [hcomp, Set.range_comp, hσ.2.range_eq, Set.image_univ]
    have hKT : d.KT c = IntermediateField.adjoin K (Set.range (_root_.ReciprocityTheory.MultiplicativeHeights.sImage (D := d.D) (d.x c))) := by
      unfold _root_.ReciprocityTheory.ChartRestriction.G.T0.Data.KT
      rw [hrange]
    rw [hKT]
    exact hfin

end GlobalTheory
