import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.StalkDom
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.GenDense
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.GenRange
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.ClopenExt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.CoverCut
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.ResEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.LiesCut
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.FEtCut
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.CorrCut
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.PtIdCut

noncomputable section

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open GlobalTheory.GalV (HTower)

namespace UpperTheory.Gal.Int.Geo

open Cut

private theorem cut {k L O : Type} [Field k] [Field L] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O k]
    [IsFractionRing O k] {H : HTower k} {θ : H.Γ → L} (C : Cover H θ O) :
    ∃ (C' : Cover H θ O) (j : C'.Y ⟶ C.Y), Part j ∧ C'.p = j ≫ C.p ∧ C'.π ≫ j = C.π ∧ C'.Onto ∧
      ∀ y ∈ Set.range j, (C.p y).asIdeal = ⊥ → y ∈ Set.range C.π := by
  haveI := C.finπ
  haveI := C.etπ
  have hU : IsClopen (Set.range (pullback.lift C.π H.q C.ov)) :=
    ⟨(Scheme.Hom.isClosedMap _).isClosed_range, (Scheme.Hom.isOpenMap _).isOpen_range⟩
  obtain ⟨V, hVc, hVpre⟩ := clopenExt O k C.Y C.p C.smooth _ hU
  obtain ⟨C', j, hj, hrj, hp, hπ, hon⟩ := coverCut k L O H θ C V hVc hVpre
  refine ⟨C', j, hj, hp, hπ, hon, ?_⟩
  intro y hy hgen
  have hyV : y ∈ (V : Set C.Y) := hrj ▸ hy
  have hy' : y ∈ Set.range (pullback.fst C.p (gen O k)) := by
    rw [(genRange O k C.Y C.p).1]
    exact hgen
  obtain ⟨z, rfl⟩ := hy'
  have hz : z ∈ Set.range (pullback.lift C.π H.q C.ov) := by
    rw [← hVpre]
    exact hyV
  obtain ⟨x, rfl⟩ := hz
  exact ⟨x, by rw [← Scheme.Hom.comp_apply, pullback.lift_fst]⟩

private theorem over_eq {Y' Y T' T S : Scheme.{0}} {j : Y' ⟶ Y} {s t : T ⟶ Y} {i : T' ⟶ T} {s' t' : T' ⟶ Y'}
    (h : Res j s t i s' t') {p : Y ⟶ S} (e : t ≫ p = s ≫ p) : t' ≫ j ≫ p = s' ≫ j ≫ p := by
  rw [← Category.assoc, h.et, Category.assoc, e, ← Category.assoc, ← h.es, Category.assoc]

private theorem mem_range_of_lies_of_mem_range_of_asIdeal_bot {k L O : Type} [Field k] [Field L] [CommRing O] [Algebra O k] {H : HTower k}
    {θ : H.Γ → L} {C C' : Cover H θ O} {j : C'.Y ⟶ C.Y} (hj : Part j) (hπ : C'.π ≫ j = C.π)
    (hgen : ∀ y ∈ Set.range j, (C.p y).asIdeal = ⊥ → y ∈ Set.range C.π) {g : H.Γ} {T : Scheme}
    {s t : T ⟶ C.Y} {m : ℕ} (hl : C.Lies g s t m) (x : T) (hx : s x ∈ Set.range j)
    (hxg : (C.p (s x)).asIdeal = ⊥) : t x ∈ Set.range j := by
  obtain ⟨z, hz⟩ := (liesCut k L O H θ C C' j hj hπ g T s t m hl).1 x (hgen _ hx hxg)
  exact ⟨C'.π z, by rw [← Scheme.Hom.comp_apply, hπ, hz]⟩

private theorem mem_range_of_fEt_of_lies_of_mem_range {k L O : Type} [Field k] [Field L] [CommRing O] [IsDomain O] [Algebra O k]
    {H : HTower k} {θ : H.Γ → L} {C C' : Cover H θ O} {j : C'.Y ⟶ C.Y} (hj : Part j)
    (hπ : C'.π ≫ j = C.π) (hgen : ∀ y ∈ Set.range j, (C.p y).asIdeal = ⊥ → y ∈ Set.range C.π)
    {g : H.Γ} {T : Scheme} {s t : T ⟶ C.Y} {d m : ℕ} (hs : FEt s d) (hl : C.Lies g s t m) :
    ∀ x, s x ∈ Set.range j → t x ∈ Set.range j := by
  haveI : Etale s := hs.2.1
  haveI := C.smooth
  haveI := hj.op
  have hD := genDense O T (s ≫ C.p) inferInstance
  by_contra hne
  push_neg at hne
  obtain ⟨x, hx, hxt⟩ := hne
  have hopen : IsOpen ({x | s x ∈ Set.range j} ∩ {x | t x ∈ Set.range j}ᶜ) :=
    IsOpen.inter (j.isOpenEmbedding.isOpen_range.preimage s.continuous)
      (hj.cl.preimage t.continuous).isOpen_compl
  obtain ⟨y, ⟨hy1, hy2⟩, hyg⟩ := hD.inter_open_nonempty _ hopen ⟨x, hx, hxt⟩
  rw [Set.mem_setOf_eq, Scheme.Hom.comp_apply] at hyg
  exact hy2 (mem_range_of_lies_of_mem_range_of_asIdeal_bot hj hπ hgen hl y hy1 hyg)

private theorem asIdeal_eq_bot_of_mem_basicOpen_natCast {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {Y : Scheme}
    (q : Y ⟶ Spec (CommRingCat.of (Ow w))) (p : ℕ) (hp : (p : 𝓞 E) ∈ w.asIdeal) (y : Y)
    (hy : y ∈ Y.basicOpen (p : Γ(Y, ⊤))) : (q y).asIdeal = ⊥ := by
  have hmax : (p : Ow w) ∈ IsLocalRing.maximalIdeal (Ow w) := by
    rw [ValuationSubring.valuation_lt_one_iff]
    have h1 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) w (p : 𝓞 E)).2 hp
    have h2 := (Valuation.isEquiv_iff_val_lt_one.1
      (Valuation.isEquiv_valuation_valuationSubring (w.valuation E))).1 h1
    convert h2 using 2
    push_cast
    rfl
  have h3 : (p : Γ(Y, ⊤)) =
      (q.appTop) ((Scheme.ΓSpecIso (CommRingCat.of (Ow w))).inv (p : Ow w)) := by
    simp
  rw [h3, ← Scheme.Hom.preimage_basicOpen_top] at hy
  have h5 : q y ∈ ((Spec (CommRingCat.of (Ow w))).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of (Ow w))).inv (p : Ow w)) : Set _) := hy
  rw [basicOpen_eq_of_affine] at h5
  have h6 : (p : Ow w) ∉ (q y).asIdeal := h5
  by_contra hne
  have hM := IsLocalRing.eq_maximalIdeal ((q y).isPrime.isMaximal hne)
  exact h6 (hM ▸ hmax)

theorem cutStep_holds : CutStep := by
  intro E _ _ L _ H θ _ w
  constructor
  · rintro ⟨C, hC⟩
    obtain ⟨C', j, hj, hp, hπ, hon, hgen⟩ := cut C
    refine ⟨C', hon, fun g => ?_⟩
    obtain ⟨T, s, t, d, m, hs, ht, hl⟩ := hC g
    obtain ⟨T', i, s', t', hR⟩ := resEx _ _ _ j s t hj
    have hst := mem_range_of_fEt_of_lies_of_mem_range hj hπ hgen hs hl
    refine ⟨T', s', t', d, m, fEtCut _ _ _ _ j s t i s' t' d hj hR hst hs, ?_, ?_⟩
    · rw [hp]
      exact over_eq hR ht
    · exact (liesCut _ _ _ H θ C C' j hj hπ g T s t m hl).2 T' i s' t' hR
  · rintro n ϑ ⟨C, p, f, hpr, hpw, hnorm, ϖ, T, γ, m, hirr, hpt, hT⟩
    obtain ⟨C', j, hj, hp, hπ, hon, hgen⟩ := cut C
    have hres := fun a => resEx _ _ _ j (T a).p (T a).r hj
    choose Z i s' t' hR using hres
    have hcond : ∀ a (x : (T a).Z), (T a).p x ∈ Set.range j →
        (T a).p x ∈ C.Y.basicOpen (p : Γ(C.Y, ⊤)) → (T a).r x ∈ Set.range j :=
      fun a x hx hb => mem_range_of_lies_of_mem_range_of_asIdeal_bot hj hπ hgen (hT a).2.1 x hx (asIdeal_eq_bot_of_mem_basicOpen_natCast w C.p p hpw _ hb)
    have hc := fun a => corrCut p _ _ _ j (T a) (i a) (s' a) (t' a) hj (hR a) (hcond a)
    let T' : Fin (n + 1) → crystallineComparison.Corr p C'.Y := fun a =>
      ⟨Z a, s' a, t' a, (T a).d, (hc a).1, (hc a).2.1, (hc a).2.2⟩
    refine ⟨C', p, f, hpr, hpw, hnorm, hon, ϖ, T', γ, m, hirr, ?_, fun a => ⟨?_, ?_, (hT a).2.2⟩⟩
    · have := ptIdCut p (p ^ f) n _ _ j (crystallineComparison.fn C.p ϖ) T T' i hj hR hcond hpt
      convert this using 2
      rw [hp]
      simp only [crystallineComparison.fn, Scheme.Hom.comp_appTop]
      rfl
    · show t' a ≫ C'.p = s' a ≫ C'.p
      rw [hp]
      exact over_eq (hR a) (hT a).1
    · exact (liesCut _ _ _ H θ C C' j hj hπ (γ a) _ _ _ (m a) (hT a).2.1).2 _ (i a) _ _ (hR a)

end UpperTheory.Gal.Int.Geo
