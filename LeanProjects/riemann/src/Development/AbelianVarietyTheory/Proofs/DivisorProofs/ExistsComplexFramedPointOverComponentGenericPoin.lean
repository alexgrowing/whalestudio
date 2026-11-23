import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.KapFgTrdeg
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsAlgHomOfIsTranscendenceBasis

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory.AllWt (ptF)

namespace GlobalTheory.GenCxPt

open Cardinal

theorem mk_le_aleph0 (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] : #K ≤ ℵ₀ := by
  haveI : Algebra.IsAlgebraic ℚ K := Algebra.IsAlgebraic.of_finite ℚ K
  have h := Algebra.IsAlgebraic.cardinalMk_le_max ℚ K
  rw [Cardinal.mkRat, max_self] at h
  exact h

theorem transcendental_complex (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] :
    Algebra.Transcendental K ℂ := by
  rw [Algebra.transcendental_iff_not_isAlgebraic]
  intro halg
  have h := Algebra.IsAlgebraic.cardinalMk_le_max K ℂ
  rw [Cardinal.mk_complex, max_eq_right (mk_le_aleph0 K)] at h
  exact absurd h (not_le.2 Cardinal.aleph0_lt_continuum)

theorem infinite_of_isTranscendenceBasis (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] {κ : Type}
    {w : κ → ℂ} (hw : IsTranscendenceBasis K w) : Infinite κ := by
  haveI : Nonempty κ := hw.nonempty_iff_transcendental.2 (transcendental_complex K)
  have h := hw.lift_cardinalMk_eq_max_lift
  simp only [Cardinal.lift_id, Cardinal.mk_complex] at h
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  have h1 : #κ ≤ ℵ₀ := (Cardinal.lt_aleph0_of_finite κ).le
  have h2 : #K ⊔ #κ ⊔ ℵ₀ ≤ ℵ₀ := sup_le (sup_le (mk_le_aleph0 K) h1) le_rfl
  rw [← h] at h2
  exact absurd h2 (not_le.2 Cardinal.aleph0_lt_continuum)

theorem nonempty_algHom_complex (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] (L : Type) [Field L]
    [Algebra K L] (n : ℕ) (hn : Algebra.trdeg K L = n) : Nonempty (L →ₐ[K] ℂ) := by
  obtain ⟨ι, v, hv⟩ := exists_isTranscendenceBasis' K L
  obtain ⟨κ, w, hw⟩ := exists_isTranscendenceBasis' K ℂ
  haveI := infinite_of_isTranscendenceBasis K hw
  have hι : #ι < ℵ₀ := by rw [hv.cardinalMk_eq_trdeg, hn]; exact Cardinal.natCast_lt_aleph0
  haveI : Finite ι := Cardinal.lt_aleph0_iff_finite.1 hι
  have hle : #ι ≤ #κ := hι.le.trans (Cardinal.infinite_iff.1 inferInstance)
  obtain ⟨f⟩ := hle
  obtain ⟨j, -⟩ := GlobalTheory.GenericValue.exists_algHom_of_isTranscendenceBasis hv (hw.1.comp f f.injective)
  exact ⟨j⟩

end GlobalTheory.GenCxPt

namespace GlobalTheory.GenCxPt

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : A →+* B) (f : B →+* C) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem genSp_strK (Z : Comp Xo c) : genSp Z ≫ strK = spMap (algebraMap c.F (kap Z)) :=
  (Spec.map_preimage _).symm

end GlobalTheory.GenCxPt

open GlobalTheory.GenCxPt in

theorem GlobalTheory.GenCxPt.exists_frPt_ptF_eq_genPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : Comp Xo c),
    ∃ y : FrPt Xo c ℂ, ∀ s, ptF y s = genPt Z := by
  intro E _ _ _ H Dw l Xo c Z
  haveI := c.fin
  obtain ⟨e⟩ := nonempty_algHom_complex c.F (kap Z) Dw.dim ((GlobalTheory.Reg.kap_fg_trdeg E H Dw l Xo c).2 Z)
  have hsnd : spMap (e : kap Z →+* ℂ) ≫ genSp Z ≫ strK = spMap (algebraMap c.F ℂ) := by
    rw [genSp_strK, spMap_comp_spMap, AlgHom.comp_algebraMap]
  have hx : (spMap (e : kap Z →+* ℂ) ≫ xGen Z) ≫ Xo.s = sOf c ℂ := by
    rw [xGen, Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (genSp Z),
      ← Category.assoc, hsnd, sOf, spMap_comp_spMap]
  obtain ⟨y, hy⟩ := GlobalTheory.FlagTan.exists_frPt _ hx
  refine ⟨y, fun s => ?_⟩
  have hpt : ptF y = spMap (e : kap Z →+* ℂ) ≫ genSp Z := by
    apply pullback.hom_ext
    · rw [ptF, pullback.lift_fst, hy, xGen, Category.assoc]
    · rw [ptF, pullback.lift_snd, Category.assoc, ← hsnd]
  rw [hpt]
  have : (spMap (e : kap Z →+* ℂ) ≫ genSp Z) s ∈ Set.range (genSp Z) :=
    ⟨spMap (e : kap Z →+* ℂ) s, (Scheme.Hom.comp_apply _ _ _).symm⟩
  rwa [genSp, Scheme.range_fromSpecResidueField] at this
