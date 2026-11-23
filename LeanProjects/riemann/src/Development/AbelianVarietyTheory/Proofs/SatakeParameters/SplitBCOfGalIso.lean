import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCharpolyCoeffOfMatrix

noncomputable section

namespace GlobalTheory.SplitDetermines

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem spehLoc_unr (p : Part A.CG) (w : PlE H) (h : A.unr (A.locG p.π w)) : A.unr (spehLoc N A p w) := by
  unfold spehLoc
  induction List.range p.d with
  | nil => exact A.lpZero_unr w
  | cons k l ih => exact (A.unr_sum _ _).2 ⟨(A.unr_tw _ _).2 h, ih⟩

theorem isoLoc_unr_ae (P : List (Part A.CG)) : ∀ᶠ w in Filter.cofinite, A.unr (isoLoc N A P w) := by
  induction P with
  | nil => exact Filter.Eventually.of_forall fun w => A.lpZero_unr w
  | cons p P ih =>
    filter_upwards [ih, A.locG_unr_ae p.π] with w h1 h2
    exact (A.unr_sum _ _).2 ⟨spehLoc_unr N A p w h2, h1⟩

end GlobalTheory.SplitDetermines

namespace GlobalTheory.RowTie

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem splitBC_of_galIso : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N)
    (i : N.Loc), GlobalTheory.RowTie.GalIso N A i → GlobalTheory.RowTie.ChebSplit N → GlobalTheory.RowCopy.IsobaricDiscreteSelfDualStrongMultiplicityOne N A →
    GlobalTheory.RowTie.SplitBC N A i := by
  intro R H what₂ N A i hG hC hAN P P' hag Pa Pa' hB hB'
  obtain ⟨r, hrc, -, hr⟩ := hG P Pa hB
  obtain ⟨r', hrc', -, hr'⟩ := hG P' Pa' hB'
  have hfin : (placesOver H.E (N.l i)).Finite := by
    have h0 : Ideal.span {((N.l i : ℕ) : 𝓞 H.E)} ≠ 0 := by
      simpa using (Fact.out : (N.l i).Prime).ne_zero
    exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 hv
  have hinj : Function.Injective (Polynomial.map (A.iotaQC i).toRingHom) :=
    Polynomial.map_injective _ (A.iotaQC i).injective
  have hgood : ∀ᶠ w in Filter.cofinite, (w ∉ placesOver H.E (N.l i) ∧ A.unr (isoLoc N A Pa w) ∧
      A.unr (isoLoc N A Pa' w)) ∧ (IsSplitPl H w → A.locV i P w = A.locV i P' w) := by
    filter_upwards [hfin.eventually_cofinite_notMem, GlobalTheory.SplitDetermines.isoLoc_unr_ae N A Pa,
      GlobalTheory.SplitDetermines.isoLoc_unr_ae N A Pa', hag] with w h1 h2 h3 h4
    exact ⟨⟨h1, h2, h3⟩, h4⟩
  have hS := Filter.eventually_cofinite.1 hgood
  have hd := hC hS.toFinset
  have hu : ∀ w, w ∉ placesOver H.E (N.l i) → A.unr (isoLoc N A Pa w) → A.unr (A.wdOf i r w) := fun w h1 h2 => by
    rw [hr w h1]; exact (A.unr_tw _ _).2 h2
  have hu' : ∀ w, w ∉ placesOver H.E (N.l i) → A.unr (isoLoc N A Pa' w) → A.unr (A.wdOf i r' w) := fun w h1 h2 => by
    rw [hr' w h1]; exact (A.unr_tw _ _).2 h2
  have key := GlobalTheory.TypeLeaf.charpoly_eq_of_dense (G H.E N.Om) (Qbar (N.l i)) R.nV
    (fun g => ((r g : GL (Fin R.nV) (Qbar (N.l i))) : Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i))))
    (fun g => ((r' g : GL (Fin R.nV) (Qbar (N.l i))) : Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i))))
    _ hd hrc hrc' (by
      rintro g ⟨w, hw, hsp, B, hBw, hg⟩
      have hw' : ¬ ¬ ((w ∉ placesOver H.E (N.l i) ∧ A.unr (isoLoc N A Pa w) ∧
          A.unr (isoLoc N A Pa' w)) ∧ (IsSplitPl H w → A.locV i P w = A.locV i P' w)) := by
        simpa using hw
      obtain ⟨⟨h1, h2, h3⟩, h4⟩ := not_not.1 hw'
      apply hinj
      have e : A.wdOf i r w = A.wdOf i r' w := by
        rw [hr w h1, hr' w h1, hB.2.2.2.1 w hsp, hB'.2.2.2.1 w hsp, h4 hsp]
      rw [A.wdOf_frob i r w h1 hrc (hu w h1 h2) B g hBw hg,
        A.wdOf_frob i r' w h1 hrc' (hu' w h1 h3) B g hBw hg, e])
  refine hAN Pa Pa' hB.1 hB'.1 ?_
  filter_upwards [hgood] with w hw
  obtain ⟨⟨h1, h2, h3⟩, -⟩ := hw
  obtain ⟨σ, hσ⟩ := exists_isFrob (N.plOm.2 w)
  have e1 := A.wdOf_frob i r w h1 hrc (hu w h1 h2) _ σ (N.plOm.2 w) hσ
  have e2 := A.wdOf_frob i r' w h1 hrc' (hu' w h1 h3) _ σ (N.plOm.2 w) hσ
  have hm : A.frobEig (A.wdOf i r w) = A.frobEig (A.wdOf i r' w) := by
    have e3 := congrArg Polynomial.roots (e1.symm.trans ((congrArg _ (key σ)).trans e2))
    rwa [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at e3
  have e4 : A.wdOf i r w = A.wdOf i r' w := by
    rw [A.unr_eq_lpUnr _ (hu w h1 h2), hm, ← A.unr_eq_lpUnr _ (hu' w h1 h3)]
  rw [hr w h1, hr' w h1] at e4
  have e5 := congrArg (fun a => A.lpTw a (-((1 - (R.nV : ℝ)) / 2))) e4
  simpa only [A.lpTw_add, add_neg_cancel, A.lpTw_zero] using e5

end GlobalTheory.RowTie
