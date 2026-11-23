import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepUniqueBaseChange
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeGaloisOfUnramifiedMatch
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitBCOfGalIso
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace UpperTheory.GalS

section
open Formalism.MainNotions.SumRepresentations Polynomial GlobalTheory.BaseChangeConj

theorem rep_conj : ∀ D : D7, SumRepresentations.adm5 D → ∀ (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GoodR D.nd i r → ∀ (x : D.nd.X i) (P : D.naut.AV i) (Pa : List (Formalism.BasicNotions.Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa → ∀ ρ : GE D.nd →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.ContQ D.nd i ρ → IsSSRep ρ → (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → RelW D.nd D.naut (D.naut.wdOf i ρ w) (D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2))) → ∃ Pm : GL (Fin D.R.nV) (Qbar (D.nd.l i)), ∀ g, mapRep (iotaOQ D.nd D.naut i) (r x) g = Pm⁻¹ * ρ g * Pm := by
  intro D hAN i r hr x P Pa hP hB ρ hρc hρs hwd
  obtain ⟨-, -, hCheb, hBN⟩ := hAN
  have hl : (D.nd.l i).Prime := Fact.out
  have hfin : (((placesOver D.host.E (D.nd.l i)) ∪ (D.nd.S i : Set _)) ∪ (D.nd.Q i : Set _)).Finite :=
    ((placesOver_finite D.host.E (D.nd.l i) hl.ne_zero).union (D.nd.S i).finite_toSet).union
      (D.nd.Q i).finite_toSet
  have hdense := hCheb _ hfin

  have hfrob : ∀ g ∈ {σ : G D.host.E D.nd.Om | ∃ w ∉ (((placesOver D.host.E (D.nd.l i)) ∪ (D.nd.S i : Set _)) ∪
      (D.nd.Q i : Set _)), IsSplitPl D.host w ∧ ∃ B : ValuationSubring D.nd.Om,
      IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ},
      ((ρ g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly =
      ((mapRep (iotaOQ D.nd D.naut i) (r x) g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).charpoly := by
    rintro σ ⟨w, hw, hsp, B, hB', hσ⟩
    simp only [Set.mem_union, not_or] at hw
    obtain ⟨⟨hwl, hwS⟩, hwQ⟩ := hw
    replace hwS : w ∉ D.nd.S i := by simpa using hwS
    replace hwQ : w ∉ D.nd.Q i := by simpa using hwQ
    have hso : SplitOut D.nd i w := ⟨hsp, hwl, hwS, hwQ⟩
    have hS := hwS
    rw [D.nd.S_def] at hS
    have hS' := fun h => hS ⟨h, hwl⟩
    have hu : D.naut.unr (D.naut.locV i P w) := D.naut.locV_unr i P w hsp hwQ
      (Fin.forall_fin_two.2 ⟨fun h => hS' (Or.inl h), fun h => hS' (Or.inr (Or.inl h))⟩)
      fun h => hS' (Or.inr (Or.inr h))
    have hloc := hB.2.2.2.1 w hsp
    have hwd' := hwd w hwl
    rw [hloc] at hwd'
    replace hwd' := hwd'.eq_of_unr ((D.naut.unr_tw _ _).2 hu)
    have hun : D.naut.unr (D.naut.wdOf i ρ w) := by rw [hwd']; exact (D.naut.unr_tw _ _).2 hu
    have e1 := D.naut.wdOf_frob i ρ w hwl hρc hun B σ hB' hσ
    rw [hwd', ← D.naut.pt_loc i P x hP w hso] at e1
    have e2 := (hr x).2.2 w hso B σ hB' hσ
    apply Polynomial.map_injective (D.naut.iotaQC i).toRingHom (D.naut.iotaQC i).injective
    have e3 : ((mapRep (iotaOQ D.nd D.naut i) (r x) σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))) =
        ((r x σ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map (iotaOQ D.nd D.naut i) := rfl
    rw [e1, e3, Matrix.charpoly_map, e2, Polynomial.map_map]
    rfl
  have hc2 : SumRepresentations.At.ContQ D.nd i (mapRep (iotaOQ D.nd D.naut i) (r x)) :=
    contQ_of_continuous D.nd D.naut i (r x) (hr x).1
  have hall := charpoly_eq_of_dense' ρ (mapRep (iotaOQ D.nd D.naut i) (r x)) hρc hc2 _ hdense hfrob
  have : CharZero (Kf D.nd i) := RingHom.charZero (D.naut.iotaQ i)
  have hss : IsSSRep (mapRep (iotaOQ D.nd D.naut i) (r x)) := by
    have h := GlobalTheory.TraceSemisimple.isSSRep_mapRep _ _ _ (D.naut.iotaQ i) _ _ (hr x).2.1
    have e : mapRep (iotaOQ D.nd D.naut i) (r x) =
        mapRep (D.naut.iotaQ i) (mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (r x)) := by
      ext g a b
      rfl
    rw [e]
    exact h
  exact hBN _ _ ρ _ hρs hss hall

end

section
open Polynomial
local notation "Part" => Formalism.BasicNotions.Part

theorem heckeQ : ∀ (D : D7) (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i)
    (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa →
    ∀ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.ContQ D.nd i ρ → IsSSRep ρ →
    (∀ w, w ∉ placesOver D.host.E (D.nd.l i) →
      RelW D.nd D.naut (D.naut.wdOf i ρ w) (D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2))) →
    SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ := by
  intro D i x P Pa hP hBC ρ hc hss hwd
  refine ⟨hc, hss, fun w hw B σ hB hσ => ?_⟩
  have hS := (D.nd.S_def i w).not.1 hw.2.2.1
  have hunr : D.naut.unr (D.naut.locV i P w) := by
    refine D.naut.locV_unr i P w hw.1 hw.2.2.2 (fun k hk => hS ⟨?_, hw.2.1⟩)
      (fun hk => hS ⟨Or.inr (Or.inr hk), hw.2.1⟩)
    fin_cases k
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk)
  have hloc := hBC.2.2.2.1 w hw.1
  have hw' := (hwd w hw.2.1).eq_of_unr ((D.naut.unr_tw _ _).2 (by rw [hloc]; exact hunr))
  have hu : D.naut.unr (D.naut.wdOf i ρ w) := by
    rw [hw', hloc]
    exact (D.naut.unr_tw _ _).2 hunr
  have e := D.naut.wdOf_frob i ρ w hw.2.1 hc hu B σ hB hσ
  rw [hw', hloc, ← D.naut.pt_loc i P x hP w hw] at e
  apply Polynomial.map_injective (D.naut.iotaQC i).toRingHom (D.naut.iotaQC i).injective
  rw [e, Polynomial.map_map]
  rfl

theorem splitBC_of_galIso : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N)
    (i : N.Loc), GalIsoN N A i → GlobalTheory.RowTie.ChebSplit N → GlobalTheory.RowCopy.IsobaricDiscreteSelfDualStrongMultiplicityOne N A →
    GlobalTheory.RowTie.SplitBC N A i := by
  intro R H what₂ N A i hG hC hAN P P' hag Pa Pa' hB hB'
  obtain ⟨r, hrc, -, hr0⟩ := hG P Pa hB
  obtain ⟨r', hrc', -, hr0'⟩ := hG P' Pa' hB'
  have hr := fun w h1 (h2 : A.unr (isoLoc N A Pa w)) => (hr0 w h1).eq_of_unr ((A.unr_tw _ _).2 h2)
  have hr' := fun w h1 (h2 : A.unr (isoLoc N A Pa' w)) => (hr0' w h1).eq_of_unr ((A.unr_tw _ _).2 h2)
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
    rw [hr w h1 h2]; exact (A.unr_tw _ _).2 h2
  have hu' : ∀ w, w ∉ placesOver H.E (N.l i) → A.unr (isoLoc N A Pa' w) → A.unr (A.wdOf i r' w) := fun w h1 h2 => by
    rw [hr' w h1 h2]; exact (A.unr_tw _ _).2 h2
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
        rw [hr w h1 h2, hr' w h1 h3, hB.2.2.2.1 w hsp, hB'.2.2.2.1 w hsp, h4 hsp]
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
  rw [hr w h1 h2, hr' w h1 h3] at e4
  have e5 := congrArg (fun a => A.lpTw a (-((1 - (R.nV : ℝ)) / 2))) e4
  simpa only [A.lpTw_add, add_neg_cancel, A.lpTw_zero] using e5

end

end UpperTheory.GalS
