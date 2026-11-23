import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisRepBaseChange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepUniqueBaseChange
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.PointRepAboveL

theorem place_unique {D : D7} {i : D.nd.Loc} {τ : D.host.E →+* Qbar (D.nd.l i)} {w w' : PlE D.host}
    (h : InducesW D.nd i τ w) (h' : InducesW D.nd i τ w') : w' = w := by
  apply HeightOneSpectrum.ext
  ext x
  rw [← h x, h' x]

theorem compat_above (D : D7) (h0 : SumRepresentations.tie0 D) (h2 : SumRepresentations.adm2 D) (h5 : SumRepresentations.adm5 D) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i r) (x : D.nd.X i)
    (P : D.naut.AV i) (Pa : List (Formalism.BasicNotions.Part D.naut.CG)) (hP : D.naut.ptV i P = some x)
    (hB : IsBCV D.nd D.naut i P Pa) (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w ∧
    D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w =
      D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2) ∧
    ∀ τ, InducesW D.nd i τ w →
      D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (r x)) τ = D.naut.locAutHodgeTateWeightsLevelZero i τ := by
  obtain ⟨ρ, hc, hs, hwd, hl⟩ := GlobalTheory.GalIsoBC.galRep_isobaric D h0 h2 i P Pa hB
  obtain ⟨Pm, hPm⟩ := GlobalTheory.BaseChangeConj.rep_conj_of_baseChange D h5 i r hr x P Pa hP hB ρ hc hs
    (fun w _ => hwd w)
  obtain ⟨-, hconj, -, -⟩ := h0.2.2.2.2.2 i
  obtain ⟨hdR, hWD, hJ⟩ := hconj _ ρ _ hc Pm hPm
  refine ⟨(hdR w hw).2 (hl w hw).1, ?_, fun τ hτ => ?_⟩
  · rw [hWD w (Or.inr (hl w hw).1), hwd]
  · rw [hJ τ (fun w' h' => by rw [place_unique hτ h']; exact (hl w hw).1)]
    apply Multiset.map_injective (f := fun n : ℤ => (n : ℂ)) Int.cast_injective
    rw [(hl w hw).2 τ hτ, D.naut.locAut_hodgeTateWeightsLevelZero_def i τ]

theorem main : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm1 D → SumRepresentations.adm2 D → SumRepresentations.adm5 D → AdmissibleParameterJ.DeRhamFamilyAway D ∧ AdmissibleParameterJ.DeRhamFamilyTypePrimes D := by
  intro D h0 h1 h2 h5
  have key : ∀ i x, ∃ P Pa, D.naut.ptV i P = some x ∧ IsBCV D.nd D.naut i P Pa := fun i x => by
    obtain ⟨P, hP⟩ := D.naut.pt_surj i x
    obtain ⟨Pa, hPa⟩ := h1 i P
    exact ⟨P, Pa, hP, hPa⟩
  refine ⟨fun i r hr w hw => ?_, fun i r hr _ w hw x => ?_⟩
  · have hl : (D.nd.l i).Prime := Fact.out
    refine ⟨fun hl0 hl1 x => ?_, fun _ x hm => ?_⟩
    · obtain ⟨P, Pa, hP, hB⟩ := key i x
      have h := compat_above D h0 h2 h5 i r hr x P Pa hP hB w hw
      have hc : SumRepresentations.At.ContQ D.nd i (mapRep (iotaOQ D.nd D.naut i) (r x)) :=
        SumRepresentations.contQ_of_continuous D.nd D.naut i (r x) (hr x).1
      refine ⟨(D.naut.wdOf_unrL i _ w hw hc h.1).1 ?_, h.2.2⟩
      rw [h.2.1, D.naut.unr_tw]
      by_cases hs : IsSplitPl D.host w
      · rw [hB.2.2.2.1 w hs]
        refine D.naut.locV_unr i P w hs (fun hq => D.nd.SQ_l i w (Or.inr hq) hw) (fun k => ?_) ?_
        · have hk : D.nd.l i ≠ D.host.g k := by
            fin_cases k
            · exact hl0
            · exact hl1
          exact SumRepresentations.not_over_of_ne hl (D.host.g_prime k) hk hw
        · split_ifs with hpd
          · exact SumRepresentations.not_over_of_ne hl D.host.pde'_prime (hpd ▸ D.host.pde_ne) hw
          · exact SumRepresentations.not_over_of_ne hl D.host.pde_prime hpd hw
      · exact (hB.2.2.2.2.1 w hs).1
    · obtain ⟨P, Pa, hP, hB⟩ := key i x
      have h := compat_above D h0 h2 h5 i r hr x P Pa hP hB w hw
      have hc : SumRepresentations.At.ContQ D.nd i (mapRep (iotaOQ D.nd D.naut i) (r x)) :=
        SumRepresentations.contQ_of_continuous D.nd D.naut i (r x) (hr x).1
      refine (D.naut.wdOf_mono0L i _ w hw hc h.1).1 ?_
      rw [h.2.1, D.naut.monomial_twist_iff]
      exact hm P Pa hP hB
  · obtain ⟨P, Pa, hP, hB⟩ := key i x
    have h := compat_above D h0 h2 h5 i r hr x P Pa hP hB w hw
    exact ⟨h.1, h.2.2⟩

end GlobalTheory.PointRepAboveL
