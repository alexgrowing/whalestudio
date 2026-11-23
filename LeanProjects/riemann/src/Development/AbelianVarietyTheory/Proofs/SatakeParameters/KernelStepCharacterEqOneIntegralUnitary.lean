import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfCongSet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubOneMemMapOfEq
import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.TuplesP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonAdjointHeckeOperatorEqDualLabel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralHilbert90FiniteIdelesTrivialWhereTrivialStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.OpenCharacterEqOneOfIntegralUnitOneAtRamifiedStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AfIsoEqZeroIffStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTypePrimeUnderEqStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnPrimeToBasePrimePreservesCommonPlaceStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceComponentEqOneIffComponentsOverEqOneStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmDataConjIsConjOfStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.L2.Forms
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TieUnr

set_option maxHeartbeats 4000000 in

theorem mt_eq_one_of_intUnit : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ i < D.R.m, ∀ y : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm), Matrix.GeneralLinearGroup.det y.1 ∈ intU D.host.F D.host.E → (∀ v, UnderSB t μ v → Formalism.UG.prV (E := D.host.E) v ((Matrix.GeneralLinearGroup.det y.1 : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) = 1) → (t.O u μ).mt (i + 1) (dtU y) = 1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a H T i hi y hint hsupp
  classical
  letI := D.host.cmStar
  have hzU : Matrix.GeneralLinearGroup.det y.1 ∈ U1 (sigD D) := det_in_unitary_one D.host.F D.host.E (sigD D) 1 1 (by simp) y.1 y.2
  obtain ⟨x', hx'int, hx'h90, hx'supp⟩ := GlobalTheory.T.integral_h90_preimage_trivial_at_places_over_trivial D.host.F D.host.E (sigD D) (GlobalTheory.T.cmData_conj_isConjOf _ _ D.sp.cm)
    (GlobalTheory.HeckeAdjoint.unramified_host D) _ hzU hint
  set x : (AfE t.X.F t.X.E)ˣ := Units.map A.iA.symm.toRingHom.toMonoidHom x' with hxdef
  have hxx : Units.map A.iA.toRingHom.toMonoidHom x = x' := by
    ext
    simp [x]
  have hq : A.q x = dtU y := H.q_dt x y (by rw [hxx, hx'h90])
  have hcoe : ∀ w : AfE t.X.F t.X.E, A.iA w ∈ RInt D.host.F D.host.E ↔ w ∈ RInt t.X.F t.X.E := H.iA_int
  have hxint : x ∈ intU t.X.F t.X.E := by
    refine ⟨(hcoe _).1 ?_, (hcoe _).1 ?_⟩
    · simpa [x] using hx'int.1
    · simpa [x] using hx'int.2

  have hsub : ∀ {K : Type} [Field K] [NumberField K] (w : FiniteAdeleRing (𝓞 K) K) (P : HeightOneSpectrum (𝓞 K)),
      (w - 1) P = w P - 1 := fun _ _ => rfl
  have hsuppX : ∀ Q : HeightOneSpectrum (𝓞 t.X.E), (∃ P ∈ SB t μ, P.under (𝓞 t.X.F) = Q.under (𝓞 t.X.F)) →
      GlobalTheory.Mem.Col2.afIso t.X.F t.X.E (x : AfE t.X.F t.X.E) Q = 1 := by
    rintro Q ⟨P, hP, hPQ⟩
    have hxm1 : (x : AfE t.X.F t.X.E) - 1 ∈ RInt t.X.F t.X.E := sub_mem hxint.1 (one_mem _)
    have key := GlobalTheory.T.afIso_ringEquiv_eq_zero_iff t.X.F t.X.E D.host.F D.host.E t.seam.iE A.iA H.iA_rat H.iA_int _ hxm1 Q
    have e1 : A.iA ((x : AfE t.X.F t.X.E) - 1) = (x' : AfE D.host.F D.host.E) - 1 := by
      rw [map_sub, map_one]
      simp [x]
    rw [e1] at key
    have hA : GlobalTheory.Mem.Col2.afIso t.X.F t.X.E ((x : AfE t.X.F t.X.E) - 1) Q =
        GlobalTheory.Mem.Col2.afIso t.X.F t.X.E (x : AfE t.X.F t.X.E) Q - 1 := by
      rw [map_sub, map_one]; rfl
    have hB : GlobalTheory.Mem.Col2.afIso D.host.F D.host.E ((x' : AfE D.host.F D.host.E) - 1) (seamP t.seam Q) =
        GlobalTheory.Mem.Col2.afIso D.host.F D.host.E (x' : AfE D.host.F D.host.E) (seamP t.seam Q) - 1 := by
      rw [map_sub, map_one]; rfl
    rw [← sub_eq_zero, ← hA]
    refine key.1 ?_
    show GlobalTheory.Mem.Col2.afIso D.host.F D.host.E ((x' : AfE D.host.F D.host.E) - 1) (seamP t.seam Q) = 0
    rw [hB, sub_eq_zero]
    refine hx'supp _ fun R hR => ?_
    have hv : UnderSB t μ ((seamP t.seam Q).under (𝓞 D.host.F)) := by
      refine ⟨P, hP, ?_⟩
      show ((seamP t.seam Q).under (𝓞 D.host.F)).asIdeal = ((seamP t.seam P).under (𝓞 D.host.F)).asIdeal
      rw [GlobalTheory.T.columnPrimeToBasePrime_preserves_common_place D t.X t.seam t.seam_ok H.fields.ok P Q hPQ]
    exact (GlobalTheory.T.placeComponent_eq_one_iff_components_over_eq_one _ _ _ _).1 (hsupp _ hv) R hR
  have hvG : ∀ P : HeightOneSpectrum (𝓞 t.X.E), (∃ k, ((t.Pr.g k : ℕ) : 𝓞 t.X.E) ∈ P.asIdeal) →
      GlobalTheory.Mem.Col2.afIso t.X.F t.X.E (x : AfE t.X.F t.X.E) P = 1 := by
    rintro P ⟨k, hk⟩
    obtain ⟨P', hP', hu⟩ := GlobalTheory.T.exists_typePrime_under_eq t.X t.Pr H.fields.ok t.pr_ok k P hk
    refine hsuppX P ⟨P', Finset.mem_union_left _ ?_, hu⟩
    fin_cases k
    · exact Finset.mem_union_left _ hP'
    · exact Finset.mem_union_right _ hP'
  have hiso : IsAdIso (GlobalTheory.Mem.Col2.afIso t.X.F t.X.E) :=
    ⟨GlobalTheory.Mem.Col2.afIso_tmul_one _ _, GlobalTheory.Mem.Col2.mem_rInt_iff _ _⟩
  have hmu : ∀ j : Fin D.R.m, D.muTil (j.1 + 1) (A.q x) = 1 := by
    intro j
    rw [H.muTil _ hiso j (GlobalTheory.Mem.ReadEx.toIdl t.X.F t.X.E x) x (fun w => rfl) (GlobalTheory.Mem.ReadEx.toIdl_snd x).symm]
    refine Units.ext ?_
    have h1 := GlobalTheory.Mem.ReadEx.map_toIdl_eq_one (H.mu0 j).tame hxint (fun P hP => ?_)
    · rw [h1]
    · have hg : ∃ k, ((t.Pr.g k : ℕ) : 𝓞 t.X.E) ∈ P.asIdeal := by
        by_contra hc
        push_neg at hc
        exact hP ((H.mu0 j).unr P hc)
      have h2 := hvG P hg
      show Valued.v (GlobalTheory.Mem.Col2.afIso t.X.F t.X.E ((x : AfE t.X.F t.X.E) - 1) P) ≤ _
      rw [map_sub, map_one, hsub, h2, sub_self, map_zero]
      exact zero_le'
  have hxi : (t.tup μ : Chr t.X.F t.X.E t.X.K) x = 1 := by
    have hmem := (t.tup μ).2
    simp only [tupGrp, finChar, Subgroup.mem_inf] at hmem
    refine GlobalTheory.T.openCharacter_eq_one_of_integralUnit_one_at_ramified t.X.F t.X.E t.X.K t.seam.σ₀ _ hmem.1.1.1.1.2 hmem.1.1.1.1.1 x hxint fun P hP => hsuppX P ?_
    refine ⟨t.sel (P.under (𝓞 t.X.F)), Finset.mem_union_right _ ?_, ?_⟩
    · have hs : (t.sel (P.under (𝓞 t.X.F))).under (𝓞 t.X.F) = P.under (𝓞 t.X.F) :=
        GlobalTheory.TwistPlaces.under_eq_iff.2 (H.sel _)
      refine (GlobalTheory.TwistPlaces.mem_QE_iff H.sel (t.tup μ)).2 ⟨?_, ?_⟩
      · rw [hs]; exact hP
      · rw [hs]
    · exact GlobalTheory.TwistPlaces.under_eq_iff.2 (H.sel _)
  rw [← hq]
  by_cases hμ : μ = D.what₂.mu0
  · rw [(H.ref hμ).2]
    exact hmu ⟨i, hi⟩
  · obtain ⟨ξ, hξ, hmt⟩ := H.tw μ hμ rfl
    rw [hmt u, twMt, if_pos ⟨by omega, by omega⟩, MonoidHom.mul_apply, hmu ⟨i, hi⟩, one_mul, hξ x, hxi, map_one]

end GlobalTheory.TieUnr
