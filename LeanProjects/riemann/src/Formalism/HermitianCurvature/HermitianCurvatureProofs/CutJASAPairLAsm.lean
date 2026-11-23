import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGroupAdjPair
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnTrSmooth
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLZero

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

theorem sAPairOne_of_parts (hZ : SAZero) (hL : SALocal) (hE : SAExh) (hJC : SAJCommC) (hB3 : CompactSupportClassMembership) :
    SAPairOne := by
  obtain ⟨C1, hZ'⟩ := hZ
  obtain ⟨C2, hL'⟩ := hL
  obtain ⟨C3, hE'⟩ := hE
  obtain ⟨C4, hJC'⟩ := hJC
  obtain ⟨C5, hB3'⟩ := hB3
  refine ⟨max C1 (max C2 (max C3 (max C4 C5))), ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e he Θ hΘ K hK J hJ hΘK hΘJ hKt
  have mono : ∀ c : ℝ, c ≤ max C1 (max C2 (max C3 (max C4 C5))) → BuiltOW c S T f χ ν' m₀ top A₀ :=
    fun c h => ⟨isBuiltPlace_mono h hB.1, hB.2⟩
  have hB1 := mono C1 (le_max_left _ _)
  have hB2 := mono C2 (le_trans (le_max_left _ _) (le_max_right _ _))
  have hB3 := mono C3 (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hB4 := mono C4 (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
  have hB5 := mono C5 (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))))
  have hplace : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  set Qs := MA.Qset (D.parOf S v).r (D.parOf S v).TT with hQs

  set Cs : Set (MA.E (D.parOf S v).r) :=
    ⋃ π, tsupport (MA.ext ((trJ S T v e K π : MA.SmQ (D.parOf S v).r (D.parOf S v).TT) :
      MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ)) with hCsdef
  have hCc : IsCompact Cs := isCompact_iUnion fun π => (hKt π).1
  have hCQ : Cs ⊆ Qs := Set.iUnion_subset fun π => (hKt π).2
  have hCcl : IsClosed Cs := hCc.isClosed
  have hK0 : ∀ y ∈ Qs, y ∉ Cs → K (B.gq (T v).base y) = 0 := by
    intro y hy hyC
    refine hZ' E Wp Wq S T f χ ν' m₀ top A₀ hB1 v e he K hK y hy fun π => ?_
    have hn : y ∉ tsupport (MA.ext ((trJ S T v e K π : MA.SmQ (D.parOf S v).r (D.parOf S v).TT) :
        MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ)) := fun h => hyC (Set.mem_iUnion.2 ⟨π, h⟩)
    have h0 := image_eq_zero_of_notMem_tsupport hn
    simp only [MA.ext] at h0
    first
    | exact h0 hy
    | exact (dif_pos hy).symm.trans h0
  have hΘK0 : ∀ y ∈ Qs, y ∉ Cs → B.opApply Θ K (B.gq (T v).base y) = 0 := fun y hy hyC =>
    hL' E Wp Wq S T f χ ν' m₀ top A₀ hB2 v Θ hΘ K hK (Qs \ Cs) ((MA.Qset_open _ _).sdiff hCcl)
      Set.sdiff_subset (fun y' hy' => hK0 y' hy'.1 hy'.2) y ⟨hy, hyC⟩
  refine ⟨fun π => ?_, ?_⟩
  ·
    have hsm := En.trace_smoothness E Wp Wq S T v hplace e he (B.opApply Θ K) hΘK π
    have hsupp : Function.support (MA.ext ((trJ S T v e (B.opApply Θ K) π : MA.SmQ (D.parOf S v).r (D.parOf S v).TT) :
        MA.Qp (D.parOf S v).r (D.parOf S v).TT → ℂ)) ⊆ Cs := by
      intro y hy
      by_contra hyC
      apply hy
      by_cases hyQ : y ∈ Qs
      · simp only [MA.ext]
        unfold trJ
        rw [En.toSm_val_of_mem _ hsm]
        simp [hΘK0 y hyQ hyC, GA.hsVec_zero']
      · simp only [MA.ext]
        first
        | exact fun h => absurd h hyQ
        | exact dif_neg hyQ
    have hts := closure_minimal hsupp hCcl
    exact ⟨hCc.of_isClosed_subset (isClosed_tsupport _) hts, hts.trans hCQ⟩
  ·
    obtain ⟨F₁, U₁, -, hCU₁, hF₁s, hF₁c, hF₁O, hF₁e⟩ :=
      hE' E Wp Wq S T f χ ν' m₀ top A₀ hB3 v K hK Cs hCc hCQ
    obtain ⟨F₂, U₂, hU₂o, hCU₂, hF₂s, hF₂c, hF₂O, hF₂e⟩ :=
      hE' E Wp Wq S T f χ ν' m₀ top A₀ hB3 v J hJ Cs hCc hCQ
    have hKF₁ : ∀ y ∈ Qs, K (B.gq (T v).base y) = B.JF (T v).base F₁ (B.gq (T v).base y) := by
      intro y hy
      by_cases hyU : y ∈ U₁
      · exact ((hF₁e y hy).1 hyU).symm
      · have hyC : y ∉ Cs := fun h => hyU (hCU₁ h)
        rw [hK0 y hy hyC, (hF₁e y hy).2 (hK0 y hy hyC)]
    have hc1 := hJC' E Wp Wq S T f χ ν' m₀ top A₀ hB4 v Θ hΘ F₁ hF₁s hF₁c hF₁O Set.univ K isOpen_univ hK
      (fun y hy _ => hKF₁ y hy)
    have hc2 := hJC' E Wp Wq S T f χ ν' m₀ top A₀ hB4 v Θ hΘ F₂ hF₂s hF₂c hF₂O U₂ J hU₂o hJ
      (fun y hy hyU => ((hF₂e y hy).1 hyU).symm)
    obtain ⟨hF₁5, hF₂5, hΘF₁5, hΘF₂5, hβ⟩ :=
      hB3' E Wp Wq S T f χ ν' m₀ top A₀ hB5 v Θ hΘ F₁ F₂ hF₁s hF₁c hF₁O hF₂s hF₂c hF₂O
    have hLp := GA.group_action_pairing_holds _ E Wp Wq S T f χ ν' m₀ top A₀ hB v e he (B.opApply Θ K) J (B.opApply Θ F₁) F₂
      hΘK hJ hΘF₁5 hF₂5 (Filter.Eventually.of_forall fun y hy => ⟨(hc1 y hy trivial).1, fun hne => by
        have hyC : y ∈ Cs := by
          by_contra hyC
          exact hne (hΘK0 y hy hyC)
        exact ((hF₂e y hy).1 (hCU₂ hyC)).symm⟩)
    have hRp := GA.group_action_pairing_holds _ E Wp Wq S T f χ ν' m₀ top A₀ hB v e he K (B.opAdj Θ J) F₁ (B.opAdj Θ F₂)
      hK hΘJ hF₁5 hΘF₂5 (Filter.Eventually.of_forall fun y hy => ⟨hKF₁ y hy, fun hne => by
        have hyC : y ∈ Cs := by
          by_contra hyC
          exact hne (hK0 y hy hyC)
        exact (hc2 y hy (hCU₂ hyC)).2⟩)
    rw [hLp, hRp]
    exact hβ

theorem sAPairL_of_parts (hF : JAFFStable) (hL : SALocal) (hE : SAExh) (hJC : SAJCommC) (hB3 : CompactSupportClassMembership) : SAPairL :=
  sAPairL_of_one hF (sAPairOne_of_parts self_adjoint_zero_holds hL hE hJC hB3)

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
