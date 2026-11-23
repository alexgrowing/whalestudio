import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.LocalQuotientIntegrals.OneVanish

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open scoped Pointwise

namespace PositivityTheory.Rg.BcB.CV.ClassVanishing

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

theorem exists_haar_inv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [LocallyCompactSpace G] (hc : ∀ a b : G, a * b = b * a) :
    ∃ ν : Measure G, ν.IsHaarMeasure ∧ ν.IsInvInvariant := by
  letI : CommGroup G := { (inferInstance : Group G) with mul_comm := hc }
  exact ⟨Measure.haar, inferInstance, Measure.IsHaarMeasure.isInvInvariant_of_regular _⟩

theorem gamma_fin_zero (y : (Fin 0 → SignType) → ℝ) (a : Fin 0 → ℝ) : gam y a = 1 := by
  unfold gam gamOn
  rw [Finset.sum_eq_single (∅ : Finset (Fin 0 → SignType))]
  · simp
  · intro s hs hne
    exfalso
    apply hne
    simp only [Finset.mem_filter] at hs
    exact Finset.subset_empty.mp fun e he => absurd (Subsingleton.elim e 0 ▸ he) hs.2.1
  · intro h
    exfalso
    apply h
    simp [Finset.mem_filter]

theorem quot_congr {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G) {H H' : Subgroup G} (h : H = H')
    (F : G → ℂ) : quotIntegral μ H Measure.count F = quotIntegral μ H' Measure.count F := by
  subst h; rfl

theorem quotL_congr {G : Type} [Group G] [MeasurableSpace G] (μ : Measure G) {H H' : Subgroup G} (h : H = H')
    (F : G → ENNReal) : quotLIntegral μ H Measure.count F = quotLIntegral μ H' Measure.count F := by
  subst h; rfl

end PositivityTheory.Rg.BcB.CV.ClassVanishing

open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.BcB.CV

theorem PositivityTheory.Rg.BcB.CV.pf_ClassVanish : PositivityTheory.Rg.BcB.D4.PairParam → PositivityTheory.Rg.BcB.D4.TorusChar → PositivityTheory.Rg.BcB.D4.ChiGam → PositivityTheory.Rg.BcB.D4.QuotStage → PositivityTheory.Rg.BcB.D4.RatDisc → PositivityTheory.Rg.BcB.SizeBasic → PositivityTheory.Rg.BcB.CV.QAdd → PositivityTheory.Rg.BcB.CV.Vfun → PositivityTheory.Rg.BcB.CV.AdTop → PositivityTheory.Rg.BcB.CV.CutInt → PositivityTheory.Rg.BcB.CV.Glob1 → PositivityTheory.Rg.BcB.CV.Glob2 → PositivityTheory.Rg.BcB.ClassVanish := by
  intro hPP hTC hCG hQS hRD hSB hQA hVf hAT hCI hG1 hG2
  intro E _ _ _ _ n
  obtain ⟨C₀, hC₀⟩ := hCG E n
  refine ⟨max 0 C₀, ?_⟩
  intro _ _ μ _ τ r φ d hφ hsz hvc hτ hreg hne
  obtain ⟨hLC, hT2, hSC, -, -, -⟩ := hAT E n
  haveI := hLC
  haveI := hT2
  haveI := hSC
  obtain ⟨m, Wof, hiso, huniq, hzero, hmeet, hmono, hperp⟩ := hPP E n d hreg
  obtain ⟨hcomm, a, hdegT, hadd, hrat0, hcont, hcpt⟩ := hTC E n d m Wof hiso huniq hzero hmeet hmono hreg
  obtain ⟨hle, hdisc, hclosed⟩ := hRD.1 E n d
  haveI : LocallyCompactSpace (adCent d) := hclosed.locallyCompactSpace
  haveI : BorelSpace (adCent d) := Subtype.borelSpace _
  haveI : SecondCountableTopology (adCent d) := TopologicalSpace.Subtype.secondCountableTopology _
  have hcommT : ∀ s t : adCent d, s * t = t * s := fun s t => Subtype.ext (hcomm s s.2 t t.2)
  obtain ⟨ν, hνH, hνI⟩ := ClassVanishing.exists_haar_inv hcommT
  haveI := hνH
  haveI := hνI
  have hmap : (ratIn d).map (adCent d).subtype = ratCent d := by
    rw [ratIn, Subgroup.subgroupOf_map_subtype, inf_of_le_left hle]
  set F : GA E n → ℂ := fun x => chiT τ x * φ (twConj (thetaA E n) x (ratGL E n d)) with hF
  obtain ⟨hFm, hFinv, hFfin⟩ := hCI E n μ τ φ d hφ
  have hstage := hQS (GA E n) μ (adCent d) ν (ratIn d) F hclosed hdisc hFm
    (fun g hg x => hFinv g (Subgroup.mem_subgroupOf.1 hg) x)
    (by rw [ClassVanishing.quotL_congr μ hmap]; exact hFfin)
  rw [ClassVanishing.quot_congr μ hmap] at hstage

  obtain ⟨V, hVdef⟩ : ∃ V : ((Fin m → SignType) → ℝ) → ℂ,
      V = fun y => quotIntegral ν (ratIn d) Measure.count fun t : adCent d => (gam y (a t) : ℂ) := ⟨_, rfl⟩
  have hcptT : ∀ M : ℝ, ∃ K : Set (adCent d), IsCompact K ∧ ∀ t : adCent d, (∀ i, |a t i| ≤ M) →
      t ∈ ((ratIn d : Subgroup (adCent d)) : Set (adCent d)) * K := by
    intro M
    obtain ⟨K, hK, hKt⟩ := hcpt M
    refine ⟨Subtype.val ⁻¹' K, hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage hK, fun t ht => ?_⟩
    obtain ⟨g, hg, k, hk, hgk⟩ := Set.mem_mul.1 (hKt t t.2 ht)
    have hgA : g ∈ adCent d := hle hg
    have hkA : k ∈ adCent d := by
      have : k = g⁻¹ * t := by rw [← hgk]; group
      rw [this]; exact (adCent d).mul_mem ((adCent d).inv_mem hgA) t.2
    exact Set.mem_mul.2 ⟨⟨g, hgA⟩, hg, ⟨k, hkA⟩, hk, Subtype.ext hgk⟩
  obtain ⟨hVP, hVtr⟩ := hVf (adCent d) ν (ratIn d) m (fun t => a t) hcommT hdisc
    (continuousOn_iff_continuous_domRestrict.1 hcont) (fun s t => hadd s s.2 t t.2)
    (fun t ht => hrat0 t (Subgroup.mem_subgroupOf.1 ht)) hcptT
  rw [← hVdef] at hVP
  have hVinv : ∀ t ∈ adCent d, ∀ y, V (fun e => y e - sdot e (a t)) = V y := by
    intro t ht y
    have := hVtr y ⟨t, ht⟩
    rw [hVdef]
    exact this

  have hinner : ∀ x, (quotIntegral ν (ratIn d) Measure.count fun t : adCent d => F ((t : GA E n) * x)) =
      φ (twConj (thetaA E n) x (ratGL E n d)) * V (yOf τ Wof x) := by
    intro x
    have hpt : (fun t : adCent d => F ((t : GA E n) * x)) =
        fun t : adCent d => φ (twConj (thetaA E n) x (ratGL E n d)) * (gam (yOf τ Wof x) (a t) : ℂ) := by
      funext t
      show chiT τ ((t : GA E n) * x) * φ (twConj (thetaA E n) ((t : GA E n) * x) (ratGL E n d)) = _
      rw [twConj_mul_left (thetaA E n) (ratGL E n d) t.2 x]
      by_cases h0 : φ (twConj (thetaA E n) x (ratGL E n d)) = 0
      · simp [h0]
      · have h1 := hsz _ h0
        have h2 := (hSB E n).2.1 (twConj (thetaA E n) x (ratGL E n d))
        have hτ' : C₀ * (1 + logSize (twConj (thetaA E n) x (ratGL E n d))) ≤ τ :=
          calc C₀ * (1 + logSize (twConj (thetaA E n) x (ratGL E n d)))
              ≤ max 0 C₀ * (1 + logSize (twConj (thetaA E n) x (ratGL E n d))) :=
                mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
            _ ≤ max 0 C₀ * (1 + r) := mul_le_mul_of_nonneg_left (by linarith) (le_max_left _ _)
            _ ≤ τ := hτ
        exact (mul_comm _ _).trans
          (congrArg (fun z => φ (twConj (thetaA E n) x (ratGL E n d)) * z)
            (hC₀ d m Wof a hiso huniq hzero hmeet hmono hreg hdegT τ x hτ' t t.2))
    rw [hpt, (hQA (adCent d) ν (ratIn d) Measure.count).2.2 (φ (twConj (thetaA E n) x (ratGL E n d)))
      (fun t : adCent d => (gam (yOf τ Wof x) (a t) : ℂ)), hVdef]
  have hcut : cutTerm μ τ φ d = quotIntegral μ (adCent d) ν
      (fun x => φ (twConj (thetaA E n) x (ratGL E n d)) * V (yOf τ Wof x)) := by
    show quotIntegral μ (ratCent d) Measure.count F = _
    rw [hstage]
    congr 1
    funext x
    exact hinner x
  rw [hcut]
  by_cases hm : m = 0
  · subst hm
    have hV : ∀ y, V y = V 0 := fun y => by
      rw [hVdef]
      simp only [ClassVanishing.gamma_fin_zero]
    rw [show (fun x => φ (twConj (thetaA E n) x (ratGL E n d)) * V (yOf τ Wof x)) =
        fun x => V 0 * φ (twConj (thetaA E n) x (ratGL E n d)) from funext fun x => by rw [hV, mul_comm],
      (hQA (GA E n) μ (adCent d) ν).2.2 (V 0) (fun x => φ (twConj (thetaA E n) x (ratGL E n d))),
      hG1 E n μ d ν φ hreg hne hcomm hclosed hφ hvc, mul_zero]
  · exact hG2 E n m μ d ν Wof a V τ φ hm
      ⟨hreg, hiso, huniq, hzero, hmeet, hmono, hperp, hcomm, hclosed, hdegT⟩ hVP hVinv hφ hvc
