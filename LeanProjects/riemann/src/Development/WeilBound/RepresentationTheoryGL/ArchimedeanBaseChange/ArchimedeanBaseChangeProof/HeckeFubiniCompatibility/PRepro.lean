import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PReproA
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PReproC
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.CompatFub

noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

namespace PositivityTheory.Rg.BcB.CG

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def pInfH (N : ℕ) : GA E N →* (InfinitePlace E → G N) := MonoidHom.pi fun v => gInf v

def infPH (N : ℕ) : (InfinitePlace E → G N) →* GA E N where
  toFun := infP N
  map_one' := by simp [infP]
  map_mul' := infinitePart_mul N

theorem continuous_pInfH (N : ℕ) : Continuous (pInfH (E := E) N) :=
  continuous_pi fun v => continuous_gInf N v

theorem continuous_smooth_infP (N : ℕ) (φ : Sm E N) (x : GA E N) :
    Continuous fun t : InfinitePlace E → G N => φ.1 (x * infP N t) := by
  set M : (InfinitePlace E → G N) → GL (Fin N) (Cinf E) := fun t =>
    Units.map (Matrix.piRingEquiv (n := Fin N) (β := fun _ : InfinitePlace E => ℂ)).symm.toMonoidHom
      (MulEquiv.piUnits.symm t) with hMdef
  have hM : Continuous M := by
    refine Continuous.units_map _ ?_ |>.comp (ContinuousMulEquiv.piUnits (M := fun _ : InfinitePlace E =>
      Matrix (Fin N) (Fin N) ℂ)).symm.continuous
    exact continuous_pi fun i => continuous_pi fun j => continuous_pi fun v => (continuous_apply v).matrix_elem i j
  have e : (fun t : InfinitePlace E → G N => φ.1 (x * infP N t)) = fun t => chart φ.1 x (toL (M t).val) := by
    funext t
    rw [chart_val]
    rfl
  rw [e]
  have hc : Continuous fun t => ((M t : GL (Fin N) (Cinf E)) : Matrix (Fin N) (Fin N) (Cinf E)) :=
    Units.continuous_val.comp hM
  have hc' : Continuous fun t => toL (M t).val := hc
  exact (φ.2 x).continuousOn.comp_continuous hc' fun t => val_mem_invSet (M t)

theorem hasCompactSupport_prod {ι X : Type} [Fintype ι] [TopologicalSpace X] [T2Space X] (a : ι → X → ℂ)
    (ha : ∀ i, HasCompactSupport (a i)) : HasCompactSupport fun t : ι → X => ∏ i, a i (t i) := by
  refine HasCompactSupport.intro (isCompact_univ_pi fun i => ha i) fun t ht => ?_
  simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at ht
  obtain ⟨i, hi⟩ := ht
  exact Finset.prod_eq_zero (Finset.mem_univ i) (image_eq_zero_of_notMem_tsupport hi)

theorem reproEx (hK : KerEx) (hM : MultAlg) (hB : Bridge.BridgeSt) : ReproEx := by
  intro E _ _ _ N _ _ ν _ K W R hKo hW
  let _ : MeasurableSpace (G N) := borel _
  have : BorelSpace (G N) := ⟨rfl⟩
  set μ0 : Measure (G N) := Measure.haar
  choose a ha hac hrep using fun v : InfinitePlace E => ReproL.local_repro hK hM hB W hW R v μ0
  obtain ⟨K0, hK0K, hK0o, hK0c⟩ := ReproA.exists_compact_open_le E N K hKo
  set U0 : Subgroup (GA E N) := K0.comap gFin with hU0def
  have hU0o : IsOpen (U0 : Set (GA E N)) := hK0o.preimage (continuous_gFin N)
  have hσ : ∀ t, pInfH N (infPH (E := E) N t) = t := fun t => funext fun v => gInf_infP N t v
  have hσU : ∀ t, infPH (E := E) N t ∈ U0 := fun t => by
    change gFin (infP N t) ∈ K0
    rw [gFin_infP]; exact K0.one_mem
  have hsplit : ∀ y : GA E N, y = splitGA N (pInfH N y, gFin y) := fun y => (infinitePart_mul_finGL N y).symm
  have hprop : ∀ C : Set (InfinitePlace E → G N), IsCompact C → ∃ D : Set (GA E N), IsCompact D ∧
      (U0 : Set (GA E N)) ∩ pInfH N ⁻¹' C ⊆ D := fun C hC =>
    ⟨splitGA N '' (C ×ˢ (K0 : Set _)), (hC.prod hK0c).image (splitGA N).continuous, fun y hy =>
      ⟨(pInfH N y, gFin y), ⟨hy.2, hy.1⟩, (hsplit y).symm⟩⟩
  haveI := ReproA.pi_isHaar (ι := InfinitePlace E) μ0
  obtain ⟨c, hc, hcF⟩ := ReproA.haar_restrict_eq ν (Measure.pi fun _ : InfinitePlace E => μ0) (pInfH N)
    (continuous_pInfH N) (infPH N) hσ U0 hU0o hσU hprop
  set A : (InfinitePlace E → G N) → ℂ := fun t => ∏ v, a v (t v) with hAdef
  have hAc : Continuous A := continuous_finsetProd _ fun v _ => (ha v).comp (continuous_apply v)
  have hAs : HasCompactSupport A := hasCompactSupport_prod a hac
  refine ⟨(U0 : Set (GA E N)).indicator (fun y => A (pInfH N y)), c * (1 / 2) ^ Fintype.card (InfinitePlace E),
    ?_, ?_, by positivity, ?_⟩
  · have hcl : IsClopen (U0 : Set (GA E N)) := ⟨U0.isClosed_of_isOpen hU0o, hU0o⟩
    refine continuous_indicator (by rw [hcl.frontier_eq]; simp) (hAc.comp (continuous_pInfH N)).continuousOn
  · set C : Set (InfinitePlace E → G N) := Set.pi Set.univ fun v => tsupport (a v) with hCdef
    have hCc : IsCompact C := isCompact_univ_pi fun v => hac v
    have hCcl : IsClosed C := isClosed_set_pi fun v _ => isClosed_tsupport (a v)
    refine HasCompactSupport.intro' ((hCc.prod hK0c).image (splitGA N).continuous)
      ((splitGA N).toHomeomorph.isClosedMap _ (hCcl.prod (K0.isClosed_of_isOpen hK0o))) fun y hy => ?_
    by_cases hyU : y ∈ (U0 : Set (GA E N))
    · rw [Set.indicator_of_mem hyU]
      by_contra hne
      refine hy ⟨(pInfH N y, gFin y), ⟨fun v _ => subset_tsupport _ fun h0 => hne ?_, hyU⟩, (hsplit y).symm⟩
      exact Finset.prod_eq_zero (Finset.mem_univ v) h0
    · exact Set.indicator_of_notMem hyU _
  · intro φ _ hT hR
    choose s hs1 hs2 using fun v => hrep v φ hT.2 hR
    refine ⟨c * ∏ v, s v, ?_, fun x => ?_⟩
    · rw [norm_mul, Complex.norm_of_nonneg hc.le, norm_prod]
      gcongr
      rw [← Finset.card_univ, ← Finset.prod_const]
      exact Finset.prod_le_prod (fun _ _ => by norm_num) fun v _ => hs1 v
    · set f : (InfinitePlace E → G N) → ℂ := fun t => φ.1 (x * infP N t) with hfdef
      have hfc : Continuous f := continuous_smooth_infP N φ x
      have e1 : (fun y => (U0 : Set (GA E N)).indicator (fun y => A (pInfH N y)) y * φ.1 (x * y)) =
          (U0 : Set (GA E N)).indicator (fun y => (A * f) (pInfH N y)) := by
        funext y
        by_cases hyU : y ∈ (U0 : Set (GA E N))
        · rw [Set.indicator_of_mem hyU, Set.indicator_of_mem hyU, Pi.mul_apply]
          congr 1
          have hk : gFin y ∈ K := hK0K hyU
          conv_lhs => rw [hsplit y, splitGA_apply, ← mul_assoc, hT.1 _ hk]
        · rw [Set.indicator_of_notMem hyU, Set.indicator_of_notMem hyU, zero_mul]
      rw [e1, hcF (A * f) (hAc.mul hfc) hAs.mul_right]
      have h := ReproA.integral_pi_repro μ0 a ha hac f hfc s fun v y => by
        have e2 : (fun t => a v t * f (y * Pi.mulSingle v t)) =
            fun t => a v t * φ.1 ((x * infP N y) * infP N (Pi.mulSingle v t)) := by
          funext t
          simp only [hfdef, infinitePart_mul, mul_assoc]
        rw [e2, hs2 v (x * infP N y)]
      have e3 : f 1 = φ.1 x := by
        simp only [hfdef]
        rw [show infP (E := E) N 1 = 1 from (infPH (E := E) N).map_one, mul_one]
      simp only [Pi.mul_apply]
      rw [h, e3, mul_assoc]

end PositivityTheory.Rg.BcB.CG
