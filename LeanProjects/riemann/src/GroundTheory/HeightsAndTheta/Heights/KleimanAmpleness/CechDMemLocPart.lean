import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsHomogOfMemQuotPartAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell cellMon CechC cellRes faceSign cechD locPart cechCc cechZc cechBc cechHc
  mIdealOver quotPart)

noncomputable section

namespace CellLocEval

set_option linter.unusedSectionVars false

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
  [∀ k, LinearOrder (ι k)] {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)

theorem face_subset (I : ∀ k, Finset (ι k)) (k : K) (i : ι k) (l : K) :
    Function.update I k ((I k).erase i) l ⊆ I l := by
  by_cases hl : l = k
  · subst hl
    rw [Function.update_self]
    exact Finset.erase_subset _ _
  · rw [Function.update_of_ne hl]

open Classical in

theorem cechD_apply' {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] (n : ℕ) (f : CechC S ι M n)
    (I : Cell K ι (n + 1)) :
    cechD S ι M n f I = ∑ k, ∑ i ∈ I.1 k,
      if h : (∀ l, (Function.update I.1 k ((I.1 k).erase i) l).Nonempty) ∧
          ∑ l, ((Function.update I.1 k ((I.1 k).erase i) l).card - 1) = n then
        faceSign I.1 k i • cellRes S M _ I.1 (f ⟨Function.update I.1 k ((I.1 k).erase i), h⟩)
      else 0 := by
  simp only [cechD, LinearMap.pi_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> rfl

theorem cechD_mem_locPart (γ : K → ℤ) (n : ℕ) {f : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) n}
    (hf : f ∈ cechCc ι (quotPart S (mIdealOver S y)) γ n) (I : Cell K ι (n + 1)) :
    cechD S ι _ n f I ∈ locPart ι (quotPart S (mIdealOver S y)) (cellMon S I.1) γ := by
  rw [cechD_apply']
  refine Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun i _ => ?_
  split_ifs with hc
  · have hJ : f ⟨Function.update I.1 k ((I.1 k).erase i), hc⟩ ∈ locPart ι (quotPart S (mIdealOver S y))
        (cellMon S (Function.update I.1 k ((I.1 k).erase i))) γ :=
      Submodule.mem_pi.mp hf ⟨Function.update I.1 k ((I.1 k).erase i), hc⟩ (Set.mem_univ _)
    have hm := cellRes_mem_locPart (J := Function.update I.1 k ((I.1 k).erase i)) (I := I.1)
      (cellMon_mono (face_subset I.1 k i)) γ hJ
    exact zsmul_mem hm _
  · exact Submodule.zero_mem _

theorem cechD_mem_cechCc (γ : K → ℤ) (n : ℕ) {f : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) n}
    (hf : f ∈ cechCc ι (quotPart S (mIdealOver S y)) γ n) :
    cechD S ι _ n f ∈ cechCc ι (quotPart S (mIdealOver S y)) γ (n + 1) :=
  Submodule.mem_pi.mpr fun I _ => cechD_mem_locPart y γ n hf I

def evC (n : ℕ) : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) n →ₗ[S] (Cell K ι n → Ω) :=
  LinearMap.pi fun I => (evMap y I.1).comp (LinearMap.proj (R := S)
    (φ := fun J : Cell K ι n => LocalizedModule (cellMon S J.1) (MRingOver S ι ⧸ mIdealOver S y)) I)

theorem evC_apply (n : ℕ) (w : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) n) (I : Cell K ι n) :
    evC y n w I = evMap y I.1 (w I) := rfl

theorem evC_cechD (n : ℕ) (w : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) n) :
    evC y (n + 1) (cechD S ι _ n w) = cellD S y n (evC y n w) := by
  funext I
  rw [evC_apply]
  by_cases hI : CellMeets y I.1
  · rw [cechD_apply', map_sum]
    simp only [cellD, LinearMap.pi_apply, hI, if_true, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs with hc
    · rw [map_zsmul]
      exact congrArg _ (evMap_cellRes (face_subset I.1 k i) hI _)
    · simp
  · rw [evMap_of_not y hI]
    simp only [cellD, LinearMap.pi_apply, hI, if_false, LinearMap.zero_apply]

variable (γ : K → ℤ)

theorem evC_mem (n : ℕ) {w : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) n}
    (hw : w ∈ cechCc ι (quotPart S (mIdealOver S y)) γ n) : evC y n w ∈ cellC S y γ n := by
  refine Submodule.mem_pi.mpr fun I _ => ?_
  rw [evC_apply]
  by_cases hI : CellMeets y I.1
  · rw [← map_evMap_locPart y hI γ]
    exact Submodule.mem_map_of_mem (Submodule.mem_pi.mp hw I (Set.mem_univ _))
  · rw [evMap_of_not y hI]
    exact Submodule.zero_mem _

theorem evC_lift (n : ℕ) {w' : Cell K ι n → Ω} (hw' : w' ∈ cellC S y γ n) :
    ∃ w ∈ cechCc ι (quotPart S (mIdealOver S y)) γ n, evC y n w = w' := by
  have h : ∀ I : Cell K ι n, ∃ x ∈ locPart ι (quotPart S (mIdealOver S y)) (cellMon S I.1) γ,
      evMap y I.1 x = w' I := by
    intro I
    have hI' : w' I ∈ cellSec S y γ I.1 := Submodule.mem_pi.mp hw' I (Set.mem_univ _)
    by_cases hI : CellMeets y I.1
    · rw [← map_evMap_locPart y hI γ] at hI'
      exact Submodule.mem_map.mp hI'
    · unfold cellSec at hI'
      rw [if_neg hI, Submodule.mem_bot] at hI'
      exact ⟨0, Submodule.zero_mem _, by rw [map_zero, hI']⟩
  choose w hw hφw using h
  exact ⟨w, Submodule.mem_pi.mpr fun I _ => hw I, funext hφw⟩

theorem evC_injOn (n : ℕ) :
    Set.InjOn (evC (S := S) y n) (cechCc ι (quotPart S (mIdealOver S y)) γ n) := by
  intro w hw w' hw' h
  funext I
  have h' := congrFun h I
  rw [evC_apply, evC_apply] at h'
  by_cases hI : CellMeets y I.1
  · exact evMap_injOn y hI γ (Submodule.mem_pi.mp hw I (Set.mem_univ _))
      (Submodule.mem_pi.mp hw' I (Set.mem_univ _)) h'
  · have := subsingleton_of_not (S := S) y hI
    exact Subsingleton.elim _ _

theorem evC_mem_cellZ (n : ℕ) {z : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) n}
    (hz : z ∈ cechZc ι (quotPart S (mIdealOver S y)) γ n) : evC y n z ∈ cellZ S y γ n := by
  obtain ⟨hC, hK⟩ := Submodule.mem_inf.mp hz
  rw [Submodule.restrictScalars_mem, LinearMap.mem_ker] at hK
  refine Submodule.mem_inf.mpr ⟨evC_mem y γ n hC, ?_⟩
  rw [LinearMap.mem_ker, ← evC_cechD, hK, map_zero]

theorem evC_mem_cellB (n : ℕ) {z : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) n}
    (hz : z ∈ cechBc ι (quotPart S (mIdealOver S y)) γ n) : evC y n z ∈ cellB S y γ n := by
  cases n with
  | zero =>
    change z ∈ (⊥ : Submodule S _) at hz
    change evC y 0 z ∈ (⊥ : Submodule S _)
    rw [Submodule.mem_bot] at hz ⊢
    rw [hz, map_zero]
  | succ n =>
    change z ∈ (cechCc ι (quotPart S (mIdealOver S y)) γ n).map
      ((cechD S ι (MRingOver S ι ⧸ mIdealOver S y) n).restrictScalars S) at hz
    change evC y (n + 1) z ∈ (cellC S y γ n).map (cellD S y n)
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hz
    exact Submodule.mem_map.mpr ⟨evC y n w, evC_mem y γ n hw, (evC_cechD y n w).symm⟩

theorem mem_cechBc_of (n : ℕ) {z : CechC S ι (MRingOver S ι ⧸ mIdealOver S y) n}
    (hz : z ∈ cechCc ι (quotPart S (mIdealOver S y)) γ n) (h : evC y n z ∈ cellB S y γ n) :
    z ∈ cechBc ι (quotPart S (mIdealOver S y)) γ n := by
  cases n with
  | zero =>
    change evC y 0 z ∈ (⊥ : Submodule S _) at h
    change z ∈ (⊥ : Submodule S _)
    rw [Submodule.mem_bot] at h ⊢
    exact evC_injOn y γ 0 hz (Submodule.zero_mem _) (h.trans (map_zero _).symm)
  | succ n =>
    change evC y (n + 1) z ∈ (cellC S y γ n).map (cellD S y n) at h
    change z ∈ (cechCc ι (quotPart S (mIdealOver S y)) γ n).map
      ((cechD S ι (MRingOver S ι ⧸ mIdealOver S y) n).restrictScalars S)
    obtain ⟨w', hw', hd⟩ := Submodule.mem_map.mp h
    obtain ⟨w, hw, rfl⟩ := evC_lift y γ n hw'
    refine Submodule.mem_map.mpr ⟨w, hw, ?_⟩
    exact evC_injOn y γ (n + 1) (cechD_mem_cechCc y γ n hw) hz ((evC_cechD y n w).trans hd)

def evZ (n : ℕ) : cechZc ι (quotPart S (mIdealOver S y)) γ n →ₗ[S] cellZ S y γ n :=
  (evC (S := S) y n).restrict fun _ hz => evC_mem_cellZ y γ n hz

def evH (n : ℕ) : cechHc ι (quotPart S (mIdealOver S y)) γ n →ₗ[S] cellH S y γ n :=
  Submodule.mapQ _ _ (evZ (S := S) y γ n) fun _ hz => evC_mem_cellB (S := S) y γ n hz

theorem evH_mk (n : ℕ) (z : cechZc ι (quotPart S (mIdealOver S y)) γ n) :
    evH (S := S) y γ n (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (p := (cellB S y γ n).comap (cellZ S y γ n).subtype) (evZ y γ n z) := rfl

theorem evH_bijective (n : ℕ) : Function.Bijective (evH (S := S) y γ n) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx' := (Submodule.Quotient.mk_eq_zero _).mp ((evH_mk y γ n z).symm.trans hx)
    rw [Submodule.Quotient.mk_eq_zero]
    exact mem_cechBc_of y γ n (Submodule.mem_inf.mp z.2).1 hx'
  · intro q
    obtain ⟨z', rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨hC, hK⟩ := Submodule.mem_inf.mp z'.2
    obtain ⟨w, hw, hwz⟩ := evC_lift y γ n hC
    have hdw : cechD S ι _ n w = 0 := by
      refine evC_injOn y γ (n + 1) (cechD_mem_cechCc y γ n hw) (Submodule.zero_mem _) ?_
      rw [evC_cechD, hwz, map_zero]
      exact LinearMap.mem_ker.mp hK
    have hwZ : w ∈ cechZc ι (quotPart S (mIdealOver S y)) γ n :=
      Submodule.mem_inf.mpr ⟨hw, by rw [Submodule.restrictScalars_mem, LinearMap.mem_ker]; exact hdw⟩
    refine ⟨Submodule.Quotient.mk ⟨w, hwZ⟩, ?_⟩
    exact (evH_mk y γ n ⟨w, hwZ⟩).trans (congrArg Submodule.Quotient.mk (Subtype.ext hwz))

theorem proof : CellLocEval.Statement := by
  intro S _ K _ _ ι _ _ Ω _ _ y γ n
  exact ⟨(LinearEquiv.ofBijective (evH (S := S) y γ n) (evH_bijective (S := S) y γ n)).symm⟩

end CellLocEval

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
