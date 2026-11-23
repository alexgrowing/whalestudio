import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Grampd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.RealVec
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Realsurj

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.rypos :
    ∀ (L : Type) [Field L] [NumberField L] [IsTotallyComplex L] (N : ℕ), Ry L N ⊆ Pos L N := by
  intro L _ _ _ N h hh w
  classical
  obtain ⟨hH, hq, hr, hb⟩ := gramq L N h
  have h0 : intVec (0 : Fin N × BI L → ℤ) = (0 : Lat L N) := by
    ext a; simp [intVec]
  have hpd : (gram h).PosDef := (grampd _ (gram h) hH fun c hc => by
    rw [hq, hr]
    exact hh _ fun e => hc (hb.1 (e.trans h0.symm))).1
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (mat_herm h w) fun z hz => ?_
  obtain ⟨x, hx⟩ := realsurj L N (Pi.single w z)
  have hx0 : x ≠ 0 := by
    rintro rfl
    apply hz
    have := congrFun hx w
    rw [Pi.single_eq_same] at this
    rw [← this]
    ext a; simp [realVec]
  have h1 := hpd.dotProduct_mulVec_pos hx0
  rw [star_trivial, hq, hx, qR, Finset.sum_eq_single w] at h1
  · rw [Pi.single_eq_same] at h1
    rw [Complex.lt_def]
    refine ⟨by simpa using h1, ?_⟩
    simpa using ((mat_herm h w).im_star_dotProduct_mulVec_self z).symm
  · intro v _ hv
    simp [Pi.single_eq_of_ne hv]
  · simp
