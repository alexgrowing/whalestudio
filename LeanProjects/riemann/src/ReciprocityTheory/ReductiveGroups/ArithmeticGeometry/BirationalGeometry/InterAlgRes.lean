import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterPC
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsAtlas
import ReciprocityTheory.AnalyticForms.RegularLocalRings.SNCstep
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Immersion

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.AnForm.M

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem mem_mcPts_iff_conePts_pC (P : Ideal (MRing ι)) (z : (Σ k, ι k) → ℂ) :
    z ∈ mcPts P ↔ z ∈ ReciprocityTheory.AnForm.R.conePts (pC P) := by
  rw [mcPts_eq_pC]
  exact Iff.rfl

theorem sameOrbit_trans {a b c : (Σ k, ι k) → ℂ} (h1 : SameOrbit a b) (h2 : SameOrbit b c) :
    SameOrbit a c := by
  obtain ⟨c, hc, rfl⟩ := h1
  obtain ⟨d, hd, rfl⟩ := h2
  refine ⟨fun k => c k * d k, fun k => mul_ne_zero (hc k) (hd k), ?_⟩
  funext p
  ring

theorem nonempty_anLogRes_of_algRes (P J : Ideal (MRing ι)) (e : ℕ)
    (hJ : IsMultiHomogIdeal J) (hJP : ¬ J ≤ P)
    (hPC : ∀ f : MRing ι, MvPolynomial.map (Int.castRingHom ℂ) f ∈ pC P → f ∈ P)
    (R : ReciprocityTheory.AnForm.R.AlgRes ι (pC P) (pC J) e) : Nonempty (AnLogRes P J e) := by
  classical
  obtain ⟨A, hA⟩ := R.exists_atlas
  choose idx hidx using R.cover
  refine ⟨{
    homog := hJ
    nondeg := hJP
    X := R.M
    A := A
    U := fun x => R.src (idx x)
    isOpen_U := fun x => R.isOpen_alt_bis (idx x)
    mem_U := hidx
    lift := fun x y q => eval (R.coord (idx x) y) (R.lift (idx x) q)
    holo := fun x p => hA.1 (idx x) (R.lift (idx x) p)
    mem := ?_
    compat := ?_
    surj := ?_
    inj := ?_
    immersion := ?_
    snc := ?_
    null := ?_ }⟩
  · intro x y hy
    rw [mem_mcPts_iff_conePts_pC]
    exact R.lift_mem (idx x) y hy
  · intro x x' y hy
    exact R.compat (idx x) (idx x') y hy
  · intro z hz hzJ
    rw [mem_mcPts_iff_conePts_pC] at hz hzJ
    obtain ⟨i, x, hx, hxz⟩ := R.surj z hz hzJ
    exact ⟨x, sameOrbit_trans (R.compat (idx x) i x ⟨hidx x, hx⟩) hxz⟩
  · intro x x' hxJ hxx
    rw [mem_mcPts_iff_conePts_pC] at hxJ
    exact R.inj (idx x) (idx x') x (hidx x) x' (hidx x') hxJ hxx
  · intro x hxJ p hp j hj
    rw [mem_mcPts_iff_conePts_pC] at hxJ
    exact R.fderiv_affCoord_ker_eq_bot A hA (idx x) x (hidx x) hxJ p hp j hj
  · intro f a hfP hf hz
    have hf' : ReciprocityTheory.AnForm.R.IsMultiHomog (map (Int.castRingHom ℂ) f) a :=
      fun m hm k => hf m (support_map_subset _ _ hm) k
    have hfP' : map (Int.castRingHom ℂ) f ∉ pC P := fun h => hfP (hPC f h)
    have hz' : ∀ z ∈ ReciprocityTheory.AnForm.R.conePts (pC P), eval z (map (Int.castRingHom ℂ) f) = 0 →
        z ∈ ReciprocityTheory.AnForm.R.conePts (pC J) := by
      intro z hz1 hz2
      rw [← mem_mcPts_iff_conePts_pC] at hz1 ⊢
      exact hz z hz1 hz2
    obtain ⟨m, hm⟩ := R.isSNC_pullback A hA idx hidx (fun _ _ => 0) _ a hf' hfP' hz'
    exact ⟨R.rc, m, R.comp, hm⟩
  · intro j
    refine MeasureTheory.measure_mono_null ?_ (R.volume_preimage_eq_zero A hA j)
    rintro y ⟨hy1, hy2⟩
    refine ⟨hy1, idx _, hidx _, ?_⟩
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hy2 ⊢
    rw [← mem_mcPts_iff_conePts_pC]
    exact hy2

end ReciprocityTheory.ChartRestriction.G.Geo
