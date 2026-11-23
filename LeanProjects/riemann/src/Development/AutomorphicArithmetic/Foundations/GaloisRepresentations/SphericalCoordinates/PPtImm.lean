import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.DetOfCharpoly

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private theorem flat_of_eventuallyEq {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {Y : Scheme.{0}}
    {s s' : V → (Sp ℂ ⟶ Y)} {v₀ w : V} (h : s =ᶠ[𝓝 v₀] s') (hf : Flat s v₀ w) : Flat s' v₀ w := by
  intro U f hU
  have h0 : s v₀ = s' v₀ := h.eq_of_nhds
  have hfd : fderiv ℂ (fun v => valAt' (s' v) U f) v₀ = fderiv ℂ (fun v => valAt' (s v) U f) v₀ := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [h] with v hv
    rw [hv]
  rw [hfd]
  exact hf U f (h0 ▸ hU)

set_option maxHeartbeats 800000 in
theorem UpperTheory.Gal.W2.ptImm_of :
    UpperTheory.Gal.W2.FlatComp → UpperTheory.Gal.W2.FlatPre → UpperTheory.Gal.W2.PtFibre → UpperTheory.Gal.W2.ExpImm → UpperTheory.Gal.W2.PtImm := by
  intro hComp hPre hPF hExp O _ bar g ρ D X s A _ S k m B P b₀ hB hb₀ hP hu z₀ w hw
  have hBU : IsOpen (B ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ))) := hB.prod isOpen_univ
  have hmem : (b₀, z₀) ∈ B ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ)) := ⟨hb₀, Set.mem_univ _⟩
  have hnhds : B ×ˢ (Set.univ : Set (Fin k → Fin g → ℂ)) ∈ 𝓝 (b₀, z₀) := hBU.mem_nhds hmem
  have hS := S.hol m B P hB hP
  have hw1 : w.1 = 0 := by
    have h1 := hComp ((Fin m → ℂ) × (Fin k → Fin g → ℂ)) (KS.pow A k).left X (KS.pow A k).hom
      (fun bz => S.pt k (P bz.1) bz.2) (b₀, z₀) w hw
    have h2 : Flat (fun bz : (Fin m → ℂ) × (Fin k → Fin g → ℂ) => S.u (P bz.1)) (b₀, z₀) w := by
      refine flat_of_eventuallyEq ?_ h1
      filter_upwards [hnhds] with bz hbz
      exact (hPF O bar g ρ D X s A S k (P bz.1) (hP.1 _ hbz.1)).1 bz.2
    have hfst : HasFDerivAt (fun bz : (Fin m → ℂ) × (Fin k → Fin g → ℂ) => bz.1)
        (ContinuousLinearMap.fst ℂ (Fin m → ℂ) (Fin k → Fin g → ℂ)) (b₀, z₀) := hasFDerivAt_fst
    have h3 : Flat (fun b => S.u (P b)) b₀
        (ContinuousLinearMap.fst ℂ (Fin m → ℂ) (Fin k → Fin g → ℂ) w) :=
      (hPre (Fin m → ℂ) ((Fin m → ℂ) × (Fin k → Fin g → ℂ)) X B (fun b => S.u (P b)) hS.1
        (fun bz => bz.1) (ContinuousLinearMap.fst ℂ (Fin m → ℂ) (Fin k → Fin g → ℂ))
        (b₀, z₀) w hfst hb₀).mp h2
    exact hu _ h3
  have hw2 : ∀ j, w.2 j = 0 := by
    intro j
    have h1 := hComp ((Fin m → ℂ) × (Fin k → Fin g → ℂ)) (KS.pow A k).left A.left
      (Over.Hom.left (KS.pr A j)) (fun bz => S.pt k (P bz.1) bz.2) (b₀, z₀) w hw
    have h2 : Flat (fun bz : (Fin m → ℂ) × (Fin k → Fin g → ℂ) =>
        Over.Hom.left (S.ex (P bz.1) (bz.2 j))) (b₀, z₀) w := by
      refine flat_of_eventuallyEq ?_ h1
      filter_upwards [hnhds] with bz hbz
      exact (hPF O bar g ρ D X s A S k (P bz.1) (hP.1 _ hbz.1)).2.1 bz.2 j
    let L : (Fin m → ℂ) × (Fin k → Fin g → ℂ) →L[ℂ] (Fin m → ℂ) × (Fin g → ℂ) :=
      (ContinuousLinearMap.fst ℂ (Fin m → ℂ) (Fin k → Fin g → ℂ)).prod
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin k => Fin g → ℂ) j).comp
          (ContinuousLinearMap.snd ℂ (Fin m → ℂ) (Fin k → Fin g → ℂ)))
    have hL : HasFDerivAt (fun bz : (Fin m → ℂ) × (Fin k → Fin g → ℂ) => (bz.1, bz.2 j)) L (b₀, z₀) :=
      L.hasFDerivAt
    have hmem2 : ((b₀, z₀).1, (b₀, z₀).2 j) ∈ B ×ˢ (Set.univ : Set (Fin g → ℂ)) :=
      ⟨hb₀, Set.mem_univ _⟩
    have h3 : Flat (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => Over.Hom.left (S.ex (P bz.1) bz.2))
        (b₀, z₀ j) (L w) :=
      (hPre ((Fin m → ℂ) × (Fin g → ℂ)) ((Fin m → ℂ) × (Fin k → Fin g → ℂ)) A.left
        (B ×ˢ Set.univ) (fun bz => Over.Hom.left (S.ex (P bz.1) bz.2)) hS.2
        (fun bz => (bz.1, bz.2 j)) L (b₀, z₀) w hL hmem2).mp h2
    have hLw : L w = (0, w.2 j) := by
      simp [L, hw1]
    rw [hLw] at h3
    have hι : HasFDerivAt (fun z : Fin g → ℂ => (b₀, z))
        (ContinuousLinearMap.inr ℂ (Fin m → ℂ) (Fin g → ℂ)) (z₀ j) :=
      (hasFDerivAt_const b₀ (z₀ j)).prodMk (hasFDerivAt_id (z₀ j))
    have hmem3 : (fun z : Fin g → ℂ => (b₀, z)) (z₀ j) ∈ B ×ˢ (Set.univ : Set (Fin g → ℂ)) :=
      ⟨hb₀, Set.mem_univ _⟩
    have h4 : Flat (fun z : Fin g → ℂ => Over.Hom.left (S.ex (P b₀) z)) (z₀ j) (w.2 j) :=
      (hPre ((Fin m → ℂ) × (Fin g → ℂ)) (Fin g → ℂ) A.left
        (B ×ˢ Set.univ) (fun bz => Over.Hom.left (S.ex (P bz.1) bz.2)) hS.2
        (fun z => (b₀, z)) (ContinuousLinearMap.inr ℂ (Fin m → ℂ) (Fin g → ℂ))
        (z₀ j) (w.2 j) hι hmem3).mpr h3
    exact hExp X A g (S.u (P b₀)) (S.ex (P b₀)) (S.exp _ (hP.1 _ hb₀)) (z₀ j) (w.2 j) h4
  exact Prod.ext hw1 (_root_.funext hw2)
