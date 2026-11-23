import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphic
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagBundlePartialBlockMapStatement

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem dim_eq_of_holo_inverse {a b : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : FinHolAtlas a X) (B : FinHolAtlas b Y) (f : X → Y) (g : Y → X)
    (hf : HoloMap A B f) (hg : HoloMap B A g) (hgf : ∀ x, g (f x) = x) (hfg : ∀ y, f (g y) = y) (x : X) :
    a = b := by
  obtain ⟨j, hj⟩ := A.cover x
  obtain ⟨k, hk⟩ := B.cover (f x)
  have hu_t : A.chart j x ∈ (A.chart j).target := (A.chart j).map_source hj
  have hw_t : B.chart k (f x) ∈ (B.chart k).target := (B.chart k).map_source hk
  have hsu : (A.chart j).symm (A.chart j x) = x := (A.chart j).left_inv hj
  have hsw : (B.chart k).symm (B.chart k (f x)) = f x := (B.chart k).left_inv hk
  let F : (Fin a → ℂ) → (Fin b → ℂ) := B.chart k ∘ f ∘ (A.chart j).symm
  let G : (Fin b → ℂ) → (Fin a → ℂ) := A.chart j ∘ g ∘ (B.chart k).symm
  have hFu : F (A.chart j x) = B.chart k (f x) := by
    show B.chart k (f ((A.chart j).symm (A.chart j x))) = _
    rw [hsu]
  have hGw : G (B.chart k (f x)) = A.chart j x := by
    show A.chart j (g ((B.chart k).symm (B.chart k (f x)))) = _
    rw [hsw, hgf]
  have dF : DifferentiableAt ℂ F (A.chart j x) :=
    (hf.2 j k _ ⟨hu_t, by
      show f ((A.chart j).symm (A.chart j x)) ∈ (B.chart k).source
      rw [hsu]; exact hk⟩).differentiableAt
  have dG : DifferentiableAt ℂ G (B.chart k (f x)) :=
    (hg.2 k j _ ⟨hw_t, by
      show g ((B.chart k).symm (B.chart k (f x))) ∈ (A.chart j).source
      rw [hsw, hgf]; exact hj⟩).differentiableAt
  have e1 : G ∘ F =ᶠ[𝓝 (A.chart j x)] id := by
    have c : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j x) :=
      hf.1.continuousAt.comp ((A.chart j).continuousAt_symm hu_t)
    have hs : ∀ᶠ v in 𝓝 (A.chart j x), (f ∘ (A.chart j).symm) v ∈ (B.chart k).source :=
      c.eventually ((B.chart k).open_source.mem_nhds (by
        show f ((A.chart j).symm (A.chart j x)) ∈ (B.chart k).source
        rw [hsu]; exact hk))
    filter_upwards [hs, (A.chart j).open_target.mem_nhds hu_t] with v h1 h2
    have h1' : f ((A.chart j).symm v) ∈ (B.chart k).source := h1
    show A.chart j (g ((B.chart k).symm (B.chart k (f ((A.chart j).symm v))))) = v
    rw [(B.chart k).left_inv h1', hgf, (A.chart j).right_inv h2]
  have e2 : F ∘ G =ᶠ[𝓝 (B.chart k (f x))] id := by
    have c : ContinuousAt (g ∘ (B.chart k).symm) (B.chart k (f x)) :=
      hg.1.continuousAt.comp ((B.chart k).continuousAt_symm hw_t)
    have hs : ∀ᶠ v in 𝓝 (B.chart k (f x)), (g ∘ (B.chart k).symm) v ∈ (A.chart j).source :=
      c.eventually ((A.chart j).open_source.mem_nhds (by
        show g ((B.chart k).symm (B.chart k (f x))) ∈ (A.chart j).source
        rw [hsw, hgf]; exact hj))
    filter_upwards [hs, (B.chart k).open_target.mem_nhds hw_t] with v h1 h2
    have h1' : g ((B.chart k).symm v) ∈ (A.chart j).source := h1
    show B.chart k (f ((A.chart j).symm (A.chart j (g ((B.chart k).symm v))))) = v
    rw [(A.chart j).left_inv h1', hfg, (B.chart k).right_inv h2]
  have d1 : (fderiv ℂ G (B.chart k (f x))).comp (fderiv ℂ F (A.chart j x)) = ContinuousLinearMap.id ℂ _ := by
    have dG' : DifferentiableAt ℂ G (F (A.chart j x)) := by rw [hFu]; exact dG
    have h := fderiv_comp (A.chart j x) dG' dF
    rw [e1.fderiv_eq, fderiv_id, hFu] at h
    exact h.symm
  have d2 : (fderiv ℂ F (A.chart j x)).comp (fderiv ℂ G (B.chart k (f x))) = ContinuousLinearMap.id ℂ _ := by
    have dF' : DifferentiableAt ℂ F (G (B.chart k (f x))) := by rw [hGw]; exact dF
    have h := fderiv_comp (B.chart k (f x)) dF' dG
    rw [e2.fderiv_eq, fderiv_id, hGw] at h
    exact h.symm
  let E : (Fin a → ℂ) ≃ₗ[ℂ] (Fin b → ℂ) := LinearEquiv.ofLinearMap
    (fderiv ℂ F (A.chart j x) : (Fin a → ℂ) →ₗ[ℂ] (Fin b → ℂ))
    (fderiv ℂ G (B.chart k (f x)) : (Fin b → ℂ) →ₗ[ℂ] (Fin a → ℂ))
    (LinearMap.ext fun v => congrArg (fun L : (Fin b → ℂ) →L[ℂ] (Fin b → ℂ) => L v) d2)
    (LinearMap.ext fun v => congrArg (fun L : (Fin a → ℂ) →L[ℂ] (Fin a → ℂ) => L v) d1)
  simpa using E.finrank_eq

theorem dim_eq_of_res {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {a b : ℕ}
    (R : AnLogRes P ⊤ a) (hJ : J = ⊤) (R' : AnLogRes P J b) (x : R'.X) : a = b := by
  subst hJ
  have hP : P ≤ imageZ id P := fun f hf => by
    show rename id f ∈ P
    rwa [rename_id_apply]
  obtain ⟨h, hh, ho⟩ := GlobalTheory.CompanionTheory.Ar.PB.Proj.holoMap_of_blockProj K ι K ι id id P P ⊤ a b R R' isBlockMap_id hP
  obtain ⟨g, hg, go⟩ := GlobalTheory.CompanionTheory.Ar.PB.Proj.holoMap_of_blockProj K ι K ι id id P P ⊤ b a R' R isBlockMap_id hP
  have hemp : ∀ z, z ∉ mcPts (⊤ : Ideal (MRing ι)) := fun z hz => by
    have := hz.2 1 trivial
    simp at this
  have hgh : ∀ x, g (h x) = x := fun x => R'.inj _ _ (hemp _) (orbit_trans (go (h x)) (ho x))
  have hhg : ∀ x, h (g x) = x := fun x => R.inj _ _ (hemp _) (orbit_trans (ho (g x)) (go x))
  exact dim_eq_of_holo_inverse R.A R'.A g h hg hh hhg hgh (h x)

theorem flagAn_dim : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d), d + 1 = n + Fintype.card Ψ * (j.choose 2 + (N - j).choose 2) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA
  have hk : ∀ k, k ∈ Set.range (id : K → K) ↔
      ((∀ p, M.blk p ≠ some k) ∨ ∃ p, (fun _ : Ψ × Fin N => True) p ∧ M.blk p = some k) := fun k =>
    ⟨fun _ => by
      by_cases h : ∀ p, M.blk p ≠ some k
      · exact Or.inl h
      · obtain ⟨p, hp⟩ := not_forall.1 h
        exact Or.inr ⟨p, trivial, not_not.1 hp⟩, fun _ => ⟨k, rfl⟩⟩
  obtain ⟨e, R, he, -⟩ := GlobalTheory.T.flag_bundle_partial_block_map K ι Φ y Ψ N j M n _ BM.Rb rfl (fun _ => True) K ι id id isBlockMap_id hk
  have R2 : AnLogRes (mCoordIdeal y) ⊤ e := R
  obtain ⟨z, hz, hJ⟩ :=
    GroundTheory.Heights₂.Heights.HilbertSamuel.exists_mcPts_not_mem_mcPts FA.Re.arith FA.Re.R.nondeg
  obtain ⟨x, -⟩ := FA.Re.R.surj z hz hJ
  rw [← he fun _ => trivial]
  exact (dim_eq_of_res R2 FA.J_top FA.Re.R x).symm

end GlobalTheory.CompanionTheory.Ar.PB.WSq
