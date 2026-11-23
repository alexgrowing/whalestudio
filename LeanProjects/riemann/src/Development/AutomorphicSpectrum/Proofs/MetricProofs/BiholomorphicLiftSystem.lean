import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SameOrbitRefl
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Cj.ResTop

theorem not_mem_mcPts_top {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (z : (Σ k, ι k) → ℂ) : z ∉ mcPts (⊤ : Ideal (MRing ι)) := by
  intro hz
  have h := hz.2 1 Submodule.mem_top
  simp at h

theorem fderiv_injective_of_leftInv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {τ : E → F} {σ : F → E} {a : E}
    (hτ : DifferentiableAt ℂ τ a) (hσ : DifferentiableAt ℂ σ (τ a))
    (h : σ ∘ τ =ᶠ[nhds a] id) : Function.Injective (fderiv ℂ τ a) := by
  have h1 : fderiv ℂ (σ ∘ τ) a = (fderiv ℂ σ (τ a)).comp (fderiv ℂ τ a) :=
    fderiv_comp a hσ hτ
  have h2 : fderiv ℂ (σ ∘ τ) a = ContinuousLinearMap.id ℂ E := by
    rw [h.fderiv_eq]; exact fderiv_id
  intro u v huv
  have hu : (fderiv ℂ (σ ∘ τ) a) u = u := by rw [h2]; rfl
  have hv : (fderiv ℂ (σ ∘ τ) a) v = v := by rw [h2]; rfl
  rw [← hu, ← hv, h1]
  simp [huv]

theorem differentiableAt_affCoord {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e) (x : R.X) (p : (k : K) → ι k)
    (hp : ∀ k, R.lift x x ⟨k, p k⟩ ≠ 0) (k : Fin R.A.n) (hk : x ∈ (R.A.chart k).source) :
    DifferentiableAt ℂ (fun w => affCoord p (R.lift x ((R.A.chart k).symm w)))
      (R.A.chart k x) := by
  have hmem : R.A.chart k x ∈ (R.A.chart k).target ∩ (R.A.chart k).symm ⁻¹' R.U x :=
    ⟨(R.A.chart k).map_source hk, by
      simpa only [Set.mem_preimage, (R.A.chart k).left_inv hk] using R.mem_U x⟩
  rw [differentiableAt_pi]
  intro q
  have hn : AnalyticAt ℂ ((fun y => R.lift x y q) ∘ (R.A.chart k).symm) (R.A.chart k x) :=
    R.holo x q k _ hmem
  have hd : AnalyticAt ℂ ((fun y => R.lift x y ⟨q.1, p q.1⟩) ∘ (R.A.chart k).symm)
      (R.A.chart k x) := R.holo x ⟨q.1, p q.1⟩ k _ hmem
  have hne : ((fun y => R.lift x y ⟨q.1, p q.1⟩) ∘ (R.A.chart k).symm) (R.A.chart k x) ≠ 0 := by
    simp only [Function.comp, (R.A.chart k).left_inv hk]
    exact hp q.1
  exact (hn.div hd hne).differentiableAt

theorem isLiftSys_of_top {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P J : Ideal (MRing ι)} (hJ : J = ⊤) {e : ℕ} (R : AnLogRes P J e) {X : Type}
    [TopologicalSpace X] (A : FinHolAtlas e X) (g : X → R.X) (h : R.X → X)
    (hgh : ∀ y, g (h y) = y) (hhg : ∀ x, h (g x) = x) (hg : HoloMap A R.A g)
    (hh : HoloMap R.A A h) :
    IsLiftSys A P (fun x => g ⁻¹' R.U (g x)) (fun x y => R.lift (g x) (g y)) := by
  subst hJ
  refine ⟨fun x => (R.isOpen_U (g x)).preimage hg.1, fun x => R.mem_U (g x),
    fun x p => holoOn_comp hg (R.holo (g x) p), fun x y hy => R.mem _ _ hy,
    fun x x' y hy => R.compat _ _ _ hy, ?_, ?_, ?_⟩
  · intro z hz
    obtain ⟨y, hy⟩ := R.surj z hz (not_mem_mcPts_top z)
    exact ⟨h y, by simpa only [hgh] using hy⟩
  · intro x x' hs
    have := R.inj (g x) (g x') (not_mem_mcPts_top _) hs
    rw [← hhg x, ← hhg x', this]
  · intro x p hp j hj
    obtain ⟨k, hk⟩ := R.A.cover (g x)
    set a := A.chart j with ha
    set c := R.A.chart k with hc
    have hax : a.symm (a x) = x := a.left_inv hj
    have hcx : c.symm (c (g x)) = g x := c.left_inv hk
    set τ : (Fin e → ℂ) → (Fin e → ℂ) := c ∘ g ∘ a.symm with hτdef
    set σ : (Fin e → ℂ) → (Fin e → ℂ) := a ∘ h ∘ c.symm with hσdef
    have hτx : τ (a x) = c (g x) := by simp only [hτdef, Function.comp, hax]
    have hτ : AnalyticAt ℂ τ (a x) := hg.2 j k (a x)
      ⟨a.map_source hj, show g (a.symm (a x)) ∈ c.source by rw [hax]; exact hk⟩
    have hσ : AnalyticAt ℂ σ (c (g x)) := hh.2 k j (c (g x))
      ⟨c.map_source hk, show h (c.symm (c (g x))) ∈ a.source by rw [hcx, hhg]; exact hj⟩

    have hcont : ContinuousAt (g ∘ a.symm) (a x) :=
      hg.1.continuousAt.comp (a.continuousAt_symm (a.map_source hj))
    have hnear : ∀ᶠ y in nhds (a x), g (a.symm y) ∈ c.source ∧ y ∈ a.target := by
      refine (hcont.eventually_mem (c.open_source.mem_nhds ?_)).and
        (a.open_target.mem_nhds (a.map_source hj))
      simpa only [Function.comp, hax] using hk
    have hleft : σ ∘ τ =ᶠ[nhds (a x)] id := by
      filter_upwards [hnear] with y hy
      simp only [hσdef, hτdef, Function.comp, c.left_inv hy.1, hhg, id, a.right_inv hy.2]
    have hinj := fderiv_injective_of_leftInv hτ.differentiableAt
      (by rw [hτx]; exact hσ.differentiableAt) hleft
    have hF := differentiableAt_affCoord R (g x) p hp k hk
    have himm := R.immersion (g x) (not_mem_mcPts_top _) p hp k hk
    set F : (Fin e → ℂ) → (Σ k, ι k) → ℂ :=
      fun w => affCoord p (R.lift (g x) ((R.A.chart k).symm w)) with hFdef
    have hcomp : (fun y => affCoord p (R.lift (g x) (g (a.symm y)))) =ᶠ[nhds (a x)] F ∘ τ := by
      filter_upwards [hnear] with y hy
      simp only [hFdef, hτdef, Function.comp, ← hc, c.left_inv hy.1]
    have hder : fderiv ℂ (fun y => affCoord p (R.lift (g x) (g (a.symm y)))) (a x) =
        (fderiv ℂ F (c (g x))).comp (fderiv ℂ τ (a x)) := by
      rw [hcomp.fderiv_eq, fderiv_comp (a x) (by rw [hτx]; exact hF) hτ.differentiableAt, hτx]
    show (fderiv ℂ (fun y => affCoord p (R.lift (g x) (g (a.symm y)))) (a x)).ker = ⊥
    rw [hder, eq_bot_iff]
    intro v hv
    have h1 : (fderiv ℂ F (c (g x))) ((fderiv ℂ τ (a x)) v) = 0 := by simpa using hv
    have h2 : (fderiv ℂ τ (a x)) v ∈ (fderiv ℂ F (c (g x))).ker := by simpa using h1
    rw [himm] at h2
    have h3 : (fderiv ℂ τ (a x)) v = 0 := by simpa using h2
    have h4 : v = 0 := hinj (h3.trans (map_zero _).symm)
    simp [h4]

end GlobalTheory.CompanionTheory.Ar.PB.Cj.ResTop
