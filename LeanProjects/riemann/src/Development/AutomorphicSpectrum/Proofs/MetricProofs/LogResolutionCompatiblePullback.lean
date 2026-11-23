import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsImg
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicDegreeOneBiholomorphism
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.Deg

theorem isAnalyticSubset_preimage {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {g : X → Y} (hg : HoloMap A B g) {S : Set Y}
    (hS : B.IsAnalyticSubset S) : A.IsAnalyticSubset (g ⁻¹' S) := by
  intro x
  obtain ⟨W, hW, hx, r, f, hf, hSW⟩ := hS (g x)
  refine ⟨g ⁻¹' W, hW.preimage hg.1, hx, r, fun i => f i ∘ g, fun i => Cj.holoOn_comp hg (hf i), ?_⟩
  ext y
  have h1 := Set.ext_iff.1 hSW (g y)
  simpa using h1

theorem det_fderiv_ne_zero_of_factor {n : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {T : (Fin n → ℂ) → Fin n → ℂ} {Q L : (Fin n → ℂ) → E} {t : Fin n → ℂ}
    (hT : DifferentiableAt ℂ T t) (hQ : DifferentiableAt ℂ Q (T t)) (hL : L =ᶠ[𝓝 t] Q ∘ T)
    (hker : (fderiv ℂ L t).ker = ⊥) :
    LinearMap.det (fderiv ℂ T t : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0 := by
  intro h0
  have hlt := LinearMap.bot_lt_ker_of_det_eq_zero h0
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hlt.ne'
  have hv' : fderiv ℂ T t v = 0 := hv
  have hd : fderiv ℂ L t = (fderiv ℂ Q (T t)).comp (fderiv ℂ T t) := by
    rw [hL.fderiv_eq]
    exact fderiv_comp t hQ hT
  have hmem : v ∈ (fderiv ℂ L t).ker := by
    show fderiv ℂ L t v = 0
    rw [hd]
    simp [hv']
  rw [hker] at hmem
  exact hv0 (by simpa using hmem)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem affCoord_eq_of_orbit {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (p : (k : K) → ι k) :
    affCoord p z = affCoord p z' := by
  obtain ⟨c, hc, rfl⟩ := h
  funext q
  simp only [affCoord]
  exact mul_div_mul_left _ _ (hc q.1)

theorem analyticAt_affCoord {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : E → (Σ k, ι k) → ℂ} {u : E} (hF : AnalyticAt ℂ F u) (p : (k : K) → ι k)
    (hp : ∀ k, F u ⟨k, p k⟩ ≠ 0) : AnalyticAt ℂ (fun v => affCoord p (F v)) u := by
  have hc : ∀ q, AnalyticAt ℂ (fun v => F v q) u := analyticAt_pi_iff.1 hF
  refine analyticAt_pi_iff.2 fun q => ?_
  exact (hc q).div (hc ⟨q.1, p q.1⟩) (hp q.1)

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.Deg

namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.Deg

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem det_ne_zero_of_local_inverse {P J : Ideal (MRing ι)} {P' J' : Ideal (MRing ι')} {D : ℕ}
    {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} (R : AnLogRes P J D) (R' : AnLogRes P' J' D)
    {π : R.X → X} {ρ : X → R.X} {h : R'.X → X}
    {Rel : ((Σ k, ι' k) → ℂ) → ((Σ k, ι k) → ℂ) → Prop}
    (hρ : HoloMap A R.A ρ) (hπρ : ∀ s, π (ρ s) = s) (hh : HoloMap R'.A A h)
    (hRelO : ∀ z z₁ w w₁, Rel z w → SameOrbit z₁ z → SameOrbit w₁ w → Rel z₁ w₁)
    (hgr : ∀ x x₀, π x₀ = h x → Rel (R'.lift x x) (R.lift x₀ x₀))
    (j : Fin R'.A.n) (c : Fin A.n) (t : Fin D → ℂ) (ht : t ∈ (R'.A.chart j).target)
    (hc : h ((R'.A.chart j).symm t) ∈ (A.chart c).source)
    (hzJ : R'.lift ((R'.A.chart j).symm t) ((R'.A.chart j).symm t) ∉ mcPts J')
    {V : Set ((Σ k, ι k) → ℂ)} {V' : Set ((Σ k, ι' k) → ℂ)} {f : ((Σ k, ι k) → ℂ) → (Σ k, ι' k) → ℂ}
    (hV : IsOpen V)
    (hwV : R.lift (ρ (h ((R'.A.chart j).symm t))) (ρ (h ((R'.A.chart j).symm t))) ∈ V)
    (hV' : IsOpen V') (hzV : R'.lift ((R'.A.chart j).symm t) ((R'.A.chart j).symm t) ∈ V')
    (hf : AnalyticOnNhd ℂ f V)
    (hrel : ∀ z'' ∈ V' ∩ mcPts P', ∀ w ∈ V ∩ mcPts P, Rel z'' w → SameOrbit (f w) z'') :
    LinearMap.det (fderiv ℂ (A.chart c ∘ h ∘ (R'.A.chart j).symm) t :
      (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) ≠ 0 := by
  obtain ⟨x, hx⟩ : ∃ x, x = (R'.A.chart j).symm t := ⟨_, rfl⟩
  rw [← hx] at hc hzJ hwV hzV
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ = ρ (h x) := ⟨_, rfl⟩
  rw [← hx₀] at hwV
  have hxs : x ∈ (R'.A.chart j).source := hx ▸ (R'.A.chart j).map_target ht
  have hjt : R'.A.chart j x = t := by rw [hx]; exact (R'.A.chart j).right_inv ht
  obtain ⟨T, hT⟩ : ∃ T, T = A.chart c ∘ h ∘ (R'.A.chart j).symm := ⟨_, rfl⟩
  rw [← hT]
  have hTa : AnalyticAt ℂ T t := by
    rw [hT]; exact hh.2 j c t ⟨ht, by rw [Set.mem_preimage, Set.mem_preimage, ← hx]; exact hc⟩
  have hTval : T t = A.chart c (h x) := by rw [hT, hx]; rfl
  have hTs : (A.chart c).symm (T t) = h x := by rw [hTval]; exact (A.chart c).left_inv hc
  have hTtar : T t ∈ (A.chart c).target := by rw [hTval]; exact (A.chart c).map_source hc
  obtain ⟨E, hE⟩ : ∃ E : (Fin D → ℂ) → (Σ k, ι k) → ℂ,
      E = fun u => R.lift x₀ (ρ ((A.chart c).symm u)) := ⟨_, rfl⟩
  have hEa : AnalyticAt ℂ E (T t) := by
    refine analyticAt_pi_iff.2 fun q => ?_
    have h1 := Cj.holoOn_comp hρ (R.holo x₀ q)
    have h2 := h1 c (T t) ⟨hTtar, by
      rw [Set.mem_preimage, Set.mem_preimage, hTs, ← hx₀]; exact R.mem_U x₀⟩
    rw [hE]; exact h2
  have hEt : E (T t) = R.lift x₀ x₀ := by
    rw [hE]; show R.lift x₀ (ρ ((A.chart c).symm (T t))) = _
    rw [hTs, ← hx₀]
  have hzP : R'.lift x x ∈ mcPts P' := R'.mem x x (R'.mem_U x)
  have hwP : R.lift x₀ x₀ ∈ mcPts P := R.mem x₀ x₀ (R.mem_U x₀)
  have hπ₀ : π x₀ = h x := by rw [hx₀]; exact hπρ _
  have horb0 : SameOrbit (f (R.lift x₀ x₀)) (R'.lift x x) :=
    hrel _ ⟨hzV, hzP⟩ _ ⟨hwV, hwP⟩ (hgr x x₀ hπ₀)
  choose p hp using hzP.1
  have hfE : AnalyticAt ℂ (f ∘ E) (T t) := by
    have h1 : AnalyticAt ℂ f (E (T t)) := by rw [hEt]; exact hf _ hwV
    exact h1.comp hEa
  have hfp : ∀ k, (f ∘ E) (T t) ⟨k, p k⟩ ≠ 0 := fun k => by
    obtain ⟨a, ha, hfa⟩ := horb0
    show f (E (T t)) ⟨k, p k⟩ ≠ 0
    rw [hEt, hfa]
    exact mul_ne_zero (ha k) (hp k)
  have hQ := analyticAt_affCoord hfE p hfp
  obtain ⟨L, hLdef⟩ : ∃ L : (Fin D → ℂ) → (Σ k, ι' k) → ℂ,
      L = fun y => R'.lift x ((R'.A.chart j).symm y) := ⟨_, rfl⟩
  have hLa : AnalyticAt ℂ L t := by
    refine analyticAt_pi_iff.2 fun q => ?_
    have h2 := R'.holo x q j t ⟨ht, by
      rw [Set.mem_preimage, ← hx]; exact R'.mem_U x⟩
    rw [hLdef]; exact h2
  have hLt : L t = R'.lift x x := by rw [hLdef, hx]
  have hsc : ContinuousAt (R'.A.chart j).symm t := (R'.A.chart j).continuousAt_symm ht
  have hsx : (R'.A.chart j).symm t = x := hx.symm
  have hhc : ContinuousAt (fun y => h ((R'.A.chart j).symm y)) t :=
    hh.1.continuousAt.comp hsc
  have hρc : ContinuousAt (fun y => ρ (h ((R'.A.chart j).symm y))) t :=
    hρ.1.continuousAt.comp hhc
  have e1 : ∀ᶠ y in 𝓝 t, y ∈ (R'.A.chart j).target := (R'.A.chart j).open_target.mem_nhds ht
  have e2 : ∀ᶠ y in 𝓝 t, (R'.A.chart j).symm y ∈ R'.U x :=
    hsc.eventually_mem ((R'.isOpen_U x).mem_nhds (by rw [hsx]; exact R'.mem_U x))
  have e3 : ∀ᶠ y in 𝓝 t, L y ∈ V' :=
    hLa.continuousAt.eventually_mem (hV'.mem_nhds (by rw [hLt]; exact hzV))
  have e4 : ∀ᶠ y in 𝓝 t, h ((R'.A.chart j).symm y) ∈ (A.chart c).source :=
    hhc.eventually_mem ((A.chart c).open_source.mem_nhds (by rw [hsx]; exact hc))
  have e5 : ∀ᶠ y in 𝓝 t, ρ (h ((R'.A.chart j).symm y)) ∈ R.U x₀ :=
    hρc.eventually_mem ((R.isOpen_U x₀).mem_nhds (by rw [hsx, ← hx₀]; exact R.mem_U x₀))
  have e6 : ∀ᶠ y in 𝓝 t, E (T y) ∈ V := by
    have hcc : ContinuousAt (fun y => E (T y)) t :=
      ContinuousAt.comp (g := E) hEa.continuousAt hTa.continuousAt
    exact hcc.eventually_mem (hV.mem_nhds (by rw [hEt]; exact hwV))
  have hfac : (fun y => affCoord p (L y)) =ᶠ[𝓝 t]
      (fun u => affCoord p ((f ∘ E) u)) ∘ T := by
    filter_upwards [e2, e3, e4, e5, e6] with y h2 h3 h4 h5 h6
    obtain ⟨x', hx'⟩ : ∃ x', x' = (R'.A.chart j).symm y := ⟨_, rfl⟩
    rw [← hx'] at h2 h4 h5
    have hTy : (A.chart c).symm (T y) = h x' := by
      rw [hT]; show (A.chart c).symm (A.chart c (h ((R'.A.chart j).symm y))) = _
      rw [← hx']; exact (A.chart c).left_inv h4
    have hEy : E (T y) = R.lift x₀ (ρ (h x')) := by
      rw [hE]; show R.lift x₀ (ρ ((A.chart c).symm (T y))) = _
      rw [hTy]
    have hLy : L y = R'.lift x x' := by rw [hLdef, hx']
    rw [hLy] at h3
    have hg := hgr x' (ρ (h x')) (hπρ _)
    have o1 : SameOrbit (R'.lift x x') (R'.lift x' x') := R'.compat x x' x' ⟨h2, R'.mem_U x'⟩
    have o2 : SameOrbit (R.lift x₀ (ρ (h x'))) (R.lift (ρ (h x')) (ρ (h x'))) :=
      R.compat x₀ _ _ ⟨h5, R.mem_U _⟩
    have hr : Rel (R'.lift x x') (E (T y)) := by
      rw [hEy]; exact hRelO _ _ _ _ hg o1 o2
    have hso := hrel _ ⟨h3, R'.mem x x' h2⟩ _ ⟨h6, by rw [hEy]; exact R.mem x₀ _ h5⟩ hr
    show affCoord p (L y) = affCoord p (f (E (T y)))
    rw [hLy]
    exact (affCoord_eq_of_orbit hso p).symm
  have himm := R'.immersion x hzJ p hp j hxs
  rw [hjt] at himm
  have hker : (fderiv ℂ (fun y => affCoord p (L y)) t).ker = ⊥ := by
    rw [hLdef]; exact himm
  exact det_fderiv_ne_zero_of_factor hTa.differentiableAt hQ.differentiableAt hfac hker

theorem isDegreeOff_of_correspondence : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (P J : Ideal (MRing ι)) (P' J' : Ideal (MRing ι')) (D : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas D X) (R : AnLogRes P J D) (π : R.X → X) (R' : AnLogRes P' J' D) (h : R'.X → X) (Rel : ((Σ k, ι' k) → ℂ) → ((Σ k, ι k) → ℂ) → Prop) (G : MRing ι) (G₂ : MRing ι') (aG : K → ℕ) (aG₂ : K' → ℕ) (e : ℕ), J = ⊤ → IsArithVar P (D + 1) → IsArithVar P' (D + 1) → HoloMap R.A A π → IsDegreeOff A R.A π 1 ∅ → HoloMap R'.A A h → IsMultiHomog G aG → G ∉ P → IsMultiHomog G₂ aG₂ → G₂ ∉ P' → (∀ z z₁ w w₁, Rel z w → SameOrbit z₁ z → SameOrbit w₁ w → Rel z₁ w₁) → (∀ x x₀, π x₀ = h x → Rel (R'.lift x x) (R.lift x₀ x₀)) → (∀ x x₀, Rel (R'.lift x x) (R.lift x₀ x₀) → π x₀ = h x) → (∀ w ∈ mcPts P, eval w (map (Int.castRingHom ℂ) G) ≠ 0 → {O | ∃ z ∈ mcPts P', O = {z'' | SameOrbit z'' z} ∧ Rel z w}.ncard = e) → (∀ z ∈ mcPts P', z ∈ mcPts J' → ∀ w ∈ mcPts P, Rel z w → eval w (map (Int.castRingHom ℂ) G) = 0) → (∀ z ∈ mcPts P', ∀ w ∈ mcPts P, Rel z w → eval w (map (Int.castRingHom ℂ) G) = 0 → eval z (map (Int.castRingHom ℂ) G₂) = 0) → (∀ z ∈ mcPts P', ∀ w₀ ∈ mcPts P, Rel z w₀ → eval w₀ (map (Int.castRingHom ℂ) G) ≠ 0 → ∃ (V : Set ((Σ k, ι k) → ℂ)) (V' : Set ((Σ k, ι' k) → ℂ)) (f : ((Σ k, ι k) → ℂ) → (Σ k, ι' k) → ℂ), IsOpen V ∧ w₀ ∈ V ∧ IsOpen V' ∧ z ∈ V' ∧ AnalyticOnNhd ℂ f V ∧ ∀ z'' ∈ V' ∩ mcPts P', ∀ w ∈ V ∩ mcPts P, Rel z'' w → SameOrbit (f w) z'') → IsDegreeOff A R'.A h e (π '' {x | eval (R.lift x x) (map (Int.castRingHom ℂ) G) = 0}) := by
  intro K _ ι _ K' _ ι' _ P J P' J' D X _ _ _ A R π R' h Rel G G₂ aG aG₂ e _ hP hP' hπ hπ1 hh hG hGP hG₂
    hG₂P hRelO hgr hgr' hcount hJ' hG₂z hinv
  obtain ⟨ρ, hρπ, hπρ, hρ⟩ := Cj.exists_holoMap_inverse_of_degree_one A R.A π hπ hπ1
  obtain ⟨S, hS⟩ : ∃ S : Set R.X, S = {x | eval (R.lift x x) (map (Int.castRingHom ℂ) G) = 0} := ⟨_, rfl⟩
  rw [← hS]
  have hbr : π '' S = ρ ⁻¹' S := by
    ext s
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Set.mem_preimage, hρπ]; exact hx
    · intro hs
      exact ⟨ρ s, hs, hπρ s⟩
  rw [hbr]
  have hSa : R.A.IsAnalyticSubset S := by
    rw [hS]; exact HilbertSamuel.AnResNullForm.isAnalyticSubset R.toAnRes hG
  have hSi : interior S = ∅ := by
    rw [hS]
    exact HilbertSamuel.AnResNullForm.interior_eq_empty HilbertSamuel.NonvanishingDense.full R.toAnRes hP hG hGP
  have hS₂i : interior {x | eval (R'.lift x x) (map (Int.castRingHom ℂ) G₂) = 0} = ∅ :=
    HilbertSamuel.AnResNullForm.interior_eq_empty HilbertSamuel.NonvanishingDense.full R'.toAnRes hP' hG₂ hG₂P
  have hbA : A.IsAnalyticSubset (ρ ⁻¹' S) := isAnalyticSubset_preimage hρ hSa
  refine ⟨hbA, ?_, isAnalyticSubset_preimage hh hbA, ?_, ?_, ?_⟩
  · let Eq : X ≃ₜ R.X :=
      { toFun := ρ, invFun := π, left_inv := hπρ, right_inv := hρπ,
        continuous_toFun := hρ.1, continuous_invFun := hπ.1 }
    have h1 : Eq ⁻¹' interior S = interior (Eq ⁻¹' S) := Eq.preimage_interior S
    have h2 : interior (ρ ⁻¹' S) = Eq ⁻¹' interior S := h1.symm
    rw [h2, hSi, Set.preimage_empty]
  · refine Set.eq_empty_of_subset_empty ?_
    rw [← hS₂i]
    refine interior_mono fun x hx => ?_
    have hxS : ρ (h x) ∈ S := hx
    rw [hS] at hxS
    exact hG₂z _ (R'.mem x x (R'.mem_U x)) _ (R.mem _ _ (R.mem_U _)) (hgr x _ (hπρ _)) hxS
  · intro s hs
    obtain ⟨x₀, hx₀⟩ : ∃ x₀, x₀ = ρ s := ⟨_, rfl⟩
    have hπs : π x₀ = s := by rw [hx₀]; exact hπρ s
    have hGw : eval (R.lift x₀ x₀) (map (Int.castRingHom ℂ) G) ≠ 0 := by
      intro h0
      apply hs
      show ρ s ∈ S
      rw [← hx₀, hS]
      exact h0
    have hwP : R.lift x₀ x₀ ∈ mcPts P := R.mem x₀ x₀ (R.mem_U x₀)
    have hc := hcount _ hwP hGw
    have himg : {O | ∃ z ∈ mcPts P', O = {z'' | SameOrbit z'' z} ∧ Rel z (R.lift x₀ x₀)} =
        (fun x => {z'' | SameOrbit z'' (R'.lift x x)}) '' (h ⁻¹' {s}) := by
      ext O
      constructor
      · rintro ⟨z, hz, rfl, hr⟩
        have hzJ : z ∉ mcPts J' := fun hzJ => hGw (hJ' z hz hzJ _ hwP hr)
        obtain ⟨x, hx⟩ := R'.surj z hz hzJ
        refine ⟨x, ?_, ?_⟩
        · have h1 := hgr' x x₀ (hRelO _ _ _ _ hr hx (Cj.sameOrbit_refl _))
          show h x = s
          rw [← h1, hπs]
        · ext z''
          exact ⟨fun h1 => Cj.sameOrbit_trans h1 hx, fun h1 => Cj.sameOrbit_trans h1 (Cj.sameOrbit_symm hx)⟩
      · rintro ⟨x, hx, rfl⟩
        have hxs : h x = s := hx
        exact ⟨R'.lift x x, R'.mem x x (R'.mem_U x), rfl, hgr x x₀ (by rw [hπs, hxs])⟩
    rw [himg] at hc
    rw [← hc]
    refine (Set.ncard_image_of_injOn ?_).symm
    intro x hx x' _ hxx
    have hxs : h x = s := hx
    have hxJ : R'.lift x x ∉ mcPts J' := fun hzJ =>
      hGw (hJ' _ (R'.mem x x (R'.mem_U x)) hzJ _ hwP (hgr x x₀ (by rw [hπs, hxs])))
    have hmem : R'.lift x x ∈ {z'' | SameOrbit z'' (R'.lift x' x')} := by
      have h1 : R'.lift x x ∈ {z'' | SameOrbit z'' (R'.lift x x)} := Cj.sameOrbit_refl _
      exact (Set.ext_iff.1 hxx _).1 h1
    exact R'.inj x x' hxJ hmem
  · intro j c y hy hyn hc
    have hyS : ρ (h ((R'.A.chart j).symm y)) ∉ S := hyn
    rw [hS] at hyS
    have hGw : eval (R.lift (ρ (h ((R'.A.chart j).symm y))) (ρ (h ((R'.A.chart j).symm y))))
        (map (Int.castRingHom ℂ) G) ≠ 0 := hyS
    have hzP := R'.mem _ _ (R'.mem_U ((R'.A.chart j).symm y))
    have hwP := R.mem _ _ (R.mem_U (ρ (h ((R'.A.chart j).symm y))))
    have hr := hgr ((R'.A.chart j).symm y) (ρ (h ((R'.A.chart j).symm y))) (hπρ _)
    have hzJ : R'.lift ((R'.A.chart j).symm y) ((R'.A.chart j).symm y) ∉ mcPts J' :=
      fun hzJ => hGw (hJ' _ hzP hzJ _ hwP hr)
    obtain ⟨V, V', f, hV, hwV, hV', hzV, hf, hrel⟩ := hinv _ hzP _ hwP hr hGw
    exact det_ne_zero_of_local_inverse R R' hρ hπρ hh hRelO hgr j c y hy hc hzJ hV hwV hV' hzV hf hrel

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.Deg
