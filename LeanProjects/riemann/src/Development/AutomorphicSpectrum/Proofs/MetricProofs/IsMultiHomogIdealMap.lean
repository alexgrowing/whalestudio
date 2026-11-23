import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SameOrbitRefl
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsImg
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPointsStatement
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogOfPullWeight
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFirstStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticSecondStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticThirdStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionMapLocallyAnalyticStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionCompatiblePullbackStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFourthStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFifthStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticSixthStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticSeventhStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticEighthStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticNinthStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap

section Forms

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem isMultiHomog_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
  have h1 := hf m1 hm1 k
  have h2 := hg m2 hm2 k
  simp [Finset.sum_add_distrib, h1, h2]

theorem isMultiHomog_rename {κ : K → K'} {v : (Σ k, ι k) → (Σ k, ι' k)} (hv : IsBlockMap κ v) {f : MRing ι}
    {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (rename v f : MRing ι') (Function.extend κ a 0) := by
  intro m hm k'
  rw [support_rename_of_injective hv.2.1] at hm
  obtain ⟨m0, hm0, rfl⟩ := Finset.mem_image.mp hm
  by_cases hk : k' ∈ Set.range κ
  · obtain ⟨k, rfl⟩ := hk
    rw [hv.1.extend_apply, ← hf m0 hm0 k]
    have hex : ∀ i' : ι' (κ k), ∃ i : ι k, v ⟨k, i⟩ = ⟨κ k, i'⟩ := by
      intro i'
      obtain ⟨p, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
      have h1 : κ p.1 = κ k := by rw [← hv.2.2.1 p, hp]
      obtain ⟨k₁, i⟩ := p
      obtain rfl : k₁ = k := hv.1 h1
      exact ⟨i, hp⟩
    choose g hg using hex
    have hb : Function.Bijective g := by
      constructor
      · intro a b hab
        have : (⟨κ k, a⟩ : Σ k, ι' k) = ⟨κ k, b⟩ := by rw [← hg a, ← hg b, hab]
        exact eq_of_heq (Sigma.mk.inj this).2
      · intro i
        obtain ⟨q1, q2⟩ : ∃ q : Σ k, ι' k, q = v ⟨k, i⟩ := ⟨_, rfl⟩
        have hq : ∃ i', v ⟨k, i⟩ = ⟨κ k, i'⟩ := by
          have h1 := hv.2.2.1 ⟨k, i⟩
          generalize v ⟨k, i⟩ = q at h1
          obtain ⟨q1, q2⟩ := q
          simp only at h1
          subst h1
          exact ⟨q2, rfl⟩
        obtain ⟨i', hi'⟩ := hq
        refine ⟨i', ?_⟩
        have h2 : v ⟨k, g i'⟩ = v ⟨k, i⟩ := by rw [hg i', hi']
        exact eq_of_heq (Sigma.mk.inj (hv.2.1 h2)).2
    calc ∑ i', (Finsupp.mapDomain v m0) ⟨κ k, i'⟩ = ∑ i', m0 ⟨k, g i'⟩ := by
          refine Finset.sum_congr rfl fun i' _ => ?_
          rw [← hg i', Finsupp.mapDomain_apply hv.2.1]
      _ = ∑ i, m0 ⟨k, i⟩ := hb.sum_comp fun i => m0 ⟨k, i⟩
  · rw [Function.extend_apply' _ _ _ (by simpa using hk)]
    refine Finset.sum_eq_zero fun i' _ => ?_
    refine Finsupp.mapDomain_notin_range _ _ ?_
    rintro ⟨p, hp⟩
    exact hk ⟨p.1, by rw [← hv.2.2.1 p, hp]⟩

theorem eval_map_rename (zt : (Σ k, ι' k) → ℂ) (v : (Σ k, ι k) → (Σ k, ι' k)) (s : MRing ι) :
    eval zt (map (Int.castRingHom ℂ) (rename v s : MRing ι')) = eval (fun p => zt (v p)) (map (Int.castRingHom ℂ) s) := by
  rw [map_rename, eval_rename]
  rfl

theorem mem_mcPts_map {v : (Σ k, ι k) → (Σ k, ι' k)} {J : Ideal (MRing ι)} {zt : (Σ k, ι' k) → ℂ}
    (h0 : ∀ k, ∃ i, zt ⟨k, i⟩ ≠ 0) (hz : ∀ f ∈ J, eval (fun p => zt (v p)) (map (Int.castRingHom ℂ) f) = 0) :
    zt ∈ mcPts (J.map (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom) := by
  refine ⟨h0, ?_⟩
  have hle : J.map (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom ≤
      RingHom.ker ((eval zt).comp (map (Int.castRingHom ℂ)) : MRing ι' →+* ℂ) := by
    rw [Ideal.map_le_iff_le_comap]
    intro s hs
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change eval zt (map (Int.castRingHom ℂ) (rename v s : MRing ι')) = 0
    rw [eval_map_rename]
    exact hz s hs
  intro f hf
  exact RingHom.mem_ker.mp (hle hf)

theorem isMultiHomogIdeal_map {κ : K → K'} {v : (Σ k, ι k) → (Σ k, ι' k)} (hv : IsBlockMap κ v)
    {J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J) :
    IsMultiHomogIdeal (J.map (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom) := by
  obtain ⟨S, hS, rfl⟩ := hJ
  refine ⟨_ '' S, ?_, Ideal.map_span _ _⟩
  rintro _ ⟨s, hs, rfl⟩
  obtain ⟨a, ha⟩ := hS s hs
  exact ⟨_, isMultiHomog_rename hv ha⟩

end Forms

theorem holoMap_comp {e₁ e₂ e₃ : ℕ} {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {C : FinHolAtlas e₁ Z} {B : FinHolAtlas e₂ Y} {A : FinHolAtlas e₃ X} {g : Z → Y} {f : Y → X}
    (hg : HoloMap C B g) (hf : HoloMap B A f) : HoloMap C A (f ∘ g) := by
  refine ⟨hf.1.comp hg.1, fun j k t ht => ?_⟩
  obtain ⟨ht1, ht2⟩ := ht
  obtain ⟨m, hm⟩ := B.cover (g ((C.chart j).symm t))
  have h1 : AnalyticAt ℂ (B.chart m ∘ g ∘ (C.chart j).symm) t := hg.2 j m t ⟨ht1, hm⟩
  have hu : (B.chart m).symm ((B.chart m ∘ g ∘ (C.chart j).symm) t) = g ((C.chart j).symm t) :=
    (B.chart m).left_inv hm
  have h2 : AnalyticAt ℂ (A.chart k ∘ f ∘ (B.chart m).symm) ((B.chart m ∘ g ∘ (C.chart j).symm) t) :=
    hf.2 m k _ ⟨(B.chart m).map_source hm, by
      rw [Set.mem_preimage, hu]; exact ht2⟩
  refine (h2.comp h1).congr ?_
  have hc : ContinuousAt (g ∘ (C.chart j).symm) t :=
    hg.1.continuousAt.comp ((C.chart j).continuousAt_symm ht1)
  filter_upwards [hc ((B.chart m).open_source.mem_nhds hm)] with t' ht'
  have ht'' : g ((C.chart j).symm t') ∈ (B.chart m).source := ht'
  simp only [Function.comp]
  rw [(B.chart m).left_inv ht'']

end GlobalTheory.CompanionTheory.Ar.PB.CovMap

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap

section Corr

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} {M : FlagModel y Ψ N j} {K' : Type} [Fintype K']
  {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ'] {y' : (Σ k, ι' k) → Φ'}
  {M' : FlagModel y' Ψ N j}

theorem elim_img (Cv : FlagCover M' M) {d : ℕ} (hP : IsArithVar (mCoordIdeal y) (d + 2))
    (hP' : IsArithVar (mCoordIdeal y') (d + 2)) (J : Ideal (MRing ι')) (hJ : IsMultiHomogIdeal J)
    (hn : ¬ J ≤ mCoordIdeal y') :
    ∃ (g : MRing ι) (a : K → ℕ), IsMultiHomog g a ∧ g ∉ mCoordIdeal y ∧
      ∀ z ∈ mcPts (mCoordIdeal y'), z ∈ mcPts J → ∀ w ∈ mcPts (mCoordIdeal y), IsImg Cv z w →
        eval w (map (Int.castRingHom ℂ) g) = 0 := by
  obtain ⟨Pt, hPt, h1, h2, h3⟩ := GlobalTheory.T.exists_arithVar_graph_of_flagCover K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hP hP'
  have hle : ¬ J.map (rename inrV : MRing ι' →ₐ[ℤ] MRing (Sum.elim ι ι')).toRingHom ≤ Pt := by
    rw [Ideal.map_le_iff_le_comap]
    intro h
    exact hn (h2 ▸ h)
  obtain ⟨g, a, hg, hgP, hv⟩ := GroundTheory.Heights₂.Heights.Inter.PullbackEliminationOfVariable.proof K ι (K ⊕ K') (Sum.elim ι ι') Sum.inl inlV Pt
    (J.map (rename inrV : MRing ι' →ₐ[ℤ] MRing (Sum.elim ι ι')).toRingHom) (d + 1) isBlockMap_inl hPt
    (by rw [h1]; exact hP) (isMultiHomogIdeal_map isBlockMap_inr hJ) hle
  refine ⟨g, a, hg, h1 ▸ hgP, fun z hz hzJ w hw hi => ?_⟩
  obtain ⟨zt, hzt, e1, e2⟩ := h3 z hz w hw hi
  have := hv zt hzt (mem_mcPts_map hzt.1 fun f hf => by
    have e : (fun p => zt (inrV p)) = z := funext e2
    rw [e]
    exact hzJ.2 f hf)
  have e : (fun p => zt (inlV p)) = w := funext e1
  rwa [e] at this

theorem pull_img (Cv : FlagCover M' M) {d : ℕ} (hP : IsArithVar (mCoordIdeal y) (d + 2))
    (hP' : IsArithVar (mCoordIdeal y') (d + 2)) (G : MRing ι) (a : K → ℕ) (hG : IsMultiHomog G a)
    (hn : G ∉ mCoordIdeal y) :
    ∃ (g : MRing ι') (a' : K' → ℕ), IsMultiHomog g a' ∧ g ∉ mCoordIdeal y' ∧
      ∀ z ∈ mcPts (mCoordIdeal y'), ∀ w ∈ mcPts (mCoordIdeal y), IsImg Cv z w →
        eval w (map (Int.castRingHom ℂ) G) = 0 → eval z (map (Int.castRingHom ℂ) g) = 0 := by
  obtain ⟨Pt, hPt, h1, h2, h3⟩ := GlobalTheory.T.exists_arithVar_graph_of_flagCover K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hP hP'
  have hJ : IsMultiHomogIdeal (Ideal.span {G}) :=
    ⟨{G}, fun f hf => ⟨a, (Set.mem_singleton_iff.mp hf) ▸ hG⟩, rfl⟩
  have hle : ¬ (Ideal.span {G}).map (rename inlV : MRing ι →ₐ[ℤ] MRing (Sum.elim ι ι')).toRingHom ≤ Pt := by
    rw [Ideal.map_le_iff_le_comap]
    intro h
    exact hn (h1 ▸ h (Ideal.subset_span rfl))
  obtain ⟨g, a', hg, hgP, hv⟩ := GroundTheory.Heights₂.Heights.Inter.PullbackEliminationOfVariable.proof K' ι' (K ⊕ K') (Sum.elim ι ι') Sum.inr inrV Pt
    ((Ideal.span {G}).map (rename inlV : MRing ι →ₐ[ℤ] MRing (Sum.elim ι ι')).toRingHom) (d + 1) isBlockMap_inr hPt
    (by rw [h2]; exact hP') (isMultiHomogIdeal_map isBlockMap_inl hJ) hle
  refine ⟨g, a', hg, h2 ▸ hgP, fun z hz w hw hi h0 => ?_⟩
  obtain ⟨zt, hzt, e1, e2⟩ := h3 z hz w hw hi
  have := hv zt hzt (mem_mcPts_map hzt.1 fun f hf => by
    have e : (fun p => zt (inlV p)) = w := funext e1
    rw [e]
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton'.mp hf
    rw [map_mul, map_mul, h0, mul_zero])
  have e : (fun p => zt (inrV p)) = z := funext e2
  rwa [e] at this

end Corr

end GlobalTheory.CompanionTheory.Ar.PB.CovMap

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap

theorem flag_cover_map : ResExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M), IsArithVar (mCoordIdeal y') (d + 2) → ∃ (ϖ : ((Σ k, ι' k) → ℂ) → FA.S.X) (J : Ideal (MRing ι')) (R : AnLogRes (mCoordIdeal y') J (d + 1)) (br : Set FA.S.X), (∀ z z', z ∈ mcPts (mCoordIdeal y') → SameOrbit z' z → ϖ z' = ϖ z) ∧ HoloMap R.A FA.S.A (fun x => ϖ (R.lift x x)) ∧ IsDegreeOff FA.S.A R.A (fun x => ϖ (R.lift x x)) Cv.deg br ∧ (∀ z ∈ mcPts (mCoordIdeal y'), ∀ F' F, M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal (basePart M'.blk z)) → M.GoodAt F (mCoordIdeal (basePart M'.blk z ∘ Cv.v)) → ∀ h, M'.IsFlagOf F' z h → ∀ x₀, FA.Re.π x₀ = ϖ z → ∃ z₀, SameOrbit z₀ (FA.Re.R.lift x₀ x₀) ∧ SameOrbit (basePart M.blk z₀) (basePart M'.blk z ∘ Cv.v) ∧ M.IsFlagOf F z₀ fun τ => Cv.trans F' F (basePart M'.blk z) τ * h τ) ∧ ∀ z ∈ mcPts (mCoordIdeal y'), ∃ (V : Set ((Σ k, ι' k) → ℂ)) (f : ((Σ k, ι' k) → ℂ) → (Σ k, ι k) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ f V ∧ ∀ z' ∈ V ∩ mcPts (mCoordIdeal y'), ∀ x₀, FA.Re.π x₀ = ϖ z' → SameOrbit (f z') (FA.Re.R.lift x₀ x₀) := by
  intro hRes K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA K' _ ι' _ Φ' _ y' M' Cv hP'
  have hP : IsArithVar (mCoordIdeal y) (d + 2) := FA.Re.arith
  have hJ : FA.Re.J = ⊤ := FA.J_top
  have hdeg : IsDegreeOff FA.S.A FA.Re.R.A FA.Re.π 1 ∅ := by
    have := FA.Re.degree
    rwa [FA.deg_one, FA.br_empty] at this
  have hπinj : Function.Injective FA.Re.π := by
    intro a b hab
    obtain ⟨c, hc⟩ := Set.ncard_eq_one.1 (hdeg.2.2.2.2.1 (FA.Re.π a) (by simp))
    have ha : a ∈ FA.Re.π ⁻¹' {FA.Re.π a} := rfl
    have hb : b ∈ FA.Re.π ⁻¹' {FA.Re.π a} := hab.symm
    rw [hc] at ha hb
    exact ha.trans hb.symm
  have hnot : ∀ z : (Σ k, ι k) → ℂ, z ∉ mcPts FA.Re.J := by
    intro z h
    have := h.2 1 (by rw [hJ]; trivial)
    simp at this
  have hinjR : ∀ x x', SameOrbit (FA.Re.R.lift x x) (FA.Re.R.lift x' x') → x = x' :=
    fun x x' h => FA.Re.R.inj x x' (hnot _) h
  have hloc := GlobalTheory.T.flag_cover_arithmetic_first K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hP hP'
  have huniq := GlobalTheory.T.flag_cover_arithmetic_second K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hP hP'
  have hmemY : ∀ x, FA.Re.R.lift x x ∈ mcPts (mCoordIdeal y) := fun x => FA.Re.R.mem x x (FA.Re.R.mem_U x)
  have himg : ∀ z ∈ mcPts (mCoordIdeal y'), ∃ x, IsImg Cv z (FA.Re.R.lift x x) := by
    intro z hz
    obtain ⟨V, f, -, hzV, -, hf⟩ := hloc z hz
    obtain ⟨h1, h2⟩ := hf z ⟨hzV, hz⟩
    obtain ⟨x, hx⟩ := FA.Re.R.surj (f z) h1 (hnot _)
    exact ⟨x, h2.orbit (Cj.sameOrbit_refl z) hx⟩
  haveI : Nonempty FA.S.X := FA.Re.nonempty_base
  obtain ⟨ϖ, hϖdef⟩ : ∃ ϖ : ((Σ k, ι' k) → ℂ) → FA.S.X, ϖ = fun z =>
      if h : ∃ x, IsImg Cv z (FA.Re.R.lift x x) then FA.Re.π h.choose else Classical.arbitrary _ := ⟨_, rfl⟩
  have hϖ : ∀ z ∈ mcPts (mCoordIdeal y'), ∀ z₁, SameOrbit z₁ z → ∀ x, IsImg Cv z₁ (FA.Re.R.lift x x) →
      ϖ z₁ = FA.Re.π x := by
    intro z hz z₁ hz1 x hx
    have hex : ∃ x, IsImg Cv z₁ (FA.Re.R.lift x x) := ⟨x, hx⟩
    rw [hϖdef]
    simp only [dif_pos hex]
    congr 1
    refine hinjR _ _ (huniq z hz _ _ ?_ ?_)
    · exact hex.choose_spec.orbit (Cj.sameOrbit_symm hz1) (Cj.sameOrbit_refl _)
    · exact hx.orbit (Cj.sameOrbit_symm hz1) (Cj.sameOrbit_refl _)
  have hϖ' : ∀ z ∈ mcPts (mCoordIdeal y'), ∀ x, IsImg Cv z (FA.Re.R.lift x x) → ϖ z = FA.Re.π x :=
    fun z hz x hx => hϖ z hz z (Cj.sameOrbit_refl z) x hx
  have hϖx : ∀ z ∈ mcPts (mCoordIdeal y'), ∀ x₀, FA.Re.π x₀ = ϖ z → IsImg Cv z (FA.Re.R.lift x₀ x₀) := by
    intro z hz x₀ hx₀
    obtain ⟨x, hx⟩ := himg z hz
    have : x₀ = x := hπinj (hx₀.trans (hϖ' z hz x hx))
    rw [this]
    exact hx

  have htop : IsMultiHomogIdeal (⊤ : Ideal (MRing ι')) := by
    refine ⟨{1}, fun f hf => ⟨0, ?_⟩, by simp⟩
    rw [Set.mem_singleton_iff.mp hf]
    intro m hm k
    rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
    simp [hm]
  have hnt : ¬ (⊤ : Ideal (MRing ι')) ≤ mCoordIdeal y' := fun h =>
    hP'.2.1.1.ne_top (top_le_iff.mp h)
  obtain ⟨J', -, hJ'h, hJ'n, ⟨R'⟩⟩ := hRes K' ι' (mCoordIdeal y') ⊤ (d + 1) hP' htop hnt
  have hmemY' : ∀ x, R'.lift x x ∈ mcPts (mCoordIdeal y') := fun x => R'.mem x x (R'.mem_U x)
  choose g hg using fun x => himg _ (hmemY' x)
  have hgh : (fun x => ϖ (R'.lift x x)) = FA.Re.π ∘ g := funext fun x => hϖ' _ (hmemY' x) _ (hg x)
  have hgholo : HoloMap R'.A FA.Re.R.A g := by
    refine GlobalTheory.T.log_resolution_map_locally_analytic K ι K' ι' (mCoordIdeal y) FA.Re.J (mCoordIdeal y') J' (d + 1) (d + 1) FA.Re.R R' g hJ
      fun x => ?_
    obtain ⟨V, f, hV, hzV, hf, hff⟩ := hloc _ (hmemY' x)
    refine ⟨V, f, hV, hzV, hf, fun z' hz' x' hx' => ?_⟩
    exact huniq z' hz'.2 _ _ (hff z' hz').2 ((hg x').orbit hx' (Cj.sameOrbit_refl _))
  have hholo : HoloMap R'.A FA.S.A (fun x => ϖ (R'.lift x x)) := by
    rw [hgh]
    exact holoMap_comp hgholo FA.Re.holo

  have hpts := (GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M).1
  have hbase := GlobalTheory.T.flag_cover_arithmetic_third K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hP hP'
  have hpts' := (GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M').1
  obtain ⟨D₁, a₁, hD₁, hD₁n, hcount⟩ := GlobalTheory.T.flag_cover_arithmetic_fourth K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hP hP'
  obtain ⟨G₁, b₁, hG₁, hG₁n, hG₁e⟩ := GlobalTheory.T.flag_cover_arithmetic_sixth K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hP hP' D₁ a₁ hD₁ hD₁n
  obtain ⟨D₂, a₂, hD₂, hD₂n, het⟩ := GlobalTheory.T.flag_cover_arithmetic_seventh K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hP hP'
  obtain ⟨G₂, b₂, hG₂, hG₂n, hG₂e⟩ := GlobalTheory.T.flag_cover_arithmetic_sixth K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hP hP' D₂ a₂ hD₂ hD₂n
  obtain ⟨G₃, b₃, hG₃, hG₃n, hG₃e⟩ := elim_img Cv hP hP' J' hJ'h hJ'n
  have hprime := hP.2.1.1
  have hGn : G₁ * G₂ * G₃ ∉ mCoordIdeal y := fun h => by
    rcases hprime.mem_or_mem h with h | h
    · rcases hprime.mem_or_mem h with h | h
      · exact hG₁n h
      · exact hG₂n h
    · exact hG₃n h
  have hGh : IsMultiHomog (G₁ * G₂ * G₃) (b₁ + b₂ + b₃) := isMultiHomog_mul (isMultiHomog_mul hG₁ hG₂) hG₃
  obtain ⟨G₄, b₄, hG₄, hG₄n, hG₄e⟩ := pull_img Cv hP hP' _ _ hGh hGn
  have hev : ∀ w : (Σ k, ι k) → ℂ, eval w (map (Int.castRingHom ℂ) (G₁ * G₂ * G₃)) ≠ 0 →
      eval w (map (Int.castRingHom ℂ) G₁) ≠ 0 ∧ eval w (map (Int.castRingHom ℂ) G₂) ≠ 0 := by
    intro w hw
    simp only [map_mul] at hw
    exact ⟨fun h => hw (by rw [h]; simp), fun h => hw (by rw [h]; simp)⟩
  have hdegree : IsDegreeOff FA.S.A R'.A (fun x => ϖ (R'.lift x x)) Cv.deg
      (FA.Re.π '' {x | eval (FA.Re.R.lift x x) (map (Int.castRingHom ℂ) (G₁ * G₂ * G₃)) = 0}) := by
    refine GlobalTheory.T.log_resolution_compatible_pullback K ι K' ι' (mCoordIdeal y) FA.Re.J (mCoordIdeal y') J' (d + 1) FA.S.X FA.S.A FA.Re.R
      FA.Re.π R' _ (IsImg Cv) (G₁ * G₂ * G₃) G₄ _ b₄ Cv.deg hJ hP hP' FA.Re.holo hdeg hholo hGh hGn hG₄ hG₄n
      (fun z z₁ w w₁ h h1 h2 => h.orbit h1 h2) ?_ ?_ ?_ ?_ (fun z hz w hw hi h0 => hG₄e z hz w hw hi h0) ?_
    · intro x x₀ h
      exact hϖx _ (hmemY' x) x₀ h
    · intro x x₀ h
      exact (hϖ' _ (hmemY' x) x₀ h).symm
    · intro w hw h0
      rw [GlobalTheory.T.flag_cover_arithmetic_fifth K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hP hP' w hw]
      refine hcount _ (hpts w hw) ?_
      rw [← hG₁e]
      exact (hev w h0).1
    · intro z hz hzJ w hw hi
      have := hG₃e z hz hzJ w hw hi
      simp only [map_mul, this, mul_zero]
    · intro z hz w₀ hw₀ hi h0
      have hs := hbase z hz w₀ hi
      have h2 : eval (basePart M.blk w₀) (map (Int.castRingHom ℂ) D₂) ≠ 0 := by
        rw [← hG₂e]
        exact (hev w₀ h0).2
      obtain ⟨V, V', s, hV, hwV, hV', hbV, hs1, hs2⟩ := het _ (hpts' z hz) _ hs h2
      exact GlobalTheory.T.flag_cover_arithmetic_eighth K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hP hP' z hz w₀ hw₀ hi V V' s hV hwV hV' hbV hs1 hs2
  refine ⟨ϖ, J', R', _, ?_, hholo, hdegree, ?_, ?_⟩
  · intro z z' hz hz'
    obtain ⟨x, hx⟩ := himg z hz
    rw [hϖ' z hz x hx, hϖ z hz z' hz' x (hx.orbit hz' (Cj.sameOrbit_refl _))]
  · intro z hz F' F hF' hF hg' hg₂ h hfl x₀ hx₀
    exact hϖx z hz x₀ hx₀ z (Cj.sameOrbit_refl z) F' F hF' hF hg' hg₂ h hfl
  · intro z hz
    obtain ⟨V, f, hV, hzV, hf, hff⟩ := hloc z hz
    refine ⟨V, f, hV, hzV, hf, fun z' hz' x₀ hx₀ => ?_⟩
    exact huniq z' hz'.2 _ _ (hff z' hz').2 (hϖx z' hz'.2 x₀ hx₀)

end GlobalTheory.CompanionTheory.Ar.PB.CovMap
