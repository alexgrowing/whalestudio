import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSmoothHermTrivLine
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemAbLocusIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.Chg
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Chg.Twist

section Holo

variable {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem continuousAt_holo (A : FinHolAtlas e X) {W : Set X} {g : X → ℂ} (hg : A.HoloOn W g) {x : X}
    (hx : x ∈ W) : ContinuousAt g x := by
  obtain ⟨j, hj⟩ := A.cover x
  have h1 : ContinuousAt (g ∘ (A.chart j).symm) (A.chart j x) :=
    (hg j _ ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩).continuousAt
  have h3 : ContinuousAt ((g ∘ (A.chart j).symm) ∘ A.chart j) x :=
    ContinuousAt.comp (g := g ∘ (A.chart j).symm) h1 ((A.chart j).continuousAt hj)
  refine h3.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [Function.comp, (A.chart j).left_inv hy]

theorem holoOn_comp {A : FinHolAtlas e X} {B : FinHolAtlas e' Y} {h : Y → X} (hh : HoloMap B A h) {U : Set X}
    {g : X → ℂ} (hg : A.HoloOn U g) : B.HoloOn (h ⁻¹' U) (fun y => g (h y)) := by
  rintro j y ⟨hy, hyU⟩
  obtain ⟨k, hk⟩ := A.cover (h ((B.chart j).symm y))
  have a1 : AnalyticAt ℂ (A.chart k ∘ h ∘ (B.chart j).symm) y := hh.2 j k y ⟨hy, hk⟩
  have a2 : AnalyticAt ℂ (g ∘ (A.chart k).symm) ((A.chart k ∘ h ∘ (B.chart j).symm) y) :=
    hg k _ ⟨(A.chart k).map_source hk, by
      simpa [Function.comp, (A.chart k).left_inv hk] using hyU⟩
  refine (a2.comp a1).congr ?_
  filter_upwards [((B.chart j).isOpen_inter_preimage_symm
    ((A.chart k).open_source.preimage hh.1)).mem_nhds ⟨hy, hk⟩] with y' hy'
  simp [Function.comp, (A.chart k).left_inv hy'.2]

theorem exists_log (A : FinHolAtlas e X) {W : Set X} (hW : IsOpen W) {c : X → ℂ} (hc : A.HoloOn W c) {x : X}
    (hx : x ∈ W) (h0 : c x ≠ 0) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ W ∧ ∃ L : X → ℂ, A.HoloOn V L ∧
      ∀ y ∈ V, c y ≠ 0 ∧ (L y).re = Real.log ‖c y‖ := by
  have hcont : ContinuousOn (fun y => c y / c x) W := fun y hy =>
    ((continuousAt_holo A hc hy).div_const _).continuousWithinAt
  have hV : IsOpen (W ∩ (fun y => c y / c x) ⁻¹' Complex.slitPlane) :=
    hcont.isOpen_inter_preimage hW Complex.isOpen_slitPlane
  refine ⟨_, hV, ⟨hx, ?_⟩, Set.inter_subset_left, fun y => Complex.log (c y / c x) + (Real.log ‖c x‖ : ℂ), ?_, ?_⟩
  · simp [div_self h0]
  · rintro j z ⟨hz, hzW, hzs⟩
    have a1 : AnalyticAt ℂ (c ∘ (A.chart j).symm) z := hc j z ⟨hz, hzW⟩
    have a2 : AnalyticAt ℂ (fun z => (c ∘ (A.chart j).symm) z / c x) z := a1.div analyticAt_const h0
    exact (a2.clog hzs).add analyticAt_const
  · rintro y ⟨-, hy⟩
    have hy' : c y / c x ≠ 0 := Complex.slitPlane_ne_zero hy
    have hcy : c y ≠ 0 := fun e => hy' (by simp [e])
    refine ⟨hcy, ?_⟩
    simp only [Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div]
    rw [Real.log_div (norm_ne_zero_iff.2 hcy) (norm_ne_zero_iff.2 h0)]
    ring

end Holo

variable {K₀ K : Type} [Fintype K₀] [Fintype K] {J₀ : K₀ → Type} {J : K → Type}
  [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] {κ : K₀ → K} {v : (Σ k, J₀ k) → Σ k, J k}
  {P₀ Jd₀ : Ideal (MRing J₀)} {P Jd : Ideal (MRing J)} {D : ℕ}

theorem orbit_key (R₀ : AnLogRes P₀ Jd₀ D) (R : AnLogRes P Jd D) (hv : IsBlockMap κ v) (h : R.X → R₀.X)
    (ho : ∀ x, SameOrbit (R₀.lift (h x) (h x)) (fun p => R.lift x x (v p))) {x y : R.X} (hy : y ∈ R.U x)
    (hy₀ : h y ∈ R₀.U (h x)) :
    ∃ c : K₀ → ℂ, (∀ k, c k ≠ 0) ∧ ∀ p, R.lift x y (v p) = c p.1 * R₀.lift (h x) (h y) p := by
  obtain ⟨c₁, h₁, e₁⟩ := R.compat x y y ⟨hy, R.mem_U y⟩
  obtain ⟨c₂, h₂, e₂⟩ := ho y
  obtain ⟨c₃, h₃, e₃⟩ := R₀.compat (h x) (h y) (h y) ⟨hy₀, R₀.mem_U _⟩
  refine ⟨fun k => c₁ (κ k) / (c₃ k * c₂ k), fun k => div_ne_zero (h₁ _) (mul_ne_zero (h₃ k) (h₂ k)), fun p => ?_⟩
  have a₁ := congrFun e₁ (v p)
  have a₂ := congrFun e₂ p
  have a₃ := congrFun e₃ p
  simp only at a₁ a₂ a₃
  have n₂ := h₂ p.1
  have n₃ := h₃ p.1
  rw [a₃, a₂, a₁, hv.2.2.1 p]
  field_simp

theorem exists_coeff_log (R₀ : AnLogRes P₀ Jd₀ D) (R : AnLogRes P Jd D) (hv : IsBlockMap κ v) (h : R.X → R₀.X)
    (hh : HoloMap R.A R₀.A h)
    (ho : ∀ x, SameOrbit (R₀.lift (h x) (h x)) (fun p => R.lift x x (v p))) (x : R.X) (k : K₀) :
    ∃ V : Set R.X, IsOpen V ∧ x ∈ V ∧ V ⊆ R.U x ∩ h ⁻¹' R₀.U (h x) ∧ ∃ L : R.X → ℂ, R.A.HoloOn V L ∧
      ∀ y ∈ V, ∀ c : K₀ → ℂ, (∀ k, c k ≠ 0) →
        (∀ p, R.lift x y (v p) = c p.1 * R₀.lift (h x) (h y) p) → (L y).re = Real.log ‖c k‖ := by
  have oW : IsOpen (R.U x ∩ h ⁻¹' R₀.U (h x)) := (R.isOpen_U x).inter ((R₀.isOpen_U _).preimage hh.1)
  have mW : x ∈ R.U x ∩ h ⁻¹' R₀.U (h x) := ⟨R.mem_U x, R₀.mem_U _⟩
  obtain ⟨i, hi⟩ := (R₀.mem (h x) (h x) (R₀.mem_U _)).1 k
  obtain ⟨cx, hcx, ecx⟩ := orbit_key R₀ R hv h ho (R.mem_U x) (R₀.mem_U (h x))
  have hn : R.A.HoloOn (R.U x ∩ h ⁻¹' R₀.U (h x)) (fun y => R.lift x y (v ⟨k, i⟩)) := fun j z hz =>
    R.holo x (v ⟨k, i⟩) j z ⟨hz.1, hz.2.1⟩
  have hd : R.A.HoloOn (R.U x ∩ h ⁻¹' R₀.U (h x)) (fun y => R₀.lift (h x) (h y) ⟨k, i⟩) := fun j z hz =>
    holoOn_comp hh (R₀.holo (h x) ⟨k, i⟩) j z ⟨hz.1, hz.2.2⟩
  have hnx : R.lift x x (v ⟨k, i⟩) ≠ 0 := by
    rw [ecx ⟨k, i⟩]
    exact mul_ne_zero (hcx k) hi
  obtain ⟨Vn, oVn, mVn, sVn, Ln, hLn, eLn⟩ := exists_log R.A oW hn mW hnx
  obtain ⟨Vd, oVd, mVd, -, Ld, hLd, eLd⟩ := exists_log R.A oW hd mW hi
  refine ⟨Vn ∩ Vd, oVn.inter oVd, ⟨mVn, mVd⟩, Set.inter_subset_left.trans sVn, fun y => Ln y - Ld y, ?_, ?_⟩
  · rintro j z ⟨hz, hzn, hzd⟩
    exact (hLn j z ⟨hz, hzn⟩).sub (hLd j z ⟨hz, hzd⟩)
  · rintro y ⟨hyn, hyd⟩ c hc ec
    obtain ⟨-, e1⟩ := eLn y hyn
    obtain ⟨d0, e2⟩ := eLd y hyd
    simp only [Complex.sub_re, e1, e2]
    rw [ec ⟨k, i⟩, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (hc k)) (norm_ne_zero_iff.2 d0)]
    ring

theorem samePot_twist : ∀ (K₀ K : Type) [Fintype K₀] [Fintype K] (J₀ : K₀ → Type) (J : K → Type) [∀ k, Fintype (J₀ k)] [∀ k, Fintype (J k)] (κ : K₀ → K) (v : (Σ k, J₀ k) → Σ k, J k) (P₀ Jd₀ : Ideal (MRing J₀)) (P Jd : Ideal (MRing J)) (D : ℕ) (R₀ : AnLogRes P₀ Jd₀ D) (R : AnLogRes P Jd D) (X : Type) [TopologicalSpace X] (B : FinHolAtlas D X) (Θ : LocPot X) (A₀ : HermLine J₀) (T : HermLine J) (π : R₀.X → X) (hπ : HoloMap R₀.A B π) (h : R.X → R₀.X) (hv : IsBlockMap κ v) (hc : Continuous (π ∘ h)), HoloMap R.A R₀.A h → (∀ x, SameOrbit (R₀.lift (h x) (h x)) (fun p => R.lift x x (v p))) → SamePot R₀.A Set.univ (potOf R₀ A₀) (Θ.pullback π hπ.1) → IsFlatOn R T → SamePot R.A Set.univ (potOf R ((pullHerm hv A₀).tensor T)) (Θ.pullback (π ∘ h) hc) := by
  intro K₀ K _ _ J₀ J _ _ κ v P₀ Jd₀ P Jd D R₀ R X _ B Θ A₀ T π hπ h hv hc hh ho h0 hF x _
  obtain ⟨V₀, oV₀, mV₀, G₀, hG₀, e₀⟩ := h0 (h x) trivial
  obtain ⟨V₁, oV₁, mV₁, G₁, hG₁, e₁⟩ := hF x trivial
  choose Vk oVk mVk sVk L hL eL using exists_coeff_log R₀ R hv h hh ho x
  refine ⟨(⋂ k, Vk k) ∩ ((h ⁻¹' V₀ ∩ V₁) ∩ (R.U x ∩ h ⁻¹' R₀.U (h x))),
    (isOpen_iInter_of_finite oVk).inter (((oV₀.preimage hh.1).inter oV₁).inter
      ((R.isOpen_U x).inter ((R₀.isOpen_U _).preimage hh.1))),
    ⟨Set.mem_iInter.2 mVk, ⟨mV₀, mV₁⟩, R.mem_U x, R₀.mem_U _⟩,
    fun y => G₀ (h y) + G₁ y + ∑ k, ((A₀.a k : ℝ) : ℂ) * L k y, ?_, ?_⟩
  · rintro j z ⟨hz, hzk, ⟨hz₀, hz₁⟩, -⟩
    have t0 : AnalyticAt ℂ (fun z => G₀ (h ((R.A.chart j).symm z))) z := holoOn_comp hh hG₀ j z ⟨hz, hz₀⟩
    have t1 : AnalyticAt ℂ (fun z => G₁ ((R.A.chart j).symm z)) z := hG₁ j z ⟨hz, hz₁⟩
    have t2 : ∀ k ∈ (Finset.univ : Finset K₀),
        AnalyticAt ℂ (fun z => ((A₀.a k : ℝ) : ℂ) * L k ((R.A.chart j).symm z)) z := fun k _ =>
      analyticAt_const.mul (hL k j z ⟨hz, Set.mem_iInter.1 hzk k⟩)
    exact (t0.add t1).add (Finset.analyticAt_fun_sum _ t2)
  · rintro y ⟨hyk, ⟨hy₀, hy₁⟩, hyU, hyU₀⟩
    obtain ⟨c, hc0, ec⟩ := orbit_key R₀ R hv h ho hyU hyU₀
    have E0 : Real.log (A₀.h (R₀.lift (h x) (h y))) - Θ.φ (π (h x)) (π (h y)) = (G₀ (h y)).re := e₀ (h y) hy₀
    have E1 : Real.log (T.h (R.lift x y)) - 0 = (G₁ y).re := e₁ y hy₁
    have E2 : (fun p => R.lift x y (v p)) = fun p => c p.1 * R₀.lift (h x) (h y) p := funext ec
    show Real.log (((pullHerm hv A₀).tensor T).h (R.lift x y)) - Θ.φ (π (h x)) (π (h y)) = _
    rw [log_tensor_pull hv A₀ T (R.mem x y hyU).1, E2, log_h_smul A₀ hc0 (R₀.mem _ _ hyU₀).1]
    simp only [Complex.add_re, Complex.re_sum, Complex.re_ofReal_mul, ← E0, ← E1,
      fun k => eL k y (Set.mem_iInter.1 hyk k) c hc0 ec]
    ring

end GlobalTheory.CompanionTheory.Ar.Chg.Twist
