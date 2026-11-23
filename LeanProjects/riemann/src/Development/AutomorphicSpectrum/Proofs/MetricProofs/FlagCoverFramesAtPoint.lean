import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsImg
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AevalNeZeroOfNotMem
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsValueAtOfTorus
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsBlkCover
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishingStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPointsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBasePointInPointsStatement
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverPt
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.An

section Loc

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set E} {z : E}

def LocAn (S : Set E) (z : E) (φ : E → ℂ) : Prop :=
  ∃ f : E → ℂ, AnalyticAt ℂ f z ∧ ∀ᶠ w in 𝓝[S] z, φ w = f w

theorem LocAn.of_analyticAt {φ : E → ℂ} (h : AnalyticAt ℂ φ z) : LocAn S z φ :=
  ⟨φ, h, Eventually.of_forall fun _ => rfl⟩

theorem LocAn.const (c : ℂ) : LocAn S z fun _ => c := .of_analyticAt analyticAt_const

theorem LocAn.add {φ ψ : E → ℂ} (h : LocAn S z φ) (h' : LocAn S z ψ) : LocAn S z fun w => φ w + ψ w := by
  obtain ⟨f, hf, e⟩ := h
  obtain ⟨g, hg, e'⟩ := h'
  refine ⟨fun w => f w + g w, hf.add hg, ?_⟩
  filter_upwards [e, e'] with w a b
  rw [a, b]

theorem LocAn.mul {φ ψ : E → ℂ} (h : LocAn S z φ) (h' : LocAn S z ψ) : LocAn S z fun w => φ w * ψ w := by
  obtain ⟨f, hf, e⟩ := h
  obtain ⟨g, hg, e'⟩ := h'
  refine ⟨fun w => f w * g w, hf.mul hg, ?_⟩
  filter_upwards [e, e'] with w a b
  rw [a, b]

theorem LocAn.sum {σ : Type} (s : Finset σ) {φ : σ → E → ℂ} (h : ∀ i ∈ s, LocAn S z (φ i)) :
    LocAn S z fun w => ∑ i ∈ s, φ i w := by
  induction s using Finset.induction_on with
  | empty => simpa using LocAn.const (S := S) (z := z) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem LocAn.prod {σ : Type} (s : Finset σ) {φ : σ → E → ℂ} (h : ∀ i ∈ s, LocAn S z (φ i)) :
    LocAn S z fun w => ∏ i ∈ s, φ i w := by
  induction s using Finset.induction_on with
  | empty => simpa using LocAn.const (S := S) (z := z) 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem LocAn.det {n : ℕ} {A : E → Matrix (Fin n) (Fin n) ℂ} (h : ∀ a b, LocAn S z fun w => A w a b) :
    LocAn S z fun w => (A w).det := by
  simp only [Matrix.det_apply']
  exact LocAn.sum _ fun σ _ => (LocAn.const _).mul (LocAn.prod _ fun i _ => h _ _)

theorem LocAn.minor {N : ℕ} {A : E → Matrix (Fin N) (Fin N) ℂ} (h : ∀ a b, LocAn S z fun w => A w a b)
    (I J : Finset (Fin N)) : LocAn S z fun w => minorIJ (A w) I J := by
  unfold minorIJ
  split_ifs with e
  · exact LocAn.det fun a b => h _ _
  · exact LocAn.const 0

end Loc

section Val

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set E} {z : E}
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem eval_eq_zero_of_mem {b : (Σ k, ι k) → ℂ} {f : MRing ι} (hf : f ∈ mCoordIdeal b) :
    eval b (map (Int.castRingHom ℂ) f) = 0 := by
  have h0 : mConeMap b f = 0 := hf
  have e : ∀ f : MRing ι, eval (fun _ => (1 : ℂ)) (mConeMap b f) = eval b (map (Int.castRingHom ℂ) f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp [map_add, hp, hq]
    | mul_X p q hp =>
      have e1 : eval (fun _ => (1 : ℂ)) (mConeMap b (X q)) = b q := by simp [mConeMap]
      rw [map_mul, map_mul, hp, e1, map_mul, map_mul, map_X, eval_X]
  rw [← e, h0, map_zero]

theorem notMem_of_eval_ne_zero {b : (Σ k, ι k) → ℂ} {f : MRing ι} (hf : eval b (map (Int.castRingHom ℂ) f) ≠ 0) :
    f ∉ mCoordIdeal b := fun h => hf (eval_eq_zero_of_mem h)

theorem coord_ne_zero_of_notMem {b : (Σ k, ι k) → ℂ} {q : Σ k, ι k} (h : (X q : MRing ι) ∉ mCoordIdeal b) :
    b q ≠ 0 := fun e => h (by
  show mConeMap b (X q) = 0
  rw [mConeMap, aeval_X, e, map_zero, zero_mul])

theorem analyticAt_eval {σ : Type} {b : E → σ → ℂ} (hb : ∀ q, AnalyticAt ℂ (fun w => b w q) z)
    (p : MvPolynomial σ ℤ) : AnalyticAt ℂ (fun w => eval (b w) (map (Int.castRingHom ℂ) p)) z := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p q hp hq =>
    have e : (fun w => eval (b w) (map (Int.castRingHom ℂ) (p + q))) = fun w =>
        eval (b w) (map (Int.castRingHom ℂ) p) + eval (b w) (map (Int.castRingHom ℂ) q) := by
      funext w; rw [map_add, map_add]
    rw [e]; exact hp.add hq
  | mul_X p q hp =>
    have e : (fun w => eval (b w) (map (Int.castRingHom ℂ) (p * X q))) = fun w =>
        eval (b w) (map (Int.castRingHom ℂ) p) * b w q := by
      funext w; rw [map_mul, map_mul, map_X, eval_X]
    rw [e]; exact hp.mul (hb q)

theorem regAt_eventually {x : (Σ k, ι k) → Ω} {b : E → (Σ k, ι k) → ℂ} (hb : ∀ q, AnalyticAt ℂ (fun w => b w q) z)
    {s : Ω} (hs : RegAt x (mCoordIdeal (b z)) s) : ∀ᶠ w in 𝓝 z, RegAt x (mCoordIdeal (b w)) s := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  filter_upwards [(analyticAt_eval hb h).continuousAt.eventually_ne (ValRing.eval_ne_zero_of_notMem hh hn)] with w hw
  exact ⟨d, g, h, hg, hh, notMem_of_eval_ne_zero hw, heq⟩

theorem locAn_valAt {x : (Σ k, ι k) → Ω} {b : E → (Σ k, ι k) → ℂ} (hb : ∀ q, AnalyticAt ℂ (fun w => b w q) z)
    (hpt : ∀ w ∈ S, b w ∈ mcPts (mCoordIdeal x)) (hz : z ∈ S) {s : Ω} (hs : RegAt x (mCoordIdeal (b z)) s) :
    LocAn S z fun w => valAt x s (b w) := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  have h0 := ValRing.eval_ne_zero_of_notMem hh hn
  have hx := ValRing.aeval_ne_zero_of_notMem (hpt z hz) hh hn
  refine ⟨fun w => eval (b w) (map (Int.castRingHom ℂ) g) / eval (b w) (map (Int.castRingHom ℂ) h),
    (analyticAt_eval hb g).div (analyticAt_eval hb h) h0, ?_⟩
  filter_upwards [nhdsWithin_le_nhds ((analyticAt_eval hb h).continuousAt.eventually_ne h0), self_mem_nhdsWithin]
    with w hw hwS
  exact valAt_eq (hpt w hwS) ⟨d, g, h, hg, hh, hx, heq, hw, rfl⟩

end Val

section Good

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z : E}
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Finite Ψ] {N j : ℕ}

theorem goodAt_eventually (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk)
    {b : E → (Σ k, baseIdx ι M.blk k) → ℂ} (hb : ∀ q, AnalyticAt ℂ (fun w => b w q) z)
    (hg : M.GoodAt F (mCoordIdeal (b z))) : ∀ᶠ w in 𝓝 z, M.GoodAt F (mCoordIdeal (b w)) := by
  obtain ⟨h1, h2, h3⟩ := hg
  have A : ∀ᶠ w in 𝓝 z, ∀ k, (X ⟨k, F.c k⟩ : MRing (baseIdx ι M.blk)) ∉ mCoordIdeal (b w) := by
    refine eventually_all.2 fun k => ?_
    filter_upwards [(hb ⟨k, F.c k⟩).continuousAt.eventually_ne (coord_ne_zero_of_notMem (h1 k))] with w hw
    refine notMem_of_eval_ne_zero ?_
    simpa using hw
  have B : ∀ᶠ w in 𝓝 z, ∀ q I, RegAt M.x (mCoordIdeal (b w)) (F.u q I) ∧ RegAt M.x (mCoordIdeal (b w)) (F.u' I q) :=
    eventually_all.2 fun q => eventually_all.2 fun I =>
      (regAt_eventually hb (h2 q I).1).and (regAt_eventually hb (h2 q I).2)
  have C : ∀ᶠ w in 𝓝 z, ∀ p, M.blk p = none → F.υ p ≠ 0 ∧ RegAt M.x (mCoordIdeal (b w)) (F.υ p) ∧
      RegAt M.x (mCoordIdeal (b w)) (F.υ p)⁻¹ := by
    refine eventually_all.2 fun p => ?_
    by_cases hp : M.blk p = none
    · filter_upwards [regAt_eventually hb (h3 p hp).2.1, regAt_eventually hb (h3 p hp).2.2] with w a c
      exact fun _ => ⟨(h3 p hp).1, a, c⟩
    · exact Eventually.of_forall fun _ h => absurd h hp
  filter_upwards [A, B, C] with w a c d
  exact ⟨a, c, d⟩

end Good

section Img

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ} {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ']
  {y' : (Σ k, ι' k) → Φ'}

theorem analyticAt_coord (z : (Σ k, ι' k) → ℂ) (q : Σ k, ι' k) :
    AnalyticAt ℂ (fun w : (Σ k, ι' k) → ℂ => w q) z :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, ι' k) => ℂ) q).analyticAt z

theorem locAn_img {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    {z : (Σ k, ι' k) → ℂ} {F' : FrameData ι' Ψ N M'.Ω M'.blk} {F : FrameData ι Ψ N M.Ω M.blk}
    (hz : z ∈ mcPts (mCoordIdeal y'))
    (hp1 : ∀ w ∈ mcPts (mCoordIdeal y'), basePart M'.blk w ∈ mcPts (mCoordIdeal M'.x))
    (hp2 : ∀ w ∈ mcPts (mCoordIdeal y'), basePart M'.blk w ∘ Cv.v ∈ mcPts (mCoordIdeal M.x))
    (hF' : M'.IsFrame F') (hF : M.IsFrame F)
    (hg' : M'.GoodAt F' (mCoordIdeal (basePart M'.blk z)))
    (hg : M.GoodAt F (mCoordIdeal (basePart M'.blk z ∘ Cv.v))) (q : Σ k, ι k) :
    LocAn (mcPts (mCoordIdeal y')) z fun w => img Cv F' F w q := by
  have hb : ∀ q, AnalyticAt ℂ (fun w => basePart M'.blk w q) z := fun q => analyticAt_coord z _
  have hbv : ∀ q, AnalyticAt ℂ (fun w => (basePart M'.blk w ∘ Cv.v) q) z := fun q => hb _
  obtain ⟨k, m⟩ := q
  by_cases hk : ∀ p, M.blk p ≠ some k
  · refine .of_analyticAt ?_
    have e : (fun w => img Cv F' F w ⟨k, m⟩) = fun w => basePart M'.blk w (Cv.v ⟨⟨k, hk⟩, m⟩) := by
      funext w
      exact congrFun (img_base Cv F' F w) ⟨⟨k, hk⟩, m⟩
    rw [e]
    exact hb _
  · obtain ⟨p, hp⟩ : ∃ p, M.blk p = some k := by simpa using hk
    obtain ⟨k', hp'⟩ := exists_blk_cover M' hp
    simp only [img_step Cv F' F _ hp hp' m]
    unfold stepCoord
    refine LocAn.sum _ fun I _ => (locAn_valAt hbv hp2 hz (hg.2.1 _ I).1).mul (LocAn.sum _ fun I' _ => ?_)
    by_cases hI : IsStepRows N j p.2 I'
    · simp only [if_pos hI]
      refine (LocAn.minor (fun a c => ?_) I I').mul
        (LocAn.sum _ fun m' _ => (locAn_valAt hb hp1 hz (hg'.2.1 _ I').2).mul (.of_analyticAt (analyticAt_coord z _)))
      exact locAn_valAt hb hp1 hz (Cv.agree _ (hp1 z hz) F' F hF' hF hg' hg p.1 a c).1
    · simp only [if_neg hI]
      exact LocAn.const 0

end Img

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (z : (Σ k, ι' k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk), z ∈ mcPts (mCoordIdeal y') → M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal (basePart M'.blk z)) → M.GoodAt F (mCoordIdeal (basePart M'.blk z ∘ Cv.v)) → ∃ (V : Set ((Σ k, ι' k) → ℂ)) (f : ((Σ k, ι' k) → ℂ) → (Σ k, ι k) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ f V ∧ ∀ z' ∈ V ∩ mcPts (mCoordIdeal y'), M'.GoodAt F' (mCoordIdeal (basePart M'.blk z')) ∧ M.GoodAt F (mCoordIdeal (basePart M'.blk z' ∘ Cv.v)) ∧ f z' = CovMap.LocImg.img Cv F' F z' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv z F' F hz hF' hF hg' hg
  have hp1 := (GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M').1
  have hp2 : ∀ w ∈ mcPts (mCoordIdeal y'), basePart M'.blk w ∘ Cv.v ∈ mcPts (mCoordIdeal M.x) := fun w hw =>
    (GlobalTheory.T.flag_cover_base_point_in_points K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ (hp1 w hw)).1
  have hb : ∀ q, AnalyticAt ℂ (fun w => basePart M'.blk w q) z := fun q => analyticAt_coord z _
  have hbv : ∀ q, AnalyticAt ℂ (fun w => (basePart M'.blk w ∘ Cv.v) q) z := fun q => hb _
  choose f hf hev using locAn_img Cv hz hp1 hp2 hF' hF hg' hg
  have e1 : ∀ᶠ w in 𝓝 z, AnalyticAt ℂ (fun w q => f q w) w :=
    (analyticAt_pi_iff.2 hf).eventually_analyticAt
  have e2 : ∀ᶠ w in 𝓝 z, w ∈ mcPts (mCoordIdeal y') → ∀ q, img Cv F' F w q = f q w :=
    eventually_nhdsWithin_iff.1 (eventually_all.2 hev)
  obtain ⟨V, hV, hVo, hzV⟩ := eventually_nhds_iff.1
    (e1.and (e2.and ((goodAt_eventually M' F' hb hg').and (goodAt_eventually M F hbv hg))))
  refine ⟨V, fun w q => f q w, hVo, hzV, fun w hw => (hV w hw).1, fun w hw => ?_⟩
  obtain ⟨-, a, c, d⟩ := hV w hw.1
  exact ⟨c, d, funext fun q => (a hw.2 q).symm⟩

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.An
