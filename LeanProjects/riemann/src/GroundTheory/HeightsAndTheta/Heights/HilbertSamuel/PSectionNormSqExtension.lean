import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionNormSqExtension
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionNormSqLevi
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SectionNormSquares.Pointwise
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open scoped Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace SectionNormSqExtension

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {N : ℕ}

def Uf (d : (∀ k, ι k) → K → ℕ) (G : (∀ k, ι k) → Fin N → MRing ι) (A : HermLine ι) (m : ℕ)
    (F : Finset (MRing ι × (K → ℕ))) (c₀ : ∀ k, ι k) (x : (Σ k, ι k) → ℂ) : ℝ :=
  (∑ c, ∑ j, (fun x' => 1 / Nd (d c) x') x *
      (‖ev (G c₀ j * chartMon c (d c)) x +
          ev (G c j * chartMon c₀ (d c₀) - G c₀ j * chartMon c (d c)) x‖ ^ 2 -
        ‖ev (G c₀ j * chartMon c (d c)) x‖ ^ 2)) +
    ∑ p ∈ F, (fun x' => A.h x' ^ (2 * m) * ‖ev (chartMon c₀ (d c₀)) x'‖ ^ 2 / Nd p.2 x') x *
      (‖(fun _ => (0 : ℂ)) x + ev p.1 x‖ ^ 2 - ‖(fun _ => (0 : ℂ)) x‖ ^ 2)

theorem decomp (d : (∀ k, ι k) → K → ℕ) (G : (∀ k, ι k) → Fin N → MRing ι) (A : HermLine ι) (m : ℕ)
    (F : Finset (MRing ι × (K → ℕ))) (c₀ : ∀ k, ι k) (x : (Σ k, ι k) → ℂ) :
    ‖ev (chartMon c₀ (d c₀)) x‖ ^ 2 * (Qf d G x + Ef A m F x) =
      Rf d x * ∑ j, ‖ev (G c₀ j) x‖ ^ 2 + Uf d G A m F c₀ x := by
  set H := chartMon c₀ (d c₀) with hH
  have hterm : ∀ c j, (fun x' => 1 / Nd (d c) x') x *
      (‖ev (G c₀ j * chartMon c (d c)) x + ev (G c j * H - G c₀ j * chartMon c (d c)) x‖ ^ 2 -
        ‖ev (G c₀ j * chartMon c (d c)) x‖ ^ 2) =
      ‖ev H x‖ ^ 2 * (‖ev (G c j) x‖ ^ 2 / Nd (d c) x) -
        ‖ev (chartMon c (d c)) x‖ ^ 2 / Nd (d c) x * ‖ev (G c₀ j) x‖ ^ 2 := by
    intro c j
    have e : ev (G c₀ j * chartMon c (d c)) x + ev (G c j * H - G c₀ j * chartMon c (d c)) x =
        ev (G c j) x * ev H x := by
      simp only [ev, map_mul, map_sub]
      ring
    rw [e]
    simp only [ev, map_mul, norm_mul, mul_pow]
    ring
  have e1 : (∑ c, ∑ j, (fun x' => 1 / Nd (d c) x') x *
      (‖ev (G c₀ j * chartMon c (d c)) x + ev (G c j * H - G c₀ j * chartMon c (d c)) x‖ ^ 2 -
        ‖ev (G c₀ j * chartMon c (d c)) x‖ ^ 2)) =
      ‖ev H x‖ ^ 2 * Qf d G x - Rf d x * ∑ j, ‖ev (G c₀ j) x‖ ^ 2 := by
    rw [Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => hterm c j]
    unfold Qf Rf
    simp only [Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
    congr 1
    exact Finset.sum_comm
  have e2 : (∑ p ∈ F, (fun x' => A.h x' ^ (2 * m) * ‖ev H x'‖ ^ 2 / Nd p.2 x') x *
      (‖(fun _ => (0 : ℂ)) x + ev p.1 x‖ ^ 2 - ‖(fun _ => (0 : ℂ)) x‖ ^ 2)) = ‖ev H x‖ ^ 2 * Ef A m F x := by
    unfold Ef
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [zero_add, norm_zero]
    ring
  unfold Uf
  rw [← hH, e1, e2]
  ring

theorem two_le_top' : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  show ((2 : ℕ∞) : WithTop ℕ∞) ≤ _
  exact WithTop.coe_le_coe.mpr le_top

theorem mem_of_homog {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {g : MRing ι} {δ : K → ℕ}
    (hg : IsMultiHomog g δ) (h0 : aeval y g = 0) : g ∈ mCoordIdeal y := by
  show g ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker]
  erw [mConeMap_homog y hg, h0]
  simp

theorem numer_mem {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {A : HermLine ι} {m : ℕ} {v : Fin N → Ω}
    {d e : (∀ k, ι k) → K → ℕ} {G : (∀ k, ι k) → Fin N → MRing ι}
    (he : ∀ c k, (e c k : ℤ) = d c k + m * A.a k) (hG : ∀ c j, IsMultiHomog (G c j) (e c))
    (hGy : ∀ c j, aeval y (G c j) = v j * aeval y (chartMon c (d c))) (c₀ c : ∀ k, ι k) (j : Fin N) :
    G c j * chartMon c₀ (d c₀) - G c₀ j * chartMon c (d c) ∈ mCoordIdeal y := by
  refine mem_of_homog (homog_sub (homog_mul (hG c j) (homog_chartMon c₀ (d c₀)))
    (homog_congr (homog_mul (hG c₀ j) (homog_chartMon c (d c))) fun k => ?_)) ?_
  · simp only [Pi.add_apply]
    zify
    linarith [he c k, he c₀ k]
  · rw [map_sub, map_mul, map_mul, hGy, hGy]
    ring

theorem contDiffOn_Qf (d : (∀ k, ι k) → K → ℕ) (G : (∀ k, ι k) → Fin N → MRing ι) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Qf d G) (blockNZ ι) := by
  unfold Qf
  exact ContDiffOn.sum fun c _ => ContDiffOn.sum fun j _ => contDiffOn_term _ _

theorem contDiffOn_Rf (d : (∀ k, ι k) → K → ℕ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Rf (ι := ι) d) (blockNZ ι) := by
  unfold Rf
  exact ContDiffOn.sum fun c _ => contDiffOn_term _ _

theorem contDiffOn_Ef {A : HermLine ι} (hsm : IsSmoothHerm A) (m : ℕ) (F : Finset (MRing ι × (K → ℕ))) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Ef A m F) (blockNZ ι) := by
  unfold Ef
  exact (hsm.pow _).mul (ContDiffOn.sum fun p _ => contDiffOn_term _ _)

theorem contDiffAt_of_on {f : ((Σ k, ι k) → ℂ) → ℝ} (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (blockNZ ι))
    {x : (Σ k, ι k) → ℂ} (hx : x ∈ blockNZ ι) : ContDiffAt ℝ 2 f x :=
  (hf.contDiffAt (isOpen_blockNZ.mem_nhds hx)).of_le two_le_top'

theorem sumSq_pos {M : Type} [Fintype M] {a : M → ℂ} (ha : a ≠ 0) : 0 < ∑ j, ‖a j‖ ^ 2 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp ha
  exact Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨j, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hj) 2⟩

theorem contDiff_sumSq {M : Type} [Fintype M] {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun u : M → ℂ => ∑ j, ‖u j‖ ^ 2) :=
  ContDiff.sum fun j _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ j)

theorem contDiffAt_fs {M : Type} [Fintype M] {a : M → ℂ} (ha : a ≠ 0) :
    ContDiffAt ℝ 2 (fun u : M → ℂ => Real.log (∑ j, ‖u j‖ ^ 2) / 2) a :=
  (contDiff_sumSq.contDiffAt.log (sumSq_pos ha).ne').div_const 2

theorem leviForm_zero_dir {J : Type} [Fintype J] (φ : (J → ℂ) → ℝ) (z : J → ℂ) : leviForm φ z 0 = 0 := by
  simp [leviForm]

theorem levi_log_normSq (h₃ : LeviCompHol.Statement) (h₄ : LeviFSInvariant.Statement) {J : Type} [Fintype J]
    {f : (J → ℂ) → ℂ} {x : J → ℂ} (hf : AnalyticAt ℂ f x) (hf0 : f x ≠ 0) (w : J → ℂ) :
    leviForm (fun x' => Real.log (‖f x'‖ ^ 2)) x w = 0 := by
  have hg : AnalyticAt ℂ (fun x' (_ : Fin 1) => f x') x := AnalyticAt.pi fun _ => hf
  have ha : (fun (_ : Fin 1) => f x) ≠ 0 := fun h => hf0 (congrFun h 0)
  have h1 := h₃ J (Fin 1) (fun x' (_ : Fin 1) => f x') _ x w hg (contDiffAt_fs ha)
  have h2 := h₄ (Fin 1) (fun _ => f x) (fderiv ℂ (fun x' (_ : Fin 1) => f x') x w) 1
    (-(fderiv ℂ (fun x' (_ : Fin 1) => f x') x w 0 / f x)) ha one_ne_zero
  have hb : (1 : ℂ) • fderiv ℂ (fun x' (_ : Fin 1) => f x') x w +
      (-(fderiv ℂ (fun x' (_ : Fin 1) => f x') x w 0 / f x)) • (fun (_ : Fin 1) => f x) = 0 := by
    funext i
    fin_cases i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, Pi.zero_apply]
    field_simp
    exact sub_self _
  rw [hb, one_smul, leviForm_zero_dir] at h2
  have hC : ContDiffAt ℝ 2 (fun x' => Real.log (∑ j : Fin 1, ‖(fun x' (_ : Fin 1) => f x') x' j‖ ^ 2) / 2) x :=
    (contDiffAt_fs ha).comp x (hg.contDiffAt.restrict_scalars ℝ)
  have h3 : (fun x' => Real.log (‖f x'‖ ^ 2)) =
      fun x' => 2 * (Real.log (∑ j : Fin 1, ‖(fun x' (_ : Fin 1) => f x') x' j‖ ^ 2) / 2) := by
    funext x'
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
    ring
  rw [h3, leviForm_const_mul hC 2, h1, ← h2, mul_zero]

section Graph

variable {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {A : HermLine ι} {m : ℕ} {v : Fin N → Ω}
  {d e : (∀ k, ι k) → K → ℕ} {G : (∀ k, ι k) → Fin N → MRing ι} {F : Finset (MRing ι × (K → ℕ))}

theorem isFlat_Uf (h₂ : LeviHolPerturb.Statement) (hsm : IsSmoothHerm A)
    (he : ∀ c k, (e c k : ℤ) = d c k + m * A.a k) (hG : ∀ c j, IsMultiHomog (G c j) (e c))
    (hGy : ∀ c j, aeval y (G c j) = v j * aeval y (chartMon c (d c)))
    (hF : ∀ p ∈ F, IsMultiHomog p.1 p.2 ∧ p.1 ∈ mCoordIdeal y) (c₀ : ∀ k, ι k)
    {z w : (Σ k, addIdx ι N k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal (addBlock y v)))
    (hw : IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal (addBlock y v)) z w) :
    IsFlat (Uf d G A m F c₀) (basePart₂ z) (basePart₂ w) := by
  have hx := oldPart_mem hz
  have hxo : basePart₂ z ∈ blockNZ ι := hx.1
  have hhC : ContDiffAt ℝ 2 A.h (basePart₂ z) := contDiffAt_of_on hsm hxo
  have h1 : IsFlat (fun x => ∑ c, ∑ j, (fun x' => 1 / Nd (d c) x') x *
      (‖ev (G c₀ j * chartMon c (d c)) x +
          ev (G c j * chartMon c₀ (d c₀) - G c₀ j * chartMon c (d c)) x‖ ^ 2 -
        ‖ev (G c₀ j * chartMon c (d c)) x‖ ^ 2)) (basePart₂ z) (basePart₂ w) := by
    refine isFlat_sum _ fun c _ => isFlat_sum _ fun j _ => ?_
    have hmem := numer_mem he hG hGy c₀ c j
    exact h₂ _ _ _ _ _ _ (contDiffAt_const.div (contDiff_Nd _).contDiffAt (Nd_pos _ hxo).ne')
      (analyticAt_eval _ _) (analyticAt_eval _ _) (hx.2 _ hmem) (fderiv_old_eq_zero hw hmem)
  have h2 : IsFlat (fun x => ∑ p ∈ F,
      (fun x' => A.h x' ^ (2 * m) * ‖ev (chartMon c₀ (d c₀)) x'‖ ^ 2 / Nd p.2 x') x *
      (‖(fun _ => (0 : ℂ)) x + ev p.1 x‖ ^ 2 - ‖(fun _ => (0 : ℂ)) x‖ ^ 2)) (basePart₂ z) (basePart₂ w) := by
    refine isFlat_sum _ fun p hp => ?_
    exact h₂ _ _ _ _ _ _
      (((hhC.pow _).mul (contDiff_normSq_eval _).contDiffAt).div (contDiff_Nd _).contDiffAt (Nd_pos _ hxo).ne')
      analyticAt_const (analyticAt_eval _ _) (hx.2 _ (hF p hp).2) (fderiv_old_eq_zero hw (hF p hp).2)
  exact h1.add h2

theorem graph_cross (hGy : ∀ c j, aeval y (G c j) = v j * aeval y (chartMon c (d c)))
    (hG : ∀ c j, IsMultiHomog (G c j) (e c)) (c₀ : ∀ k, ι k)
    {z w : (Σ k, addIdx ι N k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal (addBlock y v)))
    (hw : IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal (addBlock y v)) z w) (j j' : Fin N) :
    z ⟨none, j⟩ * ev (G c₀ j') (basePart₂ z) = z ⟨none, j'⟩ * ev (G c₀ j) (basePart₂ z) ∧
      w ⟨none, j⟩ * ev (G c₀ j') (basePart₂ z) + z ⟨none, j⟩ * fderiv ℂ (ev (G c₀ j')) (basePart₂ z) (basePart₂ w) =
        w ⟨none, j'⟩ * ev (G c₀ j) (basePart₂ z) + z ⟨none, j'⟩ * fderiv ℂ (ev (G c₀ j)) (basePart₂ z) (basePart₂ w) := by
  have hmem := cross_mem (v := v) (hG c₀ j) (hG c₀ j') j j' (by rw [hGy, hGy]; ring)
  have hfun : (fun z' : (Σ k, addIdx ι N k) → ℂ => eval z' (map (Int.castRingHom ℂ)
      (X ⟨none, j⟩ * rename (oldEmb ι N) (G c₀ j') - X ⟨none, j'⟩ * rename (oldEmb ι N) (G c₀ j)))) =
      fun z' => z' ⟨none, j⟩ * ev (G c₀ j') (oldL ι N z') - z' ⟨none, j'⟩ * ev (G c₀ j) (oldL ι N z') := by
    funext z'
    simp only [map_sub, map_mul, map_X, eval_X, eval_rename_old]
    rfl
  refine ⟨?_, ?_⟩
  · have h0 := hz.2 _ hmem
    simp only [map_sub, map_mul, map_X, eval_X, eval_rename_old] at h0
    exact sub_eq_zero.mp h0
  · have h0 := fderiv_eq_zero_of_tangent hw hmem
    have hd : ∀ j'', HasFDerivAt (fun z' : (Σ k, addIdx ι N k) → ℂ => ev (G c₀ j'') (oldL ι N z'))
        ((fderiv ℂ (ev (G c₀ j'')) (oldL ι N z)).comp (oldL ι N)) z :=
      fun j'' => ((analyticAt_eval _ _).differentiableAt.hasFDerivAt).comp z (oldL ι N).hasFDerivAt
    have hH := ((hasFDerivAt_apply (𝕜 := ℂ) (⟨none, j⟩ : Σ k, addIdx ι N k) z).mul (hd j')).sub
      ((hasFDerivAt_apply (𝕜 := ℂ) (⟨none, j'⟩ : Σ k, addIdx ι N k) z).mul (hd j))
    have hH' : HasFDerivAt (fun z' : (Σ k, addIdx ι N k) → ℂ =>
        z' ⟨none, j⟩ * ev (G c₀ j') (oldL ι N z') - z' ⟨none, j'⟩ * ev (G c₀ j) (oldL ι N z')) _ z := hH
    rw [hfun, hH'.fderiv] at h0
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, oldL_apply] at h0
    linear_combination h0

end Graph

section Levi

variable {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {A : HermLine ι} {m : ℕ} {v : Fin N → Ω}
  {d e : (∀ k, ι k) → K → ℕ} {G : (∀ k, ι k) → Fin N → MRing ι} {F : Finset (MRing ι × (K → ℕ))}

theorem levi_identity (h₁ : LeviLogFlat.Statement) (h₂ : LeviHolPerturb.Statement)
    (h₃ : LeviCompHol.Statement) (h₄ : LeviFSInvariant.Statement) (hsm : IsSmoothHerm A)
    (hgen : KH.GeneratesOn y (fun k => (m : ℤ) * A.a k) v)
    (he : ∀ c k, (e c k : ℤ) = d c k + m * A.a k) (hG : ∀ c j, IsMultiHomog (G c j) (e c))
    (hGy : ∀ c j, aeval y (G c j) = v j * aeval y (chartMon c (d c)))
    (hF : ∀ p ∈ F, IsMultiHomog p.1 p.2 ∧ p.1 ∈ mCoordIdeal y)
    (hFspan : mCoordIdeal y ≤ Ideal.span ((fun p => p.1) '' (F : Set (MRing ι × (K → ℕ)))))
    {z w : (Σ k, addIdx ι N k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal (addBlock y v)))
    (hw : IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal (addBlock y v)) z w) :
    leviForm (fun z' : (Σ k, addIdx ι N k) → ℂ =>
        Real.log (∑ j, ‖z' ⟨none, j⟩‖ ^ 2) / 2 - Real.log (Sf d G A m F (basePart₂ z')) / 2) z w =
      (m : ℝ) * leviForm (fun x => Real.log (A.h x)) (basePart₂ z) (basePart₂ w) := by
  have hx : basePart₂ z ∈ mcPts (mCoordIdeal y) := oldPart_mem hz
  have hxo : basePart₂ z ∈ blockNZ ι := hx.1
  obtain ⟨c₀, hc₀⟩ : ∃ c : ∀ k, ι k, ∀ k, basePart₂ z ⟨k, c k⟩ ≠ 0 :=
    ⟨fun k => (hxo k).choose, fun k => (hxo k).choose_spec⟩
  have hyc : ∀ k, y ⟨k, c₀ k⟩ ≠ 0 := fun k => y_ne_zero hx (hc₀ k)
  obtain ⟨j₀, hj₀⟩ := exists_G_ne hgen hyc (he c₀) (hG c₀) (hGy c₀) hx hc₀
  have hgan : AnalyticAt ℂ (fun x' (j : Fin N) => ev (G c₀ j) x') (basePart₂ z) :=
    AnalyticAt.pi fun j => analyticAt_eval _ _
  have hgx : (fun j => ev (G c₀ j) (basePart₂ z)) ≠ 0 := fun h => hj₀ (congrFun h j₀)
  have hDg : fderiv ℂ (fun x' (j : Fin N) => ev (G c₀ j) x') (basePart₂ z) (basePart₂ w) =
      fun j => fderiv ℂ (ev (G c₀ j)) (basePart₂ z) (basePart₂ w) := by
    rw [fderiv_pi fun j => (analyticAt_eval _ _).differentiableAt]
    rfl

  have hcr := graph_cross hGy hG c₀ hz hw
  obtain ⟨lam, hlam⟩ : ∃ lam : ℂ, lam = z ⟨none, j₀⟩ / ev (G c₀ j₀) (basePart₂ z) := ⟨_, rfl⟩
  have hzl : ∀ j, z ⟨none, j⟩ = lam * ev (G c₀ j) (basePart₂ z) := by
    intro j
    have h1 := (hcr j j₀).1
    rw [hlam]
    field_simp
    linear_combination h1
  have hlam0 : lam ≠ 0 := by
    intro h0
    obtain ⟨j1, hj1⟩ := hz.1 none
    exact hj1 (by rw [hzl j1, h0, zero_mul])
  obtain ⟨mu, hmu⟩ : ∃ mu : ℂ, mu = (w ⟨none, j₀⟩ - lam * fderiv ℂ (ev (G c₀ j₀)) (basePart₂ z) (basePart₂ w)) /
      ev (G c₀ j₀) (basePart₂ z) := ⟨_, rfl⟩
  have hwl : ∀ j, w ⟨none, j⟩ = lam * fderiv ℂ (ev (G c₀ j)) (basePart₂ z) (basePart₂ w) +
      mu * ev (G c₀ j) (basePart₂ z) := by
    intro j
    have h1 := (hcr j j₀).2
    rw [hzl j, hzl j₀] at h1
    rw [hmu]
    field_simp
    linear_combination h1
  have hnewz : newL ι N z = lam • (fun j => ev (G c₀ j) (basePart₂ z)) := by
    funext j
    rw [newL_apply, hzl j]
    rfl
  have hneww : newL ι N w = lam • (fun j => fderiv ℂ (ev (G c₀ j)) (basePart₂ z) (basePart₂ w)) +
      mu • (fun j => ev (G c₀ j) (basePart₂ z)) := by
    funext j
    rw [newL_apply, hwl j]
    rfl
  have hnz : newL ι N z ≠ 0 := by
    obtain ⟨j1, hj1⟩ := hz.1 none
    exact fun h => hj1 (congrFun h j1)

  have hFS := h₄ (Fin N) (fun j => ev (G c₀ j) (basePart₂ z))
    (fun j => fderiv ℂ (ev (G c₀ j)) (basePart₂ z) (basePart₂ w)) lam mu hgx hlam0
  have L1 : leviForm (fun z' : (Σ k, addIdx ι N k) → ℂ => Real.log (∑ j, ‖z' ⟨none, j⟩‖ ^ 2) / 2) z w =
      leviForm (fun u : Fin N → ℂ => Real.log (∑ j, ‖u j‖ ^ 2) / 2) (fun j => ev (G c₀ j) (basePart₂ z))
        (fun j => fderiv ℂ (ev (G c₀ j)) (basePart₂ z) (basePart₂ w)) := by
    have h := h₃ _ _ (newL ι N) (fun u : Fin N → ℂ => Real.log (∑ j, ‖u j‖ ^ 2) / 2) z w
      ((newL ι N).analyticAt z) (contDiffAt_fs hnz)
    rw [(newL ι N).fderiv, hnewz, hneww, hFS] at h
    exact h

  have hSC : ContDiffAt ℝ 2 (Sf d G A m F) (basePart₂ z) := contDiffAt_of_on (contDiffOn_Sf hsm) hxo
  have hSpos := Sf_pos hgen he hG hGy hFspan hxo
  have hlogSC : ContDiffAt ℝ 2 (fun u => Real.log (Sf d G A m F u)) (basePart₂ z) := hSC.log hSpos.ne'
  have L2 : leviForm (fun z' : (Σ k, addIdx ι N k) → ℂ => Real.log (Sf d G A m F (basePart₂ z')) / 2) z w =
      leviForm (fun u => Real.log (Sf d G A m F u)) (basePart₂ z) (basePart₂ w) / 2 := by
    have h := h₃ _ _ (oldL ι N) (fun u => (1 / 2 : ℝ) * Real.log (Sf d G A m F u)) z w ((oldL ι N).analyticAt z)
      (contDiffAt_const.mul hlogSC)
    rw [(oldL ι N).fderiv] at h
    simp only [oldL_apply] at h
    rw [leviForm_const_mul hlogSC] at h
    have e : (fun z' : (Σ k, addIdx ι N k) → ℂ => Real.log (Sf d G A m F (basePart₂ z')) / 2) =
        fun y => (1 / 2 : ℝ) * Real.log (Sf d G A m F (basePart₂ y)) := by
      funext y
      ring
    rw [e, h]
    ring

  have hQC : ContDiffAt ℝ 2 (Qf d G) (basePart₂ z) := contDiffAt_of_on (contDiffOn_Qf d G) hxo
  have hEC : ContDiffAt ℝ 2 (Ef A m F) (basePart₂ z) := contDiffAt_of_on (contDiffOn_Ef hsm m F) hxo
  have hRC : ContDiffAt ℝ 2 (Rf (ι := ι) d) (basePart₂ z) := contDiffAt_of_on (contDiffOn_Rf d) hxo
  have hhC : ContDiffAt ℝ 2 A.h (basePart₂ z) := contDiffAt_of_on hsm hxo
  have hQEpos := QE_pos hgen he hG hGy hFspan hxo
  have hRpos := Rf_pos d hxo
  have hhpos := A.pos _ hxo
  have lQEC : ContDiffAt ℝ 2 (fun u => Real.log (Qf d G u + Ef A m F u)) (basePart₂ z) :=
    (hQC.add hEC).log hQEpos.ne'
  have lRC : ContDiffAt ℝ 2 (fun u => Real.log (Rf d u)) (basePart₂ z) := hRC.log hRpos.ne'
  have lhC : ContDiffAt ℝ 2 (fun u => Real.log (A.h u)) (basePart₂ z) := hhC.log hhpos.ne'
  have eS : (fun u => Real.log (Sf d G A m F u)) =ᶠ[𝓝 (basePart₂ z)]
      fun u => (Real.log (Qf d G u + Ef A m F u) - Real.log (Rf d u)) -
        ((2 * m : ℕ) : ℝ) * Real.log (A.h u) := by
    filter_upwards [isOpen_blockNZ.mem_nhds hxo] with u hu
    have h1 := QE_pos hgen he hG hGy hFspan hu
    have h2 := Rf_pos d hu
    have h3 := A.pos u hu
    rw [Sf, Real.log_div h1.ne' (mul_pos h2 (pow_pos h3 _)).ne', Real.log_mul h2.ne' (pow_pos h3 _).ne',
      Real.log_pow]
    ring
  have LS : leviForm (fun u => Real.log (Sf d G A m F u)) (basePart₂ z) (basePart₂ w) =
      leviForm (fun u => Real.log (Qf d G u + Ef A m F u)) (basePart₂ z) (basePart₂ w) -
        leviForm (fun u => Real.log (Rf d u)) (basePart₂ z) (basePart₂ w) -
        ((2 * m : ℕ) : ℝ) * leviForm (fun u => Real.log (A.h u)) (basePart₂ z) (basePart₂ w) := by
    rw [leviForm_congr eS, leviForm_sub (lQEC.sub lRC) (contDiffAt_const.mul lhC), leviForm_sub lQEC lRC,
      leviForm_const_mul lhC]

  have hHx : ev (chartMon c₀ (d c₀)) (basePart₂ z) ≠ 0 := by
    rw [ev, eval_chartMon]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc₀ k)
  obtain ⟨hUC, hU0, hUd1, hUd2, hUl⟩ := isFlat_Uf h₂ hsm he hG hGy hF c₀ hz hw
  have hsumC : ContDiffAt ℝ 2 (fun u => ∑ j, ‖ev (G c₀ j) u‖ ^ 2) (basePart₂ z) :=
    ContDiffAt.sum fun j _ => (contDiff_normSq_eval _).contDiffAt
  have hsumpos : 0 < ∑ j, ‖ev (G c₀ j) (basePart₂ z)‖ ^ 2 := sumSq_pos hgx
  have hP1C : ContDiffAt ℝ 2 (fun u => Rf d u * ∑ j, ‖ev (G c₀ j) u‖ ^ 2) (basePart₂ z) := hRC.mul hsumC
  have hP1pos : 0 < Rf d (basePart₂ z) * ∑ j, ‖ev (G c₀ j) (basePart₂ z)‖ ^ 2 := mul_pos hRpos hsumpos
  have hPUpos : Rf d (basePart₂ z) * ∑ j, ‖ev (G c₀ j) (basePart₂ z)‖ ^ 2 + Uf d G A m F c₀ (basePart₂ z) ≠ 0 := by
    rw [hU0, add_zero]
    exact hP1pos.ne'
  have lHC : ContDiffAt ℝ 2 (fun u => Real.log (‖ev (chartMon c₀ (d c₀)) u‖ ^ 2)) (basePart₂ z) :=
    (contDiff_normSq_eval _).contDiffAt.log (pow_ne_zero _ (norm_ne_zero_iff.mpr hHx))
  have hHopen : IsOpen {u : (Σ k, ι k) → ℂ | ev (chartMon c₀ (d c₀)) u ≠ 0} :=
    isOpen_ne_fun (MvPolynomial.continuous_eval _) continuous_const
  have eQE : (fun u => Real.log (Qf d G u + Ef A m F u)) =ᶠ[𝓝 (basePart₂ z)]
      fun u => Real.log (Rf d u * ∑ j, ‖ev (G c₀ j) u‖ ^ 2 + Uf d G A m F c₀ u) -
        Real.log (‖ev (chartMon c₀ (d c₀)) u‖ ^ 2) := by
    filter_upwards [isOpen_blockNZ.mem_nhds hxo, hHopen.mem_nhds hHx] with u hu hHu
    have h1 := QE_pos hgen he hG hGy hFspan hu
    have h2 : (0 : ℝ) < ‖ev (chartMon c₀ (d c₀)) u‖ ^ 2 := pow_pos (norm_pos_iff.mpr hHu) 2
    rw [← decomp, Real.log_mul h2.ne' h1.ne']
    ring
  have LQE : leviForm (fun u => Real.log (Qf d G u + Ef A m F u)) (basePart₂ z) (basePart₂ w) =
      leviForm (fun u => Real.log (Rf d u * ∑ j, ‖ev (G c₀ j) u‖ ^ 2)) (basePart₂ z) (basePart₂ w) := by
    rw [leviForm_congr eQE, leviForm_sub ((hP1C.add hUC).log hPUpos) lHC,
      levi_log_normSq h₃ h₄ (analyticAt_eval _ _) hHx, sub_zero]
    exact h₁ _ (fun u => Rf d u * ∑ j, ‖ev (G c₀ j) u‖ ^ 2) (Uf d G A m F c₀) (basePart₂ z) (basePart₂ w)
      hP1C hUC hP1pos hU0 hUd1 hUd2 hUl
  have hsumopen : IsOpen {u : (Σ k, ι k) → ℂ | (∑ j, ‖ev (G c₀ j) u‖ ^ 2) ≠ 0} :=
    isOpen_ne_fun (continuous_finsetSum _ fun j _ =>
      ((MvPolynomial.continuous_eval _).norm.pow 2)) continuous_const
  have lGC : ContDiffAt ℝ 2 (fun u => Real.log (∑ j, ‖ev (G c₀ j) u‖ ^ 2)) (basePart₂ z) :=
    hsumC.log hsumpos.ne'
  have eP1 : (fun u => Real.log (Rf d u * ∑ j, ‖ev (G c₀ j) u‖ ^ 2)) =ᶠ[𝓝 (basePart₂ z)]
      fun u => Real.log (Rf d u) + Real.log (∑ j, ‖ev (G c₀ j) u‖ ^ 2) := by
    filter_upwards [isOpen_blockNZ.mem_nhds hxo, hsumopen.mem_nhds hsumpos.ne'] with u hu hsu
    exact Real.log_mul (Rf_pos d hu).ne' hsu
  have LG : leviForm (fun u => Real.log (∑ j, ‖ev (G c₀ j) u‖ ^ 2)) (basePart₂ z) (basePart₂ w) =
      2 * leviForm (fun u : Fin N → ℂ => Real.log (∑ j, ‖u j‖ ^ 2) / 2) (fun j => ev (G c₀ j) (basePart₂ z))
        (fun j => fderiv ℂ (ev (G c₀ j)) (basePart₂ z) (basePart₂ w)) := by
    have hfsC : ContDiffAt ℝ 2 (fun x' => (fun u : Fin N → ℂ => Real.log (∑ j, ‖u j‖ ^ 2) / 2)
        ((fun x' (j : Fin N) => ev (G c₀ j) x') x')) (basePart₂ z) :=
      (contDiffAt_fs hgx).comp _ (hgan.contDiffAt.restrict_scalars ℝ)
    have e : (fun u => Real.log (∑ j, ‖ev (G c₀ j) u‖ ^ 2)) = fun x' => 2 *
        (fun u : Fin N → ℂ => Real.log (∑ j, ‖u j‖ ^ 2) / 2) ((fun x' (j : Fin N) => ev (G c₀ j) x') x') := by
      funext x'
      simp only
      ring
    rw [e, leviForm_const_mul hfsC, h₃ _ _ _ _ _ _ hgan (contDiffAt_fs hgx), hDg]
  have LP1 := leviForm_congr eP1 (basePart₂ w)
  rw [leviForm_add lRC lGC, LG] at LP1

  have hf1C : ContDiffAt ℝ 2 (fun z' : (Σ k, addIdx ι N k) → ℂ => Real.log (∑ j, ‖z' ⟨none, j⟩‖ ^ 2) / 2) z :=
    (contDiffAt_fs hnz).comp z ((newL ι N).restrictScalars ℝ).contDiff.contDiffAt
  have hf2C : ContDiffAt ℝ 2 (fun z' : (Σ k, addIdx ι N k) → ℂ => Real.log (Sf d G A m F (basePart₂ z')) / 2) z :=
    (hlogSC.div_const 2).comp z ((oldL ι N).restrictScalars ℝ).contDiff.contDiffAt
  rw [leviForm_sub hf1C hf2C, L1, L2, LS, LQE, LP1]
  push_cast
  ring

end Levi

end SectionNormSqExtension

open SectionNormSqExtension in

theorem SectionNormSqExtension.proof (h₁ : LeviLogFlat.Statement) (h₂ : LeviHolPerturb.Statement)
    (h₃ : LeviCompHol.Statement) (h₄ : LeviFSInvariant.Statement) : SectionNormSqExtension.Statement := by
  intro K _ _ ι _ Ω _ y A m N v hsm hconj hv hgen
  choose d e G he hG hGy using exists_chartData y A m N v hv
  obtain ⟨F, hF, hFspan⟩ := exists_gens y
  exact ⟨Sf d G A m F, contDiffOn_Sf hsm, fun x hx => Sf_pos hgen he hG hGy hFspan hx,
    fun c x hc => Sf_smul he hG (fun p hp => (hF p hp).1) hc x, fun x => Sf_conj hconj m d G F x,
    fun x hx => Sf_value hv he hG hGy hF hx,
    fun z hz w hw => levi_identity h₁ h₂ h₃ h₄ hsm hgen he hG hGy hF hFspan hz hw⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
