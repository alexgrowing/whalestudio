import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import GroundTheory.HeightsAndTheta.Heights.Regularisation.GlueCharts
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PhiISemipositive
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlurisubharmonicLocalStatement

open Filter Topology Metric Set
open ReciprocityTheory.AnForm.A (IsPsh coordDiv limsupExt molli shrink polyMax)

namespace LevelTowerAlt.Bdd

theorem isPsh_comp {m n : ℕ} {U : Set (Fin n → ℂ)} {V : Set (Fin m → ℂ)} (hU : IsOpen U) (hV : IsOpen V)
    {u : (Fin n → ℂ) → ℝ} (hc : ContinuousOn u U) (hu : IsPsh U u) {F : (Fin m → ℂ) → Fin n → ℂ}
    (hF : AnalyticOnNhd ℂ F V) (hFU : MapsTo F V U) : IsPsh V (fun v => u (F v)) := by
  have hcF : ContinuousOn (fun v => u (F v)) V := hc.comp hF.continuousOn hFU
  refine ⟨hcF.upperSemicontinuousOn, fun z w hd => ?_⟩
  have hl : Continuous fun ζ : ℂ => z + ζ • w := by fun_prop
  have hmaps : MapsTo (fun ζ : ℂ => z + ζ • w) (closedBall 0 1) V := fun ζ hζ => hd ζ (by simpa using hζ)
  have hint : CircleIntegrable (fun ζ : ℂ => u (F (z + ζ • w))) 0 1 :=
    ((hcF.comp hl.continuousOn hmaps).mono sphere_subset_closedBall).circleIntegrable zero_le_one
  refine ⟨hint, le_of_forall_pos_le_add fun η hη => ?_⟩
  have hK : IsCompact ((fun ζ : ℂ => F (z + ζ • w)) '' closedBall 0 1) :=
    (isCompact_closedBall 0 1).image_of_continuousOn (hF.continuousOn.comp hl.continuousOn hmaps)
  set Kc := (fun ζ : ℂ => F (z + ζ • w)) '' closedBall 0 1 with hKc
  obtain ⟨δ₀, hδ₀, hsub⟩ := hK.exists_cthickening_subset_open hU
    (by rintro _ ⟨ζ, hζ, rfl⟩; exact hFU (hmaps hζ))
  have huc := (hK.cthickening (r := δ₀)).uniformContinuousOn_of_continuous (hc.mono hsub)
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.1 huc η hη
  obtain ⟨ρ⟩ := ReciprocityTheory.AnForm.A.mollifierInhabit_thm n
  have hε : 0 < min δ₀ (δ / 2) := lt_min hδ₀ (half_pos hδ)
  set ε := min δ₀ (δ / 2) with hεd
  obtain ⟨ho, hsm, hp, hb⟩ := (ReciprocityTheory.AnForm.A.mollify_thm n ρ U u hU hu).1 ε hε
  have hball : ∀ x ∈ Kc, closedBall x ε ⊆ cthickening δ₀ Kc := fun x hx =>
    (closedBall_subset_closedBall (min_le_left _ _)).trans (closedBall_subset_cthickening hx δ₀)
  have hshr : ∀ x ∈ Kc, x ∈ shrink U ε := fun x hx => (hball x hx).trans hsub
  have hup : ∀ x ∈ Kc, molli ρ ε u x ≤ u x + η := fun x hx => by
    refine (hb x (hshr x hx)).2.trans (csSup_le ⟨_, x, mem_closedBall_self hε.le, rfl⟩ ?_)
    rintro _ ⟨y, hy, rfl⟩
    have h1 := hδu y (hball x hx hy) x (hball x hx (mem_closedBall_self hε.le))
      ((mem_closedBall.1 hy).trans_lt ((min_le_right _ _).trans_lt (half_lt_self hδ)))
    rw [Real.dist_eq] at h1
    linarith [le_abs_self (u y - u x)]
  have hV' : IsOpen (V ∩ F ⁻¹' shrink U ε) := hF.continuousOn.isOpen_inter_preimage hV ho
  have h2 : ContDiffOn ℝ 2 (molli ρ ε u) (shrink U ε) := hsm.of_le (WithTop.coe_le_coe.mpr le_top)
  have hlevi := (ReciprocityTheory.AnForm.A.isPsh_iff_isLeviPsh_thm n _ _ ho h2).1 hp
  have hC : ContDiffOn ℝ 2 (molli ρ ε u ∘ F) (V ∩ F ⁻¹' shrink U ε) := fun v hv =>
    ((h2.contDiffAt (ho.mem_nhds hv.2)).comp v
      ((hF v hv.1).restrictScalars (𝕜 := ℝ)).contDiffAt).contDiffWithinAt
  have hP : IsPsh (V ∩ F ⁻¹' shrink U ε) (molli ρ ε u ∘ F) :=
    (ReciprocityTheory.AnForm.A.isPsh_iff_isLeviPsh_thm m _ _ hV' hC).2 ⟨hC, fun v hv a => by
      rw [ReciprocityTheory.AnForm.levi_comp a (hF v hv.1) (h2.contDiffAt (ho.mem_nhds hv.2))]
      exact hlevi.2 _ hv.2 _⟩
  obtain ⟨hi2, hle⟩ := hP.2 z w fun ζ hζ => ⟨hd ζ hζ, hshr _ ⟨ζ, by simpa using hζ, rfl⟩⟩
  have hz : F z ∈ Kc := ⟨0, mem_closedBall_self zero_le_one, by simp⟩
  have h3 := Real.circleAverage_mono hi2 (hint.add (circleIntegrable_const η 0 1)) fun ζ hζ =>
    hup _ ⟨ζ, sphere_subset_closedBall (by simpa using hζ), rfl⟩
  rw [Real.circleAverage_add hint (circleIntegrable_const η 0 1), Real.circleAverage_const] at h3
  exact ((hb _ (hshr _ hz)).1.trans hle).trans h3

def PH {n : ℕ} (f : (Fin n → ℂ) → ℝ) (v : Fin n → ℂ) : Prop :=
  ∃ G : (Fin n → ℂ) → ℂ, AnalyticAt ℂ G v ∧ ∀ᶠ u in 𝓝 v, f u = (G u).re

theorem PH.add {n : ℕ} {f g : (Fin n → ℂ) → ℝ} {v : Fin n → ℂ} (hf : PH f v) (hg : PH g v) :
    PH (fun u => f u + g u) v := by
  obtain ⟨F, hF, h1⟩ := hf
  obtain ⟨G, hG, h2⟩ := hg
  refine ⟨fun u => F u + G u, hF.add hG, ?_⟩
  filter_upwards [h1, h2] with u a b
  rw [a, b, Complex.add_re]

theorem PH.const_mul {n : ℕ} {f : (Fin n → ℂ) → ℝ} {v : Fin n → ℂ} (hf : PH f v) (c : ℝ) :
    PH (fun u => c * f u) v := by
  obtain ⟨F, hF, h1⟩ := hf
  refine ⟨fun u => (c : ℂ) * F u, analyticAt_const.mul hF, ?_⟩
  filter_upwards [h1] with u a
  rw [a, Complex.re_ofReal_mul]

theorem PH.sum {n : ℕ} {σ : Type} (s : Finset σ) {f : σ → (Fin n → ℂ) → ℝ} {v : Fin n → ℂ}
    (hf : ∀ i ∈ s, PH (f i) v) : PH (fun u => ∑ i ∈ s, f i u) v := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, analyticAt_const, by simp⟩
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))

theorem PH.log_norm {n : ℕ} {F : (Fin n → ℂ) → ℂ} {v : Fin n → ℂ} (hF : AnalyticAt ℂ F v) (h0 : F v ≠ 0) :
    PH (fun u => Real.log ‖F u‖) v := by
  have hH : AnalyticAt ℂ (fun t => F t / F v) v := hF.div analyticAt_const h0
  refine ⟨fun t => Complex.log (F t / F v) + (Real.log ‖F v‖ : ℝ),
    (hH.clog (by rw [div_self h0]; exact Complex.one_mem_slitPlane)).add analyticAt_const, ?_⟩
  filter_upwards [hF.continuousAt.eventually_ne h0] with t ht
  rw [Complex.add_re, Complex.ofReal_re, Complex.log_re, norm_div,
    Real.log_div (norm_ne_zero_iff.2 ht) (norm_ne_zero_iff.2 h0)]
  ring

theorem local_psh {m n : ℕ} {U : Set (Fin n → ℂ)} (hU : IsOpen U) {φ : (Fin n → ℂ) → ℝ} (hc : ContinuousOn φ U)
    (hφ : IsPsh U φ) {F : (Fin m → ℂ) → Fin n → ℂ} {v : Fin m → ℂ} (hF : AnalyticAt ℂ F v) (hv : F v ∈ U)
    {f g : (Fin m → ℂ) → ℝ} (hf : PH f v) (hg : ∀ᶠ u in 𝓝 v, g u = φ (F u) + f u) :
    ContinuousAt g v ∧ ∃ V, IsOpen V ∧ v ∈ V ∧ IsPsh V g := by
  obtain ⟨G, hG, hfG⟩ := hf
  have he : ∀ᶠ u in 𝓝 v, g u = φ (F u) + (G u).re + 0 := by
    filter_upwards [hg, hfG] with u a b
    rw [a, b, add_zero]
  refine ⟨?_, ?_⟩
  · have h1 : ContinuousAt (fun u => φ (F u) + (G u).re + 0) v :=
      (((hc.continuousAt (hU.mem_nhds hv)).comp hF.continuousAt).add
        (Complex.continuous_re.continuousAt.comp hG.continuousAt)).add continuousAt_const
    exact h1.congr (he.mono fun u h => h.symm)
  · obtain ⟨V, hV, hVo, hvV⟩ := _root_.eventually_nhds_iff.1 ((he.and hF.eventually_analyticAt).and
      (hG.eventually_analyticAt.and (hF.continuousAt.eventually (hU.mem_nhds hv))))
    refine ⟨V, hVo, hvV, GroundTheory.Heights₂.Heights.Regular.isPsh_congr (fun u hu => (hV u hu).1.1.symm) ?_⟩
    exact GroundTheory.Heights₂.Heights.NineStatements.isPsh_add_re_add_const hVo
      (isPsh_comp hU hVo hc hφ (fun u hu => (hV u hu).1.2) fun u hu => (hV u hu).2.2)
      (fun u hu => (hV u hu).2.1.differentiableAt.differentiableWithinAt) 0

theorem limsup_add_tendsto {α : Type} {l : Filter α} [l.NeBot] {q g : α → ℝ} {a C : ℝ} (hq : Tendsto q l (𝓝 a))
    (hg : ∀ᶠ x in l, |g x| ≤ C) : limsup (fun x => q x + g x) l = a + limsup g l := by
  have g1 : IsBoundedUnder (· ≤ ·) l g := isBoundedUnder_of_eventually_le (hg.mono fun x h => (abs_le.1 h).2)
  have g2 : IsCoboundedUnder (· ≤ ·) l g :=
    isCoboundedUnder_le_of_eventually_le l (hg.mono fun x h => (abs_le.1 h).1)
  refine le_antisymm ?_ ?_
  · have := limsup_add_le hq.isBoundedUnder_ge hq.isBoundedUnder_le g2 g1
    rwa [hq.limsup_eq] at this
  · have := le_limsup_add g1 g2 hq.isBoundedUnder_le hq.isBoundedUnder_ge
    rw [hq.liminf_eq, add_comm, add_comm g q] at this
    exact this

theorem abs_limsup_le {α : Type} {l : Filter α} [l.NeBot] {g : α → ℝ} {C : ℝ}
    (hg : ∀ᶠ x in l, |g x| ≤ C) : |limsup g l| ≤ C :=
  abs_le.2 ⟨le_limsup_of_frequently_le (hg.mono fun _ h => (abs_le.1 h).1).frequently
      (isBoundedUnder_of_eventually_le (hg.mono fun _ h => (abs_le.1 h).2)),
    limsup_le_of_le (isCoboundedUnder_le_of_eventually_le l (hg.mono fun _ h => (abs_le.1 h).1))
      (hg.mono fun _ h => (abs_le.1 h).2)⟩

theorem isPsh_ext {n : ℕ} {T : Set (Fin n → ℂ)} (hT : IsOpen T) (hT1 : T ⊆ ball 0 1) (S : Finset (Fin n))
    {q g g' : (Fin n → ℂ) → ℝ} {C : ℝ} (hq : ContinuousOn q T) (hg : ∀ v ∈ T \ coordDiv S, |g v| ≤ C)
    (hc : ContinuousOn (fun v => q v + g v) (T \ coordDiv S)) (hp : IsPsh (T \ coordDiv S) fun v => q v + g v)
    (h1 : ∀ v ∈ T \ coordDiv S, g' v = g v)
    (h2 : ∀ v ∈ T, v ∈ coordDiv S → g' v = limsup g (𝓝[T \ coordDiv S] v)) :
    IsPsh T fun v => q v + g' v := by
  refine GlobalTheory.T.plurisubharmonic_local n T _ hT fun v₀ hv₀ => ?_
  obtain ⟨δ, hδ, hδT⟩ := nhds_basis_closedBall.mem_iff.1 (hT.mem_nhds hv₀)
  obtain ⟨Mq, hMq⟩ := (isCompact_closedBall v₀ δ).exists_bound_of_continuousOn (hq.mono hδT)
  have hUT : ball v₀ δ ⊆ T := ball_subset_closedBall.trans hδT
  have hD : ball v₀ δ \ coordDiv S ⊆ T \ coordDiv S := sdiff_subset_sdiff_left hUT
  have hab : ∀ v ∈ ball v₀ δ \ coordDiv S, |q v + g v| ≤ Mq + C := fun v hv =>
    (abs_add_le _ _).trans (add_le_add (hMq v (ball_subset_closedBall hv.1)) (hg v (hD hv)))
  have hext := (ReciprocityTheory.AnForm.A.pshExtension_thm n S (ball v₀ δ) (fun v => q v + g v) |Mq + C| isOpen_ball
    (hUT.trans hT1) (hc.mono hD) (GroundTheory.Heights₂.Heights.Regular.isPsh_mono hp hD) fun y hy => by
      have hy1 : ‖y‖ < 1 := by simpa using hT1 (hUT hy.1)
      have hs : 0 ≤ ∑ i ∈ S, Real.log ‖y i‖⁻¹ := Finset.sum_nonneg fun i _ => by
        rw [Real.log_inv]
        exact neg_nonneg.2 (Real.log_nonpos (norm_nonneg _) ((norm_le_pi_norm y i).trans hy1.le))
      have hL : 1 ≤ Real.log (Real.exp 1 + ∑ i ∈ S, Real.log ‖y i‖⁻¹) := by
        have := Real.log_le_log (Real.exp_pos 1) (le_add_of_nonneg_right hs (a := Real.exp 1))
        rwa [Real.log_exp] at this
      exact (((le_abs_self _).trans (hab y hy)).trans (le_abs_self _)).trans
        (le_mul_of_one_le_right (abs_nonneg _) hL)).2 (Mq + C)
  refine ⟨ball v₀ δ, isOpen_ball, mem_ball_self hδ, GroundTheory.Heights₂.Heights.Regular.isPsh_congr (fun v hv => ?_) hext⟩
  have hmax : ∀ y ∈ ball v₀ δ \ coordDiv S, max (q y + g y) (-(Mq + C)) = q y + g y := fun y hy =>
    max_eq_left (abs_le.1 (hab y hy)).1
  unfold limsupExt
  split_ifs with hS
  · have hf : 𝓝[ball v₀ δ \ coordDiv S] v = 𝓝[T \ coordDiv S] v :=
      nhdsWithin_eq_nhdsWithin' (isOpen_ball.mem_nhds hv) (Set.ext fun y =>
        ⟨fun h => ⟨hD h.1, h.2⟩, fun h => ⟨⟨h.2, h.1.2⟩, h.2⟩⟩)
    have := ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.nebot_diff (S := S) hT (hUT hv)
    rw [limsup_congr (v := fun y => q y + g y) (eventually_nhdsWithin_of_forall hmax), hf]
    show _ = q v + g' v
    rw [h2 v (hUT hv) hS]
    exact limsup_add_tendsto ((hq.continuousAt (hT.mem_nhds (hUT hv))).tendsto.mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall hg)
  · show max (q v + g v) (-(Mq + C)) = q v + g' v
    rw [hmax v ⟨hv, hS⟩, h1 v ⟨hUT hv, hS⟩]

end LevelTowerAlt.Bdd
