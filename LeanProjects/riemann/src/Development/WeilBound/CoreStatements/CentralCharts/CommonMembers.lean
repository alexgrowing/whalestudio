import Development.WeilBound.CoreStatements.CentralCharts.SmoothOnOfTame
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelAnalyticDataExists
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothContinuous
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SingularPotentialLogGrowthPshStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedAtlasSmoothPotentialLocalStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdaptedAtlasSncSectionStatement

noncomputable section

namespace AnalyticReference.An

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Metric
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.PB

variable {n : ℕ} {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {P : Ideal (MRing J)}

theorem isLiftSys (R : AnLogRes P ⊤ n) : Cj.IsLiftSys R.A P R.U R.lift :=
  ⟨R.isOpen_U, R.mem_U, R.holo, R.mem, R.compat, fun z hz => R.surj z hz (not_mem_top _),
    fun x x' h => R.inj x x' (not_mem_top _) h, fun x p hp j hj => R.immersion x (not_mem_top _) p hp j hj⟩

def IsMember (R : AnLogRes P ⊤ n) (L : LocPot R.X) (s : R.X → R.X → ℂ) (d : K → ℤ) (u : R.X → ℝ) (cen : Prop)
    (ph : R.X → ℝ) (phT : ℝ → R.X → ℝ) (line : ℝ → HermLine J) (C₅ C t₀ : ℝ) : Prop :=
  IsSingWeight R.A L s (potOf R (fsHerm J d)) ph C₅ ∧
  IsRegFamily R.A (potOf R (fsHerm J fun _ => 1)) L s (potOf R (fsHerm J d)) ph phT C t₀ ∧
  IsRegFamilyC2 R.A s ph phT ∧ (∀ x ∉ bdry s, ph x = u x) ∧
  (∀ t, (line t).a = d ∧ IsSmoothHerm (line t) ∧ IsConjInvariantH (line t)) ∧
  (∀ t, 0 < t → t ≤ t₀ → ∀ x, Real.log ((line t).h (R.lift x x)) =
    Real.log ((fsHerm J d).h (R.lift x x)) + phT t x) ∧
  (cen → ∀ t, IsPsh R.A ((potOf R (fsHerm J d) + LocPot.ofFun (phT t)).rsmul (-1)) ∧
    IsPsh R.A (potOf R (fsHerm J d) + LocPot.ofFun (phT t)))

theorem exists_line (R : AnLogRes P ⊤ n) (c : R.X → R.X)
    (hc : ∀ x, SameOrbit (R.lift (c x) (c x)) (Cj.cj (R.lift x x))) (d : K → ℤ) (f : R.X → ℝ) (hf : R.A.Smooth f)
    (hfc : ∀ x, f (c x) = f x) : ∃ B : HermLine J, B.a = d ∧ IsSmoothHerm B ∧ IsConjInvariantH B ∧
      ∀ x, Real.log (B.h (R.lift x x)) = Real.log ((fsHerm J d).h (R.lift x x)) + f x := by
  obtain ⟨B, a0, hs, hl⟩ := exists_hermLine_log_eq_of_smooth _ _ _ n R f hf
  have hfs : IsSmoothHerm (fsHerm J d) := StepW.fsHerm_isSmoothHerm K J d
  have hmem : ∀ x, ∀ k, ∃ i, R.lift x x ⟨k, i⟩ ≠ 0 := fun x => (R.mem x x (R.mem_U x)).1
  have hB : ∀ x, Real.log ((Cj.conjAvg B).h (R.lift x x)) = f x := fun x => by
    rw [Cj.conjAvg_log _ (hmem x), ← FA.deg0_orbit B a0 (hc x), hl, hl, hfc]
    ring
  refine ⟨(fsHerm J d).tensor (Cj.conjAvg B), ?_, ?_, fun z => ?_, fun x => ?_⟩
  · show d + B.a = d
    rw [a0, add_zero]
  · exact ContDiffOn.mul hfs (Cj.conjAvg_smooth hs)
  · show (fsHerm J d).h _ * (Cj.conjAvg B).h _ = (fsHerm J d).h _ * (Cj.conjAvg B).h _
    rw [Cj.fs_conj d z, Cj.conjAvg_conj B z]
  · show Real.log ((fsHerm J d).h _ * (Cj.conjAvg B).h _) = _
    rw [Real.log_mul ((fsHerm J d).pos _ (hmem x)).ne' ((Cj.conjAvg B).pos _ (hmem x)).ne', hB]

theorem exists_member (hR : RegGlobalStatement) (R : AnLogRes P ⊤ n) (L : LocPot R.X) (s : R.X → R.X → ℂ) {nb : ℕ}
    (m : Fin nb → ℕ) (W : Fin nb → Set R.X) (hL : IsPotential R.A L) (hs : IsSection R.A L s)
    (snc : IsSNC R.A L s m W) (hn : ∀ y, logNormSec L s y ≤ 0)
    (hcb : ∀ x x', SameOrbit (R.lift x' x') (Cj.cj (R.lift x x)) → (x' ∈ bdry s ↔ x ∈ bdry s) ∧ rW L s x' = rW L s x)
    (d : K → ℤ) (u : R.X → ℝ) (cen : Prop)
    (huc : ∀ x x', SameOrbit (R.lift x' x') (Cj.cj (R.lift x x)) → u x' = u x)
    (hT : ∀ x, ∃ ψ a M, NChart R.A (R.U x) L s x ψ a M ∧ Tame a fun t => u (ψ.symm t))
    (hP : ∀ x ∉ bdry s, ∃ ψ : OpenPartialHomeomorph R.X (Fin n → ℂ), IsCompatChart R.A ψ ∧ x ∈ ψ.source ∧ ψ x = 0 ∧
      PshAt0 (fun t => Real.log ((fsHerm J d).h (R.lift x (ψ.symm t))) + u (ψ.symm t)) ∧
      (cen → PshAt0 fun t => -1 * (Real.log ((fsHerm J d).h (R.lift x (ψ.symm t))) + u (ψ.symm t)))) :
    ∃ ph phT line C₅ C t₀, IsMember R L s d u cen ph phT line C₅ C t₀ := by
  obtain ⟨hA, hfs, hΘ⟩ := fs_pos_potential K J P n R
  have hfd : IsSmoothHerm (fsHerm J d) := StepW.fsHerm_isSmoothHerm K J d
  have hth := hA _ hfd
  have hsys := isLiftSys R
  obtain ⟨c, hspec, hcont, hinv⟩ := GlobalTheory.T.lift_system_complex_conjugation hsys
  have hanal := GlobalTheory.T.conjugation_antiholomorphic_charts hsys c hspec hcont
  have hsm := smoothOn_of_tame hT
  obtain ⟨C₁, hC₁⟩ := size_of_tame hn hT
  have hpsh : IsPshOn R.A (bdry s)ᶜ (potOf R (fsHerm J d) + LocPot.ofFun u) := by
    refine pshOn_of_local _ (fun x z hz => ?_) fun z hz => ?_
    · obtain ⟨V, h1, h2, G, h3, h4⟩ := hth.2 x z z ⟨hz.1, R.mem_U z⟩
      refine ⟨V, h1, h2, G, h3, fun w hw => ?_⟩
      have := h4 w ⟨⟨hw.1.1, hw.1.2.1⟩, hw.2.1⟩
      show (potOf R (fsHerm J d)).φ x w + u w - ((potOf R (fsHerm J d)).φ z w + u w) = _
      linarith
    · obtain ⟨ψ, h1, h2, h3, h4, -⟩ := hP z hz
      exact ⟨ψ, h1, h2, h3, h4⟩
  obtain ⟨C₅, hsw⟩ := GlobalTheory.T.singular_potential_log_growth_psh n R.X R.A L s nb m W hL hs snc hn _ u C₁ hth hsm hpsh hC₁
  have hlines : ∀ (phT : ℝ → R.X → ℝ) (t₀ : ℝ), (∀ t, 0 < t → t ≤ t₀ → R.A.Smooth (phT t)) →
      (∀ t x, phT t (c x) = phT t x) → ∃ line : ℝ → HermLine J,
      (∀ t, (line t).a = d ∧ IsSmoothHerm (line t) ∧ IsConjInvariantH (line t)) ∧
      (∀ t, 0 < t → t ≤ t₀ → ∀ x, Real.log ((line t).h (R.lift x x)) =
        Real.log ((fsHerm J d).h (R.lift x x)) + phT t x) := by
    intro phT t₀ h1 h2
    have : ∀ t, ∃ B : HermLine J, (B.a = d ∧ IsSmoothHerm B ∧ IsConjInvariantH B) ∧ (0 < t → t ≤ t₀ → ∀ x,
        Real.log (B.h (R.lift x x)) = Real.log ((fsHerm J d).h (R.lift x x)) + phT t x) := fun t => by
      by_cases ht : 0 < t ∧ t ≤ t₀
      · obtain ⟨B, b1, b2, b3, b4⟩ := exists_line R c hspec d (phT t) (h1 t ht.1 ht.2) (h2 t)
        exact ⟨B, ⟨b1, b2, b3⟩, fun _ _ => b4⟩
      · exact ⟨fsHerm J d, ⟨rfl, hfd, Cj.fs_conj d⟩, fun a b => absurd ⟨a, b⟩ ht⟩
    choose line h3 h4 using this
    exact ⟨line, h3, h4⟩
  by_cases hcen : cen
  · have hneg : IsPshOn R.A (bdry s)ᶜ ((potOf R (fsHerm J d) + LocPot.ofFun u).rsmul (-1)) := by
      refine pshOn_of_local _ (fun x z hz => ?_) fun z hz => ?_
      · obtain ⟨V, h1, h2, G, h3, h4⟩ := hth.2 x z z ⟨hz.1, R.mem_U z⟩
        refine ⟨V, h1, h2, fun w => -G w, fun j y hy => (h3 j y hy).neg, fun w hw => ?_⟩
        have := h4 w ⟨⟨hw.1.1, hw.1.2.1⟩, hw.2.1⟩
        show -1 * ((potOf R (fsHerm J d)).φ x w + u w) - -1 * ((potOf R (fsHerm J d)).φ z w + u w) = _
        rw [Complex.neg_re]
        linarith
      · obtain ⟨ψ, h1, h2, h3, -, h4⟩ := hP z hz
        exact ⟨ψ, h1, h2, h3, h4 hcen⟩
    obtain ⟨u', C₀, hu', heq, p1, p2, s1, r1, c1⟩ := FA.central_regular R.A (potOf R (fsHerm J fun _ => 1)) L s m W
      hL hs snc hn (hA _ hfs) hΘ _ u C₅ hsw hneg
    have hc1 := Cj.smooth_continuous hu'
    have hd : Dense (bdry s)ᶜ := interior_eq_empty_iff_dense_compl.1 (LeviFormBoundaryTopology.interior_bdry_eq_empty hs snc)
    have hcp : ∀ y, u' (c y) = u' y :=
      congrFun (Continuous.ext_on hd (hc1.comp hcont) hc1 fun y hy => by
        have hy' : c y ∉ bdry s := fun h => hy ((hcb _ _ (hspec y)).1.1 h)
        show u' (c y) = u' y
        rw [heq _ hy', heq _ hy, huc _ _ (hspec y)])
    obtain ⟨line, l1, l2⟩ := hlines (fun _ => u') (Real.exp (-Real.exp 1)) (fun _ _ _ => hu') fun _ => hcp
    exact ⟨u', fun _ => u', line, C₀, C₀, _, s1, r1, c1, heq, l1, l2, fun _ _ => ⟨p2, p1⟩⟩
  · obtain ⟨B, hB⟩ := GlobalTheory.T.adapted_atlas_snc_section R.A L s m W hL hs snc hn
    obtain ⟨C₆, hg⟩ := GlobalTheory.T.adapted_atlas_smooth_potential_local n R.X R.A B L s nb m W hL hs snc hn hB u hsm fun x => by
      obtain ⟨ψ, a, M, h, ht⟩ := hT x
      obtain ⟨V', c, h1, h2, h3, h4⟩ := local_of_tame hn h ht
      exact ⟨ψ, V', c, h.1, h1, h2, h3, fun x' a b => (h4 x' a b).2⟩
    obtain ⟨m₁, -, -⟩ := enlarging_constants_smooth_members n R.X R.A (potOf R (fsHerm J fun _ => 1)) L s nb m W
      hL hs snc hn (hA _ hfs) hΘ
    have hsw' := m₁ _ _ _ _ (le_max_left C₅ C₆) hsw
    obtain ⟨C, t₀, phT, r, c2⟩ := hR R.A B _ L s m W (hA _ hfs) hΘ hL hs snc hn hB _ u _ hsw' (hg _ (le_max_right _ _))
    have hthc := GlobalTheory.T.lift_system_real_structure hsys c hspec hcont hanal (fsHerm J d) (Cj.fs_conj d) (potOf R (fsHerm J d)) fun x =>
      ⟨Set.univ, isOpen_univ, trivial, fun _ => 0, fun _ => analyticOnNhd_const,
        fun z _ => (sub_self _).trans Complex.zero_re.symm⟩
    obtain ⟨C', t', r', c'⟩ := GlobalTheory.T.conjugation_invariant_singular_potential n R.X R.A _ L s nb m W hL hs snc hn (hA _ hfs) hΘ c hcont hinv hanal
      (fun y => (hcb _ _ (hspec y)).1) (fun y => (hcb _ _ (hspec y)).2) _ u phT C t₀ hth hthc
      (fun y _ => huc _ _ (hspec y)) r c2
    obtain ⟨line, l1, l2⟩ := hlines (fun t y => (phT t y + phT t (c y)) / 2) t' (fun t h0 h1 => (r'.2.2 t h0 h1).1)
      fun t x => by rw [hinv, add_comm]
    exact ⟨u, _, line, C₅, C', t', hsw, r', c', fun _ _ => rfl, l1, l2, fun h => absurd h hcen⟩

theorem IsMember.mono {R : AnLogRes P ⊤ n} {L : LocPot R.X} {s : R.X → R.X → ℂ} {nb : ℕ}
    {m : Fin nb → ℕ} {W : Fin nb → Set R.X} (hL : IsPotential R.A L) (hs : IsSection R.A L s)
    (snc : IsSNC R.A L s m W) (hn : ∀ y, logNormSec L s y ≤ 0) {d : K → ℤ} {u : R.X → ℝ} {cen : Prop}
    {ph : R.X → ℝ} {phT : ℝ → R.X → ℝ} {line : ℝ → HermLine J} {C₅ C t₀ D₅ D T : ℝ}
    (h : IsMember R L s d u cen ph phT line C₅ C t₀) (h₅ : C₅ ≤ D₅) (hD : |C| ≤ D) (hT0 : 0 < T) (hT : T ≤ t₀)
    (hT1 : T ≤ Real.exp (-1)) : IsMember R L s d u cen ph phT line D₅ D T := by
  obtain ⟨hA, hfs, hΘ⟩ := fs_pos_potential K J P n R
  obtain ⟨m₁, m₂, -⟩ := enlarging_constants_smooth_members n R.X R.A (potOf R (fsHerm J fun _ => 1)) L s nb m W
    hL hs snc hn (hA _ hfs) hΘ
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h
  exact ⟨m₁ _ _ _ _ h₅ a1, m₂ _ _ _ _ _ _ _ hD hT0 hT hT1 a2 a1.1, a3, a4, a5, fun t h0 h1 => a6 t h0 (h1.trans hT), a7⟩

theorem member_zero (R : AnLogRes P ⊤ n) {L : LocPot R.X} {s : R.X → R.X → ℂ} {nb : ℕ}
    {m : Fin nb → ℕ} {W : Fin nb → Set R.X} (hL : IsPotential R.A L) (hs : IsSection R.A L s)
    (snc : IsSNC R.A L s m W) (hn : ∀ y, logNormSec L s y ≤ 0) (d : K → ℤ)
    (hd : IsPosPot R.A (potOf R (fsHerm J d))) :
    ∃ C₅ C t₀, IsMember R L s d 0 False 0 (fun _ => 0) (fun _ => fsHerm J d) C₅ C t₀ := by
  obtain ⟨hA, hfs, hΘ⟩ := fs_pos_potential K J P n R
  have hfd : IsSmoothHerm (fsHerm J d) := StepW.fsHerm_isSmoothHerm K J d
  obtain ⟨-, -, m₃⟩ := enlarging_constants_smooth_members n R.X R.A (potOf R (fsHerm J fun _ => 1)) L s nb m W
    hL hs snc hn (hA _ hfs) hΘ
  have hsm0 : R.A.Smooth (0 : R.X → ℝ) := fun jj => by
    show ContDiffOn ℝ _ (fun _ => (0 : ℝ)) _
    exact contDiffOn_const
  have hpsh0 : IsPsh R.A (potOf R (fsHerm J d) + LocPot.ofFun (0 : R.X → ℝ)) := by
    intro x jj z hz w
    have e1 : (potOf R (fsHerm J d) + LocPot.ofFun (0 : R.X → ℝ)).φ x ∘ (R.A.chart jj).symm =
        (potOf R (fsHerm J d)).φ x ∘ (R.A.chart jj).symm := by
      funext u
      show (potOf R (fsHerm J d)).φ x _ + (0 : ℝ) = _
      rw [add_zero]
      rfl
    rw [e1]
    by_cases hw : w = 0
    · rw [hw, levi_zero]
    · exact (hd x jj z ⟨hz.1, hz.2.1⟩ w hw).le
  obtain ⟨C₀, s0, r0, c0⟩ := m₃ _ 0 (hA _ hfd) hsm0 hpsh0
  exact ⟨C₀, C₀, _, s0, r0, c0, fun _ _ => rfl, fun _ => ⟨rfl, hfd, Cj.fs_conj d⟩,
    fun _ _ _ _ => (add_zero _).symm, False.elim⟩

theorem common_members {σ : Type} [Finite σ] {R : AnLogRes P ⊤ n} {L : LocPot R.X} {s : R.X → R.X → ℂ} {nb : ℕ}
    {m : Fin nb → ℕ} {W : Fin nb → Set R.X} (hL : IsPotential R.A L) (hs : IsSection R.A L s)
    (snc : IsSNC R.A L s m W) (hn : ∀ y, logNormSec L s y ≤ 0) {d : σ → K → ℤ} {u : σ → R.X → ℝ} {cen : σ → Prop}
    {ph : σ → R.X → ℝ} {phT : σ → ℝ → R.X → ℝ} {line : σ → ℝ → HermLine J}
    (h : ∀ a, ∃ C₅ C t₀, IsMember R L s (d a) (u a) (cen a) (ph a) (phT a) (line a) C₅ C t₀) :
    ∃ C₅ C t₀, ∀ a, IsMember R L s (d a) (u a) (cen a) (ph a) (phT a) (line a) C₅ C t₀ := by
  choose C₅ C t₀ hm using h
  obtain ⟨D₅, hD₅⟩ := FA.common_bound C₅
  obtain ⟨D, hD⟩ := FA.common_bound fun a => |C a|
  obtain ⟨T, hT0, hT⟩ := FA.common_scale (fun o : Option σ => o.elim (Real.exp (-1)) t₀) (by
    rintro (_ | p)
    · exact Real.exp_pos _
    · exact (hm p).2.1.1)
  exact ⟨D₅, D, T, fun a => (hm a).mono hL hs snc hn (hD₅ a) (hD a) hT0 (hT (some a)) (hT none)⟩

end AnalyticReference.An
