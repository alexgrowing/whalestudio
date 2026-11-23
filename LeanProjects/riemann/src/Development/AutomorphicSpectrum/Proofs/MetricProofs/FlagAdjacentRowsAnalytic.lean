import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PullbackPullback
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphic
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentSwapVarietiesArithmeticStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Pr

theorem holoMap_comp' {e₁ e₂ e₃ : ℕ} {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {C : FinHolAtlas e₁ Z} {B : FinHolAtlas e₂ Y} {A : FinHolAtlas e₃ X}
    {g : Z → Y} {f : Y → X} (hg : HoloMap C B g) (hf : HoloMap B A f) : HoloMap C A (f ∘ g) := by
  refine ⟨hf.1.comp hg.1, fun j k t ht => ?_⟩
  obtain ⟨ht1, ht2⟩ := ht
  obtain ⟨m, hm⟩ := B.cover (g ((C.chart j).symm t))
  have h1 : AnalyticAt ℂ (B.chart m ∘ g ∘ (C.chart j).symm) t := hg.2 j m t ⟨ht1, hm⟩
  have hu : (B.chart m).symm ((B.chart m ∘ g ∘ (C.chart j).symm) t) = g ((C.chart j).symm t) :=
    (B.chart m).left_inv hm
  have h2 : AnalyticAt ℂ (A.chart k ∘ f ∘ (B.chart m).symm)
      ((B.chart m ∘ g ∘ (C.chart j).symm) t) :=
    hf.2 m k _ ⟨(B.chart m).map_source hm, by
      rw [Set.mem_preimage, hu]; exact ht2⟩
  refine (h2.comp h1).congr ?_
  have hc : ContinuousAt (g ∘ (C.chart j).symm) t :=
    hg.1.continuousAt.comp ((C.chart j).continuousAt_symm ht1)
  filter_upwards [hc ((B.chart m).open_source.mem_nhds hm)] with t' ht'
  have ht'' : g ((C.chart j).symm t') ∈ (B.chart m).source := ht'
  simp only [Function.comp]
  rw [(B.chart m).left_inv ht'']

theorem injective_of_degree_one {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {π : Y → X} (hd : IsDegreeOff A B π 1 ∅) :
    Function.Injective π := by
  intro u w huw
  obtain ⟨c, hc⟩ := Set.ncard_eq_one.1 (hd.2.2.2.2.1 (π u) (Set.notMem_empty _))
  have hu : u ∈ π ⁻¹' {π u} := rfl
  have hw : w ∈ π ⁻¹' {π u} := huw.symm
  rw [hc] at hu hw
  exact hu.trans hw.symm

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_holo_of_centre {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k, ι' k)) {P : Ideal (MRing ι)} {J : Ideal (MRing ι)}
    {P' J' : Ideal (MRing ι')} {D D' : ℕ} (hJ : J = ⊤) (R : AnLogRes P J D)
    (R' : AnLogRes P' J' D') (hb : IsBlockMap κ v) (hP : P ≤ imageZ v P') :
    ∃ h : R'.X → R.X, HoloMap R'.A R.A h ∧ ∀ x, SameOrbit (R.lift (h x) (h x)) (R'.lift x x ∘ v) := by
  subst hJ
  exact Proj.holoMap_of_blockProj K ι K' ι' κ v P P' J' D D' R R' hb hP

theorem isBlockMap_v₀ (k₀ : K) :
    IsBlockMap (some : K → Option K) (v₀ (ι := ι) k₀) := by
  refine ⟨Option.some_injective _, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨k, m⟩ ⟨k', m'⟩ h
    have h1 : k = k' := Option.some.inj (congrArg Sigma.fst h)
    subst h1
    have h2 : m = m' := eq_of_heq (Sigma.mk.inj h).2
    rw [h2]
  · rintro ⟨o, m⟩ ⟨k, rfl⟩
    exact ⟨⟨k, m⟩, rfl⟩

def κ₁ (k₀ k : K) : Option K := if k = k₀ then none else some k

theorem isBlockMap_v₁ (k₀ : K) : IsBlockMap (κ₁ k₀) (v₁ (ι := ι) k₀) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u w h
    by_cases hu : u = k₀ <;> by_cases hw : w = k₀ <;> simp_all [κ₁]
  · rintro ⟨k, m⟩ ⟨k', m'⟩ h
    by_cases hk : k = k₀
    · subst hk
      by_cases hk' : k' = k
      · subst hk'
        rw [v₁_self, v₁_self] at h
        have h2 : m = m' := eq_of_heq (Sigma.mk.inj h).2
        rw [h2]
      · rw [v₁_self, v₁_ne (p := ⟨k', m'⟩) hk'] at h
        exact absurd (congrArg Sigma.fst h) (by simp)
    · by_cases hk' : k' = k₀
      · subst hk'
        rw [v₁_self, v₁_ne (p := ⟨k, m⟩) hk] at h
        exact absurd (congrArg Sigma.fst h) (by simp)
      · rw [v₁_ne (p := ⟨k, m⟩) hk, v₁_ne (p := ⟨k', m'⟩) hk'] at h
        have h1 : k = k' := Option.some.inj (congrArg Sigma.fst h)
        subst h1
        have h2 : m = m' := eq_of_heq (Sigma.mk.inj h).2
        rw [h2]
  · rintro ⟨k, m⟩
    by_cases hk : k = k₀
    · subst hk
      rw [v₁_self]
      simp [κ₁]
    · rw [v₁_ne (p := ⟨k, m⟩) hk]
      simp [κ₁, hk]
  · rintro ⟨o, m⟩ ⟨k, hk⟩
    by_cases e : k = k₀
    · subst e
      have ho : o = none := by
        have hk' : κ₁ k k = o := hk
        rw [← hk']; simp [κ₁]
      subst ho
      exact ⟨⟨k, m⟩, v₁_self k m⟩
    · have ho : o = some k := by
        have hk' : κ₁ k₀ k = o := hk
        rw [← hk']; simp [κ₁, e]
      subst ho
      exact ⟨⟨k, m⟩, v₁_ne (p := ⟨k, m⟩) e⟩

theorem basePart_orbit {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ}
    (h : SameOrbit z z') : SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc _, rfl⟩

theorem basePart_snd {σ : Type} {blk : σ → Option K} {k₀ : K} {s : σ} (hs : blk s = some k₀)
    (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) :
    basePart blk (sndPt k₀ z) = basePart blk (fstPt k₀ z) := by
  funext ⟨k, m⟩
  have hk : k.1 ≠ k₀ := fun e => k.2 s (by rw [hs, e])
  change z (v₁ k₀ ⟨k.1, m⟩) = z (v₀ k₀ ⟨k.1, m⟩)
  rw [v₁_ne (p := ⟨k.1, m⟩) hk]
  rfl

theorem orbit_of_two {k₀ : K} {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ}
    (h₀ : SameOrbit (fstPt k₀ z) (fstPt k₀ z')) (h₁ : SameOrbit (sndPt k₀ z) (sndPt k₀ z')) :
    SameOrbit z z' := by
  obtain ⟨c₀, hc₀, e₀⟩ := h₀
  obtain ⟨c₁, hc₁, e₁⟩ := h₁
  refine ⟨fun o => o.elim (c₁ k₀) c₀, ?_, ?_⟩
  · rintro (_ | k)
    · exact hc₁ k₀
    · exact hc₀ k
  · funext ⟨o, m⟩
    cases o with
    | none =>
      have := congrFun e₁ ⟨k₀, m⟩
      simpa [sndPt, v₁_self] using this
    | some k =>
      have := congrFun e₀ ⟨k, m⟩
      simpa [fstPt, v₀] using this

theorem two_projections : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (pr : RW.X → BM.Rb.X), HoloMap RW.A BM.Rb.A pr → (∀ x, SameOrbit (BM.Rb.lift (pr x) (pr x)) (basePart M.blk (fstPt k₀ (RW.lift x x)))) → ∃ q : Fin 2 → RW.X → FA.S.X, (∀ i, HoloMap RW.A FA.S.A (q i)) ∧ (∀ i, FA.pr ∘ q i = pr) ∧ (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) ∧ (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) ∧ (Function.Injective fun w => (q 0 w, q 1 w)) ∧ ∀ p, p ≠ (τ, a) → FA.S.ph (some p) ∘ q 0 = FA.S.ph (some p) ∘ q 1 ∧ ∀ t, FA.S.phT (some p) t ∘ q 0 = FA.S.phT (some p) t ∘ q 1 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b k₀ ca cb hb hab hk ha hcb hy RW pr hpr hbase
  obtain ⟨-, -, -, hi₀, hi₁⟩ := GlobalTheory.T.flag_adjacent_swap_varieties_arithmetic K ι Φ y Ψ N j M d τ a b k₀ ca cb hb hab hk ha hcb hy
  have hi₁' := hi₁ (v₁ k₀) (fun p hp => v₁_ne hp) (fun m => v₁_self k₀ m)
  obtain ⟨h₀, hh₀, ho₀⟩ := exists_holo_of_centre some (v₀ k₀) FA.J_top FA.Re.R RW
    (isBlockMap_v₀ k₀) hi₀.ge
  obtain ⟨h₁, hh₁, ho₁⟩ := exists_holo_of_centre (κ₁ k₀) (v₁ k₀) FA.J_top FA.Re.R RW
    (isBlockMap_v₁ k₀) hi₁'.ge
  have hdeg := FA.Re.degree
  rw [FA.deg_one, FA.br_empty] at hdeg
  have hπ : Function.Injective FA.Re.π := injective_of_degree_one hdeg
  have hpr' : ∀ (x₁ : FA.Re.R.X) (w : RW.X) (zz : (Σ k, ι k) → ℂ),
      SameOrbit (FA.Re.R.lift x₁ x₁) zz →
      basePart M.blk zz = basePart M.blk (fstPt k₀ (RW.lift w w)) → FA.pr (FA.Re.π x₁) = pr w := by
    intro x₁ w zz h1 h2
    refine BM.Rb.inj _ _ (Proj.not_mem_mcPts_top _) ?_
    have h3 := basePart_orbit M.blk h1
    rw [h2] at h3
    exact orbit_trans (orbit_symm (FA.pr_eq x₁)) (orbit_trans h3 (orbit_symm (hbase w)))
  have hb₀ : ∀ w, FA.pr (FA.Re.π (h₀ w)) = pr w := fun w => hpr' _ w _ (ho₀ w) rfl
  have hb₁ : ∀ w, FA.pr (FA.Re.π (h₁ w)) = pr w := fun w =>
    hpr' _ w _ (ho₁ w) (basePart_snd hk (RW.lift w w))
  refine ⟨![FA.Re.π ∘ h₀, FA.Re.π ∘ h₁], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have c₀ := holoMap_comp' hh₀ FA.Re.holo
    have c₁ := holoMap_comp' hh₁ FA.Re.holo
    exact Fin.forall_fin_two.2 ⟨c₀, c₁⟩
  · exact Fin.forall_fin_two.2 ⟨funext hb₀, funext hb₁⟩
  · intro x x₀ e
    have : x₀ = h₀ x := hπ e
    subst this
    exact ho₀ x
  · intro x x₀ e
    have : x₀ = h₁ x := hπ e
    subst this
    exact ho₁ x
  · intro w w' e
    have e₀ : FA.Re.π (h₀ w) = FA.Re.π (h₀ w') := congrArg Prod.fst e
    have e₁ : FA.Re.π (h₁ w) = FA.Re.π (h₁ w') := congrArg Prod.snd e
    have f₀ := hπ e₀
    have f₁ := hπ e₁
    have g₀ : SameOrbit (fstPt k₀ (RW.lift w w)) (fstPt k₀ (RW.lift w' w')) := by
      have := ho₀ w'
      rw [← f₀] at this
      exact orbit_trans (orbit_symm (ho₀ w)) this
    have g₁ : SameOrbit (sndPt k₀ (RW.lift w w)) (sndPt k₀ (RW.lift w' w')) := by
      have := ho₁ w'
      rw [← f₁] at this
      exact orbit_trans (orbit_symm (ho₁ w)) this
    exact RW.inj w w' (Proj.not_mem_mcPts_top _) (orbit_of_two g₀ g₁)
  · intro p hp
    have key : ∀ w, FA.S.ph (some p) (FA.Re.π (h₀ w)) = FA.S.ph (some p) (FA.Re.π (h₁ w)) ∧
        ∀ t, FA.S.phT (some p) t (FA.Re.π (h₀ w)) = FA.S.phT (some p) t (FA.Re.π (h₁ w)) := by
      intro w
      refine FA.step_ph p (h₀ w) (h₁ w) ((hb₀ w).trans (hb₁ w).symm) ?_
      intro k hkp
      have hne : k ≠ k₀ := fun e => hp (M.blk_inj p (τ, a) k₀ (e ▸ hkp) hk)
      obtain ⟨c₀, -, e₀⟩ := ho₀ w
      obtain ⟨c₁, hc₁, e₁⟩ := ho₁ w
      refine ⟨c₀ k / c₁ k, fun m => ?_⟩
      have a₀ := congrFun e₀ ⟨k, m⟩
      have a₁ := congrFun e₁ ⟨k, m⟩
      simp only [Function.comp] at a₀ a₁
      rw [v₁_ne (p := ⟨k, m⟩) hne] at a₁
      rw [a₀, a₁]
      have := hc₁ k
      simp only [v₀]
      field_simp
    exact ⟨funext fun w => (key w).1, fun t => funext fun w => (key w).2 t⟩

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Pr
