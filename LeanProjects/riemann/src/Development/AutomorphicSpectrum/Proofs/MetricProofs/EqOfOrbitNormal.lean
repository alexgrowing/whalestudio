import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsLocSec
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJMap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ElementaryTwistMinorOtherStepsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedAtlasCompatibilityStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HoloOnDivCongr
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsValueAtOfTorus
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.LForm

section Holo

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

theorem holoOn_congr' {V : Set X} {f g : X → ℂ} (hV : IsOpen V) (h : A.HoloOn V f)
    (hfg : ∀ w ∈ V, g w = f w) : A.HoloOn V g := fun j =>
  (h j).congr ((A.chart j).isOpen_inter_preimage_symm hV) fun u hu => (hfg _ hu.2).symm

theorem holoOn_mono' {U V : Set X} {g : X → ℂ} (h : A.HoloOn U g) (hVU : V ⊆ U) : A.HoloOn V g :=
  fun j => (h j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hVU))

theorem holoOn_mul' {U : Set X} {f g : X → ℂ} (hf : A.HoloOn U f) (hg : A.HoloOn U g) :
    A.HoloOn U fun x => f x * g x :=
  fun j z hz => (hf j z hz).mul (hg j z hz)

theorem holoOn_add' {U : Set X} {f g : X → ℂ} (hf : A.HoloOn U f) (hg : A.HoloOn U g) :
    A.HoloOn U fun x => f x + g x :=
  fun j z hz => (hf j z hz).add (hg j z hz)

theorem holoOn_const' (V : Set X) (c : ℂ) : A.HoloOn V fun _ => c := fun _ _ _ => analyticAt_const

theorem holoOn_sum' {σ : Type} (s : Finset σ) {V : Set X} {f : σ → X → ℂ} (h : ∀ a, A.HoloOn V (f a)) :
    A.HoloOn V fun y => ∑ a ∈ s, f a y := fun k z hz =>
  Finset.analyticAt_fun_sum s fun a _ => h a k z hz

theorem holoOn_prod' {σ : Type} (s : Finset σ) {V : Set X} {f : σ → X → ℂ} (h : ∀ a, A.HoloOn V (f a)) :
    A.HoloOn V fun y => ∏ a ∈ s, f a y := fun k z hz =>
  Finset.analyticAt_fun_prod s fun a _ => h a k z hz

theorem holoOn_minor' {N : ℕ} {V : Set X} {m : X → Matrix (Fin N) (Fin N) ℂ}
    (h : ∀ a b, A.HoloOn V fun y => m y a b) (I J : Finset (Fin N)) :
    A.HoloOn V fun y => minorIJ (m y) I J := by
  unfold minorIJ
  by_cases e : I.card = J.card
  · simp only [dif_pos e, Matrix.det_apply']
    exact holoOn_sum' _ fun s => holoOn_mul' (holoOn_const' _ _) (holoOn_prod' _ fun a => h _ _)
  · simp only [dif_neg e]
    exact holoOn_const' _ _

theorem holoOn_of_chart {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} (hψ : IsCompatChart A ψ)
    {g : (Fin e → ℂ) → ℂ} (hg : AnalyticOnNhd ℂ g ψ.target) : A.HoloOn ψ.source fun w => g (ψ w) :=
  fun j u hu => AnalyticAt.comp (g := g) (f := ψ ∘ (A.chart j).symm) (hg _ (ψ.map_source hu.2)) ((hψ j).1 u hu)

theorem holoOn_transv {N : ℕ} {V : Set X} {h : X → Matrix (Fin N) (Fin N) ℂ} {t : X → ℂ}
    (hh : ∀ a b, A.HoloOn V fun y => h y a b) (ht : A.HoloOn V t) (cb ca : Fin N) (a b : Fin N) :
    A.HoloOn V fun y => (h y * (1 + Matrix.single cb ca (t y))) a b := by
  simp only [Matrix.mul_apply]
  refine holoOn_sum' _ fun c => holoOn_mul' (hh _ _) ?_
  simp only [Matrix.add_apply, Matrix.single_apply]
  refine holoOn_add' (holoOn_const' _ _) ?_
  by_cases e : cb = c ∧ ca = b
  · simpa only [if_pos e] using ht
  · simpa only [if_neg e] using holoOn_const' V 0

end Holo

section Orbit

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem lift_fst {k₀ : K} {L' L : (Σ o : Option K, ι (o.getD k₀)) → ℂ} {z : (Σ k, ι k) → ℂ}
    (hz : SameOrbit z (fstPt k₀ L)) (hL : SameOrbit L' L) :
    ∃ b : K → ℂ, (∀ k, b k ≠ 0) ∧ ∀ q : Σ k, ι k, L' ⟨some q.1, q.2⟩ = b q.1 * z q := by
  obtain ⟨c, hc, rfl⟩ := hz
  obtain ⟨d, hd, rfl⟩ := hL
  refine ⟨fun k => d (some k) * (c k)⁻¹, fun k => mul_ne_zero (hd _) (inv_ne_zero (hc k)), fun q => ?_⟩
  have hq : c q.1 ≠ 0 := hc q.1
  show d (some q.1) * L ⟨some q.1, q.2⟩ = d (some q.1) * (c q.1)⁻¹ * (c q.1 * L ⟨some q.1, q.2⟩)
  field_simp

theorem lift_snd {k₀ : K} {L' L : (Σ o : Option K, ι (o.getD k₀)) → ℂ} {z : (Σ k, ι k) → ℂ}
    (hz : SameOrbit z (sndPt k₀ L)) (hL : SameOrbit L' L) :
    ∃ b : ℂ, b ≠ 0 ∧ ∀ m : ι k₀, L' ⟨none, m⟩ = b * z ⟨k₀, m⟩ := by
  obtain ⟨c, hc, rfl⟩ := hz
  obtain ⟨d, hd, rfl⟩ := hL
  refine ⟨d none * (c k₀)⁻¹, mul_ne_zero (hd _) (inv_ne_zero (hc k₀)), fun m => ?_⟩
  have hq : c k₀ ≠ 0 := hc k₀
  show d none * L ⟨none, m⟩ = d none * (c k₀)⁻¹ * (c k₀ * L (v₁ k₀ ⟨k₀, m⟩))
  rw [v₁_self]
  field_simp

theorem basePart_orbit' {σ : Type} {blk : σ → Option K} {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem eq_of_orbit_normal {κ : Type} {ρ : κ → Type} {z z' : (Σ k, ρ k) → ℂ} (h : SameOrbit z z')
    (c₀ : ∀ k, ρ k) (h₁ : ∀ k, z ⟨k, c₀ k⟩ = 1) (h₂ : ∀ k, z' ⟨k, c₀ k⟩ = 1) : z = z' := by
  obtain ⟨c, hc, rfl⟩ := h
  have hc1 : ∀ k, c k = 1 := fun k => by
    have := h₁ k
    simp only [h₂ k, mul_one] at this
    exact this
  funext q
  simp only [hc1, one_mul]

end Orbit

theorem holoOn_step {N e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {V : Set X} (hV : IsOpen V)
    {S : Finset (Fin N)} {f : X → ℂ} {v : Finset (Fin N) → X → ℂ} {h : X → Matrix (Fin N) (Fin N) ℂ}
    (hv : ∀ I, A.HoloOn V (v I)) (hh : ∀ a b, A.HoloOn V fun y => h y a b)
    (hf : ∀ w ∈ V, f w = ∑ I, v I w * minorIJ (h w) I S) : A.HoloOn V f :=
  holoOn_congr' hV (holoOn_sum' _ fun I => holoOn_mul' (hv I) (holoOn_minor' hh I S)) hf

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X), IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ (x : RW.X) (ψ : OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : Fin Rb.A.n) (σ : Fin n ↪ Fin e) (i₀ : Fin e) (F : FrameData ι Ψ N M.Ω M.blk) (H : Ψ → (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ), x ∈ ψ.source → IsWChart M Rb τ a k₀ ca cb RW pr ψ kb σ i₀ F H → ∃ (V : Set RW.X) (z₀ z₁ : RW.X → (Σ k, ι k) → ℂ) (c : Option K → RW.X → ℂ), IsOpen V ∧ x ∈ V ∧ V ⊆ ψ.source ∧ V ⊆ RW.U x ∧ (∀ q, RW.A.HoloOn V fun w => z₀ w q) ∧ (∀ o, RW.A.HoloOn V (c o)) ∧ (∀ o, ∀ w ∈ V, c o w ≠ 0) ∧ ∀ w ∈ V, SameOrbit (z₀ w) (fstPt k₀ (RW.lift w w)) ∧ SameOrbit (z₁ w) (sndPt k₀ (RW.lift w w)) ∧ (∀ τ' i, M.ExactAt F (τ', i) (z₀ w) (H τ' (ψ w)) ∧ M.ExactAt F (τ', i) (z₁ w) (if τ' = τ then H τ (ψ w) * (1 + Matrix.single cb ca (ψ w i₀)) else H τ' (ψ w))) ∧ (∀ q : Σ k, ι k, q.1 ≠ k₀ → z₁ w q = z₀ w q) ∧ (∀ q : Σ k, ι k, RW.lift x w ⟨some q.1, q.2⟩ = c (some q.1) w * z₀ w q) ∧ ∀ m : ι k₀, RW.lift x w ⟨none, m⟩ = c none w * z₁ w ⟨k₀, m⟩ := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a b k₀ ca cb hb hab hk hca hcb RW pr hA x ψ kb σ i₀ F H hx hw
  obtain ⟨hcc, hfr, -, -, hHan, hpts⟩ := hw
  have hex : ∀ w, ∃ z₀ z₁ : (Σ k, ι k) → ℂ, w ∈ ψ.source →
      SameOrbit z₀ (fstPt k₀ (RW.lift w w)) ∧ SameOrbit z₁ (sndPt k₀ (RW.lift w w)) ∧
        ∀ τ' i, M.ExactAt F (τ', i) z₀ (H τ' (ψ w)) ∧
          M.ExactAt F (τ', i) z₁
            (if τ' = τ then H τ (ψ w) * (1 + Matrix.single cb ca (ψ w i₀)) else H τ' (ψ w)) := fun w => by
    by_cases hwS : w ∈ ψ.source
    · obtain ⟨-, -, z₀, z₁, h⟩ := hpts w hwS
      exact ⟨z₀, z₁, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hwS⟩
  choose z₀ z₁ hz using hex
  have hpb := fun w (hwS : w ∈ ψ.source) => GlobalTheory.T.twisted_atlas_compatibility K ι Φ y Ψ N j M n e Rb τ a k₀ ca cb RW pr hk hA w
    (z₀ w) (z₁ w) (hz w hwS).1 (hz w hwS).2.1
  have hn₀ : ∀ w ∈ ψ.source, ∀ k, basePart M.blk (z₀ w) ⟨k, F.c k⟩ = 1 := fun w hwS =>
    ((hz w hwS).2.2 τ a).1.1
  have hn₁ : ∀ w ∈ ψ.source, ∀ k, basePart M.blk (z₁ w) ⟨k, F.c k⟩ = 1 := fun w hwS =>
    ((hz w hwS).2.2 τ a).2.1
  have hbeq : ∀ w ∈ ψ.source, basePart M.blk (z₁ w) = basePart M.blk (z₀ w) := fun w hwS =>
    eq_of_orbit_normal (hpb w hwS).2.1 F.c (hn₁ w hwS) (hn₀ w hwS)
  obtain ⟨W, hWdef⟩ : ∃ W, W = ψ.source ∩ RW.U x := ⟨_, rfl⟩
  have hWo : IsOpen W := hWdef ▸ ψ.open_source.inter (RW.isOpen_U x)
  have hxW : x ∈ W := hWdef ▸ ⟨hx, RW.mem_U x⟩
  have hWS : W ⊆ ψ.source := hWdef ▸ Set.inter_subset_left
  have hWU : W ⊆ RW.U x := hWdef ▸ Set.inter_subset_right
  have hlift : ∀ w ∈ W, SameOrbit (RW.lift x w) (RW.lift w w) := fun w hwW =>
    RW.compat x w w ⟨hWU hwW, RW.mem_U w⟩
  have hb₀ := fun w (hwW : w ∈ W) => lift_fst (hz w (hWS hwW)).1 (hlift w hwW)
  have hb₁ := fun w (hwW : w ∈ W) => lift_snd (hz w (hWS hwW)).2.1 (hlift w hwW)
  have hbase : ∀ (k : NonPluckerBlocks M.blk) (m : ι k.1), RW.A.HoloOn W fun w => z₀ w ⟨k.1, m⟩ := fun k m => by
    refine StepW.ValHolo.holoOn_div_congr RW.A hWo (f := fun w => RW.lift x w ⟨some k.1, m⟩)
      (g := fun w => RW.lift x w ⟨some k.1, F.c k⟩) (holoOn_mono' (RW.holo x _) hWU)
      (holoOn_mono' (RW.holo x _) hWU) ?_ ?_
    · intro w hwW
      obtain ⟨d, hd, hq⟩ := hb₀ w hwW
      have h1 := hq ⟨k.1, F.c k⟩
      have h2 : z₀ w ⟨k.1, F.c k⟩ = 1 := hn₀ w (hWS hwW) k
      rw [h2, mul_one] at h1
      exact h1 ▸ hd k.1
    · intro w hwW
      obtain ⟨d, hd, hq⟩ := hb₀ w hwW
      have h1 := hq ⟨k.1, F.c k⟩
      have h2 : z₀ w ⟨k.1, F.c k⟩ = 1 := hn₀ w (hWS hwW) k
      rw [h2, mul_one] at h1
      have h3 := hq ⟨k.1, m⟩
      show z₀ w ⟨k.1, m⟩ = RW.lift x w ⟨some k.1, m⟩ / RW.lift x w ⟨some k.1, F.c k⟩
      rw [h3, h1, mul_div_cancel_left₀ _ (hd k.1)]
  have hbH : ∀ q, RW.A.HoloOn W fun w => basePart M.blk (z₀ w) q := fun q => hbase q.1 q.2
  have hid : mCoordIdeal (basePart M.blk (z₀ x)) = mCoordIdeal (basePart M.blk (fstPt k₀ (RW.lift x x))) := by
    obtain ⟨c, hc, hce⟩ := basePart_orbit' (blk := M.blk) (hz x hx).1
    rw [hce]
    exact StepW.TorusAct.mCoordIdeal_torus c hc _
  have hreg : ∀ q I, RegAt M.x (mCoordIdeal (basePart M.blk (z₀ x))) (F.u q I) := fun q I => by
    rw [hid]
    exact ((hpts x hx).2.1.2.1 q I).1
  have hval := fun q I => StepW.ValHolo.holoOn_valAt _ _ _ M.x (F.u q I) e RW.X RW.A W
    (fun w => basePart M.blk (z₀ w)) x hWo hxW hbH (fun w hwW => (hpb w (hWS hwW)).1) (hreg q I)
  choose Wv hWv₁ hWv₂ hWv₃ hWv₄ using hval
  obtain ⟨V₁, hV₁def⟩ : ∃ V₁, V₁ = W ∩ ⋂ q, ⋂ I, Wv q I := ⟨_, rfl⟩
  have hV₁o : IsOpen V₁ := hV₁def ▸ hWo.inter
    (isOpen_iInter_of_finite fun q => isOpen_iInter_of_finite fun I => hWv₁ q I)
  have hxV₁ : x ∈ V₁ := hV₁def ▸ ⟨hxW, Set.mem_iInter.2 fun q => Set.mem_iInter.2 fun I => hWv₂ q I⟩
  have hV₁W : V₁ ⊆ W := hV₁def ▸ Set.inter_subset_left
  have hV₁S : V₁ ⊆ ψ.source := hV₁W.trans hWS
  have hvV : ∀ q I, RW.A.HoloOn V₁ fun w => valAt M.x (F.u q I) (basePart M.blk (z₀ w)) := fun q I =>
    holoOn_mono' (hWv₄ q I) fun w hwV => by
      rw [hV₁def] at hwV
      exact Set.mem_iInter.1 (Set.mem_iInter.1 hwV.2 q) I
  have hHH : ∀ τ' r s, RW.A.HoloOn ψ.source fun w => H τ' (ψ w) r s := fun τ' r s =>
    holoOn_of_chart hcc (hHan τ' r s)
  have hti : RW.A.HoloOn ψ.source fun w => ψ w i₀ := holoOn_of_chart hcc (g := fun v => v i₀)
    fun v _ => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) i₀).analyticAt v
  have hzH : ∀ q, RW.A.HoloOn V₁ fun w => z₀ w q := fun q => by
    by_cases hq : ∀ p, M.blk p ≠ some q.1
    · exact holoOn_mono' (hbase ⟨q.1, hq⟩ q.2) hV₁W
    · push_neg at hq
      obtain ⟨⟨τ', i⟩, hp⟩ := hq
      exact holoOn_step hV₁o (v := fun I w => valAt M.x (F.u q I) (basePart M.blk (z₀ w)))
        (h := fun w => H τ' (ψ w)) (S := stepCols N j i) (fun I => hvV q I)
        (fun r s => holoOn_mono' (hHH τ' r s) hV₁S)
        fun w hwV => ((hz w (hV₁S hwV)).2.2 τ' i).1.2 q.1 hp q.2
  have hz₁H : ∀ m : ι k₀, RW.A.HoloOn V₁ fun w => z₁ w ⟨k₀, m⟩ := fun m => by
    refine holoOn_step hV₁o (v := fun I w => valAt M.x (F.u ⟨k₀, m⟩ I) (basePart M.blk (z₀ w)))
      (h := fun w => H τ (ψ w) * (1 + Matrix.single cb ca (ψ w i₀))) (S := stepCols N j a)
      (fun I => hvV _ I)
      (fun r s => holoOn_transv (fun r s => holoOn_mono' (hHH τ r s) hV₁S) (holoOn_mono' hti hV₁S) cb ca r s)
      fun w hwV => ?_
    have h1 := ((hz w (hV₁S hwV)).2.2 τ a).2.2 k₀ hk m
    rw [if_pos rfl, hbeq w (hV₁S hwV)] at h1
    exact h1
  choose mk hmk using (hpb x hx).2.2.1
  obtain ⟨m₁, hm₁⟩ := (hpb x hx).2.2.2 k₀
  obtain ⟨V, hVdef⟩ : ∃ V, V = (⋂ k, (V₁ ∩ {w | z₀ w ⟨k, mk k⟩ ≠ 0})) ∩ (V₁ ∩ {w | z₁ w ⟨k₀, m₁⟩ ≠ 0}) :=
    ⟨_, rfl⟩
  have hVo : IsOpen V := hVdef ▸ (isOpen_iInter_of_finite fun k =>
    StepW.ValHolo.isOpen_inter_ne RW.A hV₁o (hzH ⟨k, mk k⟩)).inter
      (StepW.ValHolo.isOpen_inter_ne RW.A hV₁o (hz₁H m₁))
  have hxV : x ∈ V := hVdef ▸ ⟨Set.mem_iInter.2 fun k => ⟨hxV₁, hmk k⟩, hxV₁, hm₁⟩
  have hVV₁ : V ⊆ V₁ := fun w hwV => by
    rw [hVdef] at hwV
    exact hwV.2.1
  have hV0 : ∀ w ∈ V, ∀ k, z₀ w ⟨k, mk k⟩ ≠ 0 := fun w hwV k => by
    rw [hVdef] at hwV
    exact (Set.mem_iInter.1 hwV.1 k).2
  have hV1 : ∀ w ∈ V, z₁ w ⟨k₀, m₁⟩ ≠ 0 := fun w hwV => by
    rw [hVdef] at hwV
    exact hwV.2.2
  have hVW : V ⊆ W := hVV₁.trans hV₁W
  have hVS : V ⊆ ψ.source := hVW.trans hWS
  obtain ⟨c, hcs, hcn⟩ : ∃ c : Option K → RW.X → ℂ,
      (∀ k w, c (some k) w = RW.lift x w ⟨some k, mk k⟩ / z₀ w ⟨k, mk k⟩) ∧
        ∀ w, c none w = RW.lift x w ⟨none, m₁⟩ / z₁ w ⟨k₀, m₁⟩ :=
    ⟨fun o w => o.elim (RW.lift x w ⟨none, m₁⟩ / z₁ w ⟨k₀, m₁⟩)
      fun k => RW.lift x w ⟨some k, mk k⟩ / z₀ w ⟨k, mk k⟩, fun _ _ => rfl, fun _ => rfl⟩
  have hcs' : ∀ w ∈ V, ∀ (d : K → ℂ), (∀ q : Σ k, ι k, RW.lift x w ⟨some q.1, q.2⟩ = d q.1 * z₀ w q) →
      ∀ k, c (some k) w = d k := fun w hwV d hq k => by
    rw [hcs]
    have h1 := hq ⟨k, mk k⟩
    exact h1 ▸ mul_div_cancel_right₀ _ (hV0 w hwV k)
  have hcn' : ∀ w ∈ V, ∀ d : ℂ, (∀ m : ι k₀, RW.lift x w ⟨none, m⟩ = d * z₁ w ⟨k₀, m⟩) → c none w = d :=
    fun w hwV d hq => by
      rw [hcn, hq m₁]
      exact mul_div_cancel_right₀ _ (hV1 w hwV)
  refine ⟨V, z₀, z₁, c, hVo, hxV, hVS, hVW.trans hWU, fun q => holoOn_mono' (hzH q) hVV₁, ?_, ?_, ?_⟩
  · rintro (_ | k)
    · exact StepW.ValHolo.holoOn_div_congr RW.A hVo (holoOn_mono' (RW.holo x _) (hVW.trans hWU))
        (holoOn_mono' (hz₁H m₁) hVV₁) hV1 fun w _ => hcn w
    · exact StepW.ValHolo.holoOn_div_congr RW.A hVo (holoOn_mono' (RW.holo x _) (hVW.trans hWU))
        (holoOn_mono' (hzH ⟨k, mk k⟩) hVV₁) (fun w hwV => hV0 w hwV k) fun w _ => hcs k w
  · rintro (_ | k) w hwV
    · obtain ⟨d, hd, hq⟩ := hb₁ w (hVW hwV)
      rw [hcn' w hwV d hq]
      exact hd
    · obtain ⟨d, hd, hq⟩ := hb₀ w (hVW hwV)
      rw [hcs' w hwV d hq k]
      exact hd k
  · intro w hwV
    have hwS := hVS hwV
    refine ⟨(hz w hwS).1, (hz w hwS).2.1, (hz w hwS).2.2, fun q hq₀ => ?_, fun q => ?_, fun m => ?_⟩
    · by_cases hq : ∀ p, M.blk p ≠ some q.1
      · exact congrFun (hbeq w hwS) ⟨⟨q.1, hq⟩, q.2⟩
      · push_neg at hq
        obtain ⟨⟨τ', i⟩, hp⟩ := hq
        have e₀ := ((hz w hwS).2.2 τ' i).1.2 q.1 hp q.2
        have e₁ := ((hz w hwS).2.2 τ' i).2.2 q.1 hp q.2
        refine e₁.trans (Eq.trans ?_ e₀.symm)
        rw [hbeq w hwS]
        refine Finset.sum_congr rfl fun I _ => ?_
        congr 1
        by_cases ht : τ' = τ
        · subst ht
          rw [if_pos rfl]
          have hia : i ≠ a := fun hia => hq₀ (by
            subst hia
            exact Option.some_injective _ (hp.symm.trans hk))
          exact GlobalTheory.T.elementary_twist_minor_other_steps N j a b ca cb M.j_le hb hab hca hcb _ _ i hia I
        · rw [if_neg ht]
    · obtain ⟨d, hd, hq'⟩ := hb₀ w (hVW hwV)
      rw [hcs' w hwV d hq' q.1]
      exact hq' q
    · obtain ⟨d, hd, hq'⟩ := hb₁ w (hVW hwV)
      rw [hcn' w hwV d hq']
      exact hq' m

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.LForm
