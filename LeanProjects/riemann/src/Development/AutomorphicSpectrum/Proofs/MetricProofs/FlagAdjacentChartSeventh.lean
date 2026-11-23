import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsValueAtOfTorus
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Orb

section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem blockMap_fst (k₀ : K) : IsBlockMap (ι := ι) (ι' := fun o : Option K => ι (o.getD k₀)) some (v₀ k₀) := by
  refine ⟨Option.some_injective _, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨k, i⟩ ⟨k', i'⟩ h
    simp only [v₀, Sigma.mk.injEq, Option.some.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [Option.getD_some, heq_eq_eq] at h
    subst h
    rfl
  · rintro ⟨o, i⟩ ⟨k, hk⟩
    obtain rfl : o = some k := hk.symm
    exact ⟨⟨k, i⟩, rfl⟩

theorem baseOf_mem (M : FlagModel y Ψ N j) {τ : Ψ} {a : Fin N} {k₀ : K} {ca cb : Fin N}
    {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (hz : z ∈ mcPts (wP M τ a k₀ ca cb)) :
    baseOf M k₀ z ∈ mcPts (mCoordIdeal M.x) :=
  CPts.base_mem M (CPts.comp_mem_mcPts (blockMap_fst k₀) (algebraMap Φ (RatFunc Φ)) (funext fun _ => rfl) hz)

theorem twMinor_scale (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {zb zb' : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hv : ∀ s, valAt M.x s zb' = valAt M.x s zb) (i : Fin N) (k : K) (g : Matrix (Fin N) (Fin N) ℂ)
    {u u' : (Σ k, ι k) → ℂ} {t : ℂ} (hu : ∀ m : ι k, u' ⟨k, m⟩ = t * u ⟨k, m⟩) (J : Finset (Fin N)) :
    twMinor M F zb' i k g u' J = t * twMinor M F zb i k g u J := by
  have hp : ∀ I, pluck M F zb' k u' I = t * pluck M F zb k u I := fun I => by
    unfold pluck
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hv, hu]
    ring
  unfold twMinor
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [hp]
  ring

theorem lr_key (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {zb zb' : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hv : ∀ s, valAt M.x s zb' = valAt M.x s zb) (g : Matrix (Fin N) (Fin N) ℂ) (i : Fin N) (k : K)
    {u u' : (Σ k, ι k) → ℂ} {t : ℂ} (ht : t ≠ 0) (hu : ∀ m : ι k, u' ⟨k, m⟩ = t * u ⟨k, m⟩) (J J' : Finset (Fin N)) :
    twMinor M F zb' i k g u' J / twMinor M F zb' i k g u' J' = twMinor M F zb i k g u J / twMinor M F zb i k g u J' := by
  rw [twMinor_scale M F hv i k g hu J, twMinor_scale M F hv i k g hu J']
  exact mul_div_mul_left _ _ ht

theorem lowRead_scale (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {zb zb' : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hv : ∀ s, valAt M.x s zb' = valAt M.x s zb) (h : Ψ → Matrix (Fin N) (Fin N) ℂ)
    {u u' : (Σ k, ι k) → ℂ} {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (hu : ∀ k (m : ι k), u' ⟨k, m⟩ = c k * u ⟨k, m⟩)
    (τ' : Ψ) (a' b' : Fin N) : lowRead M F zb' h u' τ' a' b' = lowRead M F zb h u τ' a' b' := by
  unfold lowRead
  exact congrArg (Option.elim (M.blk (τ', stepOf N j b')) 0) (funext fun k => lr_key M F hv _ _ k (hc k) (hu k) _ _)

end

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ z ∈ wO M Rb τ a k₀ ca cb F kb V r h, ∀ z' ∈ mcPts (wP M τ a k₀ ca cb), SameOrbit z' z → z' ∈ wO M Rb τ a k₀ ca cb F kb V r h ∧ wRho M Rb τ k₀ ca cb F kb r h ε z' = wRho M Rb τ k₀ ca cb F kb r h ε z := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε ctx z hz z' hz' ho
  obtain ⟨-, -, -, -, -, -, -, -, hr, -, -⟩ := ctx
  obtain ⟨hzP, hs, hV, hm₁, hm₂⟩ := hz
  obtain ⟨c, hc, rfl⟩ := ho
  set z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ := fun p => c p.1 * z p with hz'def
  have hb := baseOf_mem M hzP
  have hb' := baseOf_mem M hz'
  have eb : baseOf M k₀ z' = fun q => c (some q.1.1) * baseOf M k₀ z q := rfl
  have hob : SameOrbit (baseOf M k₀ z') (baseOf M k₀ z) := ⟨fun k => c (some k.1), fun k => hc _, eb⟩
  have hnot : ∀ x : Rb.X, Rb.lift x x ∉ mcPts (⊤ : Ideal (MRing (baseIdx ι M.blk))) := fun x hx => by
    have := hx.2 1 Submodule.mem_top
    simp at this
  have hrr : r (baseOf M k₀ z') = r (baseOf M k₀ z) :=
    Rb.inj _ _ (hnot _) (orbit_trans (hr _ hb') (orbit_trans hob (orbit_symm (hr _ hb))))
  have hv : ∀ s, valAt M.x s (baseOf M k₀ z') = valAt M.x s (baseOf M k₀ z) := fun s => by
    have := StepW.TorusAct.valAt_torus (x := M.x) (fun k => c (some k.1)) (fun k => hc _) hb (eb ▸ hb') s
    rw [eb]
    exact this
  have h₁ : ∀ k (m : ι k), fstPt k₀ z' ⟨k, m⟩ = c (some k) * fstPt k₀ z ⟨k, m⟩ := fun _ _ => rfl
  let c₂ : K → ℂ := fun k => if k = k₀ then c none else c (some k)
  have hc₂ : ∀ k, c₂ k ≠ 0 := fun k => by
    simp only [c₂]
    split_ifs
    exacts [hc _, hc _]
  have h₂ : ∀ k (m : ι k), sndPt k₀ z' ⟨k, m⟩ = c₂ k * sndPt k₀ z ⟨k, m⟩ := fun k m => by
    by_cases hk : k = k₀
    · subst hk
      simp only [sndPt, Function.comp, v₁_self, c₂, if_true, hz'def]
    · simp only [sndPt, Function.comp, v₁_ne (p := ⟨k, m⟩) hk, c₂, if_neg hk, hz'def]
  refine ⟨?_, ?_⟩
  · show z' ∈ mcPts _ ∧ _
    refine ⟨hz', ?_, ?_, fun p k hp => ?_, ?_⟩
    · rw [hrr]; exact hs
    · rw [hrr]; exact hV
    · rw [twMinor_scale M F hv _ k _ (h₁ k)]
      exact mul_ne_zero (hc _) (hm₁ p k hp)
    · rw [twMinor_scale M F hv _ k₀ _ (h₂ k₀)]
      exact mul_ne_zero (hc₂ _) hm₂
  · funext i
    unfold wRho
    rcases ε.symm i with l | q | u
    · show Rb.A.chart kb (r (baseOf M k₀ z')) l = Rb.A.chart kb (r (baseOf M k₀ z)) l
      rw [hrr]
    · exact lowRead_scale M F hv h (fun k => hc (some k)) h₁ _ _ _
    · show lowRead M F _ h (sndPt k₀ z') τ cb ca - lowRead M F _ h (fstPt k₀ z') τ cb ca = _ - _
      rw [lowRead_scale M F hv h hc₂ h₂, lowRead_scale M F hv h (fun k => hc (some k)) h₁]

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Orb
