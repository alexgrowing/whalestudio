import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogPeriodStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFifth
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFirst
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesAtPointStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticEighthStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticSecondStatement
import Development.WeilBound.CoreStatements.PluriharmonicCharts.PullDegSome
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.CovMap PositivityTheory.Xgp.c_algsq

noncomputable section
namespace PositivityTheory.Xgp.c_sqsys

section Join

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def joinPt {R : Type} (k₀ : K) (z₀ z₁ : (Σ k, ι k) → R) : (Σ o : Option K, ι (o.getD k₀)) → R
  | ⟨some k, m⟩ => z₀ ⟨k, m⟩
  | ⟨none, m⟩ => z₁ ⟨k₀, m⟩

theorem join_v₀ {R : Type} (k₀ : K) (z₀ z₁ : (Σ k, ι k) → R) : joinPt k₀ z₀ z₁ ∘ v₀ k₀ = z₀ := rfl

theorem join_v₁ {R : Type} {k₀ : K} {z₀ z₁ : (Σ k, ι k) → R} (h : ∀ k, k ≠ k₀ → ∀ m, z₀ ⟨k, m⟩ = z₁ ⟨k, m⟩) :
    joinPt k₀ z₀ z₁ ∘ v₁ k₀ = z₁ := by
  funext ⟨k, m⟩
  by_cases e : k = k₀
  · subst e
    show joinPt k z₀ z₁ (v₁ k ⟨k, m⟩) = _
    rw [v₁_self]; rfl
  · show joinPt k₀ z₀ z₁ (v₁ k₀ ⟨k, m⟩) = _
    rw [v₁_ne (p := ⟨k, m⟩) e]
    exact h k e m

theorem orbit_of_blocks {z z' : (Σ k, ι k) → ℂ} (h : ∀ k, ∃ c : ℂ, c ≠ 0 ∧ ∀ m, z ⟨k, m⟩ = c * z' ⟨k, m⟩) :
    SameOrbit z z' := by
  choose c hc e using h
  exact ⟨c, hc, funext fun q => e q.1 q.2⟩

theorem blocks_of_orbit {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (k : K) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ m, z ⟨k, m⟩ = c * z' ⟨k, m⟩ := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨c k, hc k, fun _ => rfl⟩

theorem fst_orbit {k₀ : K} {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (fstPt k₀ z) (fstPt k₀ z') := FibreCount.comp_orbit (Pts.isBlockMap_v₀ k₀) h

theorem snd_orbit {k₀ : K} {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (sndPt k₀ z) (sndPt k₀ z') := FibreCount.comp_orbit (isBlockMap_v₁ k₀) h

theorem sameOrbit_of_sameOrbit_fstPt_sndPt {k₀ : K} {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h₀ : SameOrbit (fstPt k₀ z) (fstPt k₀ z'))
    (h₁ : SameOrbit (sndPt k₀ z) (sndPt k₀ z')) : SameOrbit z z' := by
  refine orbit_of_blocks fun o => ?_
  cases o with
  | none =>
    obtain ⟨c, hc, e⟩ := blocks_of_orbit h₁ k₀
    exact ⟨c, hc, fun m => by simpa only [Pts.snd_self] using e m⟩
  | some k => exact blocks_of_orbit h₀ k

theorem join_orbit {k₀ : K} {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ} {z₀ z₁ : (Σ k, ι k) → ℂ}
    (h₀ : SameOrbit z₀ (fstPt k₀ z)) (h₁ : SameOrbit z₁ (sndPt k₀ z)) : SameOrbit (joinPt k₀ z₀ z₁) z := by
  refine orbit_of_blocks fun o => ?_
  cases o with
  | none =>
    obtain ⟨c, hc, e⟩ := blocks_of_orbit h₁ k₀
    exact ⟨c, hc, fun m => (e m).trans (by rw [Pts.snd_self])⟩
  | some k => exact blocks_of_orbit h₀ k

theorem analytic_join {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (k₀ : K) {f₀ f₁ : E → (Σ k, ι k) → ℂ}
    {x : E} (h₀ : AnalyticAt ℂ f₀ x) (h₁ : AnalyticAt ℂ f₁ x) :
    AnalyticAt ℂ (fun u => joinPt k₀ (f₀ u) (f₁ u)) x := by
  refine analyticAt_pi_iff.2 ?_
  rintro ⟨_ | k, m⟩
  · exact analyticAt_pi_iff.1 h₁ ⟨k₀, m⟩
  · exact analyticAt_pi_iff.1 h₀ ⟨k, m⟩

theorem analytic_comp_idx {α β : Type} [Fintype α] [Fintype β] (v : α → β) (x : β → ℂ) :
    AnalyticAt ℂ (fun z : β → ℂ => z ∘ v) x :=
  analyticAt_pi_iff.2 fun a => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : β => ℂ) (v a)).analyticAt x

theorem continuous_comp_idx {α β : Type} (v : α → β) : Continuous (fun z : β → ℂ => z ∘ v) :=
  continuous_pi fun a => continuous_apply (v a)

end Join

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

def WA : Prop := ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (d : ℕ) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → IsArithVar (mCoordIdeal y) (d + 2) → IsArithVar (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) (d + 3) ∧ IsArithVar (mCoordIdeal (M.wCo (τ, a) k₀ ca cb 0)) (d + 2) ∧ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X) ≤ mCoordIdeal (M.wCo (τ, a) k₀ ca cb 0) ∧ imageZ (fun p : (Σ k, ι k) => (⟨some p.1, p.2⟩ : Σ o : Option K, ι (o.getD k₀))) (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) = mCoordIdeal y ∧ ∀ v₁ : (Σ k, ι k) → (Σ o : Option K, ι (o.getD k₀)), (∀ p : (Σ k, ι k), p.1 ≠ k₀ → v₁ p = ⟨some p.1, p.2⟩) → (∀ m : ι k₀, v₁ ⟨k₀, m⟩ = ⟨none, m⟩) → imageZ v₁ (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) = mCoordIdeal y

structure Sw (M : FlagModel y Ψ N j) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) : Prop where
  hb : (b : ℕ) = a + 1
  hab : (b : ℕ) < j ∨ j ≤ (a : ℕ)
  hk : M.blk (τ, a) = some k₀
  hca : (ca : ℕ) = lastCol N j a
  hcb : (cb : ℕ) = ca + 1
  wa : WA

section W

variable {M : FlagModel y Ψ N j} {τ : Ψ} {a b : Fin N} {k₀ : K} {ca cb : Fin N} {d : ℕ}

theorem Sw.arith (S : Sw M τ a b k₀ ca cb) (hy : IsArithVar (mCoordIdeal y) (d + 2)) :
    IsArithVar (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) (d + 2 + 1) :=
  (S.wa K ι Φ y Ψ N j M d τ a b k₀ ca cb S.hb S.hab S.hk S.hca S.hcb hy).1

theorem Sw.im₀ (S : Sw M τ a b k₀ ca cb) (hy : IsArithVar (mCoordIdeal y) (d + 2)) :
    imageZ (v₀ k₀) (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) = mCoordIdeal y :=
  (S.wa K ι Φ y Ψ N j M d τ a b k₀ ca cb S.hb S.hab S.hk S.hca S.hcb hy).2.2.2.1

theorem fst_mem {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X))) : fstPt k₀ z ∈ mcPts (mCoordIdeal y) :=
  CPts.comp_mem_mcPts (Pts.isBlockMap_v₀ k₀) (algebraMap Φ (RatFunc Φ)) (funext fun _ => rfl) hz

theorem Sw.snd_mem (S : Sw M τ a b k₀ ca cb) (hy : IsArithVar (mCoordIdeal y) (d + 2))
    {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X))) : sndPt k₀ z ∈ mcPts (mCoordIdeal y) :=
  Pts.snd_mem ((S.wa K ι Φ y Ψ N j M d τ a b k₀ ca cb S.hb S.hab S.hk S.hca S.hcb hy).2.2.2.2 (v₁ k₀)
    (fun _ h => v₁_ne h) (v₁_self k₀)) hz

theorem Sw.data (S : Sw M τ a b k₀ ca cb) {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ}
    (h₀ : fstPt k₀ z ∈ mcPts (mCoordIdeal y)) (h₁ : sndPt k₀ z ∈ mcPts (mCoordIdeal y))
    {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) (hG : M.GoodAt F (mCoordIdeal (basePart M.blk (fstPt k₀ z)))) :
    ∃ z', SameOrbit z' z ∧ ∃ (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (t : ℂ), M.IsFlagOf F (fstPt k₀ z') h ∧
      M.IsFlagOf F (sndPt k₀ z') (Function.update h τ (h τ * (1 + Matrix.single cb ca t))) := by
  obtain ⟨z₁, ⟨c, hc, e⟩, hn⟩ := FibreCount.exists_normal_base M.blk F.c (fstPt k₀ z) fun k =>
    FibreCount.chart_ne (hG.1 k)
  let z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ := fun q => q.1.elim 1 c * z q
  have ho : SameOrbit z' z := ⟨fun o => o.elim 1 c, fun o => by cases o <;> simp [hc], rfl⟩
  have e' : fstPt k₀ z' = z₁ := by rw [e]; rfl
  have hI := CoordinateConeArithVar.isMultiHomogIdeal y
  have m₀ := mem_mcPts_of_sameOrbit hI (fst_orbit ho) h₀
  have m₁ := mem_mcPts_of_sameOrbit hI (snd_orbit ho) h₁
  have hG' : M.GoodAt F (mCoordIdeal (basePart M.blk (fstPt k₀ z'))) := by
    rw [FibreCount.mCoordIdeal_eq_of_orbit (FibreCount.basePart_orbit M.blk (fst_orbit ho))]; exact hG
  have hsnd := Pts.basePart_snd M S.hk z'
  have hc' : ∀ k, basePart M.blk (fstPt k₀ z') ⟨k, F.c k⟩ = 1 := by rw [e']; exact hn
  obtain ⟨h, H⟩ := CPts.flag_fwd M hF m₀ hG' hc'
  obtain ⟨h', H'⟩ := CPts.flag_fwd M hF m₁ (hsnd ▸ hG') (hsnd ▸ hc')
  exact ⟨z', ho, Pts.fwd_flags M S.hb S.hab S.hk S.hca S.hcb hF (CPts.base_mem M m₀) hG' H H'⟩

theorem Sw.mem (S : Sw M τ a b k₀ ca cb) {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ}
    (h₀ : fstPt k₀ z ∈ mcPts (mCoordIdeal y)) (h₁ : sndPt k₀ z ∈ mcPts (mCoordIdeal y)) :
    z ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) := by
  obtain ⟨F, hF, hG⟩ := (GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M).2.1 _ (CPts.base_mem M h₀)
  obtain ⟨z', ho, h, t, H, H'⟩ := S.data h₀ h₁ hF hG
  have m₀ := mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal y) (fst_orbit ho) h₀
  have hG' : M.GoodAt F (mCoordIdeal (basePart M.blk (fstPt k₀ z'))) := by
    rw [FibreCount.mCoordIdeal_eq_of_orbit (FibreCount.basePart_orbit M.blk (fst_orbit ho))]; exact hG
  exact mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal _) (orbit_symm ho)
    (Pts.back M S.hb S.hab S.hk S.hca S.hcb hF (CPts.base_mem M m₀) hG' H H')

theorem ideal_W_le {Φ₂ : Type} [Field Φ₂] {y₂ : (Σ k, ι k) → Φ₂} {M₂ : FlagModel y₂ Ψ N j}
    (S : Sw M τ a b k₀ ca cb) (S₂ : Sw M₂ τ a b k₀ ca cb) (hy : IsArithVar (mCoordIdeal y) (d + 2))
    (e : mCoordIdeal y₂ = mCoordIdeal y) :
    mCoordIdeal (M₂.wCo (τ, a) k₀ ca cb RatFunc.X) ≤ mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X) := by
  by_contra hn
  obtain ⟨z, hz, hz'⟩ := HilbertSamuel.exists_mcPts_not_mem_mcPts (S.arith hy) hn
  exact hz' (S₂.mem (e ▸ fst_mem hz) (e ▸ S.snd_mem hy hz))

theorem ideal_W_eq {Φ₂ : Type} [Field Φ₂] {y₂ : (Σ k, ι k) → Φ₂} {M₂ : FlagModel y₂ Ψ N j}
    (S : Sw M τ a b k₀ ca cb) (S₂ : Sw M₂ τ a b k₀ ca cb) (hy : IsArithVar (mCoordIdeal y) (d + 2))
    (e : mCoordIdeal y₂ = mCoordIdeal y) :
    mCoordIdeal (M₂.wCo (τ, a) k₀ ca cb RatFunc.X) = mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X) :=
  le_antisymm (ideal_W_le S S₂ hy e) (ideal_W_le S₂ S (e ▸ hy) e.symm)

end W

variable {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ'] {y' : (Σ k, ι' k) → Φ'}

section Cov

variable {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j}

open FibreCount in

theorem img_blk (Cv : FlagCover M' M) {d : ℕ}
    (hy : IsArithVar (mCoordIdeal y) (d + 2)) (hy' : IsArithVar (mCoordIdeal y') (d + 2))
    {w₁ w₂ : (Σ k, ι k) → ℂ} (hw : w₁ ∈ mcPts (mCoordIdeal y)) {z₁ z₂ : (Σ k, ι' k) → ℂ}
    (h₁ : z₁ ∈ mcPts (mCoordIdeal y')) (h₂ : z₂ ∈ mcPts (mCoordIdeal y'))
    (i₁ : IsImg Cv z₁ w₁) (i₂ : IsImg Cv z₂ w₂)
    (hb : SameOrbit (basePart M'.blk z₁) (basePart M'.blk z₂)) {p : Ψ × Fin N} {k : K} {k' : K'}
    (hk : M.blk p = some k) (hp' : M'.blk p = some k') (hww : ∀ m, w₁ ⟨k, m⟩ = w₂ ⟨k, m⟩) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ m, z₁ ⟨k', m⟩ = c * z₂ ⟨k', m⟩ := by
  have P := GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M
  have P' := GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M'
  obtain ⟨F', hF', hg'⟩ := P'.2.1 _ (P'.1 z₁ h₁)
  obtain ⟨a₁, o₁, n₁⟩ := exists_normal_base M'.blk F'.c z₁ fun k => chart_ne (hg'.1 k)
  obtain ⟨a₂, o₂, n₂⟩ := exists_normal_base M'.blk F'.c z₂ fun k =>
    chart_ne (by rw [← mCoordIdeal_eq_of_orbit hb]; exact hg'.1 k)
  have ob₁ := basePart_orbit M'.blk o₁
  have ob₂ := basePart_orbit M'.blk o₂
  have eb : basePart M'.blk a₁ = basePart M'.blk a₂ := eq_of_orbit_normal (c := F'.c)
    (Cj.sameOrbit_trans ob₁ (Cj.sameOrbit_trans hb (Cj.sameOrbit_symm ob₂))) n₁ n₂
  have hbm : basePart M'.blk a₁ ∈ mcPts (mCoordIdeal M'.x) :=
    mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal _) ob₁ (P'.1 z₁ h₁)
  have hgb : M'.GoodAt F' (mCoordIdeal (basePart M'.blk a₁)) := by rw [mCoordIdeal_eq_of_orbit ob₁]; exact hg'
  have ha₁ := mem_mcPts_of_sameOrbit hy'.2.1.2.1 o₁ h₁
  have ha₂ := mem_mcPts_of_sameOrbit hy'.2.1.2.1 o₂ h₂
  have hbw : SameOrbit (basePart M'.blk a₁ ∘ Cv.v) (basePart M.blk w₁) := Cj.sameOrbit_trans
    (comp_orbit Cv.block ob₁) (Cj.sameOrbit_symm (GlobalTheory.T.flag_cover_arithmetic_third K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy' z₁ h₁ w₁ i₁))
  have hbv := mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal _) hbw (P.1 w₁ hw)
  obtain ⟨F, hF, hg⟩ := P.2.1 _ hbv
  obtain ⟨g₁, fl₁⟩ := (P'.2.2 F' hF' a₁ hbm hgb n₁).1 ha₁
  obtain ⟨g₂, fl₂⟩ := (P'.2.2 F' hF' a₂ (by rw [← eb]; exact hbm) (by rw [← eb]; exact hgb) n₂).1 ha₂
  obtain ⟨z₀, s₁, t₁, f₁⟩ := i₁ a₁ o₁ F' F hF' hF hgb hg g₁ fl₁
  obtain ⟨z₀', s₂, t₂, f₂⟩ := i₂ a₂ o₂ F' F hF' hF (by rw [← eb]; exact hgb) (by rw [← eb]; exact hg) g₂ fl₂
  rw [← eb] at t₂ f₂
  have eβ : basePart M.blk z₀ = basePart M.blk z₀' :=
    eq_of_orbit_normal (c := F.c) (Cj.sameOrbit_trans t₁ (Cj.sameOrbit_symm t₂)) f₁.1 f₂.1
  have hβ : basePart M.blk z₀ ∈ mcPts (mCoordIdeal M.x) :=
    mem_mcPts_of_sameOrbit (CoordinateConeArithVar.isMultiHomogIdeal _) t₁ hbv
  have hgβ : M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) := by rw [mCoordIdeal_eq_of_orbit t₁]; exact hg
  obtain ⟨c₁, hc₁, ez₁⟩ := blocks_of_orbit s₁ k
  obtain ⟨c₂, hc₂, ez₂⟩ := blocks_of_orbit s₂ k
  obtain ⟨c, hc, ez⟩ : ∃ c : ℂ, c ≠ 0 ∧ ∀ m, z₀ ⟨k, m⟩ = c * z₀' ⟨k, m⟩ :=
    ⟨c₁ / c₂, div_ne_zero hc₁ hc₂, fun m => by rw [ez₁, ez₂, hww]; field_simp⟩
  have hT := trans_unit Cv hbm hF' hF hgb hg
  have hpr : IsProperStep N j p.2 := by
    by_contra hn
    rw [(M'.blk_none p).2 hn] at hp'
    exact absurd hp' (by simp)
  obtain ⟨e₁, he₁, v₁⟩ := f₁.2.2 p k hk
  obtain ⟨e₂, he₂, v₂⟩ := f₂.2.2 p k hk
  have key := step_prop (M' := M') (c := c) (e₁ := e₁) (e₂ := e₂) hF hβ hgβ hk hpr (hT p.1) (fl₁.2.1 p.1).1
    (fl₂.2.1 p.1).1 he₁ (fun m => by
      have x3 := ez m
      have x1 := v₁ m
      have x2 := v₂ m
      rw [← eβ] at x2
      rw [x1, x2] at x3
      exact x3)
  obtain ⟨a, ha, w₁⟩ := fl₁.2.2 p k' hp'
  obtain ⟨a', ha', w₂⟩ := fl₂.2.2 p k' hp'
  obtain ⟨b₁, hb₁, eb₁⟩ := blocks_of_orbit o₁ k'
  obtain ⟨b₂, hb₂, eb₂⟩ := blocks_of_orbit o₂ k'
  refine ⟨a * (c * e₂ / e₁) / a' * b₂ / b₁, div_ne_zero (mul_ne_zero
    (div_ne_zero (mul_ne_zero ha (div_ne_zero (mul_ne_zero hc he₂) he₁)) ha') hb₂) hb₁, fun m => ?_⟩
  have g0 : a₁ ⟨k', m⟩ = a * (c * e₂ / e₁) / a' * a₂ ⟨k', m⟩ := by
    rw [w₁ m, w₂ m, ← eb]
    simp only [key]
    have g1 : ∑ I, valAt M'.x (F'.u ⟨k', m⟩ I) (basePart M'.blk a₁) *
        ((c * e₂ / e₁) * minorIJ (g₂ p.1) I (stepCols N j p.2)) =
        (c * e₂ / e₁) * ∑ I, valAt M'.x (F'.u ⟨k', m⟩ I) (basePart M'.blk a₁) * minorIJ (g₂ p.1) I (stepCols N j p.2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [g1]
    field_simp
  rw [eb₁, eb₂] at g0
  rw [div_mul_eq_mul_div, eq_div_iff hb₁]
  linear_combination g0

theorem blk_cover (M : FlagModel y Ψ N j) (M' : FlagModel y' Ψ N j) {p : Ψ × Fin N} {k' : K'}
    (hp : M'.blk p = some k') : ∃ k, M.blk p = some k :=
  Option.ne_none_iff_exists'.1 fun e => by
    rw [(M'.blk_none p).2 ((M.blk_none p).1 e)] at hp
    cases hp

variable {τ : Ψ} {a b : Fin N} {k₀ : K} {k₀' : K'} {ca cb : Fin N} {d : ℕ}

def RelW (Cv : FlagCover M' M) (k₀ : K) (k₀' : K') (z : (Σ o : Option K', ι' (o.getD k₀')) → ℂ)
    (w : (Σ o : Option K, ι (o.getD k₀)) → ℂ) : Prop :=
  IsImg Cv (fstPt k₀' z) (fstPt k₀ w) ∧ IsImg Cv (sndPt k₀' z) (sndPt k₀ w)

theorem RelW.orbit {Cv : FlagCover M' M} {z z₁ : (Σ o : Option K', ι' (o.getD k₀')) → ℂ}
    {w w₁ : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : RelW Cv k₀ k₀' z w) (hz : SameOrbit z₁ z)
    (hw : SameOrbit w₁ w) : RelW Cv k₀ k₀' z₁ w₁ :=
  ⟨h.1.orbit (fst_orbit hz) (fst_orbit hw), h.2.orbit (snd_orbit hz) (snd_orbit hw)⟩

theorem exists_relW_lift_of_isImg (Cv : FlagCover M' M) (S : Sw M τ a b k₀ ca cb) (S' : Sw M' τ a b k₀' ca cb)
    (hy : IsArithVar (mCoordIdeal y) (d + 2)) (hy' : IsArithVar (mCoordIdeal y') (d + 2))
    {w : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (hw : w ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)))
    {z₀ : (Σ k, ι' k) → ℂ} (hz₀ : z₀ ∈ mcPts (mCoordIdeal y')) (hi : IsImg Cv z₀ (fstPt k₀ w)) :
    ∃ z ∈ mcPts (mCoordIdeal (M'.wCo (τ, a) k₀' ca cb RatFunc.X)), fstPt k₀' z = z₀ ∧ RelW Cv k₀ k₀' z w := by
  have hb := GlobalTheory.T.flag_cover_arithmetic_third K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv d hy hy' z₀ hz₀ _ hi
  obtain ⟨z₁, hz₁, ho, hi₁⟩ := FibreCount.img_surj Cv hy hy' (S.snd_mem hy hw) (CPts.base_mem M' hz₀)
    (by rw [Pts.basePart_snd M S.hk]; exact orbit_symm hb)
  have hs : SameOrbit (sndPt k₀' (joinPt k₀' z₀ z₁)) z₁ := by
    refine orbit_of_blocks fun k' => ?_
    by_cases e : k' = k₀'
    · subst e
      exact ⟨1, one_ne_zero, fun m => by rw [Pts.snd_self, one_mul]; rfl⟩
    · simp only [Pts.snd_fst_ne e]
      by_cases hk : ∀ p, M'.blk p ≠ some k'
      · exact blocks_of_orbit (orbit_symm ho) ⟨k', hk⟩
      · push_neg at hk
        obtain ⟨p, hp⟩ := hk
        obtain ⟨k, hk⟩ := blk_cover M M' hp
        have hne : k ≠ k₀ := fun e' => e (by
          have := M.blk_inj _ _ _ hk (e' ▸ S.hk)
          rw [this, S'.hk] at hp
          exact (Option.some.inj hp).symm)
        exact img_blk Cv hy hy' (fst_mem hw) hz₀ hz₁ hi hi₁ (orbit_symm ho) hk hp
          fun m => (Pts.snd_fst_ne hne w m).symm
  exact ⟨joinPt k₀' z₀ z₁, S'.mem hz₀ (mem_mcPts_of_sameOrbit hy'.2.1.2.1 hs hz₁), rfl, hi,
    hi₁.orbit hs (Cj.sameOrbit_refl _)⟩

theorem ncard_orbits_relW_eq_ncard_orbits_isImg (Cv : FlagCover M' M) (S : Sw M τ a b k₀ ca cb) (S' : Sw M' τ a b k₀' ca cb)
    (hy : IsArithVar (mCoordIdeal y) (d + 2)) (hy' : IsArithVar (mCoordIdeal y') (d + 2))
    {w : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (hw : w ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X))) :
    {O | ∃ z ∈ mcPts (mCoordIdeal (M'.wCo (τ, a) k₀' ca cb RatFunc.X)),
        O = {z'' | SameOrbit z'' z} ∧ RelW Cv k₀ k₀' z w}.ncard =
      {O | ∃ z ∈ mcPts (mCoordIdeal y'), O = {z'' | SameOrbit z'' z} ∧ IsImg Cv z (fstPt k₀ w)}.ncard := by
  have key : ∀ z : (Σ o : Option K', ι' (o.getD k₀')) → ℂ,
      {u | ∃ z₂ ∈ {z'' | SameOrbit z'' z}, SameOrbit u (fstPt k₀' z₂)} = {u | SameOrbit u (fstPt k₀' z)} := fun z => by
    ext u
    exact ⟨fun ⟨z₂, h1, h2⟩ => orbit_trans h2 (fst_orbit h1), fun h => ⟨z, Cj.sameOrbit_refl z, h⟩⟩
  refine Set.ncard_congr (fun O _ => {u | ∃ z₂ ∈ O, SameOrbit u (fstPt k₀' z₂)}) ?_ ?_ ?_
  · rintro O ⟨z, hz, rfl, hr⟩
    exact ⟨fstPt k₀' z, fst_mem hz, key z, hr.1⟩
  · rintro O O' ⟨z, hz, rfl, hr⟩ ⟨z', hz', rfl, hr'⟩ e
    simp only [key] at e
    have h0 := FibreCount.orbit_eq_iff.1 e
    refine FibreCount.orbit_eq_iff.2 (sameOrbit_of_sameOrbit_fstPt_sndPt h0 ?_)
    refine FibreCount.img_inj Cv hy hy' (S.snd_mem hy hw) (S'.snd_mem hy' hz) (S'.snd_mem hy' hz') hr.2 hr'.2 ?_
    rw [Pts.basePart_snd M' S'.hk, Pts.basePart_snd M' S'.hk]
    exact FibreCount.basePart_orbit _ h0
  · rintro O ⟨z₀, hz₀, rfl, hi⟩
    obtain ⟨z, hz, rfl, hr⟩ := exists_relW_lift_of_isImg Cv S S' hy hy' hw hz₀ hi
    exact ⟨_, ⟨z, hz, rfl, hr⟩, key z⟩

theorem local_analytic_section_coords (Cv : FlagCover M' M) (S : Sw M τ a b k₀ ca cb) (S' : Sw M' τ a b k₀' ca cb)
    (hy' : IsArithVar (mCoordIdeal y') (d + 2))
    {z : (Σ o : Option K', ι' (o.getD k₀')) → ℂ} (hz : z ∈ mcPts (mCoordIdeal (M'.wCo (τ, a) k₀' ca cb RatFunc.X))) :
    ∃ (V : Set ((Σ o : Option K', ι' (o.getD k₀')) → ℂ))
      (f : ((Σ o : Option K', ι' (o.getD k₀')) → ℂ) → (Σ o : Option K, ι (o.getD k₀)) → ℂ), IsOpen V ∧ z ∈ V ∧
      AnalyticOnNhd ℂ f V ∧ ∀ z' ∈ V ∩ mcPts (mCoordIdeal (M'.wCo (τ, a) k₀' ca cb RatFunc.X)),
        f z' ∈ mcPts (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ∧ RelW Cv k₀ k₀' z' (f z') := by
  have hz₀ := fst_mem hz
  have hz₁ := S'.snd_mem hy' hz
  have hb := CPts.base_mem M' hz₀
  have hbv := (GlobalTheory.T.flag_cover_base_point_in_points K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ hb).1
  obtain ⟨F', hF', hg'⟩ := (GlobalTheory.T.flag_model_base_projection_points K' ι' Φ' y' Ψ N j M').2.1 _ hb
  obtain ⟨F, hF, hg⟩ := (GlobalTheory.T.flag_model_base_projection_points K ι Φ y Ψ N j M).2.1 _ hbv
  have hsb := Pts.basePart_snd M' S'.hk
  obtain ⟨V₀, f₀, hV₀, hzV₀, hf₀, hs₀⟩ := GlobalTheory.T.flag_cover_frames_at_point K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ F' F hz₀ hF' hF hg' hg
  obtain ⟨V₁, f₁, hV₁, hzV₁, hf₁, hs₁⟩ := GlobalTheory.T.flag_cover_frames_at_point K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ F' F hz₁ hF' hF
    (by rw [hsb]; exact hg') (by rw [hsb]; exact hg)
  refine ⟨fstPt k₀' ⁻¹' V₀ ∩ sndPt k₀' ⁻¹' V₁, fun u => joinPt k₀ (f₀ (fstPt k₀' u)) (f₁ (sndPt k₀' u)),
    (hV₀.preimage (continuous_comp_idx _)).inter (hV₁.preimage (continuous_comp_idx _)), ⟨hzV₀, hzV₁⟩,
    fun u hu => analytic_join k₀ ((hf₀ _ hu.1).comp (analytic_comp_idx _ u))
      ((hf₁ _ hu.2).comp (analytic_comp_idx _ u)), fun u hu => ?_⟩
  have hu₀ := fst_mem hu.2
  have hu₁ := S'.snd_mem hy' hu.2
  obtain ⟨g1, g2, e₀⟩ := hs₀ _ ⟨hu.1.1, hu₀⟩
  obtain ⟨g3, g4, e₁⟩ := hs₁ _ ⟨hu.1.2, hu₁⟩
  obtain ⟨m₀, i₀⟩ := LocImg.img_spec K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ F' F hu₀ hF' hF g1 g2
  obtain ⟨m₁, i₁⟩ := LocImg.img_spec K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ F' F hu₁ hF' hF g3 g4
  have e : sndPt k₀ (joinPt k₀ (LocImg.img Cv F' F (fstPt k₀' u)) (LocImg.img Cv F' F (sndPt k₀' u))) =
      LocImg.img Cv F' F (sndPt k₀' u) := by
    refine join_v₁ fun k hk m => ?_
    by_cases hkb : ∀ p, M.blk p ≠ some k
    · have h1 := congrFun (LocImg.img_base Cv F' F (fstPt k₀' u)) ⟨⟨k, hkb⟩, m⟩
      have h2 := congrFun (LocImg.img_base Cv F' F (sndPt k₀' u)) ⟨⟨k, hkb⟩, m⟩
      rw [hsb] at h2
      exact h1.trans h2.symm
    · push_neg at hkb
      obtain ⟨p, hp⟩ := hkb
      obtain ⟨k', hk'⟩ := blk_cover M' M hp
      have hne : k' ≠ k₀' := fun e' => hk (by
        have := M'.blk_inj _ _ _ hk' (e' ▸ S'.hk)
        rw [this, S.hk] at hp
        exact (Option.some.inj hp).symm)
      rw [LocImg.img_step Cv F' F _ hp hk', LocImg.img_step Cv F' F _ hp hk']
      simp only [LocImg.stepCoord, hsb, Pts.snd_fst_ne hne]
  simp only [e₀, e₁]
  exact ⟨S.mem m₀ (by rw [e]; exact m₁), i₀, by rw [e]; exact i₁⟩

end Cov

end PositivityTheory.Xgp.c_sqsys
