import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UpVApply
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMapFrameRestriction
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockMapFrameRestrictionRegularStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalResolutionOpen
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PMatStepColsEntry
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJLowerUniSwap
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsLowerUniBlockDiagFactorizationStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentArithmeticHeight
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartSeventh
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsValueAtOfTorus
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockDiagonalMinorVanishing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.Onto

section Mat

variable {Ψ : Type} {N j : ℕ}

theorem pMat_of_low (keep : Ψ × Fin N → Prop) (L : Ψ → Matrix (Fin N) (Fin N) ℂ) (hb : ∀ τ, IsBlockDiag j (L τ))
    (hl : ∀ τ, IsLowerUni (L τ))
    (hs : ∀ (τ : Ψ) (a b : Fin N), b < a → ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) →
      (¬ ∃ i, keep (τ, i) ∧ IsProperStep N j i ∧ b ∈ stepCols N j i ∧ a ∉ stepCols N j i) → L τ a b = 0) (τ : Ψ) :
    pMat keep (fun q : PIdx j keep => L q.1.1.1 q.1.1.2.1 q.1.1.2.2) τ = L τ := by
  ext a b
  unfold pMat lowMat cExt
  by_cases h : b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)
  · rw [dif_pos h]
    by_cases hS : Sep keep (⟨(τ, a, b), h⟩ : LowIdx Ψ N j)
    · rw [dif_pos hS]
    · rw [dif_neg hS]
      exact (hs τ a b h.1 h.2 hS).symm
  · rw [dif_neg h]
    by_cases e : a = b
    · subst e
      rw [if_pos rfl, (hl τ).1]
    · rw [if_neg e]
      rcases lt_or_gt_of_ne e with hlt | hgt
      · exact ((hl τ).2 a b hlt).symm
      · exact (hb τ a b fun hi => h ⟨hgt, hi⟩).symm

theorem minor_self {X : Matrix (Fin N) (Fin N) ℂ} (hX : IsLowerUni X) (C : Finset (Fin N)) :
    minorIJ X C C = 1 := by
  unfold minorIJ
  rw [dif_pos rfl, det_of_lowerTriangular (X.submatrix (C.orderEmbOfFin rfl) (C.orderEmbOfFin rfl)) fun a b e =>
    hX.2 _ _ ((C.orderEmbOfFin rfl).strictMono (show a < b from e))]
  exact Finset.prod_eq_one fun a _ => hX.1 _

theorem minor_mul_self {G W L : Matrix (Fin N) (Fin N) ℂ} (hGW : G * W = L) (hL : IsLowerUni L) {S : Finset (Fin N)}
    (hz : ∀ k c, c ∈ S → k ∉ S → W k c = 0) : 1 = minorIJ G S S * minorIJ W S S := by
  rw [← MinorCalc.minorIJ_mul_of_support G W S S hz, hGW, minor_self hL]

theorem ratio {α g s w sg x : ℂ} (hα : α ≠ 0) (h1 : sg * x = g * w) (h2 : 1 = s * w) (hsg : sg ≠ 0) :
    α * g / (sg * (α * s)) = x := by
  have hs : s ≠ 0 := fun e => by simp [e] at h2
  rw [div_eq_iff (mul_ne_zero hsg (mul_ne_zero hα hs))]
  linear_combination (α * g) * h2 - (α * s) * h1

end Mat

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)]

theorem upV_scale {κ : Kk → K} {v : (Σ k, ιk k) → (Σ k, ι k)} (hb : IsBlockMap κ v) (c : Kk → ℂ)
    (z : (Σ k, ιk k) → ℂ) {k : K} {t : ℂ} (hr : k ∈ Set.range κ) (hk : ∀ k', κ k' = k → c k' = t) (m : ι k) :
    upV v (fun p => c p.1 * z p) ⟨k, m⟩ = t * upV v z ⟨k, m⟩ := by
  obtain ⟨q, e⟩ := hb.2.2.2 ⟨k, m⟩ hr
  rw [← e, upV_apply hb.2.1, upV_apply hb.2.1]
  have e' : κ q.1 = k := by
    have := hb.2.2.1 q
    rw [e] at this
    exact this.symm
  rw [hk _ e']

end Flag

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∀ z ∈ pO M Rb keep v F kb V r h, pRho M Rb keep v F kb r h ε z ∈ pD ε V ∧ SameOrbit (pPhi M F keep v bl h ε (pRho M Rb keep v F kb r h ε z)) z := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb keep Kk _ ιk _ κ v F kb V bl r h ε ctx z hz
  have ctx0 := ctx
  obtain ⟨hbm, hκ, hF, hBC, hr1, hr2, hh⟩ := ctx
  obtain ⟨hzP, hs, hV, hm⟩ := hz
  have hzb : pBase M v z ∈ mcPts (mCoordIdeal M.x) := (GlobalTheory.CompanionTheory.Ar.PB.PFl.PtsBase.main K ι Φ y Ψ N j M keep Kk ιk κ v hbm hκ).1 z hzP
  have hB : pB ε (pRho M Rb keep v F kb r h ε z) = Rb.A.chart kb (r (pBase M v z)) := by
    funext l
    simp only [pB, pRho, Equiv.symm_apply_apply]
  have hLp : ∀ q : PIdx j keep, pL ε (pRho M Rb keep v F kb r h ε z) q =
      pRead M F keep (pBase M v z) h (upV v z) q.1.1.1 q.1.1.2.1 q.1.1.2.2 := fun q => by
    simp only [pL, pRho, Equiv.symm_apply_apply]
  have hwD : pRho M Rb keep v F kb r h ε z ∈ pD ε V := by
    show pB ε _ ∈ V
    rw [hB]
    exact hV
  refine ⟨hwD, ?_⟩
  obtain ⟨hblm, hblnorm, hblgood, hblorb⟩ := hBC.2.2.2.2 _ hV
  rw [(Rb.A.chart kb).left_inv hs] at hblorb
  generalize hzc : bl (Rb.A.chart kb (r (pBase M v z))) = zc at hblm hblnorm hblgood hblorb
  have horb : SameOrbit zc (pBase M v z) := orbit_trans (orbit_symm hblorb) (hr1 _ hzb)
  obtain ⟨c₀, hc₀, he⟩ := horb
  have hv : ∀ s, valAt M.x s zc = valAt M.x s (pBase M v z) := fun s => by
    have := StepW.TorusAct.valAt_torus (x := M.x) c₀ hc₀ hzb (he ▸ hblm) s
    rw [he]
    exact this
  let c : Kk → ℂ := fun k => if hk : ∀ p, M.blk p ≠ some (κ k) then c₀ ⟨κ k, hk⟩ else 1
  have hc : ∀ k, c k ≠ 0 := fun k => by
    by_cases hk : ∀ p, M.blk p ≠ some (κ k)
    · simp only [c, dif_pos hk]
      exact hc₀ _
    · simp only [c, dif_neg hk]
      exact one_ne_zero
  let z' : (Σ k, ιk k) → ℂ := fun p => c p.1 * z p
  have hz' : z' ∈ mcPts (mCoordIdeal (y ∘ v)) :=
    mcPts_smul (GroundTheory.Heights₂.Heights.CoordinateConeArithVar.isMultiHomogIdeal _) c hc hzP
  have hbase : ∀ (k : NonPluckerBlocks M.blk) (m : ι k.1), upV v z' ⟨k.1, m⟩ = c₀ k * upV v z ⟨k.1, m⟩ := fun k m =>
    upV_scale hbm c z ((hκ k.1).2 (Or.inl k.2)) (fun k' e' => by
      have hk' : ∀ p, M.blk p ≠ some (κ k') := e' ▸ k.2
      simp only [c, dif_pos hk']
      congr 1
      exact Subtype.ext e') m
  have hbp : pBase M v z' = zc := by
    rw [he]
    funext q
    obtain ⟨k, m⟩ := q
    exact hbase k m
  have hkept : ∀ p k, keep p → M.blk p = some k → ∀ m : ι k, upV v z' ⟨k, m⟩ = 1 * upV v z ⟨k, m⟩ :=
    fun p k hp hk m => upV_scale hbm c z ((hκ k).2 (Or.inr ⟨p, hp, hk⟩)) (fun k' e' => by
      have hk' : ¬ ∀ p, M.blk p ≠ some (κ k') := fun hn => hn p (hk.trans (by rw [e']))
      simp only [c, dif_neg hk']) m
  obtain ⟨H, hH, hHf⟩ := GlobalTheory.T.blockMap_frame_restriction_regular K ι Φ y Ψ N j M keep Kk ιk κ v hbm hκ F z' hF hz' (hbp ▸ hblgood)
    (by rw [hbp]; exact hblnorm)
  rw [hbp] at hHf
  have hmin : ∀ p k, keep p → M.blk p = some k → ∃ α : ℂ, α ≠ 0 ∧
      (∀ m : ι k, upV v z' ⟨k, m⟩ = α * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zc * minorIJ (H p.1) I (stepCols N j p.2)) ∧
      ∀ (g : Matrix (Fin N) (Fin N) ℂ) (J : Finset (Fin N)),
        twMinor M F (pBase M v z) p.2 k g (upV v z) J = α * minorIJ (g * H p.1) J (stepCols N j p.2) := by
    intro p k hp hk
    obtain ⟨α, hα, hw⟩ := hHf p k hp hk
    refine ⟨α, hα, hw, fun g J => ?_⟩
    have h1 := Cover.twMinor_of_flag M hF hblm hblgood hk (hH p.1).1 hw g J
    have h2 := Orb.twMinor_scale M F hv p.2 k g (hkept p k hp hk) J
    rw [one_mul] at h2
    rw [← h2]
    exact h1
  have hsome : ∀ p, IsProperStep N j p.2 → ∃ k, M.blk p = some k := fun p hp =>
    Option.ne_none_iff_exists'.1 fun e' => (M.blk_none p).1 e' hp
  have hproper : ∀ p k, M.blk p = some k → IsProperStep N j p.2 := fun p k hk => by
    by_contra hn
    rw [(M.blk_none p).2 hn] at hk
    exact absurd hk (by simp)
  have hjN := M.j_le
  have hdec := fun τ => GlobalTheory.T.exists_lowerUni_blockDiag_factorization N j (fun i => keep (τ, i)) ((h τ)⁻¹ * H τ) hjN
    (((hh τ).1.inv (hh τ).2.isUnit).mul (hH τ).1)
    (by
      rw [Matrix.det_mul]
      exact mul_ne_zero (Matrix.isUnit_nonsing_inv_det _ (hh τ).2.isUnit).ne_zero (hH τ).2)
    (fun i hk hp => by
      obtain ⟨k, hbk⟩ := hsome (τ, i) hp
      obtain ⟨α, -, -, hT⟩ := hmin (τ, i) k hk hbk
      have := hm (τ, i) k hk hbk
      rw [hT] at this
      exact right_ne_zero_of_mul this)
  choose L W hLb hLu hLs hWb hWs hGW using hdec
  have hpm : ∀ τ, pMat keep (fun q : PIdx j keep => L q.1.1.1 q.1.1.2.1 q.1.1.2.2) τ = L τ :=
    pMat_of_low keep L hLb hLu hLs
  have hread : ∀ q : PIdx j keep, pRead M F keep (pBase M v z) h (upV v z) q.1.1.1 q.1.1.2.1 q.1.1.2.2 =
      L q.1.1.1 q.1.1.2.1 q.1.1.2.2 := by
    intro q
    obtain ⟨hk1, hp1, hb1, ha1, hc1⟩ := GlobalTheory.CompanionTheory.Ar.PB.PFl.SmallStep.pStep_reads Ψ N j keep q hjN
    obtain ⟨-, hc3⟩ := hc1 fun q : PIdx j keep => L q.1.1.1 q.1.1.2.1 q.1.1.2.2
    rw [hpm] at hc3
    obtain ⟨k, hbk⟩ := hsome (q.1.1.1, pStep j keep q.1.1.1 q.1.1.2.2) hp1
    obtain ⟨α, hα, -, hT⟩ := hmin (q.1.1.1, pStep j keep q.1.1.1 q.1.1.2.2) k hk1 hbk
    have hsup : ∀ x c, c ∈ stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2) →
        x ∉ stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2) → W q.1.1.1 x c = 0 :=
      fun x c hc' hx => hWs q.1.1.1 _ hk1 hp1 c hc' x hx
    obtain ⟨r1, r2⟩ := GlobalTheory.CompanionTheory.Ar.PB.PFl.MatRead.minor_replace N (L q.1.1.1) _ _ _ (hLu _) ha1 hb1 q.1.2.1 (fun x hx hne => hc3 x hx hne)
    have e1 := MinorCalc.minorIJ_mul_of_support ((h q.1.1.1)⁻¹ * H q.1.1.1) (W q.1.1.1)
      (insert q.1.1.2.1 ((stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2)).erase q.1.1.2.2)) _ hsup
    rw [hGW, r1] at e1
    have e2 := minor_mul_self (hGW q.1.1.1) (hLu _) hsup
    unfold pRead
    rw [hbk]
    show twMinor _ _ _ _ _ _ _ _ / (_ * twMinor _ _ _ _ _ _ _ _) = _
    rw [hT, hT]
    exact ratio hα e1 e2 r2
  have hLw : pL ε (pRho M Rb keep v F kb r h ε z) = fun q : PIdx j keep => L q.1.1.1 q.1.1.2.1 q.1.1.2.2 :=
    funext fun q => (hLp q).trans (hread q)
  have hHw : ∀ τ, pH keep h ε τ (pRho M Rb keep v F kb r h ε z) = H τ * W τ := fun τ => by
    unfold pH
    rw [hLw, hpm, ← hGW τ, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (hh τ).2.isUnit]
  obtain ⟨-, hpb, hpk⟩ := GlobalTheory.CompanionTheory.Ar.PB.PFl.Exact.chart_points K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε ctx0 _ hwD
  have hbw : bl (pB ε (pRho M Rb keep v F kb r h ε z)) = zc := by rw [hB, hzc]
  rw [hbw] at hpb hpk
  generalize hφ : pPhi M F keep v bl h ε (pRho M Rb keep v F kb r h ε z) = φ at hpb hpk ⊢
  have hblock : ∀ k : Kk, ∃ t : ℂ, t ≠ 0 ∧ ∀ m : ιk k, φ ⟨k, m⟩ = t * z' ⟨k, m⟩ := by
    intro k
    by_cases hk : ∀ p, M.blk p ≠ some (κ k)
    · refine ⟨1, one_ne_zero, fun m => ?_⟩
      rw [one_mul, ← upV_apply hbm.2.1 φ, ← upV_apply hbm.2.1 z']
      have hfst : (v ⟨k, m⟩).1 = κ k := hbm.2.2.1 _
      generalize v ⟨k, m⟩ = q at hfst
      obtain ⟨k', m'⟩ := q
      obtain rfl : k' = κ k := hfst
      exact congrFun (hpb.trans hbp.symm) ⟨⟨κ k, hk⟩, m'⟩
    · obtain ⟨p, hp, hbk⟩ := ((hκ (κ k)).1 ⟨k, rfl⟩).resolve_left hk
      obtain ⟨α, hα, hw, -⟩ := hmin p (κ k) hp hbk
      have hsup : ∀ x c, c ∈ stepCols N j p.2 → x ∉ stepCols N j p.2 → W p.1 x c = 0 :=
        fun x c hc' hx => hWs p.1 p.2 hp (hproper p _ hbk) c hc' x hx
      have e2 := minor_mul_self (hGW p.1) (hLu _) hsup
      have hmw : minorIJ (W p.1) (stepCols N j p.2) (stepCols N j p.2) ≠ 0 := fun e0 => by
        simp [e0] at e2
      refine ⟨minorIJ (W p.1) (stepCols N j p.2) (stepCols N j p.2) / α, div_ne_zero hmw hα, fun m => ?_⟩
      rw [← upV_apply hbm.2.1 φ, ← upV_apply hbm.2.1 z']
      have hfst : (v ⟨k, m⟩).1 = κ k := hbm.2.2.1 _
      generalize v ⟨k, m⟩ = q at hfst
      obtain ⟨k', m'⟩ := q
      obtain rfl : k' = κ k := hfst
      rw [hpk p _ hp hbk m', hw m', hHw, div_mul_eq_mul_div, mul_left_comm _ α, mul_div_cancel_left₀ _ hα,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [MinorCalc.minorIJ_mul_of_support _ _ _ _ hsup]
      ring
  choose t ht1 ht2 using hblock
  have o1 : SameOrbit φ z' := ⟨t, ht1, funext fun q => ht2 q.1 q.2⟩
  exact orbit_trans o1 ⟨c, hc, rfl⟩

end GlobalTheory.CompanionTheory.Ar.PB.PFl.Onto
