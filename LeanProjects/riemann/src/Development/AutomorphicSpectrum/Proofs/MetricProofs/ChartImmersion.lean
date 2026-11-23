import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.UpVApply
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalResolutionOpenStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FrameDataLocalIntegrabilityStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PMatStepColsEntryStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinorIJLowerUniSwapStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartNinth
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan
open GlobalTheory.CompanionTheory.Ar.PB.PFl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.PFl.Imm

open GlobalTheory.CompanionTheory.Ar.PB.WMan.Imm

section Block

variable {K : Type} {ι : K → Type} {Kk : Type} {ιk : Kk → Type}

theorem block_equiv {κ : Kk → K} {v : (Σ k, ιk k) → (Σ k, ι k)} (hv : IsBlockMap κ v) (k₂ : Kk) :
    ∃ σ : ιk k₂ ≃ ι (κ k₂), ∀ m, v ⟨k₂, m⟩ = ⟨κ k₂, σ m⟩ := by
  have h1 : ∀ m, ∃ m', v ⟨k₂, m⟩ = ⟨κ k₂, m'⟩ := fun m => by
    rcases e : v ⟨k₂, m⟩ with ⟨a, m'⟩
    have ha : a = κ k₂ := by
      have := hv.2.2.1 ⟨k₂, m⟩
      rw [e] at this
      exact this
    subst ha
    exact ⟨m', rfl⟩
  choose σ hσ using h1
  have inj : Function.Injective σ := fun m₁ m₂ e => by
    have e1 : v ⟨k₂, m₁⟩ = v ⟨k₂, m₂⟩ := by rw [hσ, hσ, e]
    exact eq_of_heq (Sigma.mk.inj_iff.1 (hv.2.1 e1)).2
  have surj : Function.Surjective σ := fun m => by
    obtain ⟨⟨k', m'⟩, e⟩ := hv.2.2.2 ⟨κ k₂, m⟩ ⟨k₂, rfl⟩
    have hk : k' = k₂ := hv.1 (by
      have := hv.2.2.1 ⟨k', m'⟩
      rw [e] at this
      exact this.symm)
    subst hk
    refine ⟨m', ?_⟩
    rw [hσ] at e
    exact eq_of_heq (Sigma.mk.inj_iff.1 e).2
  exact ⟨Equiv.ofBijective σ ⟨inj, surj⟩, hσ⟩

end Block

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}
  {Kk : Type} [Fintype Kk] {ιk : Kk → Type} [∀ k, Fintype (ιk k)]

theorem twMinor_up (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ)
    (i : Fin N) {κ : Kk → K} {v : (Σ k, ιk k) → (Σ k, ι k)} (hinj : Function.Injective v) {k₂ : Kk}
    (σ : ιk k₂ ≃ ι (κ k₂)) (hσ : ∀ m, v ⟨k₂, m⟩ = ⟨κ k₂, σ m⟩) (g : Matrix (Fin N) (Fin N) ℂ)
    (z : (Σ k, ιk k) → ℂ) (J : Finset (Fin N)) :
    twMinor M F zb i (κ k₂) g (upV v z) J = ∑ m, twC M F zb i (κ k₂) g J (σ m) * z ⟨k₂, m⟩ := by
  rw [twMinor_eq, ← Equiv.sum_comp σ]
  refine Finset.sum_congr rfl fun m _ => ?_
  have e : upV v z ⟨κ k₂, σ m⟩ = z ⟨k₂, m⟩ := by
    rw [← hσ m]
    exact upV_apply hinj z _
  rw [e]
  rfl

theorem pRead_some (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (keep : Ψ × Fin N → Prop)
    (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (z : (Σ k, ι k) → ℂ) {τ : Ψ} (a : Fin N)
    {b : Fin N} {k : K} (hk : M.blk (τ, pStep j keep τ b) = some k) :
    pRead M F keep zb h z τ a b =
      twMinor M F zb (pStep j keep τ b) k (h τ)⁻¹ z (insert a ((stepCols N j (pStep j keep τ b)).erase b)) /
        (pSgn (stepCols N j (pStep j keep τ b)) a b *
          twMinor M F zb (pStep j keep τ b) k (h τ)⁻¹ z (stepCols N j (pStep j keep τ b))) := by
  unfold pRead
  rw [hk]
  rfl

theorem pRead_none (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (keep : Ψ × Fin N → Prop)
    (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (z : (Σ k, ι k) → ℂ) {τ : Ψ} (a : Fin N)
    {b : Fin N} (hk : M.blk (τ, pStep j keep τ b) = none) : pRead M F keep zb h z τ a b = 0 := by
  unfold pRead
  rw [hk]
  rfl

theorem pRead_deriv (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (keep : Ψ × Fin N → Prop)
    (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) {κ : Kk → K}
    {v : (Σ k, ιk k) → (Σ k, ι k)} (hv : IsBlockMap κ v) {Z : ℂ → (Σ k, ιk k) → ℂ} {p : (k : Kk) → ιk k}
    (hd : HasDerivAt (fun s => affCoord p (Z s)) 0 0) (hc : ∀ q, ContinuousAt (fun s => Z s q) 0)
    (hp : ∀ k, Z 0 ⟨k, p k⟩ ≠ 0) {τ : Ψ} (a : Fin N) {b : Fin N} {k₂ : Kk}
    (hk : M.blk (τ, pStep j keep τ b) = some (κ k₂))
    (h0 : twMinor M F zb (pStep j keep τ b) (κ k₂) (h τ)⁻¹ (upV v (Z 0)) (stepCols N j (pStep j keep τ b)) ≠ 0) :
    HasDerivAt (fun s => pRead M F keep zb h (upV v (Z s)) τ a b) 0 0 := by
  obtain ⟨σ, hσ⟩ := block_equiv hv k₂
  simp only [pRead_some M F keep zb h _ a hk, twMinor_up M F zb _ hv.2.1 σ hσ, div_mul_eq_div_div_swap]
  rw [twMinor_up M F zb _ hv.2.1 σ hσ] at h0
  have := (ratio_deriv (ρ := ιk) hd hc hp k₂
    (fun m => twC M F zb (pStep j keep τ b) (κ k₂) (h τ)⁻¹ (insert a ((stepCols N j (pStep j keep τ b)).erase b)) (σ m))
    _ h0).div_const (pSgn (stepCols N j (pStep j keep τ b)) a b)
  simpa using this

variable {M : FlagModel y Ψ N j} {n e : ℕ} {Rb : AnLogRes (mCoordIdeal M.x) ⊤ n} {keep : Ψ × Fin N → Prop}
  {κ : Kk → K} {v : (Σ k, ιk k) → (Σ k, ι k)} {F : FrameData ι Ψ N M.Ω M.blk} {kb : Fin Rb.A.n}
  {V : Set (Fin n → ℂ)} {bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ}
  {r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X} {h : Ψ → Matrix (Fin N) (Fin N) ℂ}
  {ε : Fin n ⊕ PIdx j keep ≃ Fin e}

theorem pB_diff (w : Fin e → ℂ) : DifferentiableAt ℂ (pB ε) w :=
  differentiableAt_pi.2 fun _ => differentiableAt_apply _ _

theorem pH_diff (τ : Ψ) (a b : Fin N) (w : Fin e → ℂ) :
    DifferentiableAt ℂ (fun w' => pH keep h ε τ w' a b) w := by
  have hl : ∀ x, DifferentiableAt ℂ (fun w' => pMat keep (pL ε w') τ x b) w := by
    intro x
    unfold pMat lowMat
    by_cases hh : b < x ∧ ((x : ℕ) < N - j ↔ (b : ℕ) < N - j)
    · simp only [dif_pos hh, cExt]
      split_ifs with hs
      · exact differentiableAt_apply _ _
      · exact differentiableAt_const _
    · simp only [dif_neg hh]
      exact differentiableAt_const _
  simp only [pH, Matrix.mul_apply]
  exact DifferentiableAt.fun_sum fun x _ => (differentiableAt_const _).fun_mul (hl x)

theorem pPhi_diff (hb : IsBaseChart M Rb F kb V bl) {w : Fin e → ℂ} (hw : w ∈ pD ε V) (q : Σ k, ιk k) :
    DifferentiableAt ℂ (fun w' => pPhi M F keep v bl h ε w' q) w := by
  have hz : ∀ q, DifferentiableAt ℂ (fun w' => bl (pB ε w') q) w := fun q =>
    DifferentiableAt.comp (g := fun u => bl u q) w (hb.2.2.1 q _ hw).differentiableAt (pB_diff w)
  have hv' : ∀ q I, DifferentiableAt ℂ (fun w' => valAt M.x (F.u q I) (bl (pB ε w'))) w := fun q I =>
    DifferentiableAt.comp (g := fun u => valAt M.x (F.u q I) (bl u)) w (hb.2.2.2.1 q I _ hw).differentiableAt
      (pB_diff w)
  exact flagZ_diff M F hz hv' (H := fun w' τ' => pH keep h ε τ' w') (fun τ' a b => pH_diff τ' a b w) (v q)

theorem base_inj (hb : IsBaseChart M Rb F kb V bl) {u : Fin n → ℂ} (hu : u ∈ V)
    (pb : (k : NonPluckerBlocks M.blk) → baseIdx ι M.blk k) (hp : ∀ k, bl u ⟨k, pb k⟩ ≠ 0) :
    (fderiv ℂ (fun u' => affCoord pb (bl u')) u).ker = ⊥ := by
  obtain ⟨hV, hVt, -, -, hbl⟩ := hb
  have hut := hVt hu
  set x := (Rb.A.chart kb).symm u with hx
  have hxs : x ∈ (Rb.A.chart kb).source := (Rb.A.chart kb).map_target hut
  have hcx : Rb.A.chart kb x = u := (Rb.A.chart kb).right_inv hut
  have ho := (hbl u hu).2.2.2
  have hnot : Rb.lift x x ∉ mcPts (⊤ : Ideal (MRing (baseIdx ι M.blk))) := fun hm => by
    have := hm.2 1 Submodule.mem_top
    simp at this
  have hne : ∀ k, Rb.lift x x ⟨k, pb k⟩ ≠ 0 := fun k => by
    obtain ⟨c, hcne, e⟩ := ho
    rw [e]
    exact mul_ne_zero (hcne k) (hp k)
  have him := Rb.immersion x hnot pb hne kb hxs
  rw [hcx] at him
  have hev : (fun u' => affCoord pb (Rb.lift x ((Rb.A.chart kb).symm u'))) =ᶠ[𝓝 u] fun u' => affCoord pb (bl u') := by
    have h1 : ∀ᶠ u' in 𝓝 u, (Rb.A.chart kb).symm u' ∈ Rb.U x :=
      ((Rb.A.chart kb).continuousAt_symm hut).eventually_mem ((Rb.isOpen_U x).mem_nhds (Rb.mem_U x))
    filter_upwards [h1, hV.mem_nhds hu] with u' h1 h2
    exact affCoord_orbit pb (orbit_trans (Rb.compat x _ _ ⟨h1, Rb.mem_U _⟩) (hbl u' h2).2.2.2)
  rw [← hev.fderiv_eq]
  exact him

theorem pPhi_base (w' : Fin e → ℂ) {q' : Σ k, ιk k} (k : NonPluckerBlocks M.blk) (m : ι k.1) (hq : v q' = ⟨k.1, m⟩) :
    pPhi M F keep v bl h ε w' q' = bl (pB ε w') ⟨k, m⟩ := by
  simp only [pPhi, hq]
  exact flagZ_base M F _ _ k m

theorem exists_base_pt (hc : IsPCtx M Rb keep κ v F kb V bl r h) (p : (k : Kk) → ιk k) (k : NonPluckerBlocks M.blk) :
    ∃ (k' : Kk) (m : ι k.1), κ k' = k.1 ∧ v ⟨k', p k'⟩ = ⟨k.1, m⟩ := by
  obtain ⟨k', hk'⟩ := (hc.2.1 k.1).2 (Or.inl k.2)
  obtain ⟨k₀, hk₀⟩ := k
  simp only at hk'
  subst hk'
  obtain ⟨σ, hσ⟩ := block_equiv hc.1 k'
  exact ⟨k', σ (p k'), rfl, hσ _⟩

theorem base_zero (hc : IsPCtx M Rb keep κ v F kb V bl r h) {w : Fin e → ℂ} (hw : w ∈ pD ε V)
    (p : (k : Kk) → ιk k) (hp : ∀ k, pPhi M F keep v bl h ε w ⟨k, p k⟩ ≠ 0)
    {D : (Fin e → ℂ) →L[ℂ] (Σ k, ιk k) → ℂ}
    (hD : HasFDerivAt (fun w' => affCoord p (pPhi M F keep v bl h ε w')) D w)
    {u : Fin e → ℂ} (hu : D u = 0) : pB ε u = 0 := by
  have hb : IsBaseChart M Rb F kb V bl := hc.2.2.2.1
  choose k' pb hk' hpb using exists_base_pt hc p
  have hs : ∀ q : Σ k, baseIdx ι M.blk k, ∃ q', v q' = ⟨q.1.1, q.2⟩ := fun q =>
    hc.1.2.2.2 ⟨q.1.1, q.2⟩ ((hc.2.1 q.1.1).2 (Or.inl q.1.2))
  choose s hs using hs
  have hblock : ∀ q, (s q).1 = k' q.1 := fun q => hc.1.1 (by
    have := hc.1.2.2.1 (s q)
    rw [hs] at this
    rw [← this, hk'])
  have hpk : ∀ a b : Kk, a = b → (⟨a, p a⟩ : Σ k, ιk k) = ⟨b, p b⟩ := by
    rintro a b rfl
    rfl
  have hne : ∀ k : NonPluckerBlocks M.blk, bl (pB ε w) ⟨k, pb k⟩ ≠ 0 := fun k => by
    have := hp (k' k)
    rwa [pPhi_base w k (pb k) (hpb k)] at this
  have hbd : ∀ q, DifferentiableAt ℂ (fun u => bl u q) (pB ε w) := fun q =>
    (hb.2.2.1 q _ hw).differentiableAt
  have hB : DifferentiableAt ℂ (fun u' => affCoord pb (bl u')) (pB ε w) :=
    differentiableAt_pi.2 fun q => diff_div (hbd q) (hbd _) (hne q.1)
  have hinj := base_inj hb hw pb hne
  have hcoord : ∀ (w' : Fin e → ℂ) (q : Σ k, baseIdx ι M.blk k),
      affCoord p (pPhi M F keep v bl h ε w') (s q) = affCoord pb (bl (pB ε w')) q := fun w' q => by
    obtain ⟨k, m⟩ := q
    simp only [affCoord]
    rw [hpk _ _ (hblock ⟨k, m⟩), pPhi_base w' k m (hs ⟨k, m⟩), pPhi_base w' k (pb k) (hpb k)]
  have hz := comp_zero (W := ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (ε (Sum.inl i)))
    (e := s) (fun w' q => hcoord w' q) hD hB hu
  have hm : pB ε u ∈ (fderiv ℂ (fun u' => affCoord pb (bl u')) (pB ε w)).ker := hz
  rw [hinj] at hm
  exact hm

theorem line_zero (hc : IsPCtx M Rb keep κ v F kb V bl r h) {w : Fin e → ℂ} (hw : w ∈ pD ε V)
    (p : (k : Kk) → ιk k) (hp : ∀ k, pPhi M F keep v bl h ε w ⟨k, p k⟩ ≠ 0)
    {D : (Fin e → ℂ) →L[ℂ] (Σ k, ιk k) → ℂ}
    (hD : HasFDerivAt (fun w' => affCoord p (pPhi M F keep v bl h ε w')) D w)
    {u : Fin e → ℂ} (hu : D u = 0) (hb0 : pB ε u = 0) : u = 0 := by
  have hb : IsBaseChart M Rb F kb V bl := hc.2.2.2.1
  have hE := GlobalTheory.T.frameData_local_resolution_open K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
  have hR := GlobalTheory.T.frameData_local_integrability K ι Φ y Ψ N j M n e Rb keep Kk ιk κ v F kb V bl r h ε hc
  have hwB : ∀ s : ℂ, pB ε (w + s • u) = pB ε w := fun s => by
    funext i
    have : u (ε (Sum.inl i)) = 0 := congrFun hb0 i
    simp [pB, this]
  have hmem : ∀ s : ℂ, w + s • u ∈ pD ε V := fun s => by
    show pB ε (w + s • u) ∈ V
    rw [hwB]
    exact hw
  have hcurve : HasDerivAt (fun s : ℂ => w + s • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const u).const_add w
  have h00 : w = (fun s : ℂ => w + s • u) 0 := by simp
  have hdZ : HasDerivAt (fun s : ℂ => affCoord p (pPhi M F keep v bl h ε (w + s • u))) 0 0 := by
    have := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hD hcurve h00
    rw [hu] at this
    exact this
  have hcZ : ∀ q, ContinuousAt (fun s : ℂ => pPhi M F keep v bl h ε (w + s • u) q) 0 := fun q =>
    ContinuousAt.comp_of_eq (g := fun w' => pPhi M F keep v bl h ε w' q) (pPhi_diff hb hw q).continuousAt
      hcurve.continuousAt h00.symm
  have hZ0 : pPhi M F keep v bl h ε (w + (0 : ℂ) • u) = pPhi M F keep v bl h ε w := by simp
  have hp0 : ∀ k, pPhi M F keep v bl h ε (w + (0 : ℂ) • u) ⟨k, p k⟩ ≠ 0 := fun k => by
    rw [hZ0]
    exact hp k
  have hbase : ∀ s : ℂ, pBase M v (pPhi M F keep v bl h ε (w + s • u)) = bl (pB ε w) := fun s => by
    rw [(hE _ (hmem s)).2.1, hwB]
  have hlin : ∀ i, HasDerivAt (fun s : ℂ => w i + s * u i) (u i) 0 := fun i => by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (u i)).const_add (w i)
  have hcell : ∀ q : PIdx j keep, u (ε (Sum.inr q)) = 0 := fun q => by
    have hrel : ∀ s : ℂ, pRead M F keep (bl (pB ε w)) h (upV v (pPhi M F keep v bl h ε (w + s • u)))
        q.1.1.1 q.1.1.2.1 q.1.1.2.2 = w (ε (Sum.inr q)) + s * u (ε (Sum.inr q)) := fun s => by
      have := congrFun (hR _ (hmem s)).2 (ε (Sum.inr q))
      simp only [pRho, Equiv.symm_apply_apply] at this
      rw [hbase s] at this
      simpa using this
    have hS := GlobalTheory.T.pMat_stepCols_entry Ψ N j keep q M.j_le
    cases hk : M.blk (q.1.1.1, pStep j keep q.1.1.1 q.1.1.2.2) with
    | none =>
      have e0 := hrel 0
      have e1 := hrel 1
      rw [pRead_none M F keep _ h _ _ hk] at e0 e1
      simp only [zero_mul, add_zero, one_mul] at e0 e1
      rw [← e0, zero_add] at e1
      exact e1.symm
    | some k =>
      obtain ⟨k₂, rfl⟩ := (hc.2.1 k).2 (Or.inr ⟨_, hS.1, hk⟩)
      have h0 : twMinor M F (bl (pB ε w)) (pStep j keep q.1.1.1 q.1.1.2.2) (κ k₂) (h q.1.1.1)⁻¹
          (upV v (pPhi M F keep v bl h ε (w + (0 : ℂ) • u))) (stepCols N j (pStep j keep q.1.1.1 q.1.1.2.2)) ≠ 0 := by
        have := (hR w hw).1.2.2.2 _ _ hS.1 hk
        rw [(hE w hw).2.1] at this
        rw [hZ0]
        exact this
      have h1 := pRead_deriv M F keep (bl (pB ε w)) h hc.1
        (Z := fun s : ℂ => pPhi M F keep v bl h ε (w + s • u)) hdZ hcZ hp0 q.1.1.2.1 hk h0
      rw [funext hrel] at h1
      exact (hlin _).unique h1
  funext i
  obtain ⟨x, rfl⟩ := ε.surjective i
  rcases x with l | q
  · exact congrFun hb0 l
  · exact hcell q

theorem chart_immersion : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (keep : Ψ × Fin N → Prop) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ PIdx j keep ≃ Fin e), IsPCtx M Rb keep κ v F kb V bl r h → ∀ w ∈ pD ε V, ∀ p : (k : Kk) → ιk k, (∀ k, pPhi M F keep v bl h ε w ⟨k, p k⟩ ≠ 0) → (fderiv ℂ (fun w' => affCoord p (pPhi M F keep v bl h ε w')) w).ker = ⊥ := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb keep Kk _ ιk _ κ v F kb V bl r h ε hc w hw p hp
  have hb : IsBaseChart M Rb F kb V bl := hc.2.2.2.1
  have hT : DifferentiableAt ℂ (fun w' => affCoord p (pPhi M F keep v bl h ε w')) w :=
    differentiableAt_pi.2 fun q => diff_div (pPhi_diff hb hw q) (pPhi_diff hb hw _) (hp q.1)
  rw [eq_bot_iff]
  intro u hu
  have hu' : fderiv ℂ (fun w' => affCoord p (pPhi M F keep v bl h ε w')) w u = 0 := hu
  exact (Submodule.mem_bot ℂ).2
    (line_zero hc hw p hp hT.hasFDerivAt hu' (base_zero hc hw p hp hT.hasFDerivAt hu'))

end Flag

end GlobalTheory.CompanionTheory.Ar.PB.PFl.Imm
