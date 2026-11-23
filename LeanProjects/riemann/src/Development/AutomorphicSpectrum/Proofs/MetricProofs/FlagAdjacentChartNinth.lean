import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartSecondStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartFourthStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Imm

section Gen

variable {κ : Type} [Fintype κ] {ρ : κ → Type} [∀ k, Fintype (ρ k)]

theorem affCoord_orbit (p : (k : κ) → ρ k) {z z' : (Σ k, ρ k) → ℂ} (h : SameOrbit z z') :
    affCoord p z = affCoord p z' := by
  obtain ⟨c, hc, rfl⟩ := h
  funext q
  simp only [affCoord]
  rw [mul_div_mul_left _ _ (hc q.1)]

theorem ratio_deriv {Z : ℂ → (Σ k, ρ k) → ℂ} {p : (k : κ) → ρ k}
    (hd : HasDerivAt (fun s => affCoord p (Z s)) 0 0) (hc : ∀ q, ContinuousAt (fun s => Z s q) 0)
    (hp : ∀ k, Z 0 ⟨k, p k⟩ ≠ 0) (k : κ) (α β : ρ k → ℂ) (hb : ∑ m, β m * Z 0 ⟨k, m⟩ ≠ 0) :
    HasDerivAt (fun s => (∑ m, α m * Z s ⟨k, m⟩) / ∑ m, β m * Z s ⟨k, m⟩) 0 0 := by
  have hq : ∀ q, HasDerivAt (fun s => affCoord p (Z s) q) 0 0 := fun q => hasDerivAt_pi.1 hd q
  have hA : ∀ γ : ρ k → ℂ, HasDerivAt (fun s => ∑ m, γ m * affCoord p (Z s) ⟨k, m⟩) 0 0 := fun γ => by
    have := HasDerivAt.fun_sum (u := Finset.univ) (fun m _ => (hq ⟨k, m⟩).const_mul (γ m))
    simpa using this
  have hne : ∀ᶠ s in 𝓝 (0 : ℂ), Z s ⟨k, p k⟩ ≠ 0 := (hc _).eventually_ne (hp k)
  have hden : ∑ m, β m * affCoord p (Z 0) ⟨k, m⟩ ≠ 0 := by
    have e : ∑ m, β m * affCoord p (Z 0) ⟨k, m⟩ = (∑ m, β m * Z 0 ⟨k, m⟩) / Z 0 ⟨k, p k⟩ := by
      simp only [affCoord, Finset.sum_div, mul_div_assoc]
    rw [e]
    exact div_ne_zero hb (hp k)
  have h1 := (hA α).fun_div (hA β) hden
  simp only [zero_mul, mul_zero, sub_zero, zero_div] at h1
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [hne] with s hs
  have e : ∀ γ : ρ k → ℂ, ∑ m, γ m * Z s ⟨k, m⟩ = Z s ⟨k, p k⟩ * ∑ m, γ m * affCoord p (Z s) ⟨k, m⟩ := fun γ => by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [affCoord]
    field_simp
  rw [e α, e β, mul_div_mul_left _ _ hs]

theorem comp_zero {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E'] [NormedSpace ℂ E']
    {A A' : Type} [Fintype A] [Fintype A'] {T : E → A → ℂ} {B : E' → A' → ℂ} {W : E →L[ℂ] E'} {e : A' → A}
    (h : ∀ w q, T w (e q) = B (W w) q) {D : E →L[ℂ] A → ℂ} {w v : E} (hD : HasFDerivAt T D w)
    (hB : DifferentiableAt ℂ B (W w)) (hv : D v = 0) : fderiv ℂ B (W w) (W v) = 0 := by
  have hcomp : HasFDerivAt (fun w' => B (W w')) ((fderiv ℂ B (W w)).comp W) w :=
    hB.hasFDerivAt.comp w W.hasFDerivAt
  funext q
  have e1 := hasFDerivAt_pi'.1 hcomp q
  have e2 := hasFDerivAt_pi'.1 hD (e q)
  have e3 : (fun w' => T w' (e q)) = fun w' => B (W w') q := funext fun w' => h w' q
  rw [e3] at e2
  have e4 := congrArg (fun L => L v) (e2.unique e1)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, hv] at e4
  exact e4.symm

end Gen

section Mat

variable {N : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem diff_prod {A : Type} (s : Finset A) {f : A → E → ℂ} {x : E} (h : ∀ i, DifferentiableAt ℂ (f i) x) :
    DifferentiableAt ℂ (fun w => ∏ i ∈ s, f i w) x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i).fun_mul ih

theorem diff_div {f g : E → ℂ} {x : E} (hf : DifferentiableAt ℂ f x) (hg : DifferentiableAt ℂ g x) (hx : g x ≠ 0) :
    DifferentiableAt ℂ (fun w => f w / g w) x := by
  simp only [div_eq_mul_inv]
  exact hf.fun_mul (hg.fun_inv hx)

theorem minorIJ_diff {A : E → Matrix (Fin N) (Fin N) ℂ} {x : E} (hA : ∀ a b, DifferentiableAt ℂ (fun w => A w a b) x)
    (I J : Finset (Fin N)) : DifferentiableAt ℂ (fun w => minorIJ (A w) I J) x := by
  unfold minorIJ
  split_ifs with e
  · have hP : ∀ σ : Equiv.Perm (Fin J.card), DifferentiableAt ℂ
        (fun w => ∏ i, A w (I.orderEmbOfFin e (σ i)) (J.orderEmbOfFin rfl i)) x := fun σ =>
      diff_prod _ fun i => hA _ _
    simp only [Matrix.det_apply', Matrix.submatrix_apply]
    exact DifferentiableAt.fun_sum fun σ _ => (hP σ).const_mul _
  · exact differentiableAt_const _

end Mat

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem stepOf_lastCol {a ca : Fin N} (hj : j ≤ N) (h : (ca : ℕ) = lastCol N j a) : stepOf N j ca = a := by
  apply Fin.ext
  have := a.2
  have := ca.2
  simp only [stepOf]
  simp only [lastCol] at h
  split_ifs at h ⊢ <;> omega

theorem twMinor_eq (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ)
    (i : Fin N) (k : K) (g : Matrix (Fin N) (Fin N) ℂ) (z : (Σ k, ι k) → ℂ) (J : Finset (Fin N)) :
    twMinor M F zb i k g z J = ∑ m : ι k,
      (∑ I ∈ Finset.univ.filter (IsStepRows N j i), minorIJ g J I * valAt M.x (F.u' I ⟨k, m⟩) zb) * z ⟨k, m⟩ := by
  simp only [twMinor, pluck, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun I _ => by ring

def twC (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ)
    (i : Fin N) (k : K) (g : Matrix (Fin N) (Fin N) ℂ) (J : Finset (Fin N)) (m : ι k) : ℂ :=
  ∑ I ∈ Finset.univ.filter (IsStepRows N j i), minorIJ g J I * valAt M.x (F.u' I ⟨k, m⟩) zb

theorem twMinor_fst (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ)
    (i : Fin N) (k k₀ : K) (g : Matrix (Fin N) (Fin N) ℂ) (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ)
    (J : Finset (Fin N)) :
    twMinor M F zb i k g (fstPt k₀ z) J = ∑ m : ι k, twC M F zb i k g J m * z ⟨some k, m⟩ :=
  twMinor_eq M F zb i k g _ J

theorem twMinor_snd (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ)
    (i : Fin N) (k₀ : K) (g : Matrix (Fin N) (Fin N) ℂ) (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ)
    (J : Finset (Fin N)) :
    twMinor M F zb i k₀ g (sndPt k₀ z) J = ∑ m : ι k₀, twC M F zb i k₀ g J m * z ⟨none, m⟩ := by
  rw [twMinor_eq]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [sndPt, Function.comp, v₁_self]
  rfl

theorem lowRead_some (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (z : (Σ k, ι k) → ℂ) {τ' : Ψ} (a' : Fin N) {b' : Fin N} {k : K}
    (hk : M.blk (τ', stepOf N j b') = some k) :
    lowRead M F zb h z τ' a' b' =
      twMinor M F zb (stepOf N j b') k (h τ')⁻¹ z (insert a' ((stepCols N j (stepOf N j b')).erase b')) /
        twMinor M F zb (stepOf N j b') k (h τ')⁻¹ z (stepCols N j (stepOf N j b')) := by
  unfold lowRead
  rw [hk]
  rfl

theorem lowRead_none (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (z : (Σ k, ι k) → ℂ) {τ' : Ψ} (a' : Fin N) {b' : Fin N}
    (hk : M.blk (τ', stepOf N j b') = none) : lowRead M F zb h z τ' a' b' = 0 := by
  unfold lowRead
  rw [hk]
  rfl

theorem fst_deriv (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) {k₀ : K} {Z : ℂ → (Σ o : Option K, ι (o.getD k₀)) → ℂ}
    {p : (o : Option K) → ι (o.getD k₀)} (hd : HasDerivAt (fun s => affCoord p (Z s)) 0 0)
    (hc : ∀ q, ContinuousAt (fun s => Z s q) 0) (hp : ∀ o, Z 0 ⟨o, p o⟩ ≠ 0) {τ' : Ψ} (a' : Fin N) {b' : Fin N} {k : K}
    (hk : M.blk (τ', stepOf N j b') = some k)
    (h0 : twMinor M F zb (stepOf N j b') k (h τ')⁻¹ (fstPt k₀ (Z 0)) (stepCols N j (stepOf N j b')) ≠ 0) :
    HasDerivAt (fun s => lowRead M F zb h (fstPt k₀ (Z s)) τ' a' b') 0 0 := by
  simp only [lowRead_some M F zb h _ a' hk, twMinor_fst]
  rw [twMinor_fst] at h0
  exact ratio_deriv (ρ := fun o : Option K => ι (o.getD k₀)) hd hc hp (some k) _ _ h0

theorem snd_deriv (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) {k₀ : K} {Z : ℂ → (Σ o : Option K, ι (o.getD k₀)) → ℂ}
    {p : (o : Option K) → ι (o.getD k₀)} (hd : HasDerivAt (fun s => affCoord p (Z s)) 0 0)
    (hc : ∀ q, ContinuousAt (fun s => Z s q) 0) (hp : ∀ o, Z 0 ⟨o, p o⟩ ≠ 0) {τ' : Ψ} (a' : Fin N) {b' : Fin N}
    (hk : M.blk (τ', stepOf N j b') = some k₀)
    (h0 : twMinor M F zb (stepOf N j b') k₀ (h τ')⁻¹ (sndPt k₀ (Z 0)) (stepCols N j (stepOf N j b')) ≠ 0) :
    HasDerivAt (fun s => lowRead M F zb h (sndPt k₀ (Z s)) τ' a' b') 0 0 := by
  simp only [lowRead_some M F zb h _ a' hk, twMinor_snd]
  rw [twMinor_snd] at h0
  exact ratio_deriv (ρ := fun o : Option K => ι (o.getD k₀)) hd hc hp none _ _ h0

theorem flagZ_base (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (zb : (Σ k, baseIdx ι M.blk k) → ℂ)
    (H : Ψ → Matrix (Fin N) (Fin N) ℂ) (k : NonPluckerBlocks M.blk) (m : ι k.1) :
    flagZ M F zb H ⟨k.1, m⟩ = zb ⟨k, m⟩ := by
  unfold flagZ
  rw [dif_neg fun ⟨p, hp⟩ => k.2 p hp]

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem flagZ_diff (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {zb : E → (Σ k, baseIdx ι M.blk k) → ℂ}
    {H : E → Ψ → Matrix (Fin N) (Fin N) ℂ} {x : E} (hz : ∀ q, DifferentiableAt ℂ (fun w => zb w q) x)
    (hv : ∀ q I, DifferentiableAt ℂ (fun w => valAt M.x (F.u q I) (zb w)) x)
    (hH : ∀ τ' a b, DifferentiableAt ℂ (fun w => H w τ' a b) x) (q : Σ k, ι k) :
    DifferentiableAt ℂ (fun w => flagZ M F (zb w) (H w) q) x := by
  unfold flagZ
  by_cases e : ∃ p, M.blk p = some q.1
  · simp only [dif_pos e]
    exact DifferentiableAt.fun_sum fun I _ => (hv q I).mul (minorIJ_diff (fun a b => hH _ a b) _ _)
  · simp only [dif_neg e]
    exact hz _

end Flag

section Main

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} {M : FlagModel y Ψ N j} {n d : ℕ}
  {Rb : AnLogRes (mCoordIdeal M.x) ⊤ n} {τ : Ψ} {a b : Fin N} {k₀ : K} {ca cb : Fin N}
  {F : FrameData ι Ψ N M.Ω M.blk} {kb : Fin Rb.A.n} {V : Set (Fin n → ℂ)}
  {bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ} {r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X}
  {h : Ψ → Matrix (Fin N) (Fin N) ℂ} {ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)}

theorem wB_diff (w : Fin (d + 2) → ℂ) : DifferentiableAt ℂ (wB ε) w :=
  differentiableAt_pi.2 fun _ => differentiableAt_apply _ _

theorem wPhi_diff (hc : IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h) {w : Fin (d + 2) → ℂ} (hw : w ∈ wD ε V)
    (q : Σ o : Option K, ι (o.getD k₀)) :
    DifferentiableAt ℂ (fun w' => wPhi M F bl h ε k₀ τ ca cb w' q) w := by
  have hb : IsBaseChart M Rb F kb V bl := hc.2.2.2.2.2.2.2.1
  have hz : ∀ q, DifferentiableAt ℂ (fun w' => bl (wB ε w') q) w := fun q =>
    DifferentiableAt.comp (g := fun u => bl u q) w (hb.2.2.1 q _ hw).differentiableAt (wB_diff w)
  have hv : ∀ q I, DifferentiableAt ℂ (fun w' => valAt M.x (F.u q I) (bl (wB ε w'))) w := fun q I =>
    DifferentiableAt.comp (g := fun u => valAt M.x (F.u q I) (bl u)) w (hb.2.2.2.1 q I _ hw).differentiableAt (wB_diff w)
  have hH : ∀ τ' a b, DifferentiableAt ℂ (fun w' => wH h ε τ' w' a b) w := fun τ' a' b' =>
    ((GlobalTheory.T.flag_adjacent_chart_second K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc).1 τ' a' b' w hw).differentiableAt
  have hT : DifferentiableAt ℂ (wT ε) w := differentiableAt_apply _ _
  obtain ⟨o, m⟩ := q
  cases o with
  | some k => exact flagZ_diff M F hz hv (H := fun w' τ' => wH h ε τ' w') hH ⟨k, m⟩
  | none =>
    refine flagZ_diff M F hz hv
      (H := fun w' => Function.update (fun τ' => wH h ε τ' w') τ (wH h ε τ w' * (1 + Matrix.single cb ca (wT ε w'))))
      (fun τ' a' b' => ?_) ⟨k₀, m⟩
    by_cases e : τ' = τ
    · subst e
      simp only [Function.update_self, Matrix.mul_apply]
      refine DifferentiableAt.fun_sum fun c _ => (hH _ _ _).fun_mul ?_
      simp only [Matrix.add_apply, Matrix.single_apply]
      refine (differentiableAt_const _).fun_add ?_
      split_ifs
      · exact hT
      · exact differentiableAt_const _
    · simp only [Function.update_of_ne e]
      exact hH _ _ _

theorem base_inj (hc : IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h) {u : Fin n → ℂ} (hu : u ∈ V)
    (pb : (k : NonPluckerBlocks M.blk) → baseIdx ι M.blk k) (hp : ∀ k, bl u ⟨k, pb k⟩ ≠ 0) :
    (fderiv ℂ (fun u' => affCoord pb (bl u')) u).ker = ⊥ := by
  have hb : IsBaseChart M Rb F kb V bl := hc.2.2.2.2.2.2.2.1
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

theorem wPhi_some (w' : Fin (d + 2) → ℂ) (k : K) (m : ι k) :
    wPhi M F bl h ε k₀ τ ca cb w' ⟨some k, m⟩ = flagZ M F (bl (wB ε w')) (fun τ' => wH h ε τ' w') ⟨k, m⟩ := rfl

theorem wPhi_base (w' : Fin (d + 2) → ℂ) (k : NonPluckerBlocks M.blk) (m : ι k.1) :
    wPhi M F bl h ε k₀ τ ca cb w' ⟨some k.1, m⟩ = bl (wB ε w') ⟨k, m⟩ :=
  (wPhi_some w' k.1 m).trans (flagZ_base M F (bl (wB ε w')) (fun τ' => wH h ε τ' w') k m)

theorem coord_base (p : (o : Option K) → ι (o.getD k₀)) (w' : Fin (d + 2) → ℂ) (q : Σ k, baseIdx ι M.blk k) :
    affCoord p (wPhi M F bl h ε k₀ τ ca cb w') ⟨some q.1.1, q.2⟩ =
      affCoord (fun k : NonPluckerBlocks M.blk => p (some k.1)) (bl (wB ε w')) q := by
  obtain ⟨k, m⟩ := q
  simp only [affCoord]
  rw [wPhi_base, wPhi_base]

theorem base_zero (hc : IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h) {w : Fin (d + 2) → ℂ} (hw : w ∈ wD ε V)
    (p : (o : Option K) → ι (o.getD k₀)) (hp : ∀ o, wPhi M F bl h ε k₀ τ ca cb w ⟨o, p o⟩ ≠ 0)
    {D : (Fin (d + 2) → ℂ) →L[ℂ] (Σ o : Option K, ι (o.getD k₀)) → ℂ}
    (hD : HasFDerivAt (fun w' => affCoord p (wPhi M F bl h ε k₀ τ ca cb w')) D w)
    {v : Fin (d + 2) → ℂ} (hv : D v = 0) : wB ε v = 0 := by
  have hb : IsBaseChart M Rb F kb V bl := hc.2.2.2.2.2.2.2.1
  have hne : ∀ k : NonPluckerBlocks M.blk, bl (wB ε w) ⟨k, p (some k.1)⟩ ≠ 0 := fun k => by
    have := hp (some k.1)
    rwa [wPhi_base] at this
  have hbd : ∀ q, DifferentiableAt ℂ (fun u => bl u q) (wB ε w) := fun q =>
    (hb.2.2.1 q _ hw).differentiableAt
  have hB : DifferentiableAt ℂ (fun u' => affCoord (fun k : NonPluckerBlocks M.blk => p (some k.1)) (bl u')) (wB ε w) :=
    differentiableAt_pi.2 fun q => diff_div (hbd q) (hbd _) (hne q.1)
  have hinj := base_inj hc hw (fun k : NonPluckerBlocks M.blk => p (some k.1)) hne
  have hz := comp_zero (W := ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (ε (Sum.inl i)))
    (e := fun q : Σ k, baseIdx ι M.blk k => (⟨some q.1.1, q.2⟩ : Σ o : Option K, ι (o.getD k₀)))
    (fun w' q => coord_base p w' q) hD hB hv
  have hm : wB ε v ∈ (fderiv ℂ (fun u' => affCoord (fun k : NonPluckerBlocks M.blk => p (some k.1)) (bl u')) (wB ε w)).ker := hz
  rw [hinj] at hm
  exact hm

theorem line_zero (hc : IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h) {w : Fin (d + 2) → ℂ} (hw : w ∈ wD ε V)
    (p : (o : Option K) → ι (o.getD k₀)) (hp : ∀ o, wPhi M F bl h ε k₀ τ ca cb w ⟨o, p o⟩ ≠ 0)
    {D : (Fin (d + 2) → ℂ) →L[ℂ] (Σ o : Option K, ι (o.getD k₀)) → ℂ}
    (hD : HasFDerivAt (fun w' => affCoord p (wPhi M F bl h ε k₀ τ ca cb w')) D w)
    {v : Fin (d + 2) → ℂ} (hv : D v = 0) (hb0 : wB ε v = 0) : v = 0 := by
  have hE := GlobalTheory.T.flag_adjacent_chart_second K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
  have hR := GlobalTheory.T.flag_adjacent_chart_fourth K ι Φ y Ψ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc
  have hwB : ∀ s : ℂ, wB ε (w + s • v) = wB ε w := fun s => by
    funext i
    have : v (ε (Sum.inl i)) = 0 := congrFun hb0 i
    simp [wB, this]
  have hmem : ∀ s : ℂ, w + s • v ∈ wD ε V := fun s => by
    show wB ε (w + s • v) ∈ V
    rw [hwB]
    exact hw
  have hcurve : HasDerivAt (fun s : ℂ => w + s • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add w
  have h00 : w = (fun s : ℂ => w + s • v) 0 := by simp
  have hdZ : HasDerivAt (fun s : ℂ => affCoord p (wPhi M F bl h ε k₀ τ ca cb (w + s • v))) 0 0 := by
    have := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hD hcurve h00
    rw [hv] at this
    exact this
  have hcZ : ∀ q, ContinuousAt (fun s : ℂ => wPhi M F bl h ε k₀ τ ca cb (w + s • v) q) 0 := fun q =>
    ContinuousAt.comp_of_eq (g := fun w' => wPhi M F bl h ε k₀ τ ca cb w' q) (wPhi_diff hc hw q).continuousAt
      hcurve.continuousAt h00.symm
  have hZ0 : wPhi M F bl h ε k₀ τ ca cb (w + (0 : ℂ) • v) = wPhi M F bl h ε k₀ τ ca cb w := by simp
  have hp0 : ∀ o, wPhi M F bl h ε k₀ τ ca cb (w + (0 : ℂ) • v) ⟨o, p o⟩ ≠ 0 := fun o => by
    rw [hZ0]
    exact hp o
  have hO := (hR w hw).1
  have hbw : baseOf M k₀ (wPhi M F bl h ε k₀ τ ca cb w) = bl (wB ε w) := (hE.2 w hw).2.1
  have hfst : ∀ (p' : Ψ × Fin N) (k : K), M.blk p' = some k → twMinor M F (bl (wB ε w)) p'.2 k (h p'.1)⁻¹
      (fstPt k₀ (wPhi M F bl h ε k₀ τ ca cb (w + (0 : ℂ) • v))) (stepCols N j p'.2) ≠ 0 := fun p' k hk => by
    have := hO.2.2.2.1 p' k hk
    rw [hbw] at this
    rw [hZ0]
    exact this
  have hsnd : twMinor M F (bl (wB ε w)) a k₀ (h τ)⁻¹
      (sndPt k₀ (wPhi M F bl h ε k₀ τ ca cb (w + (0 : ℂ) • v))) (stepCols N j a) ≠ 0 := by
    have := hO.2.2.2.2
    rw [hbw] at this
    rw [hZ0]
    exact this
  have hbase : ∀ s : ℂ, baseOf M k₀ (wPhi M F bl h ε k₀ τ ca cb (w + s • v)) = bl (wB ε w) := fun s => by
    rw [(hE.2 _ (hmem s)).2.1, hwB]
  have hlin : ∀ i, HasDerivAt (fun s : ℂ => w i + s * v i) (v i) 0 := fun i => by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const (v i)).const_add (w i)
  have hlow : ∀ q : LowIdx Ψ N j, v (ε (Sum.inr (Sum.inl q))) = 0 := fun q => by
    have hrel : ∀ s : ℂ, lowRead M F (bl (wB ε w)) h (fstPt k₀ (wPhi M F bl h ε k₀ τ ca cb (w + s • v)))
        q.1.1 q.1.2.1 q.1.2.2 = w (ε (Sum.inr (Sum.inl q))) + s * v (ε (Sum.inr (Sum.inl q))) := fun s => by
      have := congrFun (hR _ (hmem s)).2 (ε (Sum.inr (Sum.inl q)))
      simp only [wRho, Equiv.symm_apply_apply] at this
      rw [hbase s] at this
      simpa using this
    cases hk : M.blk (q.1.1, stepOf N j q.1.2.2) with
    | none =>
      have e0 := hrel 0
      have e1 := hrel 1
      rw [lowRead_none M F _ h _ _ hk] at e0 e1
      simp only [zero_mul, add_zero, one_mul] at e0 e1
      rw [← e0, zero_add] at e1
      exact e1.symm
    | some k =>
      have h1 := fst_deriv M F (bl (wB ε w)) h (Z := fun s : ℂ => wPhi M F bl h ε k₀ τ ca cb (w + s • v)) hdZ hcZ hp0
        (τ' := q.1.1) (b' := q.1.2.2) q.1.2.1 hk (hfst (q.1.1, stepOf N j q.1.2.2) k hk)
      rw [funext hrel] at h1
      exact (hlin _).unique h1
  have hst : stepOf N j ca = a := stepOf_lastCol M.j_le hc.2.2.2.1
  have hk₀ : M.blk (τ, stepOf N j ca) = some k₀ := by
    rw [hst]
    exact hc.2.2.1
  have ht : v (ε (Sum.inr (Sum.inr ()))) = 0 := by
    have hrel : ∀ s : ℂ, lowRead M F (bl (wB ε w)) h (sndPt k₀ (wPhi M F bl h ε k₀ τ ca cb (w + s • v))) τ cb ca -
        lowRead M F (bl (wB ε w)) h (fstPt k₀ (wPhi M F bl h ε k₀ τ ca cb (w + s • v))) τ cb ca =
        w (ε (Sum.inr (Sum.inr ()))) + s * v (ε (Sum.inr (Sum.inr ()))) := fun s => by
      have := congrFun (hR _ (hmem s)).2 (ε (Sum.inr (Sum.inr ())))
      simp only [wRho, Equiv.symm_apply_apply] at this
      rw [hbase s] at this
      simpa using this
    have h1 := snd_deriv M F (bl (wB ε w)) h (Z := fun s : ℂ => wPhi M F bl h ε k₀ τ ca cb (w + s • v)) hdZ hcZ hp0
      (τ' := τ) (b' := ca) cb hk₀ (by rw [hst]; exact hsnd)
    have h2 := fst_deriv M F (bl (wB ε w)) h (Z := fun s : ℂ => wPhi M F bl h ε k₀ τ ca cb (w + s • v)) hdZ hcZ hp0
      (τ' := τ) (b' := ca) cb hk₀ (hfst (τ, stepOf N j ca) k₀ hk₀)
    have h3 := h1.fun_sub h2
    rw [funext hrel, sub_zero] at h3
    exact (hlin _).unique h3
  funext i
  obtain ⟨x, rfl⟩ := ε.surjective i
  rcases x with l | q | u
  · exact congrFun hb0 l
  · exact hlow q
  · exact ht

theorem chart_immersion : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ w ∈ wD ε V, ∀ p : (o : Option K) → ι (o.getD k₀), (∀ o, wPhi M F bl h ε k₀ τ ca cb w ⟨o, p o⟩ ≠ 0) → (fderiv ℂ (fun w' => affCoord p (wPhi M F bl h ε k₀ τ ca cb w')) w).ker = ⊥ := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hc w hw p hp
  have hT : DifferentiableAt ℂ (fun w' => affCoord p (wPhi M F bl h ε k₀ τ ca cb w')) w :=
    differentiableAt_pi.2 fun q => diff_div (wPhi_diff hc hw q) (wPhi_diff hc hw _) (hp q.1)
  rw [eq_bot_iff]
  intro v hv
  have hv' : fderiv ℂ (fun w' => affCoord p (wPhi M F bl h ε k₀ τ ca cb w')) w v = 0 := hv
  exact (Submodule.mem_bot ℂ).2
    (line_zero hc hw p hp hT.hasFDerivAt hv' (base_zero hc hw p hp hT.hasFDerivAt hv'))

end Main

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Imm
