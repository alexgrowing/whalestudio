import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.WordSpan
import Development.WeilBound.CoreStatements.BranchingTraces.ExistsIntertwiner
import Development.WeilBound.CoreStatements.OrbitDecayEstimates.CurveDerivativeDecay.LipschitzEstimate

noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgHe.SM.LowWeightDensity

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition Formalism.FourierDecayAlt.P.CapelliAbstractCharacter CompanionTheory.D.DSIC

theorem signs {n : ℕ} {ε : Fin (n + 1) → Bool} {lam : Fin (n + 1) → ℝ} {ε' : Fin n → Bool} {mu : Fin n → ℝ}
    {e : Fin n ⊕ Unit ≃ Fin (n + 1)} (hG : Gp ε lam ε' mu e) : (∃ a, ε' a = false) ∧ (∃ a, ε' a = true) := by
  obtain ⟨hfit, hε'⟩ := hG.fits
  have key0 : ∀ x, x ≠ zi e → ∃ c, x = e (Sum.inl c) := by
    intro x hx
    rcases hb : e.symm x with c | u
    · exact ⟨c, (Equiv.symm_apply_eq e).1 hb⟩
    · cases u
      exact absurd ((Equiv.symm_apply_eq e).1 hb) hx
  refine ⟨?_, ?_⟩
  · obtain ⟨a, ha⟩ := hG.neg
    by_cases hz : a = zi e
    · rw [hz, hfit] at ha
      exact absurd ha (by decide)
    · obtain ⟨c, rfl⟩ := key0 a hz
      exact ⟨c, by rw [← hε' c]; exact ha⟩
  · by_contra hno
    push_neg at hno
    have key : ∀ x, x ≠ zi e → ε x = false := by
      intro x hx
      obtain ⟨c, rfl⟩ := key0 x hx
      rw [hε' c]
      simpa using hno c
    have h1 : #{a : Fin (n + 1) | ε a = true} ≤ 1 := by
      apply Finset.card_le_one.2
      intro x hx y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      have hx2 : x = zi e := by
        by_contra h'
        rw [key x h'] at hx
        exact absurd hx (by decide)
      have hy2 : y = zi e := by
        by_contra h'
        rw [key y h'] at hy
        exact absurd hy (by decide)
      rw [hx2, hy2]
    have hsub : Finset.univ.erase (zi e) ⊆ Finset.filter (fun a => ε a = false) Finset.univ := by
      intro x hx
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact key x hx
    have h2 := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at h2
    have h3 := hG.le
    have h4 := hG.two
    simp only [Nat.add_sub_cancel] at h2
    omega

theorem exists_ds {m : ℕ} (ε : Fin m → Bool) (lam : Fin m → ℝ) (hm : 1 ≤ m) (hc : Formalism.QuantumDeterminants.IsHCParam lam)
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam (200 * (m : ℝ) ^ 3)) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (σ : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)),
      IsDS ε lam σ := by
  have hq : (ReciprocityTheory.ChartRestriction.DS.S7.q0 ε : ℝ) ≤ m := by
    have : ReciprocityTheory.ChartRestriction.DS.S7.q0 ε ≤ m := by
      unfold ReciprocityTheory.ChartRestriction.DS.S7.q0 ReciprocityTheory.ChartRestriction.DS.pOf
      exact (min_le_left _ _).trans ((Finset.card_filter_le _ _).trans (by simp))
    exact_mod_cast this
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h2 : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
  have h3 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 3 := by nlinarith
  have h4 : (8 * (m : ℝ)) * ReciprocityTheory.ChartRestriction.DS.S7.q0 ε ≤ (8 * (m : ℝ)) * m :=
    mul_le_mul_of_nonneg_left hq (by positivity)
  refine ReciprocityTheory.ChartRestriction.DS.G2.discrete_series_exists_large_gap m ε lam hc _ hg (Or.inr ?_)
  rw [max_lt_iff]
  constructor
  · nlinarith
  · nlinarith

theorem exists_ne {m : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)} (hσ : IsDS ε lam σ) : ∃ v ∈ lowKSub ε lam σ, v ≠ 0 := by
  obtain ⟨S0, hS0⟩ := hσ.2.2.2.2.2.1
  obtain ⟨v, hv, hv0, -⟩ := hS0.2.2.2.1
  have hle : S0 ≤ lowKSub ε lam σ := le_sSup (s := {S | IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S}) hS0
  exact ⟨v, hle hv, hv0⟩

theorem exists_low {m : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)} (hσ : IsDS ε lam σ) : ∃ w ∈ lowKSub ε lam σ, ‖w‖ = 1 := by
  obtain ⟨v, hv, hv0⟩ := exists_ne hσ
  refine ⟨((‖v‖ : ℂ)⁻¹) • v, Submodule.smul_mem _ _ hv, ?_⟩
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv0
  rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_cancel₀ hn]

theorem exists_P {n : ℕ} {ε : Fin (n + 1) → Bool} {ε' : Fin n → Bool} {e : Fin n ⊕ Unit ≃ Fin (n + 1)} {lam : Fin (n + 1) → ℝ}
    {mu : Fin n → ℝ} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [NormedAddCommGroup H']
    [InnerProductSpace ℂ H'] [CompleteSpace H'] {π : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ → (H →L[ℂ] H)}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')} (hF : Fits ε ε' e) (hπ : IsDS ε lam π) (hσ : IsDS ε' mu σ)
    {j : H' →L[ℂ] H} (hj : j ≠ 0) (hjm : IsHMap ε' e π σ j) : ∃ P : H →L[ℂ] H', Intertw ε' e π σ P ∧ P ≠ 0 := by
  obtain ⟨-, -, hπU, -⟩ := hπ
  obtain ⟨-, -, hσU, -⟩ := hσ
  have memG : ∀ h : UJ ε', emb e (um h) ∈ PI.UpqRep.UJset ε := fun h =>
    PositivityTheory.UnitaryDecomposition.Com.emb_mem hF h.2
  have memH : ∀ h : UJ ε', um h ∈ PI.UpqRep.UJset ε' := fun h => h.2
  have embmul : ∀ A B : Matrix (Fin n) (Fin n) ℂ, emb e A * emb e B = emb e (A * B) := by
    intro A B
    simp only [emb, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp
  have emb1 : emb e 1 = 1 := by
    simp [emb]
  have huinv : ∀ h : UJ ε', um h * um h⁻¹ = 1 := by
    intro h
    simp [um]
  have hπinner : ∀ h : UJ ε', ∀ (u x : H),
      ⟪π (emb e (um h⁻¹)) u, x⟫_ℂ = ⟪u, π (emb e (um h)) x⟫_ℂ := by
    intro h u x
    have hmul := hπU.1.2 _ (memG h) _ (memG h⁻¹)
    rw [embmul, huinv, emb1, hπU.1.1] at hmul
    have hcomp : π (emb e (um h)) (π (emb e (um h⁻¹)) u) = u := by
      have h2 := congrArg (fun T : H →L[ℂ] H => T u) hmul
      simpa using h2.symm
    let L : H →ₗᵢ[ℂ] H := ⟨(π (emb e (um h))).toLinearMap, hπU.2.1 _ (memG h)⟩
    calc ⟪π (emb e (um h⁻¹)) u, x⟫_ℂ = ⟪L (π (emb e (um h⁻¹)) u), L x⟫_ℂ := (L.inner_map_map _ _).symm
      _ = ⟪u, π (emb e (um h)) x⟫_ℂ := by
        show ⟪π (emb e (um h)) (π (emb e (um h⁻¹)) u), π (emb e (um h)) x⟫_ℂ = _
        rw [hcomp]
  have hσinner : ∀ h : UJ ε', ∀ (y z : H'),
      ⟪σ (um h⁻¹) y, z⟫_ℂ = ⟪y, σ (um h) z⟫_ℂ := by
    intro h y z
    have hmul := hσU.1.2 _ (memH h) _ (memH h⁻¹)
    rw [huinv, hσU.1.1] at hmul
    have hcomp : σ (um h) (σ (um h⁻¹) y) = y := by
      have h2 := congrArg (fun T : H' →L[ℂ] H' => T y) hmul
      simpa using h2.symm
    let L : H' →ₗᵢ[ℂ] H' := ⟨(σ (um h)).toLinearMap, hσU.2.1 _ (memH h)⟩
    calc ⟪σ (um h⁻¹) y, z⟫_ℂ = ⟪L (σ (um h⁻¹) y), L z⟫_ℂ := (L.inner_map_map _ _).symm
      _ = ⟪y, σ (um h) z⟫_ℂ := by
        show ⟪σ (um h) (σ (um h⁻¹) y), σ (um h) z⟫_ℂ = _
        rw [hcomp]
  have hjn : ‖j‖ ≠ 0 := norm_ne_zero_iff.2 hj
  have hadj : ∀ (h : UJ ε') (x : H),
      ContinuousLinearMap.adjoint j (π (emb e (um h)) x) = σ (um h) (ContinuousLinearMap.adjoint j x) := by
    intro h x
    apply ext_inner_left ℂ
    intro y
    rw [ContinuousLinearMap.adjoint_inner_right, ← hπinner, ← hjm h⁻¹ y,
      ← ContinuousLinearMap.adjoint_inner_right, hσinner]
  refine ⟨((‖j‖ : ℂ)⁻¹) • ContinuousLinearMap.adjoint j, ⟨?_, ?_⟩, ?_⟩
  · rw [norm_smul, norm_inv, Complex.norm_real, norm_norm, LinearIsometryEquiv.norm_map,
      inv_mul_cancel₀ hjn]
  · intro h x
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.map_smul, hadj]
  · intro h0
    have hc : ((‖j‖ : ℂ)⁻¹) ≠ 0 := inv_ne_zero (by exact_mod_cast hjn)
    have h1 : ContinuousLinearMap.adjoint j = 0 := by
      have := congrArg (fun T => ((‖j‖ : ℂ)) • T) h0
      simpa [smul_smul, hc] using this
    apply hj
    rw [← ContinuousLinearMap.adjoint_adjoint j, h1, map_zero]

theorem dense_sm {m : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)} {S : Submodule ℂ H} {E : Fin m → Fin m → Module.End ℂ S} (hm : 2 ≤ m)
    (hc : Formalism.QuantumDeterminants.IsHCParam lam) (hσ : IsDS ε lam σ) (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam (100 * (m : ℝ) ^ 3))
    (hS : IsSmMod ε σ S E) : Dense (S : Set H) := by
  obtain ⟨hcs, -, hU, hI, -, ⟨K, hK⟩, -⟩ := hσ
  haveI := hcs
  obtain ⟨v, hvK, hv0, -⟩ := hK.2.2.2.1
  have hvS : v ∈ S :=
    (hS.mem v).2 (CompanionTheory.D.gk.admitted.kFin_mem_smoothVecs m ε H σ hU hI v ⟨K, hK.1, hvK, hK.2.1⟩)
  have hstab : ∀ g ∈ PI.UpqRep.UJset ε, ∀ w ∈ S.topologicalClosure, σ g w ∈ S.topologicalClosure := by
    intro g hg w hw
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hw ⊢
    exact map_mem_closure (σ g).continuous hw (fun x hx => hS.stab g hg x hx)
  rcases hI S.topologicalClosure S.isClosed_topologicalClosure hstab with h | h
  · have hv' : v ∈ S.topologicalClosure := S.le_topologicalClosure hvS
    rw [h, Submodule.mem_bot] at hv'
    exact absurd hv' hv0
  · exact Submodule.dense_iff_topologicalClosure_eq_top.2 h

theorem one_le_hs' {m : ℕ} {ε : Fin m → Bool} (g : UJ ε) (j : Fin m) : 1 ≤ hs (um g) := by
  exact ReciprocityTheory.ChartRestriction.DS.sigZeroDecay_one_le_hs g.2 j

theorem decay_low {n : ℕ} {ε' : Fin n → Bool} {mu : Fin n → ℝ} {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] {σ : Matrix (Fin n) (Fin n) ℂ → (K →L[ℂ] K)} (hn : 1 ≤ n) (hc : Formalism.QuantumDeterminants.IsHCParam mu) (hσ : IsDS ε' mu σ)
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε' mu (200 * ((n : ℝ) + 1) ^ 3)) {w : K} (hw : w ∈ lowKSub ε' mu σ) (hw1 : ‖w‖ = 1) :
    Continuous (fun h : UJ ε' => conj ⟪w, σ (um h) w⟫_ℂ) ∧ ∃ C : ℝ, ∀ h : UJ ε',
      ‖conj ⟪w, σ (um h) w⟫_ℂ‖ ≤ C * hs (um h) ^ (-((n : ℝ) ^ 2 + 1 + (n : ℝ))) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨-, -, hU, -⟩ := hσ
    have h1 : Continuous (fun h : UJ ε' => um h) :=
      Units.continuous_val.comp continuous_subtype_val
    have hcont : Continuous (fun h : UJ ε' => σ (um h) w) :=
      (hU.2.2 w).comp_continuous h1 (fun h => h.2)
    exact (continuous_const.inner hcont).star
  · set N : ℕ := n ^ 2 + 1 + n with hN
    refine ⟨(Real.exp 1 * √(n : ℝ)) ^ (2 * N), fun h => ?_⟩
    have hA : 2 * N ≤ 12 * (n + 1) ^ 2 := by
      rw [hN]
      nlinarith
    have hb := CompanionTheory.Lime.T3.dec_low (N := n + 1) hn (by omega) hc hσ (by push_cast; exact hg) hw hw1
      (A := 2 * N) (by omega) hA h
    have hpos : 0 ≤ hs (um h) := le_trans zero_le_one (one_le_hs' h ⟨0, hn⟩)
    have hexp : ((n : ℝ) ^ 2 + 1 + n) = (N : ℝ) := by
      rw [hN]
      push_cast
      ring
    have key : (CompanionTheory.Lime.T3.nG h)⁻¹ ^ (2 * N) = hs (um h) ^ (-((n : ℝ) ^ 2 + 1 + n)) := by
      rw [pow_mul, inv_pow, CompanionTheory.Lime.T3.nG_sq, hexp, Real.rpow_neg hpos, Real.rpow_natCast, inv_pow]
    rw [RCLike.norm_conj, ← key]
    exact hb

end PositivityTheory.RgHe.SM.LowWeightDensity
