import Development.WeilBound.CoreStatements.OrbitDecayEstimates.CurveDerivativeDecay.HasDerivAtCurve

noncomputable section

open Matrix Finset MeasureTheory Formalism.REAL Formalism.MainNotions.S Filter Topology
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.Lime.T3

open ReciprocityTheory.ChartRestriction.DS (smD smE actM dS IsSmoothVecU mem_smD_iff isDerivedOn_smE dS_eq_actM)

theorem interp {f f' : ℝ → ℂ} (hf : ∀ s, HasDerivAt f (f' s) s) {M η τ a : ℝ} (hM : 0 ≤ M)
    (hL : ∀ s t, ‖f' s - f' t‖ ≤ M * |s - t|) (hη : ∀ s ∈ Set.Icc (0 : ℝ) 2, ‖f s‖ ≤ η) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) : ‖f a - f 0‖ ≤ (2 * η / τ + M * τ) * a := by
  obtain ⟨ha0, ha1⟩ := ha
  have key : ∀ s ∈ Set.Icc (0:ℝ) 1, ‖f' s‖ ≤ 2 * η / τ + M * τ := by
    intro s hs
    obtain ⟨hs0, hs1⟩ := hs
    have hg : ∀ t ∈ Set.Icc (0:ℝ) τ, HasDerivWithinAt (fun t : ℝ => f (s + t) - (t : ℂ) * f' s)
        (f' (s + t) - f' s) (Set.Icc 0 τ) t := by
      intro t _
      have h1 : HasDerivAt (fun t : ℝ => f (s + t)) (f' (s + t)) t := by
        have := (hf (s + t)).scomp t ((hasDerivAt_id' t).const_add s)
        simpa [Function.comp_def] using this
      have h2 : HasDerivAt (fun t : ℝ => (t : ℂ) * f' s) (f' s) t := by
        have := (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const (f' s)
        simpa using this
      exact (h1.sub h2).hasDerivWithinAt
    have hb : ∀ t ∈ Set.Ico (0:ℝ) τ, ‖f' (s + t) - f' s‖ ≤ M * τ := by
      intro t ht
      calc ‖f' (s + t) - f' s‖ ≤ M * |s + t - s| := hL _ _
        _ ≤ M * τ := by
          apply mul_le_mul_of_nonneg_left _ hM
          rw [add_sub_cancel_left, abs_of_nonneg ht.1]
          exact ht.2.le
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment' hg hb τ ⟨hτ.le, le_rfl⟩
    simp only [Complex.ofReal_zero, zero_mul, sub_zero, add_zero] at hmv
    have e1 := hη (s + τ) ⟨by linarith, by linarith⟩
    have e2 := hη s ⟨hs0, by linarith⟩
    have htri : ‖(τ : ℂ) * f' s‖ ≤ ‖f (s + τ) - (τ:ℂ) * f' s - f s‖ + ‖f (s + τ)‖ + ‖f s‖ := by
      calc ‖(τ : ℂ) * f' s‖ = ‖-(f (s + τ) - (τ:ℂ) * f' s - f s) + f (s + τ) - f s‖ := by
            congr 1
            ring
        _ ≤ ‖-(f (s + τ) - (τ:ℂ) * f' s - f s) + f (s + τ)‖ + ‖f s‖ := norm_sub_le _ _
        _ ≤ ‖-(f (s + τ) - (τ:ℂ) * f' s - f s)‖ + ‖f (s + τ)‖ + ‖f s‖ := by
          gcongr
          exact norm_add_le _ _
        _ = _ := by rw [norm_neg]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hτ.le] at htri
    rw [div_add' _ _ _ hτ.ne', le_div_iff₀ hτ]
    nlinarith
  have hg2 : ∀ x ∈ Set.Icc (0:ℝ) a, HasDerivWithinAt f (f' x) (Set.Icc 0 a) x :=
    fun x _ => (hf x).hasDerivWithinAt
  have hb2 : ∀ x ∈ Set.Ico (0:ℝ) a, ‖f' x‖ ≤ 2 * η / τ + M * τ :=
    fun x hx => key x ⟨hx.1, by linarith [hx.2]⟩
  have hfin := norm_image_sub_le_of_norm_deriv_le_segment' hg2 hb2 a ⟨ha0, le_rfl⟩
  simpa using hfin

variable {m : ℕ} {ε : Fin m → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {π : Matrix (Fin m) (Fin m) ℂ → (H →L[ℂ] H)}

theorem orbit_deriv (hπ : IsURepOn (UJset ε) π) (x : smD ε π) {c : ℝ → UJ ε} {Z : Matrix (Fin m) (Fin m) ℂ}
    (h0 : c 0 = 1) (hadd : ∀ s t, c (s + t) = c s * c t) (hc : HasDerivAt (fun t => uMat (c t)) Z 0) (s : ℝ) :
    HasDerivAt (fun t : ℝ => π (uMat (c t)) (x : H)) (π (uMat (c s)) (actM (smE ε π) Z x : smD ε π)) s := by
  have mem : ∀ h : UJ ε, uMat h ∈ UJset ε := fun h => h.2
  have hu0 : uMat (c 0) = 1 := by
    rw [h0]
    rfl
  have hd0 : HasDerivAt (fun t : ℝ => π (uMat (c t)) (x : H)) (actM (smE ε π) Z x : smD ε π) 0 := by
    have hev : ∀ᶠ t : ℝ in 𝓝 0, inUJ ε (uMat (c t)) := Filter.Eventually.of_forall fun t => (c t).2
    have h1 := hasDerivAt_curve hπ x.2 hu0 hc hev
    rwa [dS_eq_actM (isDerivedOn_smE hπ) (inG_of_curve hu0 hc hev) x] at h1
  set L := π (uMat (c s)) with hL
  have h4 : HasDerivAt (fun t : ℝ => π (uMat (c t)) (x : H)) (actM (smE ε π) Z x : smD ε π) (s - s) := by
    rw [sub_self]
    exact hd0
  have h2 : HasDerivAt (fun t : ℝ => L (π (uMat (c (t - s))) (x : H)))
      (L (actM (smE ε π) Z x : smD ε π)) s := by
    have h3 := (L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (s - s) h4
    exact h3.comp_sub_const s s
  convert h2 using 1
  funext t
  have e : c t = c s * c (t - s) := by
    rw [← hadd]
    congr 1
    ring
  show π (uMat (c t)) (x : H) = L (π (uMat (c (t - s))) x)
  rw [e, show uMat (c s * c (t - s)) = uMat (c s) * uMat (c (t - s)) from rfl,
    hπ.1.2 _ (mem _) _ (mem _)]
  rfl

theorem coef_interp (hπ : IsURepOn (UJset ε) π) (x : smD ε π) {c : ℝ → UJ ε} {Z : Matrix (Fin m) (Fin m) ℂ}
    (h0 : c 0 = 1) (hadd : ∀ s t, c (s + t) = c s * c t) (hc : HasDerivAt (fun t => uMat (c t)) Z 0) {u : H}
    (hu : ‖u‖ ≤ 1) {M η τ a : ℝ} (hM : ‖actM (smE ε π) Z (actM (smE ε π) Z x)‖ ≤ M)
    (hη : ∀ s ∈ Set.Icc (0 : ℝ) 2, ‖⟪π (uMat (c s)) (x : H), u⟫_ℂ‖ ≤ η) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    ‖⟪π (uMat (c a)) (x : H), u⟫_ℂ - ⟪π (uMat (c 0)) (x : H), u⟫_ℂ‖ ≤ (2 * η / τ + M * τ) * a := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  set y : smD ε π := actM (smE ε π) Z x with hy
  have hF : ∀ s, HasDerivAt (fun t : ℝ => π (uMat (c t)) (x : H)) (π (uMat (c s)) (y : H)) s :=
    orbit_deriv hπ x h0 hadd hc
  have hG : ∀ s, HasDerivAt (fun t : ℝ => π (uMat (c t)) (y : H))
      (π (uMat (c s)) (actM (smE ε π) Z y : H)) s :=
    orbit_deriv hπ y h0 hadd hc
  have hf : ∀ s, HasDerivAt (fun t : ℝ => ⟪π (uMat (c t)) (x : H), u⟫_ℂ)
      ⟪π (uMat (c s)) (y : H), u⟫_ℂ s := by
    intro s
    have h1 := (hF s).inner ℂ (hasDerivAt_const s u)
    simpa using h1
  have hL : ∀ s t, ‖⟪π (uMat (c s)) (y : H), u⟫_ℂ - ⟪π (uMat (c t)) (y : H), u⟫_ℂ‖ ≤ M * |s - t| := by
    intro s t
    rw [← inner_sub_left]
    have hmv : ‖π (uMat (c s)) (y : H) - π (uMat (c t)) (y : H)‖ ≤ M * ‖s - t‖ := by
      apply Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (fun r _ => (hG r).hasDerivWithinAt) _
        convex_univ (Set.mem_univ _) (Set.mem_univ _)
      intro r _
      rw [hπ.2.1 _ (c r).2 _]
      exact hM
    rw [Real.norm_eq_abs] at hmv
    calc _ ≤ ‖π (uMat (c s)) (y : H) - π (uMat (c t)) (y : H)‖ * ‖u‖ := norm_inner_le_norm _ _
      _ ≤ M * |s - t| * 1 := mul_le_mul hmv hu (norm_nonneg _) (mul_nonneg hM0 (abs_nonneg _))
      _ = M * |s - t| := mul_one _
  exact interp hf hM0 hL hη hτ hτ1 ha

theorem inner_move (hπ : IsURepOn (UJset ε) π) (g k : UJ ε) (a b : H) :
    ⟪π (uMat g) a, π (uMat k) b⟫_ℂ = ⟪a, π (uMat (g⁻¹ * k)) b⟫_ℂ := by
  have mem : ∀ h : UJ ε, uMat h ∈ UJset ε := fun h => h.2
  have hk : uMat k = uMat g * uMat (g⁻¹ * k) := by
    have e : k = g * (g⁻¹ * k) := (mul_inv_cancel_left g k).symm
    conv_lhs => rw [e]
    rfl
  rw [hk, hπ.1.2 _ (mem g) _ (mem _), ContinuousLinearMap.comp_apply]
  let L : H →ₗᵢ[ℂ] H := { toLinearMap := (π (uMat g)).toLinearMap, norm_map' := hπ.2.1 _ (mem g) }
  exact L.inner_map_map a _

theorem low_bounds {lam : Fin m → ℝ} {B : ℝ} (hm : 2 ≤ m) (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hDS : IsDS ε lam π)
    (hB : ∀ a, |lam a| ≤ B) (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam (100 * (m : ℝ) ^ 3)) {v : H} (hv : v ∈ lowKSub ε lam π)
    (hv1 : ‖v‖ = 1) : ∃ x : smD ε π, (x : H) = v ∧ (∀ X, hs X ≤ 1 → ‖actM (smE ε π) X x‖ ≤ 8 * Real.sqrt m * (B + 2)) ∧
      ∀ Z, ‖actM (smE ε π) Z (actM (smE ε π) Z x)‖ ≤ hs Z * (8 * Real.sqrt m * (B + 2)) ^ 2 := by
  obtain ⟨hv_s, hW⟩ := kFiniteWordBound_indefUnitary m ε lam B H π hm hl hDS hB hg v hv
  have hπ : IsURepOn (UJset ε) π := hDS.2.2.1
  have hsm : v ∈ smD ε π := by
    rw [mem_smD_iff]
    intro g₀ hg₀
    obtain ⟨U, F, hU, hgU, hF, hfe⟩ := hv_s g₀ hg₀
    exact ⟨U, F, hU, hgU, hF, fun g hg hgi => hfe g hg hgi⟩
  set x : smD ε π := ⟨v, hsm⟩ with hx
  have hC : ∀ W : List (Matrix (Fin m) (Fin m) ℂ), W.length ≤ 2 → (∀ X ∈ W, hs X ≤ 1) →
      ‖PI.DSInfCharCap.dsigCW ε π W v‖ ≤ (8 * Real.sqrt m * (B + 2)) ^ W.length := by
    intro W hl1 hX
    have h := hW 2 W hl1 hX
    rw [hv1, mul_one] at h
    simpa using h
  have one : ∀ X, hs X ≤ 1 → ‖actM (smE ε π) X x‖ ≤ 8 * Real.sqrt m * (B + 2) := by
    intro X hX
    have h := hC [X] (by simp) (by simpa using hX)
    have e : PI.DSInfCharCap.dsigCW ε π [X] v = (actM (smE ε π) X x : H) := dsigC_eq_actM hπ X x
    rw [e] at h
    simpa using h
  have two : ∀ X, hs X ≤ 1 →
      ‖actM (smE ε π) X (actM (smE ε π) X x)‖ ≤ (8 * Real.sqrt m * (B + 2)) ^ 2 := by
    intro X hX
    have h := hC [X, X] (by simp) (by simp [hX])
    have e : PI.DSInfCharCap.dsigCW ε π [X, X] v = (actM (smE ε π) X (actM (smE ε π) X x) : H) := by
      show PI.DSInfCharCap.dsigC ε π X (PI.DSInfCharCap.dsigC ε π X (x : H)) = _
      rw [dsigC_eq_actM hπ X x, dsigC_eq_actM hπ X]
    rw [e] at h
    simpa using h
  refine ⟨x, rfl, one, ?_⟩
  intro Z
  have hnn : 0 ≤ hs Z := by
    unfold hs
    positivity
  rcases hnn.eq_or_lt with h0 | hpos
  · have hZ0 : Z = 0 := by
      ext i j
      have hsum : ∑ i, ∑ j, ‖Z i j‖ ^ 2 = 0 := h0.symm
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)] at hsum
      have hi := hsum i (Finset.mem_univ _)
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)] at hi
      have hij := hi j (Finset.mem_univ _)
      simpa using hij
    subst hZ0
    have hz := actM_smul (actM (smE ε π) 0 x) 0 (0 : Matrix (Fin m) (Fin m) ℂ)
    simp only [Complex.ofReal_zero, zero_smul] at hz
    rw [hz, ← h0]
    simp
  · set a := (Real.sqrt (hs Z))⁻¹ with ha
    have hsq : Real.sqrt (hs Z) ^ 2 = hs Z := Real.sq_sqrt hpos.le
    have hspos : 0 < Real.sqrt (hs Z) := Real.sqrt_pos.mpr hpos
    have ha0 : 0 ≤ a := by positivity
    have ha2 : a * a * hs Z = 1 := by
      rw [ha, ← sq, inv_pow, hsq, inv_mul_cancel₀ hpos.ne']
    have hY : hs ((a : ℂ) • Z) ≤ 1 := by
      rw [hs_smul, ← ha2, sq]
    have h := two _ hY
    rw [actM_smul, actM_smul, map_smul, norm_smul, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg ha0] at h
    have hw0 := norm_nonneg (actM (smE ε π) Z (actM (smE ε π) Z x))
    nlinarith [mul_le_mul_of_nonneg_left h hpos.le]

end CompanionTheory.Lime.T3
