import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockSignTransposeExchangesLocalGlActionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelUnitaryIrreducibleOrthonormal
import Formalism.LocalToGlobal.IndefiniteReal.GvPairOfOrbitDerivCont
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SmoothVectorsOfLieClosedFamilyStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdjLocIt

theorem weak_deriv : ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (f g : ℝ → H), Continuous g → (∀ (y : H) (t : ℝ), HasDerivAt (fun s => ⟪y, f s⟫_ℂ) ⟪y, g t⟫_ℂ t) → ∀ t, HasDerivAt f (g t) t := by
  intro H _ _ _ f g hg hw
  set F : ℝ → H := fun t => f 0 + ∫ s in (0 : ℝ)..t, g s with hFdef
  have hF : ∀ t, HasDerivAt F (g t) t := fun t =>
    ((hg.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add (f 0)
  have heq : f = F := by
    funext t
    refine ext_inner_left ℂ fun y => ?_
    have hd : ∀ s, HasDerivAt (fun s => ⟪y, f s⟫_ℂ - ⟪y, F s⟫_ℂ) 0 s := fun s => by
      have h2 := (hasDerivAt_const s y).inner ℂ (hF s)
      simp only [inner_zero_left, add_zero] at h2
      have h3 := (hw y s).sub h2
      rwa [sub_self] at h3
    have hc := is_const_of_deriv_eq_zero (f := fun s => ⟪y, f s⟫_ℂ - ⟪y, F s⟫_ℂ)
      (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
    have hF0 : F 0 = f 0 := by simp [hFdef]
    simp only [hF0, sub_self] at hc
    exact sub_eq_zero.1 hc
  intro t
  rw [heq]
  exact hF t

theorem continuous_of_adj {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F] (T : E →ₗ[ℂ] F)
    (h : ∀ y : F, ∃ y' : E, ∀ x, ⟪y, T x⟫_ℂ = ⟪y', x⟫_ℂ) : Continuous T := by
  refine T.continuous_of_isClosed_graph (IsSeqClosed.isClosed fun {u p} hu hp => ?_)
  rw [SetLike.mem_coe, LinearMap.mem_graph_iff]
  refine ext_inner_left ℂ fun y => ?_
  obtain ⟨y', hy'⟩ := h y
  have h1 : Filter.Tendsto (fun n => ⟪y, (u n).2⟫_ℂ) Filter.atTop (nhds ⟪y, p.2⟫_ℂ) :=
    ((continuous_const.inner continuous_snd).tendsto p).comp hp
  have h2 : Filter.Tendsto (fun n => ⟪y, (u n).2⟫_ℂ) Filter.atTop (nhds ⟪y', p.1⟫_ℂ) := by
    have e : (fun n => ⟪y, (u n).2⟫_ℂ) = fun n => ⟪y', (u n).1⟫_ℂ := funext fun n => by
      rw [(LinearMap.mem_graph_iff _ _).1 (SetLike.mem_coe.1 (hu n)), hy']
    rw [e]
    exact ((continuous_const.inner continuous_fst).tendsto p).comp hp
  rw [hy', tendsto_nhds_unique h1 h2]

theorem conj_trace_of_lie {n : ℕ} {G X : Matrix (Fin n) (Fin n) ℂ} (hG : G.det ≠ 0) (hX : Xᴴ * G + G * X = 0) :
    starRingEnd ℂ X.trace = -X.trace := by
  have hu : IsUnit G.det := isUnit_iff_ne_zero.2 hG
  have e : Xᴴ = -(G * X) * G⁻¹ := by
    have h1 : Xᴴ * G = -(G * X) := eq_neg_of_add_eq_zero_left hX
    rw [← h1, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  rw [starRingEnd_apply, ← Matrix.trace_conjTranspose, e, Matrix.neg_mul, Matrix.trace_neg, Matrix.mul_assoc,
    Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

theorem gram_det_ne {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) :
    (gramAt D V τ).det ≠ 0 := by
  rw [← M.fr_gram τ, det_mul, det_mul, det_conjTranspose]
  have h1 : (M.fr τ).det ≠ 0 := ((isUnit_iff_isUnit_det _).1 (M.fr_unit τ)).ne_zero
  have hJ : Formalism.REAL.Jm (M.ε τ) * Formalism.REAL.Jm (M.ε τ) = 1 := by
    rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    cases M.ε τ a <;> simp
  have h2 : (Formalism.REAL.Jm (M.ε τ)).det ≠ 0 := by
    intro h
    have := congrArg det hJ
    rw [det_mul, h, zero_mul, det_one] at this
    exact zero_ne_one this
  exact mul_ne_zero (mul_ne_zero (star_ne_zero.2 h1) h2) h1

section Exp

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem exp_cont {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) : Continuous fun t : ℝ => NormedSpace.exp (t • X) :=
  NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)

end Exp

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem cont_rep_exp (M : DSModel V S) (τ : D.what₂.Tau) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (x : M.H τ) : Continuous fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) x :=
  ((GlobalTheory.HolDict.ModelRep.model_rep D V S M τ).2.1.2.2 x).comp_continuous (exp_cont X)
    (fun t => SchurOrthogonalityAlt.gp_exp_mem τ hX t)

theorem inner_rep_exp (M : DSModel V S) (τ : D.what₂.Tau) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (t : ℝ) (y x : M.H τ) :
    ⟪y, M.rep τ (NormedSpace.exp (t • X)) x⟫_ℂ = ⟪M.rep τ (NormedSpace.exp ((-t) • X)) y, x⟫_ℂ := by
  have hm := SchurOrthogonalityAlt.gp_exp_mem τ hX (-t)
  have hp := SchurOrthogonalityAlt.gp_exp_mem τ hX t
  have hU := (GlobalTheory.HolDict.ModelRep.model_rep D V S M τ).2.1
  have h2 : M.rep τ (NormedSpace.exp ((-t) • X)) (M.rep τ (NormedSpace.exp (t • X)) x) = x := by
    rw [← ContinuousLinearMap.comp_apply, ← SchurOrthogonalityAlt.rep_mul M τ hm hp, ← SchurOrthogonalityAlt.gp_exp_split, neg_add_cancel,
      zero_smul, NormedSpace.exp_zero, SchurOrthogonalityAlt.gp_rep_one]
    rfl
  let Li : M.H τ →ₗᵢ[ℂ] M.H τ :=
    { toLinearMap := (M.rep τ (NormedSpace.exp ((-t) • X))).toLinearMap, norm_map' := hU.2.1 _ hm }
  have h1 := Li.inner_map_map y (M.rep τ (NormedSpace.exp (t • X)) x)
  rw [← h1]
  show ⟪_, M.rep τ (NormedSpace.exp ((-t) • X)) (M.rep τ (NormedSpace.exp (t • X)) x)⟫_ℂ = _
  rw [h2]
  rfl

theorem neg_mem_lie {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ) :
    -X ∈ lieAt V τ := by
  have h : Xᴴ * gramAt D V τ + gramAt D V τ * X = 0 := hX
  show (-X)ᴴ * gramAt D V τ + gramAt D V τ * (-X) = 0
  rw [conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, h, neg_zero]

section Loc
variable {a b : ℕ} (ε : Fin a → Bool) (ε' : Fin b → Bool)

theorem locS_add (X Y : Matrix (Fin a) (Fin a) ℂ) : locS (b := b) ε ε' (X + Y) = locS ε ε' X + locS ε ε' Y := by
  simp only [locS, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem locS_smul (c : ℂ) (X : Matrix (Fin a) (Fin a) ℂ) : locS (b := b) ε ε' (c • X) = c • locS ε ε' X := by
  simp only [locS, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem locS_neg (X : Matrix (Fin a) (Fin a) ℂ) : locS (b := b) ε ε' (-X) = -locS ε ε' X := by
  simp only [locS, Matrix.neg_apply, neg_smul, Finset.sum_neg_distrib]

theorem locT_neg (Y : Matrix (Fin b) (Fin b) ℂ) : locT (a := a) ε ε' (-Y) = -locT ε ε' Y := by
  simp only [locT, Matrix.neg_apply, neg_smul, Finset.sum_neg_distrib]

end Loc

theorem exists_adj {L L' E F : Type} [AddCommGroup L] [Module ℂ L] [AddCommGroup L'] [Module ℂ L']
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (A : L →ₗ[ℂ] F →ₗ[ℂ] E) (j : L ≃+ L') (hj : ∀ (c : ℂ) P, j (c • P) = conj c • j P)
    (h : ∀ P w, ∃ w', ∀ y, ⟪w, A P y⟫_ℂ = ⟪w', y⟫_ℂ) :
    ∃ A' : L' →ₗ[ℂ] E →ₗ[ℂ] F, ∀ Q w y, ⟪A' Q w, y⟫_ℂ = ⟪w, A (j.symm Q) y⟫_ℂ := by
  choose f hf using h
  have hjs : ∀ (c : ℂ) Q, j.symm (c • Q) = conj c • j.symm Q := fun c Q => by
    apply j.injective
    rw [hj, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, Complex.conj_conj]
  refine ⟨LinearMap.mk₂ ℂ (fun Q w => f (j.symm Q) w) ?_ ?_ ?_ ?_, fun Q w y => (hf _ _ y).symm⟩
  · intro Q₁ Q₂ w
    refine ext_inner_right ℂ fun y => ?_
    simp only [inner_add_left, ← hf, map_add, LinearMap.add_apply, inner_add_right]
  · intro c Q w
    refine ext_inner_right ℂ fun y => ?_
    simp only [inner_smul_left, ← hf, hjs, map_smul, LinearMap.smul_apply, inner_smul_right, Complex.conj_conj]
  · intro Q w₁ w₂
    refine ext_inner_right ℂ fun y => ?_
    simp only [inner_add_left, ← hf]
  · intro c Q w
    refine ext_inner_right ℂ fun y => ?_
    simp only [inner_smul_left, ← hf]

theorem adj_locIt : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (τ : D.what₂.Tau) (aS aT : ℚ) (A : LPol W.rank V.rank →ₗ[ℂ] M'.H τ →ₗ[ℂ] M.H τ), LocIt M M' τ aS aT A → ∃ A' : LPol V.rank W.rank →ₗ[ℂ] M.H τ →ₗ[ℂ] M'.H τ, LocIt M' M τ aT aS A' := by
  intro D V W S S' M M' τ aS aT A hA
  obtain ⟨j, hjc, hj⟩ := GlobalTheory.T.fock_sign_transpose_exchanges_local_gl_actions V.rank W.rank (M.ε τ) (M'.ε τ)
  obtain ⟨A', hA'⟩ := exists_adj A j hjc hA.adj
  haveI := (GlobalTheory.HolDict.ModelRep.model_rep D V S M τ).1
  haveI := (GlobalTheory.HolDict.ModelRep.model_rep D W S' M' τ).1
  have hA'r : ∀ Q w y, ⟪y, A' Q w⟫_ℂ = ⟪A (j.symm Q) y, w⟫_ℂ := fun Q w y => by
    rw [← inner_conj_symm, hA' Q w y, inner_conj_symm]
  have hcont : ∀ Q, Continuous (A' Q) := fun Q =>
    continuous_of_adj (A' Q) fun y => ⟨A (j.symm Q) y, fun x => hA'r Q x y⟩
  have hcq : ∀ q : ℚ, starRingEnd ℂ (q : ℂ) = q := fun q => map_ratCast (starRingEnd ℂ) q

  have hsrc : ∀ Y ∈ lieAt W τ, ∀ Q w, HasDerivAt (fun t : ℝ => M'.rep τ (NormedSpace.exp (t • Y)) (A' Q w))
      (A' (locS (M'.ε τ) (M.ε τ) ((M'.fr τ * Y * (M'.fr τ)⁻¹).map (starRingEnd ℂ)) Q - ((aS : ℂ) * Y.trace) • Q) w) 0 := by
    intro Y hY Q w
    set Q₂ := locS (M'.ε τ) (M.ε τ) ((M'.fr τ * Y * (M'.fr τ)⁻¹).map (starRingEnd ℂ)) Q - ((aS : ℂ) * Y.trace) • Q
      with hQ₂
    set P₂ := locT (M.ε τ) (M'.ε τ) (M'.fr τ * Y * (M'.fr τ)⁻¹) (j.symm Q) + ((aS : ℂ) * Y.trace) • j.symm Q with hP₂
    have hjP : j P₂ = Q₂ := by
      have hc : starRingEnd ℂ ((aS : ℂ) * Y.trace) = -((aS : ℂ) * Y.trace) := by
        rw [map_mul, hcq, conj_trace_of_lie (gram_det_ne M' τ) hY, mul_neg]
      rw [hP₂, hQ₂, map_add, (hj _).1, hjc, AddEquiv.apply_symm_apply, hc, neg_smul, ← sub_eq_add_neg]
    have hg : Continuous fun t : ℝ => M'.rep τ (NormedSpace.exp (t • Y)) (A' Q₂ w) := cont_rep_exp M' τ hY _
    have hw : ∀ (y : M'.H τ) (t₀ : ℝ), HasDerivAt (fun s : ℝ => ⟪y, M'.rep τ (NormedSpace.exp (s • Y)) (A' Q w)⟫_ℂ)
        ⟪y, M'.rep τ (NormedSpace.exp (t₀ • Y)) (A' Q₂ w)⟫_ℂ t₀ := by
      intro y t₀
      have e : (fun s : ℝ => ⟪y, M'.rep τ (NormedSpace.exp (s • Y)) (A' Q w)⟫_ℂ) =
          fun s : ℝ => ⟪A (j.symm Q) (M'.rep τ (NormedSpace.exp ((-s) • Y)) y), w⟫_ℂ :=
        funext fun s => by rw [inner_rep_exp M' τ hY, hA'r]
      rw [e]
      set y₀ := M'.rep τ (NormedSpace.exp ((-t₀) • Y)) y with hy₀
      have h1 := hA.tgt (-Y) (neg_mem_lie hY) (j.symm Q) y₀
      have hv : -A (locT (M.ε τ) (M'.ε τ) (M'.fr τ * -Y * (M'.fr τ)⁻¹) (j.symm Q) + ((aS : ℂ) * (-Y).trace) • j.symm Q) y₀ =
          A P₂ y₀ := by
        rw [Matrix.mul_neg, Matrix.neg_mul, locT_neg, Matrix.trace_neg, mul_neg, neg_smul, LinearMap.neg_apply, ← neg_add,
          map_neg, LinearMap.neg_apply, neg_neg]
      rw [hv] at h1
      have h2 : HasDerivAt (fun s : ℝ => A (j.symm Q) (M'.rep τ (NormedSpace.exp ((-s) • Y)) y)) (A P₂ y₀) t₀ := by
        have h3 : HasDerivAt (fun s : ℝ => A (j.symm Q) (M'.rep τ (NormedSpace.exp ((s - t₀) • -Y)) y₀)) (A P₂ y₀) t₀ :=
          HasDerivAt.comp_sub_const t₀ t₀ (by rw [sub_self]; exact h1)
        refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
        show A (j.symm Q) (M'.rep τ (NormedSpace.exp ((-s) • Y)) y) = A (j.symm Q) (M'.rep τ (NormedSpace.exp ((s - t₀) • -Y)) y₀)
        rw [hy₀, ← ContinuousLinearMap.comp_apply, ← SchurOrthogonalityAlt.rep_mul M' τ (SchurOrthogonalityAlt.gp_exp_mem τ (neg_mem_lie hY) _)
          (SchurOrthogonalityAlt.gp_exp_mem τ hY _)]
        have e2 : NormedSpace.exp ((s - t₀) • -Y) * NormedSpace.exp ((-t₀) • Y) = NormedSpace.exp ((-s) • Y) := by
          rw [smul_neg, ← neg_smul, ← SchurOrthogonalityAlt.gp_exp_split]
          congr 2
          ring
        rw [e2]
      have h4 := h2.inner ℂ (hasDerivAt_const t₀ w)
      simp only [inner_zero_right, zero_add] at h4
      refine h4.congr_deriv ?_
      rw [inner_rep_exp M' τ hY t₀, ← hjP, hA'r, AddEquiv.symm_apply_apply]
    have h5 := weak_deriv (M'.H τ) _ _ hg hw 0
    simpa only [zero_smul, NormedSpace.exp_zero, SchurOrthogonalityAlt.gp_rep_one, ContinuousLinearMap.one_apply] using h5

  have htgt : ∀ X ∈ lieAt V τ, ∀ Q w, HasDerivAt (fun t : ℝ => A' Q (M.rep τ (NormedSpace.exp (t • X)) w))
      (-A' (locT (M'.ε τ) (M.ε τ) (M.fr τ * X * (M.fr τ)⁻¹) Q + ((aT : ℂ) * X.trace) • Q) w) 0 := by
    intro X hX Q w
    set Q₁ := locT (M'.ε τ) (M.ε τ) (M.fr τ * X * (M.fr τ)⁻¹) Q + ((aT : ℂ) * X.trace) • Q with hQ₁
    set P₁ := locS (M.ε τ) (M'.ε τ) ((M.fr τ * X * (M.fr τ)⁻¹).map (starRingEnd ℂ)) (j.symm Q) -
      ((aT : ℂ) * X.trace) • j.symm Q with hP₁
    have hjP : j P₁ = Q₁ := by
      have hc : starRingEnd ℂ ((aT : ℂ) * X.trace) = -((aT : ℂ) * X.trace) := by
        rw [map_mul, hcq, conj_trace_of_lie (gram_det_ne M τ) hX, mul_neg]
      rw [hP₁, hQ₁, map_sub, (hj _).2, hjc, AddEquiv.apply_symm_apply, hc, neg_smul, sub_neg_eq_add]
    have hg : Continuous fun t : ℝ => -A' Q₁ (M.rep τ (NormedSpace.exp (t • X)) w) :=
      ((hcont Q₁).comp (cont_rep_exp M τ hX w)).neg
    have hw : ∀ (y : M'.H τ) (t₀ : ℝ), HasDerivAt (fun s : ℝ => ⟪y, A' Q (M.rep τ (NormedSpace.exp (s • X)) w)⟫_ℂ)
        ⟪y, -A' Q₁ (M.rep τ (NormedSpace.exp (t₀ • X)) w)⟫_ℂ t₀ := by
      intro y t₀
      have e : (fun s : ℝ => ⟪y, A' Q (M.rep τ (NormedSpace.exp (s • X)) w)⟫_ℂ) =
          fun s : ℝ => ⟪M.rep τ (NormedSpace.exp ((-s) • X)) (A (j.symm Q) y), w⟫_ℂ :=
        funext fun s => by rw [hA'r, inner_rep_exp M τ hX]
      rw [e]
      have h1 := hA.src (-X) (neg_mem_lie hX) (j.symm Q) y
      have hv : A (locS (M.ε τ) (M'.ε τ) ((M.fr τ * -X * (M.fr τ)⁻¹).map (starRingEnd ℂ)) (j.symm Q) -
          ((aT : ℂ) * (-X).trace) • j.symm Q) y = -A P₁ y := by
        have em : (M.fr τ * -X * (M.fr τ)⁻¹).map (starRingEnd ℂ) = -(M.fr τ * X * (M.fr τ)⁻¹).map (starRingEnd ℂ) := by
          rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.map_neg _ (map_neg _)]
        rw [em, locS_neg, Matrix.trace_neg, mul_neg, neg_smul, LinearMap.neg_apply, hP₁]
        simp only [map_sub, map_add, map_neg, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.neg_apply]
        abel
      rw [hv] at h1
      have h2 : HasDerivAt (fun s : ℝ => M.rep τ (NormedSpace.exp ((-s) • X)) (A (j.symm Q) y))
          (M.rep τ (NormedSpace.exp ((-t₀) • X)) (-A P₁ y)) t₀ := by
        have h3 : HasDerivAt (fun s : ℝ => M.rep τ (NormedSpace.exp ((s - t₀) • -X)) (A (j.symm Q) y)) (-A P₁ y) t₀ :=
          HasDerivAt.comp_sub_const t₀ t₀ (by rw [sub_self]; exact h1)
        have h4 := ((M.rep τ (NormedSpace.exp ((-t₀) • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t₀ h3
        refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
        show M.rep τ (NormedSpace.exp ((-s) • X)) (A (j.symm Q) y) =
          M.rep τ (NormedSpace.exp ((-t₀) • X)) (M.rep τ (NormedSpace.exp ((s - t₀) • -X)) (A (j.symm Q) y))
        rw [← ContinuousLinearMap.comp_apply, ← SchurOrthogonalityAlt.rep_mul M τ (SchurOrthogonalityAlt.gp_exp_mem τ hX _)
          (SchurOrthogonalityAlt.gp_exp_mem τ (neg_mem_lie hX) _)]
        have e2 : NormedSpace.exp ((-t₀) • X) * NormedSpace.exp ((s - t₀) • -X) = NormedSpace.exp ((-s) • X) := by
          rw [smul_neg, ← neg_smul, ← SchurOrthogonalityAlt.gp_exp_split]
          congr 2
          ring
        rw [e2]
      have h4 := h2.inner ℂ (hasDerivAt_const t₀ w)
      simp only [inner_zero_right, zero_add] at h4
      refine h4.congr_deriv ?_
      rw [inner_neg_right, ← hjP, hA'r, AddEquiv.symm_apply_apply, inner_rep_exp M τ hX t₀, map_neg, inner_neg_left]
    have h5 := weak_deriv (M'.H τ) _ _ hg hw 0
    simpa only [zero_smul, NormedSpace.exp_zero, SchurOrthogonalityAlt.gp_rep_one, ContinuousLinearMap.one_apply] using h5

  have hsm : ∀ Q w, A' Q w ∈ M'.sm τ := by
    intro Q w
    refine Submodule.subset_span ?_
    let δ : Matrix (Fin W.rank) (Fin W.rank) ℂ → LPol V.rank W.rank → LPol V.rank W.rank := fun Y Q =>
      locS (M'.ε τ) (M.ε τ) ((M'.fr τ * Y * (M'.fr τ)⁻¹).map (starRingEnd ℂ)) Q - ((aS : ℂ) * Y.trace) • Q
    have hadd : ∀ Q Y₁ Y₂, A' (δ (Y₁ + Y₂) Q) w = A' (δ Y₁ Q) w + A' (δ Y₂ Q) w := by
      intro Q Y₁ Y₂
      have em : (M'.fr τ * (Y₁ + Y₂) * (M'.fr τ)⁻¹).map (starRingEnd ℂ) =
          (M'.fr τ * Y₁ * (M'.fr τ)⁻¹).map (starRingEnd ℂ) + (M'.fr τ * Y₂ * (M'.fr τ)⁻¹).map (starRingEnd ℂ) := by
        rw [Matrix.mul_add, Matrix.add_mul, Matrix.map_add _ (map_add _)]
      have e : δ (Y₁ + Y₂) Q = δ Y₁ Q + δ Y₂ Q := by
        show locS (M'.ε τ) (M.ε τ) ((M'.fr τ * (Y₁ + Y₂) * (M'.fr τ)⁻¹).map (starRingEnd ℂ)) Q - ((aS : ℂ) * (Y₁ + Y₂).trace) • Q =
          (locS (M'.ε τ) (M.ε τ) ((M'.fr τ * Y₁ * (M'.fr τ)⁻¹).map (starRingEnd ℂ)) Q - ((aS : ℂ) * Y₁.trace) • Q) +
          (locS (M'.ε τ) (M.ε τ) ((M'.fr τ * Y₂ * (M'.fr τ)⁻¹).map (starRingEnd ℂ)) Q - ((aS : ℂ) * Y₂.trace) • Q)
        rw [em, locS_add, LinearMap.add_apply, Matrix.trace_add, mul_add, add_smul]
        abel
      rw [e, map_add, LinearMap.add_apply]
    have hsmul : ∀ Q (c : ℝ) Y, A' (δ ((c : ℂ) • Y) Q) w = (c : ℂ) • A' (δ Y Q) w := by
      intro Q c Y
      have em : (M'.fr τ * ((c : ℂ) • Y) * (M'.fr τ)⁻¹).map (starRingEnd ℂ) =
          (c : ℂ) • (M'.fr τ * Y * (M'.fr τ)⁻¹).map (starRingEnd ℂ) := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
        ext i k
        simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal]
      have e : δ ((c : ℂ) • Y) Q = (c : ℂ) • δ Y Q := by
        show locS (M'.ε τ) (M.ε τ) ((M'.fr τ * ((c : ℂ) • Y) * (M'.fr τ)⁻¹).map (starRingEnd ℂ)) Q -
            ((aS : ℂ) * ((c : ℂ) • Y).trace) • Q =
          (c : ℂ) • (locS (M'.ε τ) (M.ε τ) ((M'.fr τ * Y * (M'.fr τ)⁻¹).map (starRingEnd ℂ)) Q - ((aS : ℂ) * Y.trace) • Q)
        rw [em, locS_smul, LinearMap.smul_apply, Matrix.trace_smul, smul_sub, smul_smul, smul_eq_mul, mul_left_comm]
      rw [e, map_smul, LinearMap.smul_apply]
    exact GlobalTheory.T.smoothVectors_of_lie_closed_family W.rank (gramAt D W τ) (M'.H τ) (M'.rep τ) (LPol V.rank W.rank) (fun Q => A' Q w) δ
      (gram_det_ne M' τ) (GlobalTheory.HolDict.ModelRep.model_rep D W S' M' τ).2.1 hadd hsmul (fun Y hY Q => hsrc Y hY Q w) Q
  refine ⟨A', hsm, ?_, fun Q y => ⟨A (j.symm Q) y, fun w => hA'r Q w y⟩, hsrc, htgt⟩
  obtain ⟨P, y, -, hne⟩ := hA.ne
  refine ⟨j P, A P y, hA.sm P y, fun h0 => hne ?_⟩
  have h1 := hA'r (j P) (A P y) y
  rw [h0, inner_zero_right, AddEquiv.symm_apply_apply] at h1
  exact inner_self_eq_zero.1 h1.symm

end GlobalTheory.AdjLocIt
