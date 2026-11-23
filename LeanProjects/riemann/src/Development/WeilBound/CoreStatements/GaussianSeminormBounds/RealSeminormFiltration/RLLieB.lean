import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GroupGeneratedByExp
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieA
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.EvIHalfTrace
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLines

noncomputable section

open MeasureTheory Complex SchwartzMap Matrix Filter Topology Asymptotics
open scoped Real RealInnerProductSpace ContDiff

namespace PositivityTheory.RL.Up

open GlobalTheory.RealWeil

variable {l : Type} [Fintype l]

theorem phase_tg (w : l ⊕ l → ℝ) : (phase w).HasTemperateGrowth := by
  have h : (fun x : EuclideanSpace ℝ l => ⟪qPart w, x⟫ + ⟪pPart w, qPart w⟫ / 2).HasTemperateGrowth :=
    (innerSL ℝ (qPart w)).hasTemperateGrowth.add (Function.HasTemperateGrowth.const _)
  convert Der.chirp_tg (-1) h using 1
  funext x
  simp only [phase, Der.chirp]
  congr 1
  push_cast
  ring

def rhoS (w : l ⊕ l → ℝ) : Sch l →L[ℂ] Sch l := smulLeftCLM ℂ (phase w) ∘L compSubConstCLM ℂ (-pPart w)

theorem rhoS_apply (w : l ⊕ l → ℝ) (f : Sch l) (x : EuclideanSpace ℝ l) : rhoS w f x = phase w x * f (x + pPart w) := by
  rw [rhoS, ContinuousLinearMap.comp_apply, smulLeftCLM_apply_apply (phase_tg w)]
  simp

theorem rho_toLp (w : l ⊕ l → ℝ) (f : Sch l) : rho w (f.toLp 2 volume) = (rhoS w f).toLp 2 volume := by
  refine Lp.ext ((coeFn_rho w _).trans ((rhoFun_congr w (f.coeFn_toLp 2 volume)).trans ?_))
  filter_upwards [(rhoS w f).coeFn_toLp 2 volume] with x hx
  rw [hx, rhoS_apply, rhoFun]

theorem hasDerivAt_rhoS (w : l ⊕ l → ℝ) (f : Sch l) (T : Sch l →L[ℂ] ℂ) :
    HasDerivAt (fun t : ℝ => T (rhoS (t • w) f)) (T (dRho w f)) 0 := by
  obtain ⟨G, hG, hD⟩ := Der.hl_deriv (pPart w) (-innerSL ℝ (qPart w)) f
  have e1 : ∀ t : ℝ, rhoS (t • w) f = G t := fun t => by
    ext x
    rw [hG, rhoS_apply, Der.hl, phase, pPart_smul, qPart_smul]
    congr 2
    simp only [real_inner_smul_left, real_inner_smul_right, ContinuousLinearMap.neg_apply, innerSL_apply_apply,
      real_inner_comm (pPart w) (qPart w)]
    push_cast
    ring
  have e2 : dRho w f = Der.dop (pPart w) (-innerSL ℝ (qPart w)) f := by
    ext x
    rw [dRho_apply, Der.dop_apply]
    simp
  simp only [e1, e2]
  exact hD T

theorem exists_ne : ∃ f : Sch l, f ≠ 0 := by
  let b : ContDiffBump (0 : EuclideanSpace ℝ l) := ⟨1, 2, by norm_num, by norm_num⟩
  have h1 : HasCompactSupport fun x => ((b x : ℝ) : ℂ) := b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) rfl
  refine ⟨h1.toSchwartzMap (ofRealCLM.contDiff.comp b.contDiff), fun h => ?_⟩
  have h2 : ((b 0 : ℝ) : ℂ) = 0 := congrArg (fun f : Sch l => f 0) h
  rw [b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)] at h2
  simp at h2

variable [DecidableEq l]

theorem quad_eq {ι : Type} [Fintype ι] (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) (u v : ι → l ⊕ l → ℝ)
    (h : ∀ w, X *ᵥ w = ∑ j, sympl (v j) w • u j) :
    quad X = (8 * π * I : ℂ)⁻¹ • ∑ j, (dRho (u j) * dRho (v j) + dRho (v j) * dRho (u j)) := by
  have hS : ∀ a b, (X * Matrix.J l ℝ) a b = ∑ j, u j a * v j b := fun a b => by
    have := congrFun (h (Matrix.J l ℝ *ᵥ Pi.single b 1)) a
    rw [mulVec_mulVec, mulVec_single_one] at this
    rw [show (X * Matrix.J l ℝ) a b = _ from this, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, mul_comm]
    congr 1
    rcases b with b | b <;>
      simp [sympl, pPart, qPart, PiLp.inner_apply, Matrix.J, mulVec, dotProduct, Pi.single_apply, Matrix.one_apply]
  have e : ∀ j, dRho (u j) * dRho (v j) + dRho (v j) * dRho (u j) = ∑ a, ∑ b, ((u j a * v j b : ℝ) : ℂ) •
      (dRho (Pi.single a 1) * dRho (Pi.single b 1) + dRho (Pi.single b 1) * dRho (Pi.single a 1)) := fun j => by
    rw [dRho_eq_sum (u j), dRho_eq_sum (v j), Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (s := Finset.univ)
      (f := fun b a => ((v j b : ℂ) • dRho (Pi.single b 1)) * ((u j a : ℂ) • dRho (Pi.single a 1))),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [smul_mul_assoc, mul_smul_comm, ofReal_mul]
    module
  have h8 : (8 * π * I : ℂ)⁻¹ = (4 * π * I : ℂ)⁻¹ * (1 / 2) := by
    have : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    field_simp
    norm_num
  rw [quad, h8, mul_smul]
  congr 1
  simp only [e, hS]
  rw [Finset.sum_comm (s := (Finset.univ : Finset ι)), Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm (s := (Finset.univ : Finset ι)), Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_smul, smul_smul]
  congr 1
  push_cast
  ring

variable (l) in

structure Meta : Type 1 where
  G : Type
  [grp : Group G]
  [top : TopologicalSpace G]
  pr : G →* Matrix.symplecticGroup l ℝ
  om : G →* (Sch l →L[ℂ] Sch l)
  quot : IsQuotientMap pr
  sgn : ∀ g, pr g = 1 → om g = 1 ∨ om g = -1
  cont : ∀ f, Continuous fun g => (om g f).toLp 2 volume
  bdd : ∀ g, ∃ L : L2 l →L[ℂ] L2 l, ∀ f, (om g f).toLp 2 volume = L (f.toLp 2 volume)
  cov : ∀ g w f, om g (rhoS w f) = rhoS ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f)
  line : ∀ X ∈ LieAlgebra.Symplectic.sp l ℝ, ∃ γ : ℝ → G, Continuous γ ∧ γ 0 = 1 ∧ (∀ s t, γ (s + t) = γ s * γ t) ∧
    (∀ t, (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = NormedSpace.exp (t • X)) ∧
    ∀ f : Sch l, HasDerivAt (fun t => (om (γ t) f).toLp 2 volume) ((quad X f).toLp 2 volume) 0

attribute [instance] Meta.grp Meta.top

theorem exists_meta (h : GlobalTheory.Published.RealMetaplecticRepresentation) : Nonempty (Meta l) := by
  rcases isEmpty_or_nonempty l with hl | hl
  · refine ⟨{ G := Matrix.symplecticGroup l ℝ, pr := MonoidHom.id _, om := 1, quot := IsQuotientMap.id
              sgn := fun _ _ => .inl rfl, cont := fun f => continuous_const (y := f.toLp 2 volume), bdd := fun g => ⟨1, fun _ => rfl⟩
              cov := fun g w f => by rw [Subsingleton.elim (_ *ᵥ w) w]; rfl
              line := fun X _ => ⟨fun _ => 1, continuous_const, rfl, fun _ _ => (one_mul _).symm,
                fun _ => Subsingleton.elim _ _, fun f => ?_⟩ }⟩
    have : quad X f = 0 := by simp [quad]
    rw [this, ← toLpCLM_apply (𝕜 := ℂ) (f := 0), map_zero]
    exact hasDerivAt_const _ _
  · obtain ⟨G, _, _, _, pr, om, omS, ⟨h1, h2, ε, -, h3, h4⟩, h5, h6, h7, -, h8⟩ := h l
    have inj := SchwartzMap.injective_toLp (E := EuclideanSpace ℝ l) (F := ℂ) 2 volume
    refine ⟨{ G := G, pr := pr, om := omS, quot := h1.isQuotientMap h2, sgn := fun g hg => ?_, cont := fun f => ?_
              bdd := fun g => ⟨(om g).toContinuousLinearEquiv, fun f => (h7 g f).symm⟩
              cov := fun g w f => inj ?_, line := fun X hX => ?_ }⟩
    · rcases (h3 g).1 hg with rfl | rfl
      · exact .inl (map_one _)
      · refine .inr (ContinuousLinearMap.ext fun f => inj ?_)
        show (omS g f).toLp 2 volume = (-f).toLp 2 volume
        rw [← h7, h4, ← toLpCLM_apply (𝕜 := ℂ) (f := -f), map_neg, toLpCLM_apply]
    · simp only [← h7]
      exact h5 _
    · show (omS g _).toLp 2 volume = (rhoS _ _).toLp 2 volume
      rw [← h7, ← rho_toLp, ← rho_toLp, h6, h7]
    · simp only [← h7]
      exact h8 X hX

theorem Meta.covD (M : Meta l) (g : M.G) (w : l ⊕ l → ℝ) :
    M.om g * dRho w = dRho ((M.pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) * M.om g := by
  ext f x
  let T : Sch l →L[ℂ] ℂ := BoundedContinuousFunction.evalCLM ℂ x ∘L toBoundedContinuousFunctionCLM ℂ _ ℂ
  have h1 := hasDerivAt_rhoS w f (T ∘L M.om g)
  have h2 := hasDerivAt_rhoS ((M.pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (M.om g f) T
  simp only [ContinuousLinearMap.comp_apply, M.cov, mulVec_smul] at h1
  exact h1.unique h2

theorem Meta.smul_inj (M : Meta l) (g : M.G) {c c' : ℂ} (h : c • M.om g = c' • M.om g) : c = c' := by
  obtain ⟨f, hf⟩ := exists_ne (l := l)
  have := congrArg (fun L => (L * M.om g⁻¹) f) h
  simp only [smul_mul_assoc, ← map_mul, mul_inv_cancel, map_one] at this
  exact smul_left_injective ℂ hf this

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem hasDerivAt_exp_mulVec {n : Type} [Fintype n] [DecidableEq n] (X : Matrix n n ℝ) (w : n → ℝ) (a : n) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • X) *ᵥ w) a) ((X *ᵥ w) a) 0 := by
  have : CompleteSpace (Matrix n n ℝ) := FiniteDimensional.complete ℝ _
  let L : Matrix n n ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun Y => (Y *ᵥ w) a
      map_add' := fun _ _ => by simp [add_mulVec]
      map_smul' := fun _ _ => by simp [smul_mulVec] }
  have := L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at this
  exact this

theorem core (M : Meta l) {G0 : Type} [Group G0] [TopologicalSpace G0] (s : G0 →* Matrix.symplecticGroup l ℝ)
    (hs : Continuous s) (A : G0 →* (Sch l →L[ℂ] Sch l))
    (hA : ∀ g g', M.pr g' = s g → ∃ c : ℂ, A g = c • M.om g')
    (hw : ∀ (T : Sch l →L[ℂ] ℂ) f, Continuous fun g => T (A g f)) :
    ∃ χ : G0 →* ℂ, ContinuousAt χ 1 ∧ ∀ γ : ℝ → G0, Continuous γ → γ 0 = 1 → (∀ s t, γ (s + t) = γ s * γ t) →
      ∀ X ∈ LieAlgebra.Symplectic.sp l ℝ, (∀ t, (s (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = NormedSpace.exp (t • X)) →
        ∃ z : ℂ, (∀ t : ℝ, χ (γ t) = cexp (2 * z * t)) ∧
          ∀ (T : Sch l →L[ℂ] ℂ) f, HasDerivAt (fun t => T (A (γ t) f)) (T (quad X f + z • f)) 0 := by
  obtain ⟨f0, hf0⟩ := exists_ne (l := l)
  let T0 : Sch l →L[ℂ] ℂ := innerSL ℂ (f0.toLp 2 volume) ∘L toLpCLM ℂ ℂ 2 volume
  have hT0 : T0 f0 ≠ 0 := fun h => hf0 (SchwartzMap.injective_toLp (E := EuclideanSpace ℝ l) (F := ℂ) 2 volume (by
    have : f0.toLp 2 volume = 0 := inner_self_eq_zero.1 h
    show f0.toLp 2 volume = (0 : Sch l).toLp 2 volume
    rw [this, ← toLpCLM_apply (𝕜 := ℂ) (f := 0), map_zero]))
  let n : M.G → ℂ := fun g => T0 (M.om g f0)
  have hn : Continuous n := (innerSL ℂ (f0.toLp 2 volume)).continuous.comp (M.cont f0)
  have hn1 : n 1 = T0 f0 := by simp [n]
  have fib : ∀ g g', M.pr g = M.pr g' → M.om g' = M.om g ∨ M.om g' = -M.om g := fun g g' h => by
    have e : M.om g' = M.om g * M.om (g⁻¹ * g') := by rw [← map_mul, mul_inv_cancel_left]
    rcases M.sgn (g⁻¹ * g') (by rw [map_mul, map_inv, h, inv_mul_cancel]) with h1 | h1 <;> simp [e, h1]
  choose L hL using M.quot.surjective
  choose c hc using fun g => hA g _ (hL (s g))
  have spec : ∀ g g' c', M.pr g' = s g → A g = c' • M.om g' → c g ^ 2 = c' ^ 2 := fun g g' c' h1 h2 => by
    rw [hc] at h2
    rcases fib (L (s g)) g' (by rw [hL, h1]) with h | h
    · rw [h] at h2
      rw [M.smul_inj _ h2]
    · rw [h, smul_neg, ← neg_smul] at h2
      rw [M.smul_inj _ h2, neg_sq]
  let χ : G0 →* ℂ :=
    { toFun := fun g => c g ^ 2
      map_one' := (spec 1 1 1 (by simp) (by simp)).trans (one_pow 2)
      map_mul' := fun a b => (spec (a * b) (L (s a) * L (s b)) (c a * c b) (by simp [hL])
        (by rw [map_mul, map_mul, hc, hc, smul_mul_smul_comm])).trans (mul_pow _ _ _) }
  refine ⟨χ, ?_, fun γ hγ h0 hm X hX hγX => ?_⟩
  · have hN : Continuous fun σ => n (L σ) ^ 2 := by
      rw [M.quot.continuous_iff]
      refine (hn.pow 2).congr fun g => ?_
      rcases fib g (L (M.pr g)) (hL _).symm with h | h <;> simp [n, h]
    have hN1 : n (L (s 1)) ^ 2 ≠ 0 := by
      rcases fib 1 (L (s 1)) (by simp [hL]) with h | h <;> simp only [n, h] <;> simpa using hT0
    have h1 : ContinuousAt (fun g => T0 (A g f0) ^ 2 / n (L (s g)) ^ 2) 1 :=
      ((hw T0 f0).pow 2).continuousAt.div (hN.comp hs).continuousAt hN1
    refine h1.congr ?_
    filter_upwards [(hN.comp hs).continuousAt.eventually_ne hN1] with g hg
    rw [div_eq_iff (show n (L (s g)) ^ 2 ≠ 0 from hg), hc]
    simp [χ, n, mul_pow]
  · obtain ⟨δ, hδ, d0, dm, hδX, hd⟩ := M.line X hX
    have hpr : ∀ t, M.pr (δ t) = s (γ t) := fun t => Subtype.ext ((hδX t).trans (hγX t).symm)
    choose a ha using fun t => hA (γ t) (δ t) (hpr t)
    have a0 : a 0 = 1 := M.smul_inj (δ 0) (by rw [← ha, h0, d0]; simp)
    have am : ∀ s t, a (s + t) = a s * a t := fun s t => M.smul_inj (δ (s + t)) (by
      rw [← ha, hm, dm, map_mul, map_mul, ha, ha, smul_mul_smul_comm])
    have ac0 : ContinuousAt a 0 := by
      have hne : n (δ 0) ≠ 0 := by rw [d0, hn1]; exact hT0
      have h1 : ContinuousAt (fun t => T0 (A (γ t) f0) / n (δ t)) 0 :=
        ((hw T0 f0).comp hγ).continuousAt.div (hn.comp hδ).continuousAt hne
      refine h1.congr ?_
      filter_upwards [(hn.comp hδ).continuousAt.eventually_ne hne] with t ht
      rw [div_eq_iff (show n (δ t) ≠ 0 from ht), ha]
      simp [n]
    have ac : Continuous a := continuous_iff_continuousAt.2 fun u => by
      have h1 : ContinuousAt (fun t => a (t - u) * a u) u :=
        (ContinuousAt.comp (f := fun t => t - u) (by simpa using ac0) (by fun_prop)).mul continuousAt_const
      exact h1.congr (.of_forall fun t => by simp only [← am, sub_add_cancel])
    obtain ⟨z, hz⟩ := hasDerivAt_oneParam a ac a0 am
    refine ⟨z, fun t => ?_, fun T => ?_⟩
    · show c (γ t) ^ 2 = _
      rw [spec _ _ _ (hpr t) (ha t), eq_exp_of_hasDerivAt a a0 am hz t, ← Complex.exp_eq_exp_ℂ, sq, ← Complex.exp_add]
      congr 1
      rw [real_smul]
      ring
    · have U0 : A (γ 0) = 1 := by rw [h0, map_one]
      refine weak_deriv (fun t => A (γ t)) (quad X + z • 1) U0
        (good_sup _ _ U0 (fun s t => by rw [hm, map_mul]) (fun f => ?_) (fun u => ?_) fun T f => (hw T f).comp hγ) X
        (fun t w => NormedSpace.exp (t • -X) *ᵥ w) (fun w => by simp) (fun w b => ?_) (fun t w => ?_) (fun w => ?_) T
      · have := hz.smul (hd f)
        simp only [a0, d0, map_one, one_smul] at this
        refine (this.congr_deriv ?_).congr_of_eventuallyEq (.of_forall fun t => ?_)
        · simp only [← toLpCLM_apply (𝕜 := ℂ), ← map_smul, ← map_add]
          rfl
        · simp only [ha]
          exact map_smul (toLpCLM ℂ ℂ 2 volume) (a t) (M.om (δ t) f)
      · obtain ⟨L, hL⟩ := M.bdd (δ u)
        refine ⟨a u • L, fun f => ?_⟩
        rw [ContinuousLinearMap.smul_apply, ← hL, ha]
        exact map_smul (toLpCLM ℂ ℂ 2 volume) (a u) (M.om (δ u) f)
      · simpa [neg_mulVec] using hasDerivAt_exp_mulVec (-X) w b
      · simp only [ha, smul_mul_assoc, mul_smul_comm]
        rw [M.covD, hδX, mulVec_mulVec, ← Matrix.exp_add_of_commute _ _
          (((Commute.refl X).neg_right.smul_left t).smul_right t)]
        simp
      · rw [← quad_comm hX]
        simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
        abel

end PositivityTheory.RL.Up

end
