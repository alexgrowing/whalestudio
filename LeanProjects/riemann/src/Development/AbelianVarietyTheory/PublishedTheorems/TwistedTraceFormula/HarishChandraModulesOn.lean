import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedType
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat

noncomputable section

open Matrix
open scoped ContDiff

namespace GlobalTheory.Published

open Formalism.BasicNotions.TH (GrpData URep GKMod KFin Smooth ProvA)
open Formalism.MainNotions.SchurIrreducible (IrrU IsHCMod AdmGK IrrGK admQ5)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin UJset)

def AnalyticOnUJ {n : ℕ} (ε : Fin n → Bool) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Matrix (Fin n) (Fin n) ℂ → E) : Prop :=
  ∀ g₀ ∈ UJset ε, ∃ (U : Set (Fin n → Fin n → ℂ)) (F : (Fin n → Fin n → ℂ) → E),
    IsOpen U ∧ Matrix.of.symm g₀ ∈ U ∧ AnalyticOnNhd ℝ F U ∧
      ∀ z ∈ U, Matrix.of z ∈ UJset ε → f (Matrix.of z) = F z

def HarishChandraModulesOn {p q : ℕ} (T : GrpData p q) : Prop :=
  (∀ πU : URep T, IrrU πU →
    (∀ x, KFin T πU.π x → Smooth T πU.π x) ∧
    (∃ (M : GKMod p q) (io : M.V →ₗ[ℂ] πU.H), IsHCMod πU M io) ∧
    ∀ (M : GKMod p q) (io : M.V →ₗ[ℂ] πU.H), IsHCMod πU M io → AdmGK M ∧ IrrGK M) ∧
  (∀ π₁ π₂ : URep T, IrrU π₁ → IrrU π₂ →
    ∀ (M₁ M₂ : GKMod p q) (io₁ : M₁.V →ₗ[ℂ] π₁.H) (io₂ : M₂.V →ₗ[ℂ] π₂.H),
      IsHCMod π₁ M₁ io₁ → IsHCMod π₂ M₂ io₂ →
      ∀ e : M₁.V ≃ₗ[ℂ] M₂.V, (∀ Z v, e (M₁.act Z v) = M₂.act Z (e v)) →
      ∃ U : π₁.H ≃ₗᵢ[ℂ] π₂.H, ∀ g x, U (π₁.π g x) = π₂.π g (U x)) ∧
  (∀ (πU : URep T) (M : GKMod p q) (io : M.V →ₗ[ℂ] πU.H), IsHCMod πU M io →
    AdmGK M → IrrGK M → IrrU πU)

def KFiniteAnalyticUJ : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Nontrivial H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ →
    ∀ v : H, IsKFin ε σ v → AnalyticOnUJ ε fun g => σ g v

def HarishChandraModules : Prop :=
  (∀ (p q : ℕ), 1 ≤ p + q → ∀ T : GrpData p q, HarishChandraModulesOn T) ∧ KFiniteAnalyticUJ

namespace HarishChandraModules

theorem admQ5_of_harishChandraModules (h : HarishChandraModules) (X : ProvA) : admQ5 X :=
  fun p q hpq => h.1 p q hpq (X.grp p q)

end HarishChandraModules

section Consequences

variable {n : ℕ} {ε : Fin n → Bool}

theorem AnalyticOnUJ.comp {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup P]
    [NormedSpace ℝ P] {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : AnalyticOnUJ ε f)
    {x : P → Matrix (Fin n) (Fin n) ℂ} {t₀ : P} (hx : ∀ a b, AnalyticAt ℝ (fun t => x t a b) t₀)
    (hm : ∀ᶠ t in nhds t₀, x t ∈ UJset ε) : AnalyticAt ℝ (fun t => f (x t)) t₀ := by
  obtain ⟨U, F, hU, h0, hF, he⟩ := hf _ hm.self_of_nhds
  have hx' : AnalyticAt ℝ (fun t => (Matrix.of.symm (x t) : Fin n → Fin n → ℂ)) t₀ :=
    analyticAt_pi_iff.2 fun a => analyticAt_pi_iff.2 fun b => hx a b
  have hc : AnalyticAt ℝ (fun t => F (Matrix.of.symm (x t))) t₀ := AnalyticAt.comp (hF _ h0) hx'
  refine hc.congr ?_
  filter_upwards [hm, hx'.continuousAt.eventually (hU.mem_nhds h0)] with t h1 h2
  exact (he _ h2 h1).symm

theorem AnalyticOnUJ.contDiff_comp {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : AnalyticOnUJ ε f)
    {x : P → Matrix (Fin n) (Fin n) ℂ} (hx : ∀ a b, ContDiff ℝ ∞ fun t => x t a b)
    (hm : ∀ t, x t ∈ UJset ε) : ContDiff ℝ ∞ fun t => f (x t) := by
  refine contDiff_iff_contDiffAt.2 fun t₀ => ?_
  obtain ⟨U, F, hU, h0, hF, he⟩ := hf _ (hm t₀)
  have hx' : ContDiff ℝ ∞ (fun t => (Matrix.of.symm (x t) : Fin n → Fin n → ℂ)) :=
    contDiff_pi.2 fun a => contDiff_pi.2 fun b => hx a b
  have hc : ContDiffAt ℝ ∞ (fun t => F (Matrix.of.symm (x t))) t₀ :=
    ContDiffAt.comp t₀ (hF _ h0).contDiffAt hx'.contDiffAt
  refine hc.congr_of_eventuallyEq ?_
  filter_upwards [hx'.continuous.continuousAt.eventually (hU.mem_nhds h0)] with t h2
  exact he _ h2 (hm t)

theorem AnalyticOnUJ.smoothOnH {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : AnalyticOnUJ ε f) :
    Formalism.QuantumDeterminants.SmoothOnH (Formalism.REAL.Jm ε) f := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, h0, hF, he⟩ := hf g₀ hg₀
  exact ⟨U, F, hU, h0, hF.contDiffOn_of_completeSpace, he⟩

theorem AnalyticOnUJ.clm {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : AnalyticOnUJ ε f) (L : E →L[ℝ] E') :
    AnalyticOnUJ ε fun g => L (f g) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, h0, hF, he⟩ := hf g₀ hg₀
  exact ⟨U, fun z => L (F z), hU, h0, L.comp_analyticOnNhd hF, fun z hz hm => by simp only [he z hz hm]⟩

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

private def entryCLM (a b : Fin n) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ a b)

theorem AnalyticOnUJ.analytic_exp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Matrix (Fin n) (Fin n) ℂ → E} (hf : AnalyticOnUJ ε f) {g X : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ UJset ε) (hX : Formalism.REAL.inG ε X) (t₀ : ℝ) :
    AnalyticAt ℝ (fun t : ℝ => f (g * NormedSpace.exp (t • X))) t₀ := by
  refine hf.comp (fun a b => ?_) (Filter.Eventually.of_forall fun t => ?_)
  · have h1 : AnalyticAt ℝ (fun t : ℝ => g * NormedSpace.exp (t • X)) t₀ :=
      analyticAt_const.mul (AnalyticAt.comp (NormedSpace.exp_analytic (𝕂 := ℝ) _)
        (analyticAt_id.smul analyticAt_const))
    exact ((entryCLM a b).analyticAt _).comp h1
  · have := GlobalTheory.GardingVec.list_prod_mem (G := Formalism.REAL.Jm ε) [g, NormedSpace.exp (t • X)] (by
      intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · exact hg
      · exact GlobalTheory.GardingVec.exp_mem (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε)) hX t)
    simpa [UJset, Formalism.REAL.inUJ] using this

theorem AnalyticOnUJ.smoothVec {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {v : H} (hv : AnalyticOnUJ ε fun g => σ g v)
    {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (h : Pᴴ * Formalism.REAL.Jm ε * P = G) :
    Formalism.L2.Theta.SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) v := by
  have hG : IsUnit G := by
    rw [← h]
    exact (((Matrix.isUnit_conjTranspose _).2 hP).mul
      (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε))).mul hP
  intro k Xs hX
  refine hv.contDiff_comp (x := fun t : Fin k → ℝ =>
    P * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * P⁻¹) (fun a b => ?_) fun t => ?_
  · exact (entryCLM a b).contDiff.comp
      ((contDiff_const.mul (GlobalTheory.GardingVec.contDiff_expProd Xs)).mul contDiff_const)
  · refine GlobalTheory.GardingVec.conj_mem hP h (GlobalTheory.GardingVec.list_prod_mem _ fun g hg => ?_)
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
    exact GlobalTheory.GardingVec.exp_mem hG (hX i) _

end

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem HarishChandraModules.analytic (h : HarishChandraModules) (hU : IsURepOn (UJset ε) σ)
    (hI : IsIrredOn (UJset ε) σ) {v : H} (hv : IsKFin ε σ v) : AnalyticOnUJ ε fun g => σ g v := by
  rcases subsingleton_or_nontrivial H with hs | hn
  · intro g₀ _
    exact ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, analyticOnNhd_const, fun _ _ _ => Subsingleton.elim _ _⟩
  · exact h.2 n ε H σ hU hI v hv

theorem HarishChandraModules.smoothOnH (h : HarishChandraModules) (hU : IsURepOn (UJset ε) σ)
    (hI : IsIrredOn (UJset ε) σ) {v : H} (hv : IsKFin ε σ v) :
    Formalism.QuantumDeterminants.SmoothOnH (Formalism.REAL.Jm ε) fun g => σ g v :=
  (h.analytic hU hI hv).smoothOnH

theorem HarishChandraModules.smoothVec (h : HarishChandraModules) (hU : IsURepOn (UJset ε) σ)
    (hI : IsIrredOn (UJset ε) σ) {v : H} (hv : IsKFin ε σ v)
    {P G : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (hG : Pᴴ * Formalism.REAL.Jm ε * P = G) :
    Formalism.L2.Theta.SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) v :=
  (h.analytic hU hI hv).smoothVec hP hG

end Consequences

section Inhabitants

private theorem sub_line (S : Submodule ℂ ℂ) : S = ⊥ ∨ S = ⊤ := eq_bot_or_eq_top S

def sqrtDetRep {p q : ℕ} (T : GrpData p q) : URep T where
  H := ℂ
  π :=
    { toFun := fun g => ((T.sq g : ℂˣ) : ℂ) • (1 : ℂ →L[ℂ] ℂ)
      map_one' := by simp
      map_mul' := fun a b => by ext; simp [mul_comm] }
  isom := fun g x => by
    have hm : (((T.cov g : GL _ ℂ) : Formalism.BasicNotions.TH.Mat p q))ᴴ * Formalism.UG.Jpq p q * (T.cov g : GL _ ℂ) =
        Formalism.UG.Jpq p q := T.cov_mem g
    have hd := congrArg (fun A => ‖Matrix.det A‖) hm
    have hJ : ‖(Formalism.UG.Jpq p q).det‖ = 1 := by
      simp [Formalism.UG.Jpq, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
    simp only [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star, hJ, ← T.sq_sq g, norm_pow] at hd
    have h1 : ‖((T.sq g : ℂˣ) : ℂ)‖ = 1 := by
      have h4 : ‖((T.sq g : ℂˣ) : ℂ)‖ ^ 4 = 1 := by nlinarith
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h4
    simp [h1]
  cont := fun x => by
    have h1 : Continuous fun g : T.G => T.sq g := continuous_snd.comp T.emb.continuous
    have h2 : Continuous fun g : T.G => ((T.sq g : ℂˣ) : ℂ) := Units.continuous_val.comp h1
    have h3 : Continuous fun g : T.G => ((T.sq g : ℂˣ) : ℂ) * x := h2.mul continuous_const
    simpa using h3

theorem det_isURepOn {n : ℕ} (ε : Fin n → Bool) :
    IsURepOn (UJset ε) (fun g => g.det • (1 : ℂ →L[ℂ] ℂ)) ∧
    IsIrredOn (UJset ε) (fun g => g.det • (1 : ℂ →L[ℂ] ℂ)) ∧
    ∀ v, IsKFin ε (fun g => g.det • (1 : ℂ →L[ℂ] ℂ)) v := by
  refine ⟨⟨⟨by simp, fun a _ b _ => by ext; simp [mul_comm]⟩, fun g hg v => ?_, fun v => ?_⟩, fun S _ _ => sub_line S,
    fun v => ⟨⊤, inferInstance, trivial, fun _ _ _ _ => trivial⟩⟩
  · have hm : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
    have hd := congrArg (fun A => ‖Matrix.det A‖) hm
    have hJ : ‖(Formalism.REAL.Jm ε).det‖ ≠ 0 := norm_ne_zero_iff.2
      ((Matrix.isUnit_iff_isUnit_det _).1 (IsUnit.of_mul_eq_one _ (Formalism.REAL.Jm_mul_self ε))).ne_zero
    simp only [Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_star] at hd
    have h2 : ‖g.det‖ ^ 2 = 1 := mul_right_cancel₀ hJ (by nlinarith)
    have h1 : ‖g.det‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h2
    simp [h1]
  · have : Continuous fun g : Matrix (Fin n) (Fin n) ℂ => g.det * v :=
      (continuous_id.matrix_det).mul continuous_const
    simpa using this.continuousOn

end Inhabitants

end GlobalTheory.Published

end
