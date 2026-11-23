import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousIsotropicSandwichMeanTranslation

namespace GlobalTheory.FockLevelDim

open Complex
open scoped Real Topology

theorem norm_le_half {R : Type} [NormedAddCommGroup R] [NormedSpace ℝ R] {F : R → ℂ} (hF : Differentiable ℝ F)
    (x y : R) (α β q C : ℝ)
    (hcr : ∀ a b : ℝ, fderiv ℝ F (a • x + b • y) x + I * fderiv ℝ F (a • x + b • y) y =
      π * I * ((α + b * q) + I * (β - a * q)) * F (a • x + b • y))
    (hC : ∀ z, ‖F z‖ ≤ C) (h0 : F 0 = 0) (hq : Real.exp (32 * π * |q|) ≤ 2) : ‖F x‖ ≤ C / 2 := by
  let Y : ℂ →L[ℝ] R := reCLM.smulRight x + imCLM.smulRight y
  have hY : ∀ t, Y t = t.re • x + t.im • y := fun _ => rfl
  let A : ℂ →L[ℝ] ℂ := ofRealCLM.comp reCLM
  let B : ℂ →L[ℝ] ℂ := ofRealCLM.comp imCLM
  have hA : ∀ t, A t = t.re := fun _ => rfl
  have hB : ∀ t, B t = t.im := fun _ => rfl
  let φ : ℂ → ℂ := fun t => -(π * I) * (α * A t + β * B t) - π * q / 2 * (A t * A t + B t * B t)
  have hn : ∀ t, ‖cexp (φ t)‖ = Real.exp (-(π * q / 2 * ‖t‖ ^ 2)) := fun t => by
    rw [Complex.norm_exp, Complex.sq_norm, Complex.normSq_apply]
    congr 1
    simp [φ, hA, hB]
  have hd : Differentiable ℂ fun t => cexp (φ t) * F (Y t) := fun t => by
    have h1 := ((((A.hasFDerivAt (x := t)).const_mul (α : ℂ)).add (B.hasFDerivAt.const_mul (β : ℂ))).const_mul
      (-(π * I))).sub (((A.hasFDerivAt.mul A.hasFDerivAt).add (B.hasFDerivAt.mul B.hasFDerivAt)).const_mul
      (π * q / 2 : ℂ))
    have h2 := h1.cexp.mul ((hF (Y t)).hasFDerivAt.comp t Y.hasFDerivAt)
    have h3 : HasFDerivAt (fun t => cexp (φ t) * F (Y t)) _ t := h2
    refine differentiableAt_complex_iff_differentiableAt_real.2 ⟨h3.differentiableAt, ?_⟩
    rw [h3.fderiv]
    have h4 := hcr t.re t.im
    rw [← hY] at h4
    have e1 : Y 1 = x := by simp [hY]
    have e2 : Y I = y := by simp [hY]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.comp_apply, e1, e2, hA, hB, smul_eq_mul, Function.comp, Pi.add_apply, Pi.sub_apply,
      Pi.mul_apply, I_re, I_im, one_re, one_im, ofReal_zero, ofReal_one]
    generalize cexp _ = E
    linear_combination (-I * E) * h4 + (E * fderiv ℝ F (Y t) y - E * F (Y t) * π * (I * (β - t.re * q) + t.im * q)) * I_sq
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hle : ∀ s : ℝ, |s| ≤ 64 → Real.exp (π * q / 2 * s) ≤ 2 := fun s hs => by
    refine (Real.exp_le_exp.2 ((le_abs_self _).trans ?_)).trans hq
    rw [abs_mul, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two]
    have := mul_le_mul_of_nonneg_left hs (show 0 ≤ π * |q| / 2 by positivity)
    linarith
  have h1 := dist_le_div_mul_dist_of_mapsTo_ball (c := 0) (R₁ := 8) (R₂ := 2 * C) (z := 1) hd.differentiableOn
    (fun t ht => by
      rw [map_zero, h0, mul_zero, mem_closedBall_zero_iff, norm_mul, hn, ← mul_neg]
      have : ‖t‖ < 8 := mem_ball_zero_iff.1 ht
      refine mul_le_mul (hle _ ?_) (hC _) (norm_nonneg _) zero_le_two
      rw [abs_neg, abs_of_nonneg (by positivity)]
      nlinarith [norm_nonneg t]) (by simp)
  have e1 : Y 1 = x := by simp [hY]
  rw [map_zero, h0, mul_zero, dist_zero_right, dist_zero_right, norm_mul, hn, e1, norm_one, Real.exp_neg,
    inv_mul_le_iff₀ (Real.exp_pos _)] at h1
  have h2 := mul_le_mul_of_nonneg_right (hle (1 ^ 2) (by norm_num)) (show 0 ≤ 2 * C / 8 * 1 by positivity)
  linarith

theorem fg_of_compact {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    (V : Submodule ℂ (G → ℂ)) {K N : Set G} (hK : IsCompact K) (hN : N ∈ 𝓝 (0 : G))
    (hb : ∀ f ∈ V, ∃ C, ∀ x, ‖f x‖ ≤ C) (hk : ∀ x, ∃ k ∈ K, ∀ f ∈ V, ‖f x‖ = ‖f k‖)
    (hs : ∀ f ∈ V, ∀ C, (∀ x, ‖f x‖ ≤ C) → ∀ w, f w = 0 → ∀ n ∈ N, ‖f (w + n)‖ ≤ C / 2) : V.FG := by
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun w => (fun x => x - w) ⁻¹' N) fun w _ =>
    (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds (by simpa using hN)
  let ev : V →ₗ[ℂ] (t → ℂ) := (LinearMap.funLeft ℂ ℂ Subtype.val).comp V.subtype
  have hev : Function.Injective ev := by
    refine (injective_iff_map_eq_zero _).2 fun f hf => ?_
    obtain ⟨C, hC⟩ := hb f.1 f.2
    have key : ∀ n : ℕ, ∀ x, ‖f.1 x‖ ≤ C * (1 / 2) ^ n := by
      intro n
      induction n with
      | zero => simpa using hC
      | succ n ih =>
        intro x
        obtain ⟨k, hkK, hk⟩ := hk x
        obtain ⟨w, hw, hkw⟩ := Set.mem_iUnion₂.1 (ht hkK)
        have := hs f.1 f.2 _ ih w (congrFun hf ⟨w, hw⟩) _ hkw
        rw [add_sub_cancel] at this
        rw [hk f.1 f.2, pow_succ]
        linarith
    refine Subtype.ext (funext fun x => norm_le_zero_iff.1 (ge_of_tendsto' (x := Filter.atTop) ?_ fun n => key n x))
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).const_mul C
  exact Module.Finite.iff_fg.1 (Module.Finite.of_injective ev hev)

theorem exists_fg_of_words {M ι : Type} [AddCommGroup M] [Module ℂ M] [Finite ι] (P : Submodule ℂ M)
    (A : ι → M →ₗ[ℂ] M) (a : ι → M → M) (ha : ∀ i, ∀ f ∈ P, A i f = a i f) (hP : ∀ i, ∀ f ∈ P, a i f ∈ P)
    (h0 : (P ⊓ LinearMap.ker (LinearMap.pi A)).FG) (N : ℕ) : ∃ V : Submodule ℂ M, V.FG ∧
      ∀ f ∈ P, (∀ l : List ι, l.length = N → l.foldr (fun i g => a i g) f = 0) → f ∈ V := by
  induction N with
  | zero => exact ⟨⊥, Submodule.fg_bot, fun f _ h => h [] rfl⟩
  | succ N ih =>
    obtain ⟨V, hV, h⟩ := ih
    refine ⟨P ⊓ (Submodule.pi Set.univ fun _ : ι => V).comap (LinearMap.pi A), ?_, fun f hf hl => ⟨hf, fun i _ => ?_⟩⟩
    · refine Submodule.fg_of_fg_map_of_fg_inf_ker (LinearMap.pi A) ?_ ?_
      · exact (Submodule.fg_pi fun _ => hV).of_le (Submodule.map_le_iff_le_comap.2 inf_le_right)
      · exact h0.of_le (inf_le_inf_right _ inf_le_left)
    · rw [LinearMap.pi_apply, ha i f hf]
      refine h _ (hP i f hf) fun l hN => ?_
      have := hl (l ++ [i]) (by simp [hN])
      rwa [List.foldr_append] at this

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum NumberField
open GlobalTheory.FockCompare GlobalTheory.OrientedHeis
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D}
  {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}

theorem annihilation_eq (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {κ : Type}
    (b : Module.Basis κ ℝ (Fin T.rank → Fin S.rank → ℂ)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hv : ∀ τ k, annih (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (b k) f = 0) (w : WO S T) (x : RW T S) :
    fderiv ℝ (fun z : RW T S => f (w + iotaW σ T S z)) 0 x +
        I * fderiv ℝ (fun z : RW T S => f (w + iotaW σ T S z)) 0 (GlobalTheory.VacUnique.jO S T sS sT x) =
      π * I * (omO S T (piW θ T S w) x + I * omO S T (piW θ T S w) (GlobalTheory.VacUnique.jO S T sS sT x)) * f w := by
  classical
  let A : RW T S →ₗ[ℝ] ℂ := (-(π * I) * f w) • (ofRealCLM.toLinearMap ∘ₗ omO S T (piW θ T S w)) +
    (fderiv ℝ (fun z : RW T S => f (w + iotaW σ T S z)) 0).toLinearMap
  have hA : ∀ u, A u = -(π * I) * f w * (omO S T (piW θ T S w) u : ℝ) +
    fderiv ℝ (fun z : RW T S => f (w + iotaW σ T S z)) 0 u := fun _ => rfl
  have hE : ∀ τ (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f w =
      A (Pi.single τ z : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) := fun τ z => by
    rw [dRho_eq_dLine, dLine_eq_hD h hψ (isRealDir_lineAt h.inf τ z), hD_eq_fderiv _ _ _ _ (theta_sm h hf),
      GlobalTheory.FockIndep.piW_lineAt h.inf]
    exact (congrArg (· + _) (mul_right_comm _ _ _)).trans (hA _).symm
  have h0 : A + I • (A ∘ₗ GlobalTheory.VacUnique.jO S T sS sT) = 0 := by
    refine LinearMap.pi_ext' fun τ => b.ext fun k => ?_
    have h1 : Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (b k) f w +
      I * Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ) (b k)) f w = 0 := congrFun (hv τ k) w
    have h2 : GlobalTheory.VacUnique.jO S T sS sT (Pi.single τ (b k)) =
        (Pi.single τ (cplxO (sS τ) (sT τ) (b k)) : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) :=
      funext fun τ' => Pi.apply_single (fun τ (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) => cplxO (sS τ) (sT τ) z)
        (fun τ => by simp [cplxO]) τ (b k) τ'
    exact (congrArg (fun u => A (Pi.single τ (b k)) + I * A u) h2).trans
      ((congrArg₂ (fun p q : ℂ => p + I * q) (hE τ (b k)) (hE τ _)).symm.trans h1)
  have h3 : A x + I * A (GlobalTheory.VacUnique.jO S T sS sT x) = 0 := LinearMap.congr_fun h0 x
  rw [hA, hA] at h3
  linear_combination h3

def levelSub (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (U : AddSubgroup (WO S T)) : Submodule ℂ (WO S T → ℂ) where
  carrier := {f | IsThetaFunO ψ S T f ∧ ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u f = f}
  zero_mem' := ⟨theta_zero, fun u _ _ => funext fun _ => mul_zero _⟩
  add_mem' := fun {f g} hf hg => ⟨theta_add hf.1 hg.1, fun u hu h0 => funext fun w => by
    rw [Pi.add_apply, ← congrFun (hf.2 u hu h0) w, ← congrFun (hg.2 u hu h0) w]
    exact mul_add _ _ _⟩
  smul_mem' := fun c {f} hf => ⟨theta_smul c hf.1, fun u hu h0 => funext fun w => by
    rw [Pi.smul_apply, ← congrFun (hf.2 u hu h0) w]
    exact mul_left_comm _ _ _⟩

theorem fg_vacua (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {κ : Type}
    (b : Module.Basis κ ℝ (Fin T.rank → Fin S.rank → ℂ)) {U : AddSubgroup (WO S T)} (hU : IsOpen (U : Set (WO S T)))
    (V : Submodule ℂ (WO S T → ℂ)) (hV : V ≤ levelSub ψ S T U)
    (hv : ∀ f ∈ V, ∀ τ k, annih (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) (b k) f = 0) : V.FG := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨i1, -, -, -, -, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  haveI : ContinuousSub (WO S T) := IsTopologicalAddGroup.to_continuousSub
  let J := GlobalTheory.VacUnique.jO S T sS sT
  have hπ := continuous_pi' hθ T S
  have hq : Continuous fun x : RW T S => omO S T (J x) x := by
    let om := LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := RW T S) (F' := ℝ)).toLinearMap ∘ₗ omO S T ∘ₗ J)
    exact om.continuous.clm_apply continuous_id
  have sk : ∀ u v, omO S T v u = -omO S T u v := fun u v => by
    have h1 := omO_self h (S := S) (T := T) (u + v)
    simp only [LinearMap.map_add, LinearMap.add_apply, omO_self h] at h1
    linarith
  let fin : WO S T → WO S T := fun n => n - iotaW σ T S (piW θ T S n)
  have hfin : Continuous fin := continuous_id.sub ((h.continuous_iota T S).comp hπ)
  have hinf : ∀ n, (fin n).map (infPart D) = 0 := fun n => by
    have hp : piW θ T S (fin n) = 0 := by
      show piW θ T S (n - iotaW σ T S (piW θ T S n)) = 0
      rw [AddMonoidHom.map_sub, h.pi_iota, sub_self]
    ext i j
    exact ThetaCont.infPart_eq_zero h _ fun τ => congrFun (congrFun (congrFun hp τ) i) j
  refine fg_of_compact V hK
    (N := fin ⁻¹' U ∩ {n | Real.exp (32 * π * |omO S T (J (piW θ T S n)) (piW θ T S n)|) < 2})
    (IsOpen.mem_nhds ((hU.preimage hfin).inter (isOpen_lt
      (Real.continuous_exp.comp (continuous_const.mul (hq.comp hπ).abs)) continuous_const)) ⟨?_, ?_⟩)
    (fun f hf => GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ f (hV hf).1) (fun x => ?_) ?_
  · show 0 - iotaW σ T S (piW θ T S 0) ∈ U
    rw [AddMonoidHom.map_zero, AddMonoidHom.map_zero, sub_zero]
    exact U.zero_mem
  · show Real.exp (32 * π * |omO S T (J (piW θ T S 0)) (piW θ T S 0)|) < 2
    rw [AddMonoidHom.map_zero, LinearMap.map_zero]
    simp
  · obtain ⟨γ, ⟨γ', rfl⟩, hx⟩ := hKc x
    refine ⟨_, hx, fun f hf => ?_⟩
    have e := congrArg norm ((hV hf).1.quasi γ' x)
    rw [norm_mul, hψ.1.2.1, one_mul] at e
    exact e.symm
  · rintro f hf C hC w hw n ⟨hn, hn'⟩
    have e : ‖f (w + n)‖ = ‖f (w + iotaW σ T S (piW θ T S n))‖ := by
      rw [← congrFun ((hV hf).2 _ hn (hinf n)) (w + iotaW σ T S (piW θ T S n)), heisO, norm_mul, hψ.1.2.1, one_mul,
        add_assoc]
      exact congrArg (fun u => ‖f (w + u)‖) (add_sub_cancel _ _).symm
    rw [e]
    replace hn' : Real.exp (32 * π * |omO S T (J (piW θ T S n)) (piW θ T S n)|) ≤ 2 := le_of_lt hn'
    generalize piW θ T S n = x at hn'
    refine norm_le_half (F := fun z : RW T S => f (w + iotaW σ T S z))
      ((theta_sm h (hV hf).1 w).differentiable (by simp)) x (J x) (omO S T (piW θ T S w) x)
      (omO S T (piW θ T S w) (J x)) _ C (fun s t => ?_) (fun z => hC _) ?_ hn'
    · have h1 := annihilation_eq h hψ b (hV hf).1 (hv f hf) (w + iotaW σ T S (s • x + t • J x)) x
      have h2 : fderiv ℝ (fun z : RW T S => f (w + iotaW σ T S (s • x + t • J x) + iotaW σ T S z)) 0 =
          fderiv ℝ (fun z : RW T S => f (w + iotaW σ T S z)) (s • x + t • J x) := by
        have := fderiv_comp_add_left (𝕜 := ℝ) (f := fun y : RW T S => f (w + iotaW σ T S y)) (x := 0) (s • x + t • J x)
        rw [add_zero] at this
        rw [← this]
        congr 1
        funext y
        rw [add_assoc, ← AddMonoidHom.map_add]
      rw [h2, AddMonoidHom.map_add (piW θ T S), h.pi_iota] at h1
      refine h1.trans ?_
      show π * I * (omO S T (piW θ T S w + (s • x + t • J x)) x +
        I * omO S T (piW θ T S w + (s • x + t • J x)) (J x)) * _ = _
      simp only [LinearMap.map_add, LinearMap.map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        omO_self h, sk (J x) x]
      push_cast
      ring
    · show f (w + iotaW σ T S 0) = 0
      rw [AddMonoidHom.map_zero, add_zero, hw]

end GlobalTheory.FockLevelDim

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.FockLevelDim

theorem finiteDimensional_level_degree : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : RealMat S) (sT : RealMat T), IsStdChar D ψ (-1) → IsInfFam θ → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (U : AddSubgroup (WO S T)), IsOpen (U : Set (WO S T)) → ∀ N : ℕ, FiniteDimensional ℂ (Submodule.span ℂ {f : WO S T → ℂ | IsThetaFunO ψ S T f ∧ (∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u f = f) ∧ ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ), l.length = N → l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) f = 0}) := by
  intro D ψ θ S T sS sT hψ hθ _ _ U hU N
  let b := Module.finBasis ℝ (Fin T.rank → Fin S.rank → ℂ)
  let e : D.what₂.Tau × Fin (Module.finrank ℝ (Fin T.rank → Fin S.rank → ℂ)) →
    D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ := fun i => (i.1, b i.2)
  choose A hA hA' using fun p : D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ =>
    GlobalTheory.DatumFock.exists_annihLin hψ.1.1 hθ S T p.1 (cplxO (sS p.1) (sT p.1)) p.2
  obtain ⟨V, hV, h⟩ := exists_fg_of_words (levelSub ψ S T U) (fun i => A (e i))
    (fun i f => annih (heisO ψ S T) θ (e i).1 (cplxO (sS (e i).1) (sT (e i).1)) (e i).2 f)
    (fun i f hf => hA' _ f hf.1)
    (fun i f hf => ⟨GlobalTheory.FockIndep.annih_theta hψ hθ _ _ _ hf.1, fun u hu h0 => by
      rw [← hA' _ f hf.1, ← hA _ u h0, hf.2 u hu h0]⟩)
    (fg_vacua (sS := sS) (sT := sT) hψ hθ b hU _ inf_le_left fun f hf τ k =>
      (hA' (e (τ, k)) f hf.1.1).symm.trans (congrFun (LinearMap.mem_ker.1 hf.2) (τ, k))) N
  refine Module.Finite.iff_fg.2 (hV.of_le (Submodule.span_le.2 fun f hf => h f ⟨hf.1, hf.2.1⟩ fun l hl => ?_))
  have := hf.2.2 (l.map e) (by rw [List.length_map, hl])
  rwa [List.foldr_map] at this

end GlobalTheory.FockLevelDim
