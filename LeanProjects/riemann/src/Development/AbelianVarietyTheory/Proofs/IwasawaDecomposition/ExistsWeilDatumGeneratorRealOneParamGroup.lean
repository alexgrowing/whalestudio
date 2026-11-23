import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqTopOfTranslates
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtWeilRepRealOneParamAdelicPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCcrOperatorsThetaFunctions
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfNormal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FderivEqQuadComm

noncomputable section

namespace GlobalTheory.DefLift.Gen

section Abstract

open Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped Real

theorem quad_comm {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B]
    [NormedSpace ℂ B] {om : V →L[ℝ] V →L[ℝ] ℝ} {ρ : V → B →L[ℂ] B} (h0 : ∀ x, om x x = 0)
    (hH : IsHeis (fun x y => om x y) ρ) {X : V → V} {κ : Type} [Fintype κ] {c : κ → ℂ} {p q : κ → V}
    (hQ : IsQuadOf (fun x y => om x y) X c p q) {f : B} (hf : Sm ρ f) (v : V) :
    quad ρ c p q (dH ρ v f) - dH ρ v (quad ρ c p q f) = dH ρ (X v) f := by
  have C := DCalc.dH_calculus V B om ρ h0 hH
  let d : V → Module.End ℂ (smS ρ) := fun u =>
    { toFun := fun g => ⟨dH ρ u g.1, (C g.1 g.2).1 u⟩
      map_add' := fun g g' => Subtype.ext (dH_add u g.2 g'.2)
      map_smul' := fun a g => Subtype.ext (dH_smul u a g.2) }
  have hd : ∀ u w, d u * d w = d w * d u + (2 * π * I * (om u w : ℂ)) • (1 : Module.End ℂ (smS ρ)) := by
    intro u w
    refine LinearMap.ext fun g => Subtype.ext ?_
    have := (C g.1 g.2).2.2.2.2 u w
    rw [sub_eq_iff_eq_add'] at this
    exact this
  have key : ∀ a b, d a * d b * d v - d v * (d a * d b) =
      (2 * π * I : ℂ) • ((om b v : ℂ) • d a + (om a v : ℂ) • d b) := by
    intro a b
    rw [mul_assoc, hd b v, mul_add, ← mul_assoc, hd a v, add_mul, mul_assoc]
    simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
    module
  have hq : ∀ g : smS ρ, ((∑ i, c i • (d (p i) * d (q i))) g).1 = quad ρ c p q g.1 := by
    intro g
    rw [LinearMap.sum_apply, Submodule.coe_sum]
    rfl
  have e : (∑ i, c i • (d (p i) * d (q i))) * d v - d v * (∑ i, c i • (d (p i) * d (q i))) =
      (2 * π * I : ℂ) • ∑ i, c i • ((om (q i) v : ℂ) • d (p i) + (om (p i) v : ℂ) • d (q i)) := by
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, mul_smul_comm, ← smul_sub, key, smul_comm]
  have e1 := congrArg Subtype.val (LinearMap.congr_fun e ⟨f, hf⟩)
  rw [LinearMap.sub_apply, Submodule.coe_sub, Module.End.mul_apply, Module.End.mul_apply, hq,
    LinearMap.smul_apply, Submodule.coe_smul, LinearMap.sum_apply _ (fun i => c i • (_ + _)), Submodule.coe_sum] at e1
  have e2 := hQ.apply_vec (fderiv ℝ (fun u => ρ u f) 0).toLinearMap v
  refine Eq.trans ?_ (e1.trans e2)
  rw [← hq ⟨f, hf⟩]
  rfl

theorem nOp_comm {ι : Type} [Fintype ι] [DecidableEq ι] {H X : Matrix ι ι ℂ} (hH : Hᴴ = H) (hd : H.det ≠ 0)
    (hX : Xᴴ * H + H * X = 0) {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] {ρ : (ι → ℂ) → B →L[ℂ] B}
    (hρ : IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ) {f : B} (hf : Sm ρ f) (v : ι → ℂ) :
    nOp ρ H X (dH ρ v f) - dH ρ v (nOp ρ H X f) = dH ρ (X *ᵥ v) f := by
  obtain ⟨κ, _, c, p, q, hQ, hn⟩ := Normal.normal_quad ι H X hH hd hX
  obtain ⟨om, hom⟩ := Ccr.exists_om H
  have hρ' : IsHeis (fun x y => om x y) ρ := by simpa only [hom] using hρ
  have hQ' : IsQuadOf (fun x y => om x y) (fun v => X *ᵥ v) c p q := by simpa only [hom] using hQ
  rw [← hn B ρ hρ f hf, ← hn B ρ hρ _ (DCalc.sm_dH hρ' hf v)]
  exact quad_comm (fun x => by rw [hom, Ccr.im_self hH]) hρ' hQ' hf v

theorem nOp_add_comm {ι : Type} [Fintype ι] [DecidableEq ι] {H X : Matrix ι ι ℂ} (hH : Hᴴ = H) (hd : H.det ≠ 0)
    (hX : Xᴴ * H + H * X = 0) {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] {ρ : (ι → ℂ) → B →L[ℂ] B}
    (hρ : IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ) (a : ℂ) {f : B} (hf : Sm ρ f) (hn : Sm ρ (nOp ρ H X f))
    (v : ι → ℂ) :
    nOp ρ H X (dH ρ v f) + a • dH ρ v f = dH ρ v (nOp ρ H X f + a • f) + dH ρ (X *ᵥ v) f := by
  have s2 : Sm ρ (a • f) := (smS _).smul_mem _ hf
  rw [← nOp_comm hH hd hX hρ hf, dH_add _ hn s2, dH_smul _ _ hf]
  abel

theorem blk_vecL {O : Type} [Fintype O] [DecidableEq O] {m n : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) (τ τ' : O)
    (u : Matrix (Fin m) (Fin n) ℂ) :
    blk (Pi.single τ X) (fun _ => 1) *ᵥ vecL (Pi.single τ' u : O → Matrix (Fin m) (Fin n) ℂ) =
      vecL (Pi.single τ' ((Pi.single τ X : O → Matrix (Fin m) (Fin m) ℂ) τ' * u) : O → Matrix (Fin m) (Fin n) ℂ) := by
  funext ⟨⟨i, j⟩, t⟩
  have e := congrFun (congrFun (cpt_blk (Pi.single τ X) (fun _ => 1)
    (vecL (Pi.single τ' u : O → Matrix (Fin m) (Fin n) ℂ)) t) i) j
  have e' : ∀ y : O → Matrix (Fin m) (Fin n) ℂ, cpt (vecL y) t = y t := fun y => rfl
  rw [e', Matrix.mul_one] at e
  refine e.trans ?_
  change _ = (Pi.single τ' ((Pi.single τ X : O → Matrix (Fin m) (Fin m) ℂ) τ' * u) : O → Matrix (Fin m) (Fin n) ℂ) t i j
  by_cases h : t = τ'
  · subst h
    simp only [Pi.single_eq_same]
  · simp only [Pi.single_eq_of_ne h, Matrix.mul_zero]

end Abstract

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
open GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped Classical

variable {D : D7} {θ : InfFam D}

theorem hasDerivAt_comp (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (τ' : D.what₂.Tau) (i j : Fin V.rank) :
    HasDerivAt (fun t : ℝ => Datum.compAt θ τ' (Formalism.L2.Theta.mt V (oneP θ V τ X t)) i j)
      ((Pi.single τ X : D.what₂.Tau → _) τ' i j) 0 := by
  by_cases h : τ' = τ
  · subst h
    have e : ∀ t : ℝ, Datum.compAt θ τ' (Formalism.L2.Theta.mt V (oneP θ V τ' X t)) = NormedSpace.exp (t • X) :=
      fun t => (isAtTau_oneP hθ hX t).2.1
    have := hasDerivAt_exp_entry X 0 i j
    rw [zero_smul, NormedSpace.exp_zero, Matrix.one_mul] at this
    simpa only [e, Pi.single_eq_same] using this
  · have e : ∀ t : ℝ, Datum.compAt θ τ' (Formalism.L2.Theta.mt V (oneP θ V τ X t)) = 1 :=
      fun t => (isAtTau_oneP hθ hX t).2.2 τ' h
    simp only [e, Pi.single_eq_of_ne h]
    exact hasDerivAt_const _ _

theorem blk_lie {S T : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hX : X ∈ lieAt T τ) :
    (blk (Pi.single τ X) fun _ => 1 : Matrix (Ix S T) (Ix S T) ℂ)ᴴ * HM S T +
      HM S T * blk (Pi.single τ X) (fun _ => 1) = 0 := by
  have h : Xᴴ * gramAt D T τ + gramAt D T τ * X = 0 := hX
  unfold HM
  rw [blk_conjTranspose, blk_mul, blk_mul]
  simp only [conjTranspose_one, Matrix.mul_one, Matrix.one_mul]
  unfold RealWeil.blk
  rw [← blockDiagonal_add, ← blockDiagonal_zero]
  congr 1
  funext t
  rw [Pi.add_apply, ← add_kronecker]
  beta_reduce
  by_cases ht : t = τ
  · subst ht
    rw [Pi.single_eq_same, Matrix.mul_smul, Matrix.smul_mul, ← smul_add, h, smul_zero, zero_kronecker]
    rfl
  · rw [Pi.single_eq_of_ne ht]
    simp

variable {σ : (D.what₂.Tau → ℂ) →+ Formalism.L2.Theta.AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem coe_dH (h : GlobalTheory.FockCompare.Chart θ σ) (hψ : IsStdChar D ψ (-1)) (F : BB ψ S T)
    (hF : IsThetaFunO ψ S T F.1) (τ : D.what₂.Tau) (y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    ((dH (rhoV hψ σ S T) (vecL (Pi.single τ y : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ)) F).1 : WO S T → ℂ) =
      Datum.dRho (heisO ψ S T) θ τ y F.1 := by
  funext w
  refine (ev_fderiv hψ F (sm_of_theta h hψ F hF) _ w).trans ?_
  have e : ∀ t : ℝ, iotaV σ S T (t • vecL (Pi.single τ y : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ)) =
      lineAt θ τ y t := fun t => by
    rw [GlobalTheory.VacUnique.Ann.lineAt_eq h S T τ y t]
    rfl
  simp only [e]
  rfl

theorem dRho_zero (h : GlobalTheory.FockCompare.Chart θ σ) (hψ : IsStdChar D ψ (-1)) (F : BB ψ S T)
    (hF : IsThetaFunO ψ S T F.1) (τ : D.what₂.Tau) : Datum.dRho (heisO ψ S T) θ τ 0 F.1 = 0 := by
  have e : vecL (Pi.single τ 0 : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) = 0 := by
    rw [Pi.single_zero]
    rfl
  have e' : dH (rhoV hψ σ S T) 0 F = 0 := map_zero _
  rw [← coe_dH h hψ F hF, e, e']
  rfl

theorem coe_add_smul (A F : BB ψ S T) (a : ℂ) :
    (A.1 : WO S T → ℂ) + a • (F.1 : WO S T → ℂ) = ((A + a • F).1 : WO S T → ℂ) := rfl

theorem coe_add_sub (A F : BB ψ S T) :
    ((A + F).1 : WO S T → ℂ) - (A.1 : WO S T → ℂ) = (F.1 : WO S T → ℂ) := add_sub_cancel_left (A.1 : WO S T → ℂ) F.1

theorem theta_dH (h : GlobalTheory.FockCompare.Chart θ σ) (hψ : IsStdChar D ψ (-1)) (F : BB ψ S T)
    (hF : IsThetaFunO ψ S T F.1) (v : Ix S T → ℂ) : IsThetaFunO ψ S T (dH (rhoV hψ σ S T) v F).1 := by
  obtain ⟨F', hF', hd⟩ := exists_deriv h hψ F hF v
  have e : F' = dH (rhoV hψ σ S T) v F := QB_ext fun w => (hd w).unique
    (((ev _ _ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_dH v (sm_of_theta h hψ F hF)))
  exact e ▸ hF'

theorem exists_extension (h : GlobalTheory.FockCompare.Chart θ σ) (hψ : IsStdChar D ψ (-1))
    (Y : Matrix (Ix S T) (Ix S T) ℂ) (lam : ℂ) : ∃ Gn : Module.End ℂ (WO S T → ℂ), ∀ F : BB ψ S T,
      IsThetaFunO ψ S T F.1 → IsThetaFunO ψ S T (nOp (rhoV hψ σ S T) (HM S T) Y F).1 ∧
        Gn F.1 = (nOp (rhoV hψ σ S T) (HM S T) Y F + lam • F).1 := by
  obtain ⟨x, d, -, hn⟩ := exists_isCCR_theta D θ σ h ψ hψ S T
  have hA := hn Y
  generalize (∑ k, ∑ l, Y k l • (x k * d l)) = A at hA
  obtain ⟨G, hG⟩ := LinearMap.exists_extend ((thetaSub ψ S T).subtype ∘ₗ A)
  refine ⟨G + lam • 1, fun F hF => ?_⟩
  have e := hA ⟨F.1, hF⟩ F rfl
  have e' : G F.1 = (A ⟨F.1, hF⟩).1 := LinearMap.congr_fun hG ⟨F.1, hF⟩
  refine ⟨e ▸ (A ⟨F.1, hF⟩).2, ?_⟩
  rw [← coe_add_smul, ← e, ← e']
  rfl

theorem comm_dRho (h : GlobalTheory.FockCompare.Chart θ σ) (hψ : IsStdChar D ψ (-1)) {τ : D.what₂.Tau}
    {X : Matrix (Fin T.rank) (Fin T.rank) ℂ} (hX : X ∈ lieAt T τ) (lam : ℂ) {Gn : Module.End ℂ (WO S T → ℂ)}
    (hG : ∀ F : BB ψ S T, IsThetaFunO ψ S T F.1 →
      IsThetaFunO ψ S T (nOp (rhoV hψ σ S T) (HM S T) (blk (Pi.single τ X) fun _ => 1) F).1 ∧
        Gn F.1 = (nOp (rhoV hψ σ S T) (HM S T) (blk (Pi.single τ X) fun _ => 1) F + lam • F).1)
    (F : BB ψ S T) (hf : IsThetaFunO ψ S T F.1) : IsThetaFunO ψ S T (Gn F.1) ∧
      ∀ τ' (u : Matrix (Fin T.rank) (Fin S.rank) ℂ),
      Gn (Datum.dRho (heisO ψ S T) θ τ' u F.1) - Datum.dRho (heisO ψ S T) θ τ' u (Gn F.1) =
      ((dH (rhoV hψ σ S T) (vecL (Pi.single τ' ((Pi.single τ X : D.what₂.Tau → _) τ' * u) :
        D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ)) F).1 : WO S T → ℂ) := by
  obtain ⟨h2, e⟩ := hG F hf
  have h1 := GlobalTheory.OrientedHeis.theta_add h2 (GlobalTheory.OrientedHeis.theta_smul lam hf)
  rw [coe_add_smul] at h1
  refine ⟨e ▸ h1, fun τ' u => ?_⟩
  rw [← coe_dH h hψ F hf, (hG _ (theta_dH h hψ F hf _)).2, e, ← coe_dH h hψ _ h1, ← blk_vecL,
    nOp_add_comm HM_herm HM_det (blk_lie (S := S) hX) (isHeis_rhoB h hψ) lam (sm_of_theta h hψ F hf)
      (sm_of_theta h hψ _ h2)]
  exact coe_add_sub _ _

theorem exists_generator : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ τ, ∀ X ∈ lieAt T τ, ∃ Gn : Module.End ℂ (WO S T → ℂ), ∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (Gn f) ∧ (∀ u, Gn (Datum.dRho (heisO ψ S T) θ τ u f) - Datum.dRho (heisO ψ S T) θ τ u (Gn f) = Datum.dRho (heisO ψ S T) θ τ (X * u) f) ∧ (∀ τ', τ' ≠ τ → ∀ u, Gn (Datum.dRho (heisO ψ S T) θ τ' u f) = Datum.dRho (heisO ψ S T) θ τ' u (Gn f)) ∧ ∀ (p : GA D S × GA D T) (w : WO S T), HasDerivAt (fun t : ℝ => om (p * (1, oneP θ T τ X t)) f w) (om p (Gn f) w) 0 := by
  intro D ψ S T χS χT om hom θ hθ τ X hX
  have hψ := hom.std
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨lam, hl⟩ := GlobalTheory.T.hasDerivAt_weilRep_realOneParam_adelicPoint D θ σ h ψ hψ S T om (GlobalTheory.Ker.isWeak_of_datum hom) hom.om_cont
    (fun t => (1, oneP θ T τ X t)) (continuous_const.prodMk (continuous_oneP hθ hX))
    (fun s t => by rw [oneP_add hθ hX, Prod.mk_mul_mk, one_mul])
    (fun t => ⟨one_mem _, (isAtTau_oneP hθ hX t).1⟩) (blk (Pi.single τ X) fun _ => 1) (fun k l => by
      simp only [mM_apply, inv_one, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one, RealWeil.blk, blockDiagonal_apply,
        kroneckerMap_apply]
      split_ifs
      · exact (hasDerivAt_comp hθ hX _ _ _).mul_const _
      · exact hasDerivAt_const _ _)
  obtain ⟨Gn, hG⟩ := exists_extension (S := S) (T := T) h hψ (blk (Pi.single τ X) fun _ => 1) lam
  refine ⟨Gn, fun f hf => ?_⟩
  obtain ⟨F, rfl⟩ : ∃ F : BB ψ S T, (F.1 : WO S T → ℂ) = f := ⟨toB hψ f hf, coe_toB hψ f hf⟩
  obtain ⟨hth, hcomm⟩ := comm_dRho h hψ hX lam hG F hf
  refine ⟨hth, fun u => ?_, fun τ' hτ u => ?_, fun p w => ?_⟩
  · rw [hcomm, Pi.single_eq_same, coe_dH h hψ F hf]
  · rw [← sub_eq_zero, hcomm, Pi.single_eq_of_ne hτ, Matrix.zero_mul, coe_dH h hψ F hf]
    exact dRho_zero h hψ F hf τ'
  · rw [(hG F hf).2]
    exact hl F hf p w

end GlobalTheory.DefLift.Gen

end
