import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasDerivAtWeilRepRealOneParamAdelicPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCcrOperatorsThetaFunctionsStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.Mem.Lift.WeylAction

open GlobalTheory.RealWeil

section Mat

variable {O : Type} [Fintype O] [DecidableEq O] {m n : ℕ}

omit [Fintype O] in
theorem blk_apply (b : O → Matrix (Fin m) (Fin m) ℂ) (a : O → Matrix (Fin n) (Fin n) ℂ) (k l : (Fin m × Fin n) × O) :
    blk b a k l = if k.2 = l.2 then b k.2 k.1.1 l.1.1 * a k.2 l.1.2 k.1.2 else 0 := rfl

theorem sum_blk {A : Type} [AddCommGroup A] [Module ℂ A] (b : O → Matrix (Fin m) (Fin m) ℂ)
    (a : O → Matrix (Fin n) (Fin n) ℂ) (τ : O) (h : ∀ τ', τ' ≠ τ → b τ' = 0 ∨ a τ' = 0)
    (y : (Fin m × Fin n) × O → (Fin m × Fin n) × O → A) :
    ∑ k, ∑ l, blk b a k l • y k l =
      ∑ p : Fin m × Fin n, ∑ q : Fin m × Fin n, (b τ p.1 q.1 * a τ q.2 p.2) • y (p, τ) (q, τ) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_eq_single τ _ (by simp)]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp [blk_apply, ite_smul]
  · intro τ' _ hτ
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases h τ' hτ with e | e <;> simp [blk_apply, e]

theorem sum_left {A : Type} [AddCommGroup A] [Module ℂ A] (X : Matrix (Fin m) (Fin m) ℂ) (τ : O)
    (y : (Fin m × Fin n) × O → (Fin m × Fin n) × O → A) :
    ∑ k, ∑ l, blk (Pi.single τ X) (fun _ => 1) k l • y k l =
      ∑ i, ∑ j, X i j • ∑ a, y ((i, a), τ) ((j, a), τ) := by
  rw [sum_blk _ _ τ fun τ' h => Or.inl (Pi.single_eq_of_ne h _)]
  simp only [Fintype.sum_prod_type, Pi.single_eq_same, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_smul,
    zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem sum_right {A : Type} [AddCommGroup A] [Module ℂ A] (Y : Matrix (Fin n) (Fin n) ℂ) (τ : O)
    (y : (Fin m × Fin n) × O → (Fin m × Fin n) × O → A) :
    ∑ k, ∑ l, blk (fun _ => 1) (Pi.single τ (-Y)) k l • y k l =
      ∑ a, ∑ b, Y a b • -∑ i, y ((i, b), τ) ((i, a), τ) := by
  rw [sum_blk _ _ τ fun τ' h => Or.inr (Pi.single_eq_of_ne h _)]
  have e : ∀ (i : Fin m) (b : Fin n), ∑ q : Fin m × Fin n, ((1 : Matrix (Fin m) (Fin m) ℂ) i q.1 * (-Y) q.2 b) •
      y ((i, b), τ) (q, τ) = ∑ a, -(Y a b • y ((i, b), τ) ((i, a), τ)) := by
    intro i b
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp [Matrix.one_apply, ite_smul]
  simp only [Pi.single_eq_same]
  rw [Fintype.sum_prod_type]
  simp only [e, smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun b _ => Finset.sum_comm).trans Finset.sum_comm

end Mat

variable {D : D7} {θ : InfF D}

theorem hasDerivAt_comp (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (τ' : D.what₂.Tau) (i j : Fin V.rank) :
    HasDerivAt (fun t : ℝ => compAt θ τ' (Formalism.L2.Theta.mt V (oneP θ V τ X t)) i j)
      ((Pi.single τ X : D.what₂.Tau → _) τ' i j) 0 := by
  by_cases h : τ' = τ
  · subst h
    have e : ∀ t : ℝ, compAt θ τ' (Formalism.L2.Theta.mt V (oneP θ V τ' X t)) = NormedSpace.exp (t • X) :=
      fun t => (isAtTau_oneP hθ hX t).2.1
    have := hasDerivAt_exp_entry X 0 i j
    rw [zero_smul, NormedSpace.exp_zero, Matrix.one_mul] at this
    simpa only [e, Pi.single_eq_same] using this
  · have e : ∀ t : ℝ, compAt θ τ' (Formalism.L2.Theta.mt V (oneP θ V τ X t)) = 1 :=
      fun t => (isAtTau_oneP hθ hX t).2.2 τ' h
    simp only [e, Pi.single_eq_of_ne h]
    exact hasDerivAt_const _ _

theorem oneP_inv (hθ : IsInfFam θ) {V : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) (t : ℝ) : (oneP θ V τ X t)⁻¹ = oneP θ V τ (-X) t := by
  have : oneP θ V τ (-X) t = oneP θ V τ X (-t) := by
    unfold oneP
    rw [smul_neg, neg_smul]
  rw [this]
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← oneP_add hθ hX, add_neg_cancel, oneP_zero hθ]

theorem neg_mem_lieAt {V : HSp D} {τ : D.what₂.Tau} {X : Matrix (Fin V.rank) (Fin V.rank) ℂ}
    (hX : X ∈ lieAt V τ) : -X ∈ lieAt V τ := by
  have h : Xᴴ * gramAt D V τ + gramAt D V τ * X = 0 := hX
  show (-X)ᴴ * gramAt D V τ + gramAt D V τ * (-X) = 0
  rw [conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, h, neg_zero]

theorem weyl_action : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak ψ S T om → OmCont ψ S T om → ∀ θ : InfF D, IsInfFam θ → ∃ x d : D.what₂.Tau → Fin T.rank × Fin S.rank → Module.End ℂ (GlobalTheory.RealWeil.thetaSub ψ S T), ∀ τ, IsCCR (x τ) (d τ) ∧ (∀ X ∈ lieAt T τ, ∃ lam : ℂ, ∀ f g h, HasDerivAt (fun t : ℝ => thKer ψ S T om f g (h * oneP θ T τ X t)) (thKer ψ S T om ((∑ i, ∑ j, X i j • ∑ a, x τ (i, a) * d τ (j, a)) f + lam • f) g h) 0) ∧ ∀ Y ∈ lieAt S τ, ∃ lam : ℂ, ∀ f g h, HasDerivAt (fun t : ℝ => thKer ψ S T om f (g * oneP θ S τ Y t) h) (thKer ψ S T om ((∑ a, ∑ b, Y a b • -∑ i, x τ (i, b) * d τ (i, a)) f + lam • f) g h) 0 := by
  intro D ψ hψ S T om hw hc θ hθ
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨x, d, ⟨c1, c2, c3⟩, hn⟩ := GlobalTheory.T.exists_ccr_operators_thetaFunctions D θ σ h ψ hψ S T
  have key : ∀ γ : ℝ → GA D S × GA D T, Continuous γ → (∀ s t, γ (s + t) = γ s * γ t) →
      (∀ t, (γ t).1 ∈ GinfC S ∧ (γ t).2 ∈ GinfC T) → ∀ X : Matrix (Ix S T) (Ix S T) ℂ,
      (∀ k l, HasDerivAt (fun t => mM θ S T (γ t) k l) (X k l) 0) → ∃ lam : ℂ, ∀ (f : thetaSub ψ S T) p,
      HasDerivAt (fun t => om (p * γ t) f.1 0) (om p ((∑ k, ∑ l, X k l • (x k * d l)) f + lam • f).1 0) 0 := by
    intro γ h1 h2 h3 X h4
    obtain ⟨lam, hl⟩ := GlobalTheory.T.hasDerivAt_weilRep_realOneParam_adelicPoint D θ σ h ψ hψ S T om hw hc γ h1 h2 h3 X h4
    refine ⟨lam, fun f p => ?_⟩
    have e := coe_toB hψ f.1 f.2
    have h5 := hl (toB hψ f.1 f.2) (e.symm ▸ f.2) p 0
    have e2 : ((∑ k, ∑ l, X k l • (x k * d l)) f + lam • f).1 =
        ((nOp (rhoV hψ σ S T) (HM S T) X (toB hψ f.1 f.2) + lam • toB hψ f.1 f.2).1 : WO S T → ℂ) := by
      rw [Submodule.coe_add, hn X f _ e]
      rfl
    rw [e2]
    exact h5
  refine ⟨fun τ k => x (k, τ), fun τ k => d (k, τ), fun τ => ⟨⟨fun k l => c1 _ _, fun k l => c2 _ _, fun k l => ?_⟩,
    fun X hX => ?_, fun Y hY => ?_⟩⟩
  · rw [c3]
    simp
  · obtain ⟨lam, hl⟩ := key (fun t => (1, oneP θ T τ X t)) (continuous_const.prodMk (continuous_oneP hθ hX))
      (fun s t => by rw [oneP_add hθ hX, Prod.mk_mul_mk, one_mul])
      (fun t => ⟨one_mem _, (isAtTau_oneP hθ hX t).1⟩) (blk (Pi.single τ X) fun _ => 1) (fun k l => by
        simp only [mM_apply, inv_one, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one, blk_apply]
        split_ifs
        · exact (hasDerivAt_comp hθ hX _ _ _).mul_const _
        · exact hasDerivAt_const _ _)
    refine ⟨lam, fun f g k => ?_⟩
    have := hl f (g, k)
    rw [sum_left X τ fun k l => x k * d l] at this
    simp only [Prod.mk_mul_mk, mul_one] at this
    exact this
  · obtain ⟨lam, hl⟩ := key (fun t => (oneP θ S τ Y t, 1)) ((continuous_oneP hθ hY).prodMk continuous_const)
      (fun s t => by rw [oneP_add hθ hY, Prod.mk_mul_mk, one_mul])
      (fun t => ⟨(isAtTau_oneP hθ hY t).1, one_mem _⟩) (blk (fun _ => 1) (Pi.single τ (-Y))) (fun k l => by
        simp only [mM_apply, oneP_inv hθ hY, GlobalTheory.WeilVacMove.mt_one, GlobalTheory.WeilVacMove.compAt_one, blk_apply]
        split_ifs
        · exact (hasDerivAt_comp hθ (neg_mem_lieAt hY) _ _ _).const_mul _
        · exact hasDerivAt_const _ _)
    refine ⟨lam, fun f g k => ?_⟩
    have := hl f (g, k)
    rw [sum_right Y τ fun k l => x k * d l] at this
    simp only [Prod.mk_mul_mk, mul_one] at this
    exact this

end GlobalTheory.Mem.Lift.WeylAction

end
