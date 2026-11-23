import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.GIinvCut
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsplitGIinvA

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KSplit
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem T_lin_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (Φ Φ' : d.Fn) (a : ℂ) : d.T (Φ + a • Φ') = d.T Φ + a • d.T Φ' := by
  funext X
  have e : d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) (Φ + a • Φ') =
      d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) Φ + a • d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) Φ' := by
    funext x
    simp only [Darboux.rho, schr, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  show d.l (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) (Φ + a • Φ')) =
    d.l (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) Φ) + a • d.l (d.dd.rho d.B.ψ (X * (incM F d.b.1.toCols₂)ᵀ) Φ')
  rw [e, map_add, map_smul]
theorem mu_right_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : d.μ.IsMulRightInvariant := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KSplitA.mu_right_k d
theorem thetaSum_S_rat_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∀ Φ ∈ d.sch, ∀ γ ∈ ratU σ d.A.J, thetaSum F (d.S γ Φ) = thetaSum F Φ := by
  intro Φ hΦ γ hγ
  obtain ⟨γ0, hγ0⟩ := hγ
  have hS : d.S γ Φ ∈ d.sch := d.ok.dbl.lin.pres _ _ hΦ
  have h1 := (hT.2.2.2.1 F E σ d (d.S γ Φ) hS).1
  have h2 := (hT.2.2.2.1 F E σ d Φ hΦ).1
  have e : ∀ X : Matrix (Fin d.m) (Fin d.n) E, d.T (d.S γ Φ) (incM F X) = d.T Φ (incM F ((γ0⁻¹).1 * X)) := by
    intro X
    rw [(hT.2.1 F E σ d Φ hΦ).2.2 γ (incM F X)]
    congr 1
    have hm : mat γ⁻¹ = incM F (γ0⁻¹).1 := by
      have hγ1 : ((γ : UA σ d.A.J) : GL (Fin d.m) (AE F E)) =
          Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) γ0 := hγ0.symm
      show (((γ⁻¹ : UA σ d.A.J) : GL (Fin d.m) (AE F E)) : Matrix (Fin d.m) (Fin d.m) (AE F E)) = _
      rw [Subgroup.coe_inv, hγ1, ← map_inv]
      rfl
    rw [hm]
    simp only [incM, Matrix.map_mul]
  simp only [e] at h1
  let eqv : Matrix (Fin d.m) (Fin d.n) E ≃ Matrix (Fin d.m) (Fin d.n) E :=
    { toFun := fun X => (γ0⁻¹).1 * X, invFun := fun X => γ0.1 * X,
      left_inv := fun X => by simp [← Matrix.mul_assoc],
      right_inv := fun X => by simp [← Matrix.mul_assoc] }
  have h3 : HasSum (fun X => d.T Φ (incM F X)) (thetaSum F (d.S γ Φ)) :=
    (eqv.hasSum_iff (f := fun X => d.T Φ (incM F X))).1 h1
  exact h3.unique h2
theorem thetaSum_lin_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Φ Φ' : d.Fn} (hΦ : Φ ∈ d.sch) (hΦ' : Φ' ∈ d.sch) (a : ℂ) :
    thetaSum F (Φ + a • Φ') = thetaSum F Φ + a * thetaSum F Φ' := by
  have h1 := (hT.2.2.2.1 F E σ d (Φ + a • Φ') (d.sch.add_mem hΦ (d.sch.smul_mem a hΦ'))).1
  have h2 := (hT.2.2.2.1 F E σ d Φ hΦ).1
  have h3 := (hT.2.2.2.1 F E σ d Φ' hΦ').1
  rw [_root_.PositivityTheory.SiegelWeilFormula.KSplit.T_lin_k] at h1
  exact h1.unique (h2.add (h3.mul_left a))
theorem I_S_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∀ Φ ∈ d.sch, ∀ g x, d.I (d.S g Φ) x = d.I Φ x := by
  intro Φ hΦ g x
  have := d.ok.haar
  have := _root_.PositivityTheory.SiegelWeilFormula.KSplit.mu_right_k d
  have := PositivityTheory.ThKF.countable_ratU σ d.A.J
  have : BorelSpace (UA σ d.A.J) := ⟨rfl⟩
  have hinv : ∀ γ ∈ ratU σ d.A.J, ∀ h, thetaSum F (d.om x (d.S (γ * h) Φ)) = thetaSum F (d.om x (d.S h Φ)) := by
    intro γ hγ h
    have hSh : d.S h Φ ∈ d.sch := d.ok.dbl.lin.pres _ _ hΦ
    rw [map_mul, Module.End.mul_apply, (hT.2.2.2.1 F E σ d (d.S h Φ) hSh).2 x γ,
      _root_.PositivityTheory.SiegelWeilFormula.KSplit.thetaSum_S_rat_k hT d _ (d.ok.dbl.weil.2.1.pres _ _ hSh) γ hγ]
  have e : ∀ h, thetaSum F (d.om x (d.S h (d.S g Φ))) = thetaSum F (d.om x (d.S (h * g) Φ)) := fun h => by
    rw [map_mul, Module.End.mul_apply]
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.I, thetaMean, MeasureTheory.setAverage_eq, e]
  rw [PositivityTheory.ThKF.L2.integral_right d.ok.dom (fun h => thetaSum F (d.om x (d.S h Φ))) hinv g]
theorem I_lin_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {Φ Φ' : d.Fn} (hΦ : Φ ∈ d.sch) (hΦ' : Φ' ∈ d.sch) (a : ℂ) (x : d.G) :
    d.I (Φ + a • Φ') x = d.I Φ x + a * d.I Φ' x := by
  have hi : ∀ Ξ ∈ d.sch, MeasureTheory.IntegrableOn (fun h => thetaSum F (d.om x (d.S h Ξ))) d.D d.μ :=
    fun Ξ hΞ => ((hT.2.2.2.2 F E σ d).2.2 Ξ hΞ).1 x
  have e : ∀ h, thetaSum F (d.om x (d.S h (Φ + a • Φ'))) =
      thetaSum F (d.om x (d.S h Φ)) + a * thetaSum F (d.om x (d.S h Φ')) := fun h => by
    rw [map_add, map_smul, map_add, map_smul]
    exact _root_.PositivityTheory.SiegelWeilFormula.KSplit.thetaSum_lin_k hT d (d.ok.dbl.weil.2.1.pres _ _ (d.ok.dbl.lin.pres _ _ hΦ))
      (d.ok.dbl.weil.2.1.pres _ _ (d.ok.dbl.lin.pres _ _ hΦ')) a
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.I, thetaMean, MeasureTheory.setAverage_eq, e]
  rw [MeasureTheory.integral_add (hi Φ hΦ) ((hi Φ' hΦ').const_mul a), MeasureTheory.integral_const_mul, smul_add,
    mul_smul_comm]
theorem exists_embU_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (u : Matrix (Fin d.m) (Fin d.m) ℂ)
    (hu : u ∈ Matrix.unitaryGroup (Fin d.m) ℂ) : ∃ g : UA σ d.A.J, ∀ X : Mx F E d.m d.n,
      R.loc w (mat g⁻¹ * X) = (u * Matrix.of (R.loc w X) : Matrix (Fin d.m) (Fin d.n) ℂ) ∧ (∀ w', w' ≠ w → d.cw w' (mat g⁻¹ * X - X) = 0) ∧
        finOne F • (mat g⁻¹ * X - X) = 0 := by
  exact _root_.PositivityTheory.SiegelWeilFormula.KSplitA.exists_embU_k d R w u hu
theorem S_lift_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (Ψ : Mx F E d.m d.n → ℂ)
    (hΨ : Ψ ∈ R.away w) (φ : PX d.m d.n →ₗ[ℂ] d.Fn) (hφ : R.IsLift w Ψ φ) (u : Matrix (Fin d.m) (Fin d.m) ℂ)
    (hu : u ∈ Matrix.unitaryGroup (Fin d.m) ℂ) : ∃ g : UA σ d.A.J, ∀ P, d.S g (φ P) = φ (actU u P) := by
  obtain ⟨g, hg⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSplit.exists_embU_k d R w u hu
  refine ⟨g, fun P => ?_⟩
  have hP := hφ P
  have hQ := hφ (actU u P)
  have hΨi := ((hF F E σ d R).2.1 w Ψ hΨ).2
  have hS : d.S g (φ P) ∈ d.sch := d.ok.dbl.lin.pres _ _ hP.1
  have hsub : d.S g (φ P) + (-1 : ℂ) • φ (actU u P) ∈ d.sch := d.sch.add_mem hS (d.sch.smul_mem _ hQ.1)
  have hT0 : d.T (d.S g (φ P) + (-1 : ℂ) • φ (actU u P)) = 0 := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KSplit.T_lin_k]
    funext X
    rw [Pi.add_apply, Pi.smul_apply, (hT.2.1 F E σ d (φ P) hP.1).2.2 g X, hP.2, hQ.2]
    obtain ⟨h1, h2, h3⟩ := hg X
    have eX : mat g⁻¹ * X = X + (mat g⁻¹ * X - X) := by abel
    simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, smul_eq_mul, Pi.zero_apply]
    rw [h1, eX, hΨi X _ h2 h3, show fP P (u * Matrix.of (R.loc w X)) = fP (actU u P) (R.loc w X) from
      fP_unitary u hu P _]
    ring
  have h0 := (hT.1 F E σ d).2.2 _ hsub hT0
  have : d.S g (φ P) = -((-1 : ℂ) • φ (actU u P)) := eq_neg_of_add_eq_zero_left h0
  rw [this, neg_smul, one_smul, neg_neg]
theorem gIinv_of_k : _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.FockMem_k → _root_.PositivityTheory.SiegelWeilFormula.GIinv_k := by
  intro hT hF F E _ _ _ _ _ σ d R w Ψ hΨ φ hφ g a b P
  have hI0 : d.I 0 g = 0 := by
    have e := _root_.PositivityTheory.SiegelWeilFormula.KSplit.I_lin_k hT d (Submodule.zero_mem _) (Submodule.zero_mem _) 1 g
    rw [one_smul, add_zero, one_mul] at e
    linear_combination -e
  let Λ : PX d.m d.n →ₗ[ℂ] ℂ :=
    { toFun := fun P => d.I (φ P) g
      map_add' := fun P Q => by
        have e := _root_.PositivityTheory.SiegelWeilFormula.KSplit.I_lin_k hT d (hφ P).1 (hφ Q).1 1 g
        rw [one_smul, one_mul] at e
        simp only [map_add]; exact e
      map_smul' := fun c P => by
        have e := _root_.PositivityTheory.SiegelWeilFormula.KSplit.I_lin_k hT d (Submodule.zero_mem _) (hφ P).1 c g
        rw [zero_add, hI0, zero_add] at e
        simp only [map_smul, RingHom.id_apply, smul_eq_mul]; exact e }
  have hΛ : ∀ u ∈ Matrix.unitaryGroup (Fin d.m) ℂ, ∀ P, Λ (actU u P) = Λ P := by
    intro u hu P
    obtain ⟨g', hg'⟩ := _root_.PositivityTheory.SiegelWeilFormula.KSplit.S_lift_k hT hF d R w Ψ hΨ φ hφ u hu
    show d.I (φ (actU u P)) g = d.I (φ P) g
    rw [← hg', _root_.PositivityTheory.SiegelWeilFormula.KSplit.I_S_k hT d _ (hφ P).1 g' g]
  exact hOp_kill Λ hΛ (2 * Real.pi) a b P
end PositivityTheory.SiegelWeilFormula.KSplit
end
end
