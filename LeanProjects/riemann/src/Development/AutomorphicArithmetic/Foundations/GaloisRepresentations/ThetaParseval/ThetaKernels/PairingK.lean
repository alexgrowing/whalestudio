import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ProjFacts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid
set_option linter.unusedSectionVars false
noncomputable section
namespace PositivityTheory.ThKW.AdelicSchwartzProperties
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation PositivityTheory.ThKW.PhaseFourierInjectivity GlobalTheory.ThetaTransform GlobalTheory.RatDarboux
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {nS nT N : ℕ}
theorem pairing_k {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {JS : Matrix (Fin nS) (Fin nS) E}
    {JT : Matrix (Fin nT) (Fin nT) E} (hS : IsHermND σ JS) (hT : IsHermND σ JT) {ξ₀ : E} (hξ : ξ₀ ≠ 0) :
    ∃ (N : ℕ) (α β : WOF F E nS nT ≃ₗ[AF F] (Fin N → AF F)) (a b : Matrix (Fin nT) (Fin nS) E ≃ₗ[F] (Fin N → F)),
      (∀ v u, symplOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ (dCd F JT * v) (dC (AF F ⊗[F] E) nT * u) =
        α v ⬝ᵥ β u) ∧ (∀ x, α (ratWF x) = GlobalTheory.SWQ.rat (a x)) ∧ ∀ x, β (ratWF x) = GlobalTheory.SWQ.rat (b x) := by
  classical
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hinv := GlobalTheory.SplitDetCharF.sig_invol hB.cm
  have eB : (-1 : AF F ⊗[F] E) • incM F (-(ξ₀ • JS⁻¹)) = incM F (ξ₀ • JS⁻¹) := by
    funext i j
    simp [incM]
  have hbij := bijective_sympBil σ hinv (JA := (1 : Matrix (Fin nT) (Fin nT) E)ᵀ) (JB := -(ξ₀ • JS⁻¹)) (by simp)
    (by
      rw [← neg_smul, Matrix.det_smul]
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 hξ)) (Matrix.isUnit_nonsing_inv_det _ (Ne.isUnit hS.2)).ne_zero)
  let b := Module.finBasis F (Matrix (Fin nT) (Fin nS) E)
  let b' := b.dualBasis.map (LinearEquiv.ofBijective _ hbij).symm
  have hb : ∀ i j, symp σ (-1) (1 : Matrix (Fin nT) (Fin nT) E)ᵀ (-(ξ₀ • JS⁻¹)) (b' i) (b j) = if j = i then 1 else 0 :=
    fun i j => by
      have h1 := (LinearEquiv.ofBijective _ hbij).apply_symm_apply (b.dualBasis i)
      have h2 := LinearMap.congr_fun h1 (b j)
      rw [Module.Basis.dualBasis_apply_self] at h2
      exact h2
  let P : LinearMap.BilinForm (AF F) (WOF F E nS nT) :=
    sympBil (cA σ) (-1) (incM F (1 : Matrix (Fin nT) (Fin nT) E)ᵀ) (incM F (-(ξ₀ • JS⁻¹)))
  have hP : ∀ v u, P v u = (adB b').equivFun v ⬝ᵥ (adB b).equivFun u := fun v u => by
    have h0 : ∀ i j, P (adB b' i) (adB b j) = if j = i then 1 else 0 := fun i j => by
      rw [adB_apply, adB_apply]
      refine (symp_map (AF F) σ _ _ (b' i) (b j)).trans ?_
      rw [hb]
      split_ifs <;> simp
    conv_lhs => rw [← (adB b').sum_repr v, ← (adB b).sum_repr u]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, h0, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, dotProduct, Module.Basis.equivFun_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  refine ⟨_, (adB b').equivFun, (adB b).equivFun, b'.equivFun, b.equivFun, fun v u => ?_, adB_rat b', adB_rat b⟩
  rw [← hP]
  refine Eq.trans ?_ (GlobalTheory.TransportF.symplOF_eq_symp (JT := 1) rfl eB v u)
  unfold symplOF
  rw [hOF_dual JS JT hT.2, hOF_eq_trace, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
theorem coords_k {σ : E →ₐ[F] E} {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E}
    {JT : Matrix (Fin nT) (Fin nT) E} (hS : IsHermND σ JS) (hT : IsHermND σ JT) {ξ₀ : E} (hξ : ξ₀ ≠ 0)
    (hσ : σ ξ₀ = -ξ₀) :
    ∃ (N : ℕ) (α β : WOF F E nS nT ≃ₗ[AF F] (Fin N → AF F))
      (e : WOF F E nS (nT + nT) ≃ₗ[AF F] VA F N),
      (∀ u v, e (dC (AF F ⊗[F] E) nT * u + dCd F JT * v) = (α v, β u)) ∧
      (∀ w w', symplOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ w w' = symV (e w) (e w')) ∧
      (∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : Fin N → F,
        e (ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) ∧
      (∀ y z : Fin N → F, ∃ x : Matrix (Fin (nT + nT)) (Fin nS) E, e (ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) ∧
      Continuous e ∧ Continuous e.symm ∧
      Continuous α ∧ Continuous α.symm ∧ Continuous β ∧ Continuous β.symm ∧
      (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y : Fin N → F, β (ratWF x) = GlobalTheory.SWQ.rat y) ∧
      (∀ y : Fin N → F, ∃ x : Matrix (Fin nT) (Fin nS) E, β (ratWF x) = GlobalTheory.SWQ.rat y) := by
  have hinv := GlobalTheory.SplitDetCharF.sig_invol hB.cm
  obtain ⟨N, α, β, a, b, hP, ha, hb⟩ := _root_.PositivityTheory.ThKW.AdelicSchwartzProperties.pairing_k hB hS hT hξ
  obtain ⟨d, U, V, hd, hd'⟩ := split (nS := nS) JT hT
  obtain ⟨e, he0⟩ : ∃ e : WOF F E nS (nT + nT) ≃ₗ[AF F] VA F N, ∀ w, e w = (α (d w).1, β (d w).2) :=
    ⟨d.trans (α.prodCongr β), fun _ => rfl⟩
  have he : ∀ u v, e (dC (AF F ⊗[F] E) nT * u + dCd F JT * v) = (α v, β u) := fun u v => by
    rw [he0, ← hd' (v, u), d.apply_symm_apply]
  have j1 : IsModuleTopology (AF F) (Fin N → AF F) := inferInstance
  have j2 : IsModuleTopology (AF F) (VA F N) := inferInstance
  have c1 := cont2 (modTop _ _) j2 e
  have c2 := cont2 (modTop _ _) j1 α
  have c3 := cont2 (modTop _ _) j1 β
  refine ⟨N, α, β, e, he, fun w w' => ?_, fun x => ?_, fun y z => ?_, c1.1, c1.2, c2.1, c2.2, c3.1, c3.2,
    fun x => ⟨_, hb x⟩, fun y => ⟨b.symm y, by rw [hb, LinearEquiv.apply_symm_apply]⟩⟩
  · obtain ⟨⟨v, u⟩, rfl⟩ := d.symm.surjective w
    obtain ⟨⟨v', u'⟩, rfl⟩ := d.symm.surjective w'
    have s1 : symplOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ (dC (AF F ⊗[F] E) nT * u)
        (dC (AF F ⊗[F] E) nT * u') = 0 := by rw [symplOF, h_CC, mul_zero, map_zero]
    have s2 : symplOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ (dCd F JT * v) (dCd F JT * v') = 0 := by
      rw [symplOF, dCd_eq, Matrix.mul_assoc, Matrix.mul_assoc, h_AA, mul_zero, map_zero]
    have s3 := GlobalTheory.T.adelicSymplecticTraceForm_alternating_swap F E σ hinv _ _ JS _ hS (GlobalTheory.WeilSchrodinger.DblTargetF.isHermND_dblG hT) ξ₀ hσ
      (dCd F JT * v') (dC (AF F ⊗[F] E) nT * u)
    rw [hd', hd', he, he, GlobalTheory.ThetaSchurF.symplOF_add_left, GlobalTheory.ThetaSchurF.symplOF_add_right,
      GlobalTheory.ThetaSchurF.symplOF_add_right, s1, s2, s3, hP, hP, symV]
    ring
  · refine ⟨a (V * x), b (U * x), ?_⟩
    rw [he0, hd, rat_mul, rat_mul, ha, hb]
  · refine ⟨dC E nT * b.symm z + dCdE JT * a.symm y, ?_⟩
    have : (ratWF (dC E nT * b.symm z + dCdE JT * a.symm y) : WOF F E nS (nT + nT)) =
        dC (AF F ⊗[F] E) nT * (ratWF (b.symm z) : WOF F E nS nT) + dCd F JT * (ratWF (a.symm y) : WOF F E nS nT) := by
      rw [← dC_map (incAF F E), dCd, rat_mul, rat_mul]
      exact Matrix.map_add _ (map_add _) _ _
    rw [this, he, ha, hb, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
end PositivityTheory.ThKW.AdelicSchwartzProperties
end
end
