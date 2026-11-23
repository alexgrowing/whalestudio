import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.OneAddPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoMulInvOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilTransportAdelicSchwartzCmExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurLemmaHeisenbergCommutingThetaOperator
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

def adB (b : Module.Basis (Fin N) F (Matrix (Fin nT) (Fin nS) E)) : Module.Basis (Fin N) (AF F) (WOF F E nS nT) :=
  (b.baseChange (AF F)).map (matBC (AF F))

theorem adB_apply (b : Module.Basis (Fin N) F (Matrix (Fin nT) (Fin nS) E)) (i : Fin N) : adB b i = ratWF (b i) := by
  rw [adB, Module.Basis.map_apply, Module.Basis.baseChange_apply, matBC_one]; rfl

theorem adB_rat (b : Module.Basis (Fin N) F (Matrix (Fin nT) (Fin nS) E)) (x : Matrix (Fin nT) (Fin nS) E) :
    (adB b).equivFun (ratWF x) = GlobalTheory.SWQ.rat (b.equivFun x) := by
  funext i
  have e : (ratWF x : WOF F E nS nT) = matBC (AF F) ((1 : AF F) ⊗ₜ[F] x) := (matBC_one (AF F) x).symm
  rw [Module.Basis.equivFun_apply, adB, Module.Basis.map_repr, LinearEquiv.trans_apply, e, LinearEquiv.symm_apply_apply,
    Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
  rfl

theorem aC_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (n : ℕ) : (aC R n).map φ = aC S n := by
  ext i j
  obtain ⟨p, rfl⟩ := finSumFinEquiv.surjective i
  simp only [Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
  rcases p with p | p <;> simp [Matrix.one_apply, apply_ite φ]

theorem dCdE_eq (J : Matrix (Fin nT) (Fin nT) E) : dCdE J = aC E nT * ((1 / 2 : E) • J⁻¹) := by
  ext i j
  obtain ⟨p, rfl⟩ := finSumFinEquiv.surjective i
  simp only [dCdE, Matrix.mul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
  rcases p with p | p <;> simp [Matrix.one_apply]

theorem dCd_eq (J : Matrix (Fin nT) (Fin nT) E) :
    dCd F J = aC (AF F ⊗[F] E) nT * ((1 / 2 : E) • J⁻¹).map (incAF F E) := by
  rw [dCd, dCdE_eq, Matrix.map_mul, aC_map]

theorem dbl_map (J : Matrix (Fin nT) (Fin nT) E) : (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J).map (incAF F E) =
    (dbl (J.map (incAF F E))).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
  ext i j
  obtain ⟨p, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨r, rfl⟩ := finSumFinEquiv.surjective j
  simp only [GlobalTheory.WeilSchrodinger.DblTargetF.dblG, dbl, Matrix.map_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases p with p | p <;> rcases r with r | r <;> simp

theorem h_CC (JS : Matrix (Fin nS) (Fin nS) E) (J : Matrix (Fin nT) (Fin nT) E) (u u' : WOF F E nS nT) :
    hOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) (dC (AF F ⊗[F] E) nT * u) (dC (AF F ⊗[F] E) nT * u') = 0 := by
  rw [hOF_eq_trace, Matrix.map_mul, dC_map, Matrix.transpose_mul, dbl_map, Matrix.mul_assoc _ (dC _ nT)ᵀ, C_D]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (aC _ nT)ᵀ, A_C]
  simp

theorem h_AA (JS : Matrix (Fin nS) (Fin nS) E) (J : Matrix (Fin nT) (Fin nT) E) (u u' : WOF F E nS nT) :
    hOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) (aC (AF F ⊗[F] E) nT * u) (aC (AF F ⊗[F] E) nT * u') = 0 := by
  rw [hOF_eq_trace, Matrix.map_mul, aC_map, Matrix.transpose_mul, dbl_map, Matrix.mul_assoc _ (aC _ nT)ᵀ, A_D]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (dC _ nT)ᵀ, C_A]
  simp

theorem C_C {R : Type} [CommRing R] {n : ℕ} : (dC R n)ᵀ * dC R n = (2 : R) • 1 := by
  rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, diagCols, Matrix.transpose_fromRows,
    Matrix.fromCols_mul_fromRows]
  simp [two_smul]

theorem proj_facts (J : Matrix (Fin nT) (Fin nT) E) (hJ : J.det ≠ 0) :
    ∃ U V : Matrix (Fin nT) (Fin (nT + nT)) E, U * dC E nT = 1 ∧ U * dCdE J = 0 ∧ V * dC E nT = 0 ∧ V * dCdE J = 1 ∧
      dC E nT * U + dCdE J * V = 1 := by
  refine ⟨(1 / 2 : E) • (dC E nT)ᵀ, J * (aC E nT)ᵀ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.smul_mul, C_C, smul_smul]; norm_num
  · rw [dCdE_eq, ← Matrix.mul_assoc, Matrix.smul_mul, C_A]; simp
  · rw [Matrix.mul_assoc, A_C, Matrix.mul_zero]
  · rw [← C_D]; exact dC_dual J hJ
  · rw [dCdE_eq, Matrix.mul_assoc, ← Matrix.mul_assoc _ J, Matrix.smul_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hJ),
      Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_smul, ← smul_add, CC_add, smul_smul]
    norm_num

theorem rat_mul {a b c : ℕ} (M : Matrix (Fin a) (Fin b) E) (x : Matrix (Fin b) (Fin c) E) :
    (M.map (incAF F E) * (ratWF x : WOF F E c b) : Matrix (Fin a) (Fin c) (AF F ⊗[F] E)) = ratWF (M * x) :=
  Matrix.map_mul.symm

theorem pairing {B : Base F E} (hB : B.IsGood σ) {JS : Matrix (Fin nS) (Fin nS) E}
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

theorem split (JT : Matrix (Fin nT) (Fin nT) E) (hT : IsHermND σ JT) :
    ∃ (d : WOF F E nS (nT + nT) ≃ₗ[AF F] WOF F E nS nT × WOF F E nS nT) (U V : Matrix (Fin nT) (Fin (nT + nT)) E),
      (∀ w, d w = (V.map (incAF F E) * w, U.map (incAF F E) * w)) ∧
      ∀ p, d.symm p = dC (AF F ⊗[F] E) nT * p.2 + dCd F JT * p.1 := by
  obtain ⟨U, V, p1, p2, p3, p4, p5⟩ := proj_facts JT hT.2
  have m := fun {a b : ℕ} {X Y : Matrix (Fin a) (Fin b) E} (h : X = Y) =>
    congrArg (fun M : Matrix (Fin a) (Fin b) E => M.map (incAF F E)) h
  have q1 := m p1
  have q2 := m p2
  have q3 := m p3
  have q4 := m p4
  have q5 := m p5
  simp only [Matrix.map_mul, dC_map, Matrix.map_add _ (map_add (incAF F E)), Matrix.map_one _ (map_zero (incAF F E))
    (map_one (incAF F E)), Matrix.map_zero _ (map_zero (incAF F E))] at q1 q2 q3 q4 q5
  rw [show (dCdE JT).map (incAF F E) = dCd F JT from rfl] at q2 q4 q5
  let d : WOF F E nS (nT + nT) ≃ₗ[AF F] WOF F E nS nT × WOF F E nS nT :=
    { toFun := fun w => (V.map (incAF F E) * w, U.map (incAF F E) * w)
      invFun := fun p => dC (AF F ⊗[F] E) nT * p.2 + dCd F JT * p.1
      map_add' := fun x y => Prod.ext (Matrix.mul_add _ _ _) (Matrix.mul_add _ _ _)
      map_smul' := fun a x => Prod.ext (Matrix.mul_smul _ _ _) (Matrix.mul_smul _ _ _)
      left_inv := fun w => by
        simp only [← Matrix.mul_assoc]
        rw [← Matrix.add_mul, q5, Matrix.one_mul]
      right_inv := fun p => by
        simp only [Matrix.mul_add, ← Matrix.mul_assoc, q1, q2, q3, q4, Matrix.one_mul, Matrix.zero_mul, add_zero, zero_add] }
  exact ⟨d, U, V, fun _ => rfl, fun _ => rfl⟩

theorem modTop (a c : ℕ) : IsModuleTopology (AF F) (WOF F E a c) := by
  have i0 : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have := IsModuleTopology.toContinuousAdd (AF F) (AF F ⊗[F] E)
  exact inferInstanceAs (IsModuleTopology (AF F) (Fin c → Fin a → AF F ⊗[F] E))

theorem cont2 {M M' : Type} [AddCommGroup M] [AddCommGroup M'] [Module (AF F) M] [Module (AF F) M'] [TopologicalSpace M]
    [TopologicalSpace M'] (h : IsModuleTopology (AF F) M) (h' : IsModuleTopology (AF F) M') (e : M ≃ₗ[AF F] M') :
    Continuous e ∧ Continuous e.symm := by
  have := IsModuleTopology.toContinuousAdd (AF F) M
  have := IsModuleTopology.toContinuousAdd (AF F) M'
  have := IsModuleTopology.toContinuousSMul (AF F) M
  have := IsModuleTopology.toContinuousSMul (AF F) M'
  exact ⟨IsModuleTopology.continuous_of_linearMap e.toLinearMap, IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap⟩

theorem coords {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E}
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
  obtain ⟨N, α, β, a, b, hP, ha, hb⟩ := pairing hB hS hT hξ
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
