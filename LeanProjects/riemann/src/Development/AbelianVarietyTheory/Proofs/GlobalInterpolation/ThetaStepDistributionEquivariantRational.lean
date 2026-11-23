import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BelowFiniteNonempty
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SubstitutionAdjoint
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GmapToAddSubgroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmulLatMatOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetIdLatGmap
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JetOpIdentityOfEntire
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormEqOfSplit
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NotDvdDifferent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OrdDetConjFinite
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DeltaNeZero
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetStepEqZeroExample
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalisedFamilyLatticeHypAndSmoothStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JetCCompSubstStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HeckeCharProductFormulaNormOneStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TameCharacterValuesEqHeckeCharLocalValuesStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalCharEqHeckeCharLocalComponentOfValuesStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.KerT

namespace GlobalTheory.KerT.RatLaw

section Alg

open MvPolynomial

variable {K : Type} [Field K] {ι : Type} {a b : ℕ}

abbrev tabFn (J : (DVar ι a b →₀ ℕ) → K) : MvPolynomial (DVar ι a b) K →ₗ[K] K := (basisMonomials (DVar ι a b) K).constr K J

abbrev subst (g : ι → Matrix (Fin a) (Fin a) K) (h : ι → Matrix (Fin b) (Fin b) K) (k : DVar ι a b) : MvPolynomial (DVar ι a b) K :=
  ∑ i : Fin b, ∑ j : Fin a, C (h k.1 i k.2.1 * g k.1 k.2.2 j) * X (k.1, i, j)

theorem jetLin_monomial (J : (DVar ι a b →₀ ℕ) → K) (m : (ι × Fin b × Fin b) ⊕ DVar ι a b →₀ ℕ) :
    jetLin J (monomial m 1) = monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn)
      (J (m.comapDomain Sum.inr Sum.inr_injective.injOn)) := by
  have := (basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) K).constr_basis K (fun m =>
    (monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn) (J (m.comapDomain Sum.inr Sum.inr_injective.injOn)) : Pol K ι b)) m
  rw [coe_basisMonomials] at this
  exact this

theorem tabFn_monomial (J : (DVar ι a b →₀ ℕ) → K) (m : DVar ι a b →₀ ℕ) : tabFn J (monomial m 1) = J m := by
  have := (basisMonomials (DVar ι a b) K).constr_basis K J m
  rwa [coe_basisMonomials] at this

theorem monomial_split {α β : Type} (m : α ⊕ β →₀ ℕ) :
    (monomial m 1 : MvPolynomial (α ⊕ β) K) = rename Sum.inl (monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn) 1) *
      rename Sum.inr (monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn) 1) := by
  rw [rename_monomial, rename_monomial, monomial_mul, one_mul]
  congr 2
  ext (x | x)
  · rw [Finsupp.add_apply, Finsupp.mapDomain_apply Sum.inl_injective, Finsupp.mapDomain_notin_range _ _ (by simp)]
    simp
  · rw [Finsupp.add_apply, Finsupp.mapDomain_apply Sum.inr_injective, Finsupp.mapDomain_notin_range _ _ (by simp)]
    simp

theorem jetLin_mul (J : (DVar ι a b →₀ ℕ) → K) (p : Pol K ι b) (q : MvPolynomial (DVar ι a b) K) :
    jetLin J (rename Sum.inl p * rename Sum.inr q) = tabFn J q • p := by
  induction p using MvPolynomial.induction_on' with
  | add p p' h h' => rw [map_add, add_mul, map_add, h, h', smul_add]
  | monomial m c =>
    induction q using MvPolynomial.induction_on' with
    | add q q' h h' => rw [map_add, mul_add, map_add, h, h', map_add, add_smul]
    | monomial m' c' =>
      have e : ∀ {σ : Type} (m : σ →₀ ℕ) (c : K), (monomial m c : MvPolynomial σ K) = c • monomial m 1 := fun m c => by
        rw [smul_monomial, smul_eq_mul, mul_one]
      have e1 : (m.mapDomain Sum.inl + m'.mapDomain Sum.inr).comapDomain Sum.inl Sum.inl_injective.injOn = m := by
        ext x
        rw [Finsupp.comapDomain_apply, Finsupp.add_apply, Finsupp.mapDomain_apply Sum.inl_injective,
          Finsupp.mapDomain_notin_range _ _ (by simp), add_zero]
      have e2 : (m.mapDomain Sum.inl + m'.mapDomain Sum.inr).comapDomain Sum.inr Sum.inr_injective.injOn = m' := by
        ext x
        rw [Finsupp.comapDomain_apply, Finsupp.add_apply, Finsupp.mapDomain_apply Sum.inr_injective,
          Finsupp.mapDomain_notin_range _ _ (by simp), zero_add]
      rw [rename_monomial, rename_monomial, monomial_mul, e _ (c * c'), map_smul, jetLin_monomial, e1, e2, e m' c', map_smul,
        tabFn_monomial, smul_monomial, smul_monomial]
      congr 1
      simp only [smul_eq_mul]
      ring

theorem jetLin_right {J J' : (DVar ι a b →₀ ℕ) → K} (φ : DVar ι a b → MvPolynomial (DVar ι a b) K)
    (hJ : ∀ m, J' m = tabFn J (aeval φ (monomial m (1 : K)))) (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) :
    jetLin J' Q = jetLin J (aeval (Sum.elim (fun v => X (Sum.inl v)) fun k => rename Sum.inr (φ k)) Q) := by
  refine LinearMap.congr_fun (g := jetLin J ∘ₗ (aeval (Sum.elim (fun v => X (Sum.inl v)) fun k => rename Sum.inr (φ k))).toLinearMap)
    ((basisMonomials _ K).ext fun m => ?_) Q
  rw [coe_basisMonomials]
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [monomial_split, jetLin_mul, tabFn_monomial, hJ, map_mul, aeval_rename, aeval_rename, ← jetLin_mul]
  congr 2
  · refine AlgHom.congr_fun (φ₁ := rename Sum.inl) (MvPolynomial.algHom_ext fun v => ?_) _
    simp
  · refine AlgHom.congr_fun (φ₁ := (rename Sum.inr).comp (aeval φ)) (MvPolynomial.algHom_ext fun v => ?_) _
    simp

theorem jetLin_left (J : (DVar ι a b →₀ ℕ) → K) (ψ : Pol K ι b →ₐ[K] Pol K ι b)
    (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) :
    jetLin J (aeval (Sum.elim (fun v => rename Sum.inl (ψ (X v))) fun k => X (Sum.inr k)) Q) = ψ (jetLin J Q) := by
  refine LinearMap.congr_fun (f := jetLin J ∘ₗ (aeval (Sum.elim (fun v => rename Sum.inl (ψ (X v))) fun k => X (Sum.inr k))).toLinearMap)
    (g := ψ.toLinearMap ∘ₗ jetLin J) ((basisMonomials _ K).ext fun m => ?_) Q
  rw [coe_basisMonomials]
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [monomial_split, jetLin_mul, map_smul, map_mul, aeval_rename, aeval_rename, ← jetLin_mul]
  congr 2
  · refine AlgHom.congr_fun (φ₂ := (rename Sum.inl).comp ψ) (MvPolynomial.algHom_ext fun v => ?_) _
    simp
  · refine AlgHom.congr_fun (φ₂ := rename Sum.inr) (MvPolynomial.algHom_ext fun v => ?_) _
    simp

theorem subD_subst (g : ι → Matrix (Fin a) (Fin a) K) (h : ι → Matrix (Fin b) (Fin b) K) (P : Pol K ι a) :
    aeval (Sum.elim (fun v => X (Sum.inl v)) fun k => rename Sum.inr (subst g h k)) (subD K ι a b P) =
      (aeval (Sum.elim (fun v => rename Sum.inl (Formalism.GradedWeylDivisibility.blockAct K h (X v : Pol K ι b))) fun k => X (Sum.inr k))
        (subD K ι a b (Formalism.GradedWeylDivisibility.blockAct K g P)) : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) := by
  refine AlgHom.congr_fun (φ₁ := (aeval _).comp (subD K ι a b))
    (φ₂ := (aeval _).comp ((subD K ι a b).comp (Formalism.GradedWeylDivisibility.blockAct K g))) (MvPolynomial.algHom_ext fun v => ?_) P
  obtain ⟨τ, α, s⟩ := v
  by_cases hs : s.1 < b
  · simp only [AlgHom.comp_apply, Formalism.GradedWeylDivisibility.blockAct, subD, aeval_X, map_sum, map_mul, algHom_C, dif_pos hs, Sum.elim_inl,
      Sum.elim_inr, rename_X, algebraMap_eq, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_congr rfl fun _ _ => Finset.sum_comm, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun β _ => ?_
    ring
  · simp [Formalism.GradedWeylDivisibility.blockAct, subD, dif_neg hs]

theorem blockAct_frDet (g : ι → Matrix (Fin a) (Fin a) K) (τ : ι) :
    Formalism.GradedWeylDivisibility.blockAct K g (frDet K a τ) = C (g τ).det * frDet K a τ := by
  rw [frDet, AlgHom.map_det, RingHom.map_det, ← Matrix.det_mul]
  congr 1
  ext1 α s
  simp [Formalism.GradedWeylDivisibility.blockAct, Matrix.mul_apply]

variable [Fintype ι]

theorem jetMap_subst {J J' : (DVar ι a b →₀ ℕ) → K} (g : ι → Matrix (Fin a) (Fin a) K) (h : ι → Matrix (Fin b) (Fin b) K)
    (hJ : ∀ m, J' m = tabFn J (aeval (subst g h) (monomial m (1 : K)))) (n : ι → ℕ)
    (P : Pol K ι a) :
    jetMap J' n P = (∏ τ, (g τ).det ^ n τ) • Formalism.GradedWeylDivisibility.blockAct K h (jetMap J n (Formalism.GradedWeylDivisibility.blockAct K g P)) := by
  simp only [jetMap, LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.mulRight_apply]
  rw [jetLin_right _ hJ, subD_subst, jetLin_left, ← map_smul, ← map_smul, ← map_smul, map_mul, map_prod]
  congr 3
  simp only [map_pow, blockAct_frDet, mul_pow, Finset.prod_mul_distrib, smul_eq_C_mul, map_prod]
  ring

theorem map_jetMap {L : Type} [Field L] (σ : K →+* L) (J : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) (P : Pol K ι a) :
    map σ (jetMap J n P) = jetMap (fun m => σ (J m)) n (map σ P) := by
  have h1 : ∀ Q, map σ (jetLin J Q) = jetLin (fun m => σ (J m)) (map σ Q) := fun Q => by
    induction Q using MvPolynomial.induction_on' with
    | add p p' h h' => simp only [map_add, h, h']
    | monomial m c =>
      have e : ∀ {M : Type} [Field M] {σ : Type} (m : σ →₀ ℕ) (c : M), (monomial m c : MvPolynomial σ M) = c • monomial m 1 :=
        fun m c => by rw [smul_monomial, smul_eq_mul, mul_one]
      rw [map_monomial, e m c, e m (σ c), LinearMap.map_smul, LinearMap.map_smul, jetLin_monomial, jetLin_monomial, smul_monomial, smul_monomial,
        map_monomial, smul_eq_mul, map_mul, smul_eq_mul]
  have h2 : ∀ Q, map σ (subD K ι a b Q) = subD L ι a b (map σ Q) := fun Q => by
    induction Q using MvPolynomial.induction_on with
    | C c => simp [subD]
    | add p q h h' => simp only [map_add, h, h']
    | mul_X p v h =>
      simp only [map_mul, h, map_X]
      congr 1
      simp only [subD, aeval_X]
      split_ifs <;> simp
  have h3 : ∀ τ : ι, map σ (frDet K a τ) = frDet L a τ := fun τ => by
    rw [frDet, RingHom.map_det]
    congr 1
    ext1 α s
    simp
  simp only [jetMap, LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.mulRight_apply, h1, h2, map_mul, map_prod,
    map_pow, h3]

omit [Fintype ι] in
theorem map_blockAct {L : Type} [Field L] (σ : K →+* L) (g : ι → Matrix (Fin a) (Fin a) K) (P : Pol K ι a) :
    map σ (Formalism.GradedWeylDivisibility.blockAct K g P) = Formalism.GradedWeylDivisibility.blockAct L (fun τ => (g τ).map σ) (map σ P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q h h' => simp only [map_add, h, h']
  | mul_X p v h =>
    simp only [map_mul, h, map_X]
    simp [Formalism.GradedWeylDivisibility.blockAct]

end Alg

section Jet

open MvPolynomial

theorem jetMap_congr {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {a b : ℕ} (lam : ι → DomWeight a) (n : ι → ℕ)
    (J J' : (DVar ι a b →₀ ℕ) → K)
    (h : ∀ m : DVar ι a b →₀ ℕ, (∀ τ, ((∑ β : Fin b, ∑ α : Fin a, m (τ, β, α) : ℕ) : ℤ) =
      ∑ s : Fin a, ((lam τ).w s - (lam τ).detShift + (n τ : ℤ))) → J m = J' m) {P : Pol K ι a}
    (hP : ∀ τ, IsWeightedHomogeneous (GlobalTheory.JetDeg.posW a τ) P (∑ i, (lam τ).natW i)) : jetMap J n P = jetMap J' n P := by
  simp only [jetMap, LinearMap.comp_apply]
  refine GlobalTheory.JetIdentity.jetLin_congr J J' _ fun μ hμ => h _ fun τ => ?_
  have h1 := GlobalTheory.JetDeg.subD_hom (b := b) τ (GlobalTheory.JetDeg.sharp_hom n τ (hP τ)) (mem_support_iff.mp hμ)
  rw [GlobalTheory.JetDeg.weight_derW] at h1
  simp only [Finsupp.comapDomain_apply]
  rw [h1]
  push_cast
  simp [GlobalTheory.JetDeg.natW_cast, Finset.sum_add_distrib, mul_comm]

variable {X : Fields} {a b : ℕ}

def matAt (f : Sp X.E a ≃ₗ[X.E] Sp X.E a) (τ : X.Tau) : Matrix (Fin a) (Fin a) X.K :=
  (LinearMap.toMatrix' f.toLinearMap).map (X.emb τ)

theorem det_matAt (f : Sp X.E a ≃ₗ[X.E] Sp X.E a) (τ : X.Tau) :
    (matAt f τ).det = X.emb τ ((LinearEquiv.det f : X.Eˣ) : X.E) := by
  rw [matAt, LinearEquiv.coe_det, ← LinearMap.det_toMatrix', RingHom.map_det]
  rfl

theorem coe_rho (lam : X.Tau → DomWeight a) (γ : UF X.E a) (P : VV X.K lam) :
    ((rhoVr X.emb lam (ufGL X.E a γ) P : VV X.K lam) : Pol X.K X.Tau a) =
      (∏ τ, X.emb τ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) ^ (-(lam τ).detShift)) •
        Formalism.GradedWeylDivisibility.blockAct X.K (matAt γ.1.symm) (P : Pol X.K X.Tau a) := by
  have e : ∀ τ, ((invTrK (embGL X.emb (ufGL X.E a γ)) τ : GL (Fin a) X.K) : Matrix (Fin a) (Fin a) X.K).transpose =
      matAt γ.1.symm τ := fun τ => rfl
  change detTwK lam (invTrK (embGL X.emb (ufGL X.E a γ))) • trAct (invTrK (embGL X.emb (ufGL X.E a γ))) (P : Pol X.K X.Tau a) = _
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [detPow, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.det_transpose, e, det_matAt,
    LinearEquiv.det_symm, map_inv, Units.val_inv_eq_inv_val, map_inv₀, inv_zpow']

theorem jetMap_pull (A : Amb X) (n : X.Tau → ℕ) (f : Sp X.E a ≃ₗ[X.E] Sp X.E a) (f' : Sp X.E b ≃ₗ[X.E] Sp X.E b)
    (G : VCx X.Tau a b → ℂ) (hG : ∀ k : ℕ, ContDiff ℂ k G) (Q : Pol X.K X.Tau a) :
    jetMap (jetC A.cD fun z => G (A.pullV a b f f' z)) n (map A.σ₀ Q) =
      A.σ₀ (∏ τ, X.emb τ ((LinearEquiv.det f : X.Eˣ) : X.E) ^ n τ) •
        Formalism.GradedWeylDivisibility.blockAct ℂ (fun τ => (matAt f'.symm τ).map A.σ₀)
          (jetMap (jetC A.cD G) n (map A.σ₀ (Formalism.GradedWeylDivisibility.blockAct X.K (matAt f) Q))) := by
  have ch := GlobalTheory.T.jetC_constr_aeval_monomial X.Tau a b A.cD G (fun τ => (matAt f τ).map A.σ₀) (fun τ => (matAt f'.symm τ).map A.σ₀) hG
  have e0 : (fun z => G (A.pullV a b f f' z)) = fun z : VCx X.Tau a b => G fun τ i j => ∑ k : Fin b, ∑ l : Fin a,
      (matAt f'.symm τ).map A.σ₀ i k * z τ k l * (matAt f τ).map A.σ₀ l j := by
    funext z
    refine congrArg G (funext fun τ => funext fun i => funext fun j => ?_)
    simp only [Amb.pullV, matAt, Matrix.map_apply, LinearMap.toMatrix'_apply, Fields.embC, RingHom.comp_apply, LinearEquiv.coe_coe]
  have e1 := jetMap_subst (J := jetC A.cD G) (fun τ => (matAt f τ).map A.σ₀) (fun τ => (matAt f'.symm τ).map A.σ₀) ch n
    (map A.σ₀ Q)
  rw [e0, e1, map_blockAct, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← det_matAt, map_pow, RingHom.map_det]
  rfl

theorem scal_pull (lam : X.Tau → ℤ) (lam' : X.Tau → ℤ) (n : X.Tau → ℕ) (z z' : X.Eˣ) (r : X.K) :
    r * (∏ τ, X.emb τ (z : X.E) ^ ((n τ : ℤ) - lam τ)) * (∏ τ, X.emb τ (z' : X.E) ^ lam' τ) *
      (∏ τ, X.emb τ (z' : X.E) ^ (-lam' τ)) * ∏ τ, X.emb τ ((z⁻¹ : X.Eˣ) : X.E) ^ (-lam τ) = r * ∏ τ, X.emb τ (z : X.E) ^ n τ := by
  have d0 : ∀ (y : X.Eˣ) τ, X.emb τ (y : X.E) ≠ 0 := fun f τ => by simp
  have d2 : (∏ τ, X.emb τ (z' : X.E) ^ lam' τ) * ∏ τ, X.emb τ (z' : X.E) ^ (-lam' τ) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun τ _ => by rw [← zpow_add₀ (d0 _ τ), add_neg_cancel, zpow_zero]
  have d3 : (∏ τ, X.emb τ (z : X.E) ^ ((n τ : ℤ) - lam τ)) * ∏ τ, X.emb τ ((z⁻¹ : X.Eˣ) : X.E) ^ (-lam τ) =
      ∏ τ, X.emb τ (z : X.E) ^ n τ := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [Units.val_inv_eq_inv_val, map_inv₀, inv_zpow', ← zpow_add₀ (d0 _ τ), neg_neg, sub_add_cancel, zpow_natCast]
  rw [mul_assoc (r * _), d2, mul_one, mul_assoc, d3]

theorem jetOp_pull (A : Amb X) (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ)
    (hV : JetInVV X.K lam lam' n) (γ : UF X.E a) (γ' : UF X.E b) (G : VCx X.Tau a b → ℂ) (hG : ∀ k : ℕ, ContDiff ℂ k G)
    (u₁ u₂ : ℂ) (r : X.K) (hu : u₁ = A.σ₀ r * u₂)
    (h₁ : ∀ m : DVar X.Tau a b →₀ ℕ, (∀ τ, (GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.degAt m τ : ℤ) = GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.degNu lam n τ) →
      ∃ k : X.K, A.σ₀ k = u₁ * jetC A.cD (fun z => G (A.pullV a b γ.1 γ'.1 z)) m)
    (h₂ : ∀ m : DVar X.Tau a b →₀ ℕ, (∀ τ, (GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.degAt m τ : ℤ) = GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.degNu lam n τ) →
      ∃ k : X.K, A.σ₀ k = u₂ * jetC A.cD G m) :
    jetOp lam lam' (fun m => desc A.σ₀ (u₁ * jetC A.cD (fun z => G (A.pullV a b γ.1 γ'.1 z)) m)) n =
      (r * (∏ τ, X.emb τ ((LinearEquiv.det γ.1 : X.Eˣ) : X.E) ^ ((n τ : ℤ) - (lam τ).detShift)) *
          ∏ τ, X.emb τ ((LinearEquiv.det γ'.1 : X.Eˣ) : X.E) ^ (lam' τ).detShift) •
        (rhoVr X.emb lam' (ufGL X.E b γ') ∘ₗ jetOp lam lam' (fun m => desc A.σ₀ (u₂ * jetC A.cD G m)) n ∘ₗ
          rhoVr X.emb lam (ufGL X.E a γ⁻¹)) := by
  refine LinearMap.ext fun P => Subtype.ext (map_injective A.σ₀ A.σ₀.injective ?_)
  have hom : ∀ (Q : VV X.K lam) τ, IsWeightedHomogeneous (GlobalTheory.JetDeg.posW a τ) (map A.σ₀ (Q : Pol X.K X.Tau a))
      (∑ i, (lam τ).natW i) := fun Q τ d hd => GlobalTheory.JetDeg.VV_hom lam τ Q.2 fun h0 => hd (by rw [coeff_map, h0, map_zero])
  have sm : ∀ {c : ℕ} (k : X.K) (Q : Pol X.K X.Tau c), map A.σ₀ (k • Q) = A.σ₀ k • map A.σ₀ Q := fun k Q => by
    rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C]
  have js : ∀ (u : ℂ) (J : (DVar X.Tau a b →₀ ℕ) → ℂ),
      (∀ m : DVar X.Tau a b →₀ ℕ, (∀ τ, (GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.degAt m τ : ℤ) = GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.degNu lam n τ) →
        ∃ k : X.K, A.σ₀ k = u * J m) → ∀ Q : VV X.K lam,
      map A.σ₀ (jetOp lam lam' (fun m => desc A.σ₀ (u * J m)) n Q : Pol X.K X.Tau b) =
        u • jetMap J n (map A.σ₀ (Q : Pol X.K X.Tau a)) := fun u J h Q => by
    rw [jetOp_coe _ _ _ hV, map_jetMap, jetMap_congr lam n _ (fun m => u * J m) (fun m hm => GlobalTheory.JetIdentity.map_desc _ (h m hm)) (hom Q)]
    exact LinearMap.congr_fun (GlobalTheory.JetIdentity.jetLin_smul u J) _
  have e2 : LinearEquiv.det (γ⁻¹).1 = (LinearEquiv.det γ.1)⁻¹ := by rw [Subgroup.coe_inv, map_inv]
  have e3 : (γ⁻¹).1.symm = γ.1 := rfl
  rw [LinearMap.smul_apply, Submodule.coe_smul, LinearMap.comp_apply, LinearMap.comp_apply, coe_rho, smul_smul, sm, map_blockAct,
    js _ _ h₁, js _ _ h₂, jetMap_pull A n _ _ G hG, coe_rho, sm, e2, e3, LinearMap.map_smul, map_smul, map_smul, smul_smul,
    smul_smul, smul_smul, hu, mul_right_comm, ← map_mul, mul_right_comm (A.σ₀ _), ← map_mul, scal_pull]

end Jet

section Mu

open Formalism.L2.Host (HChar ordF)
open GlobalTheory.CharVal (valuation_conjP)

theorem locK_eq_zpow {E : Type} [Field E] [NumberField E] {χ : HChar E} {P : HeightOneSpectrum (𝓞 E)} (h : χ.UnrAt P) (z : Eˣ) :
    χ.locK P z = χ.val P ^ ordE P (z : E) := by
  rw [HChar.val, ← map_zpow, ← div_eq_one, ← map_div]
  refine GlobalTheory.NormOneUnit.locK_unr h ?_
  have h0 : P.valuation E (z : E) ≠ 0 := by simp
  rw [Units.val_div_eq_div_val, Units.val_zpow_eq_zpow_val, map_div₀, map_zpow₀, GlobalTheory.CharVal.val_unif, ← WithZero.exp_zsmul, ordE,
    smul_neg, smul_eq_mul, mul_one, neg_neg, WithZero.exp_log h0, div_self h0]

theorem ordDet_gmap {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E))
    (f : Sp E n ≃ₗ[E] Sp E n) {N : Submodule (𝓞 E) (Sp E n)} (hN : IsSdLat N) :
    ordDet P (gmap f N) = ordE P ((LinearEquiv.det f : Eˣ) : E) + ordDet P N := by
  obtain ⟨g, hg⟩ := GlobalTheory.CharValCompare.exists_isFr P hN.1
  have h2 : GlobalTheory.CharValCompare.IsFr P (gmap f N) (f * g) := fun x => by
    rw [mem_localization_gmap, ← hg x]
    simp
  rw [GlobalTheory.CharValCompare.ordDet_eq hg, GlobalTheory.CharValCompare.ordDet_eq h2, ordE, ordE, ordE, GlobalTheory.CharValCompare.dt, map_mul,
    Units.val_mul, map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 (Units.ne_zero _))
      ((Valuation.ne_zero_iff _).2 (Units.ne_zero _)), neg_add]

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {σ₀ : X.K →+* ℂ} {e : Fin R.m → X.Tau → ℚ} {m0 : Fin R.m → HChar X.E} {eta ξ : HChar X.E}

theorem xi_tame (hξ : GlobalTheory.Mem.Col2.Reads σ₀ (mu : Chr X.F X.E X.K) ξ) (P : HeightOneSpectrum (𝓞 X.E)) : ξ.TameAt P :=
  GlobalTheory.Mem.ReadTwist.tameAt hξ (fun v => Subgroup.mem_iInf.1 mu.2.1.2 v) P

theorem xi_unr (hξ : GlobalTheory.Mem.Col2.Reads σ₀ (mu : Chr X.F X.E X.K) ξ) {P : HeightOneSpectrum (𝓞 X.E)}
    (h : sel (P.under (𝓞 X.F)) ∉ QE sel (mu : Chr X.F X.E X.K)) : ξ.UnrAt P := by
  classical
  by_contra hn
  have hf := auxiliary_primes_finite X.F X.E X.K (mu : Chr X.F X.E X.K) mu.2.1.1.1.1.2
  apply h
  rw [QE, dif_pos hf]
  exact Finset.mem_image_of_mem _ (hf.mem_toFinset.2 ((GlobalTheory.Mem.ReadTwist.mem_qprime_iff hξ _).2 ⟨P, rfl, hn⟩))

theorem muAtT_eq (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (u : Pr.Word) (hT : Pr.T u ∈ S) (hg : ∀ k, Pr.g k ∈ S)
    (ht : Ch.Tied σ₀ e m0 eta) (hc : MuqTieG (Pr := Pr) (R := R) sel mu cst σ₀ m0)
    (hξ : GlobalTheory.Mem.Col2.Reads σ₀ (mu : Chr X.F X.E X.K) ξ) (j : Fin R.m) (P : rowSG Pr sel mu) (a : X.Eˣ) :
    σ₀ (muAtT Ch sel mu cst j.1 P (a : X.E)) = ((((m0 j * ξ).locK P.1 a)⁻¹ : ℂˣ) : ℂ) := by
  classical
  have bad := GlobalTheory.ThetaMove.BadPrimes.bad_primes X Pr sel S mu u hX hPr hsel hT hg P.1 (Finset.mem_union_right _ P.2)
  have tw := (GlobalTheory.T.tame_character_values_eq_heckeChar_local_values X.F X.E X.K σ₀ _ ξ hξ (xi_tame hξ) P.1).2 bad.2.2.1
  have lk : ∀ y, ((((m0 j * ξ)⁻¹).locK P.1 y : ℂˣ) : ℂ) =
      (((m0 j).locK P.1 y : ℂˣ) : ℂ)⁻¹ * ((ξ.locK P.1 y : ℂˣ) : ℂ)⁻¹ := fun y => by
    rw [← mul_inv, ← Units.val_mul, ← Units.val_inv_eq_inv_val]
    rfl
  have un : ∀ (x : X.Eˣ) (y : 𝓞 X.E) (c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ), (x : X.E) = (y : X.E) →
      (c : 𝓞 X.E ⧸ P.1.asIdeal) = Ideal.Quotient.mk P.1.asIdeal y → P.1.valuation X.E (x : X.E) = 1 := fun x y c h1 h2 => by
    rw [h1]
    exact GlobalTheory.NormOneUnit.val_eq_one fun hm => c.ne_zero (h2.trans (Ideal.Quotient.eq_zero_iff_mem.2 hm))
  refine GlobalTheory.T.localChar_eq_heckeChar_localComponent_of_values X.E X.K σ₀ P.1 (m0 j * ξ)⁻¹ _ _ bad.2.2.1 (fun q hq => ?_) (fun x y c h1 h2 => ?_) a
  · rw [lk]
    by_cases hP : P.1 ∈ Pr.vGs
    · rw [if_pos hP, hc j.1 j.2 P hP q hq, Units.val_inv_eq_inv_val, map_inv₀, tw q hq]
    · have hg' := GlobalTheory.MuConj.g_notMem hPr P.1 hP fun h => bad.1 (Finset.mem_union_right _ (Finset.mem_union_left _ h))
      have hv : ordE P.1 (q : X.E) = 1 := by
        rw [hq, ordE, GlobalTheory.CharVal.val_natCast_of_notMem_sq (Ideal.absNorm_mem _) bad.2.2.1, WithZero.log_exp, neg_neg]
      rw [if_neg hP, muqT, dif_pos j.2, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀,
        map_inv₀, tw q hq, ht.muVal j P.1 hg', locK_eq_zpow ((ht.mu0 j).unr _ hg'), hv, zpow_one]
  · rw [lk]
    by_cases hP : P.1 ∈ Pr.vGs
    · have h3 : ξ.UnrAt P.1 := xi_unr (sel := sel) hξ fun h => by
        rcases (GlobalTheory.NormOneUnit.under_eq_iff hX.star_F hX.rankE (GlobalTheory.NormOneUnit.exists_star_ne hX) P.1 _).1
          (HeightOneSpectrum.ext (hsel (P.1.under (𝓞 X.F)))) with e | e
        · exact Finset.disjoint_left.1 (GlobalTheory.NormOneUnit.disjoint_vGs_QE mu hPr hsel hg) hP (e ▸ h)
        · exact bad.1 (Finset.mem_union_right _ (Finset.mem_union_right _ (e ▸ h)))
      rw [if_pos hP, GlobalTheory.NormOneUnit.locK_unr h3 (un x y c h1 h2), (ht.mu0 j).atg ⟨P.1, hP⟩ x y c h1 h2, chiP, dif_pos hP, chiAt,
        extChi, dif_pos j.2, Units.val_inv_eq_inv_val, map_inv₀, inv_inv, Units.val_one, inv_one, mul_one]
    · have hg' := GlobalTheory.MuConj.g_notMem hPr P.1 hP fun h => bad.1 (Finset.mem_union_right _ (Finset.mem_union_left _ h))
      rw [if_neg hP, GlobalTheory.NormOneUnit.locK_unr ((ht.mu0 j).unr _ hg') (un x y c h1 h2), MonoidHom.inv_apply,
        Units.val_inv_eq_inv_val, map_inv₀, GlobalTheory.NormOneUnit.resChar_eq hξ (xi_tame hξ) P.1 c y x h1 h2.symm, Units.val_one, inv_one,
        one_mul]

theorem unr_off (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hξ : GlobalTheory.Mem.Col2.Reads σ₀ (mu : Chr X.F X.E X.K) ξ)
    {P : HeightOneSpectrum (𝓞 X.E)} (h : ¬ ∃ Q ∈ rowSG Pr sel mu, Q.asIdeal.under (𝓞 X.F) = (P.under (𝓞 X.F)).asIdeal) :
    (∀ k, ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.asIdeal) ∧ ξ.UnrAt P := by
  classical
  refine ⟨GlobalTheory.MuConj.g_notMem hPr P (fun a => h ⟨P, Finset.mem_union_left _ a, rfl⟩)
    fun a => h ⟨_, Finset.mem_union_left _ a, congrArg HeightOneSpectrum.asIdeal
      ((GlobalTheory.NormOneUnit.under_eq_iff hX.star_F hX.rankE (GlobalTheory.NormOneUnit.exists_star_ne hX) P _).2 (Or.inr rfl))⟩,
    xi_unr (sel := sel) hξ fun a => h ⟨_, Finset.mem_union_right _ a, hsel _⟩⟩

theorem inf_eq (hX : X.Ok) {χ : HChar X.E} {ez : X.Tau → ℤ} (h : χ.HasInfQ (X.embC σ₀) fun τ => -(ez τ : ℚ)) {x : X.Eˣ} {z : X.E}
    (hx : (x : X.E) = z * star (x : X.E)) : ((χ.inf x : ℂˣ) : ℂ) = σ₀ (∏ τ, X.emb τ z ^ (-ez τ)) := by
  obtain ⟨n, hn, hinf⟩ := h
  rw [hinf x, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hn' : n τ = 2 * -(ez τ) := by
    have h2 : (n τ : ℚ) = 2 * -(ez τ : ℚ) := hn τ
    exact_mod_cast h2
  have h1 := congrArg (X.embC σ₀ τ) hx
  rw [map_mul, hX.conjE] at h1
  rw [hn', zpow_mul, map_zpow₀]
  congr 1
  rw [zpow_ofNat, div_pow, div_eq_iff (pow_ne_zero _ (by simp)), ← Complex.ofReal_pow,
    ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  change _ = X.embC σ₀ τ z * _
  linear_combination X.embC σ₀ τ (x : X.E) * h1

theorem muProdLaw (hD : X.AbelianUnramifiedExtensionConditions) (hPr : Pr.Ok) (hsel : IsSel X sel) (u : Pr.Word) (hT : Pr.T u ∈ S) (hg : ∀ k, Pr.g k ∈ S)
    (ht : Ch.Tied σ₀ e m0 eta) (hc : MuqTieG (Pr := Pr) (R := R) sel mu cst σ₀ m0) (j : Fin R.m) (ez : X.Tau → ℤ)
    (hez : ∀ τ, e j τ = ez τ) (n : ℕ) :
    MuProdLaw n sel (rowSG Pr sel mu) (mUof Ch mu j.1) (muAtT Ch sel mu cst j.1) ez := by
  classical
  intro γ N fr hN
  have hX := hD.ok
  have hs := GlobalTheory.NormOneUnit.exists_star_ne hX
  have hu := GlobalTheory.NormOneUnit.under_eq_iff hX.star_F hX.rankE hs
  have hμ := ht.mu0 j
  obtain ⟨ξ, hξ⟩ := GlobalTheory.Mem.ReadEx.exists_reads σ₀ (mu : Chr X.F X.E X.K) mu.2.1.1.1.1.1 mu.2.1.1.1.1.2
  set z : X.Eˣ := LinearEquiv.det γ.1 with hz
  obtain ⟨x, hx⟩ := GlobalTheory.NormOneUnit.exists_quot hs (z := (z : X.E))
    (by rw [mul_comm]; exact GlobalTheory.Mem.Col2.ChiFacLaw.star_det_mul γ)
  have nc : ∀ P ∈ rowSG Pr sel mu, conjPrime₂ P ∉ rowSG Pr sel mu := fun P hP h =>
    (GlobalTheory.ThetaMove.BadPrimes.bad_primes X Pr sel S mu u hX hPr hsel hT hg P (Finset.mem_union_right _ hP)).1
      (Finset.mem_union_right _ h)
  have hsel' : ∀ v, (sel v).under (𝓞 X.F) = v := fun v => HeightOneSpectrum.ext (hsel v)
  let B : HeightOneSpectrum (𝓞 X.F) → Prop := fun v => ∃ P ∈ rowSG Pr sel mu, P.asIdeal.under (𝓞 X.F) = v.asIdeal
  have unr : ∀ P : HeightOneSpectrum (𝓞 X.E), ¬ B (P.under (𝓞 X.F)) → (m0 j * ξ).UnrAt P := fun P h y hy => by
    rw [HChar.loc_mul, hμ.unr P (unr_off hX hPr hsel hξ h).1 y hy, (unr_off hX hPr hsel hξ h).2 y hy, one_mul]
  let rep : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E) := fun v => if h : B v then h.choose else sel v
  have rep_mem : ∀ P ∈ rowSG Pr sel mu, rep (P.under (𝓞 X.F)) = P := fun P hP => by
    have h : B (P.under (𝓞 X.F)) := ⟨P, hP, rfl⟩
    simp only [rep, dif_pos h]
    exact ((hu P _).1 (HeightOneSpectrum.ext h.choose_spec.2)).resolve_right fun e => nc P hP (e ▸ h.choose_spec.1)
  have hfin : {P : HeightOneSpectrum (𝓞 X.E) | P.valuation X.E (x : X.E) ≠ 1}.Finite := by
    refine ((HeightOneSpectrum.Support.finite (𝓞 X.E) (x : X.E)).union
      (HeightOneSpectrum.Support.finite (𝓞 X.E) (x : X.E)⁻¹)).subset fun P hP => ?_
    rcases lt_or_gt_of_ne hP with h | h
    · right
      change 1 < P.valuation X.E (x : X.E)⁻¹
      rw [map_inv₀]
      exact (one_lt_inv₀ (zero_lt_iff.2 (by simp))).2 h
    · exact Or.inl h
  set V : Finset (HeightOneSpectrum (𝓞 X.F)) := (rowSG Pr sel mu ∪ hfin.toFinset).image fun P => P.under (𝓞 X.F) with hV
  have vB : ∀ v, B v → v ∈ V := fun v ⟨P, hP, e⟩ =>
    Finset.mem_image.2 ⟨P, Finset.mem_union_left _ hP, HeightOneSpectrum.ext e⟩
  have vx : ∀ P : HeightOneSpectrum (𝓞 X.E), P.under (𝓞 X.F) ∉ V → P.valuation X.E (x : X.E) = 1 := fun P hP =>
    by_contra fun hn => hP (Finset.mem_image_of_mem _ (Finset.mem_union_right _ (hfin.mem_toFinset.2 hn)))
  have ξtriv := GlobalTheory.Mem.ReadTwist.trivOn hξ mu.2.1.1.2
  have key := GlobalTheory.T.heckeChar_productFormula_normOne X.F X.E (m0 j * ξ) rep V x z hX.star_F hX.rankE hs hD.unram
    ⟨fun v k => by rw [HChar.resFin_mul, hμ.triv.1, ξtriv.1, one_mul], fun v k => by
      rw [HChar.resInf_mul, hμ.triv.2, ξtriv.2, one_mul]⟩
    (fun P y h1 h2 => by rw [HChar.loc_mul, hμ.tame P y h1 h2, xi_tame hξ P y h1 h2, one_mul])
    (fun P hP => unr P fun ⟨Q, hQ, e⟩ => by
      have e' : Q = P := ((hu P Q).1 (HeightOneSpectrum.ext e)).elim id fun e => e.trans hP
      subst e'
      exact nc Q hQ (hP.symm ▸ hQ))
    (fun v => by
      by_cases h : B v
      · simp only [rep, dif_pos h]
        exact HeightOneSpectrum.ext h.choose_spec.2
      · simp only [rep, dif_neg h, hsel'])
    hx fun P hP => ⟨unr P fun h => hP (vB _ h), vx P hP⟩
  rw [HChar.inf_mul, GlobalTheory.NormOneUnit.inf_eq_one hξ, mul_one] at key
  have hinf := inf_eq hX (ez := ez) (by simpa only [hez] using hμ.inf) hx
  have off : muOff sel (rowSG Pr sel mu) (mUof Ch mu j.1) (gmap γ.1 N) =
      (∏ v ∈ V, if B v then 1 else ((mUof Ch mu j.1 (sel v) ^ ordE (sel v) (z : X.E) : X.Kˣ) : X.K)) *
        muOff sel (rowSG Pr sel mu) (mUof Ch mu j.1) N := by
    have s1 : (Function.mulSupport fun v =>
        if B v then 1 else ((mUof Ch mu j.1 (sel v) ^ ordE (sel v) (z : X.E) : X.Kˣ) : X.K)) ⊆ V := fun v hv => by
      by_contra hn
      apply hv
      have h1 := congrArg ((sel v).valuation X.E) hx
      rw [map_mul, ← valuation_conjP, vx _ (by rwa [hsel']), vx _ (by rwa [(hu _ _).2 (Or.inr rfl), hsel']), mul_one] at h1
      simp [ordE, ← h1]
    have s2 : (Function.mulSupport fun v =>
        if B v then 1 else ((mUof Ch mu j.1 (sel v) ^ ordDet (sel v) N : X.Kˣ) : X.K)).Finite := by
      refine ((GlobalTheory.OrdDetConj.ordDet_conj_finite X.E n N hN).2.image fun P => P.under (𝓞 X.F)).subset fun v hv => ?_
      refine ⟨sel v, fun h0 => hv ?_, hsel' v⟩
      simp [h0]
    rw [← finprod_eq_prod_of_mulSupport_subset _ s1, muOff, muOff, ← finprod_mul_distrib (V.finite_toSet.subset s1) s2]
    refine finprod_congr fun v => ?_
    by_cases h : B v
    · rw [if_pos h, if_pos h, if_pos h, one_mul]
    · rw [if_neg h, if_neg h, if_neg h, ordDet_gmap _ _ hN, zpow_add, Units.val_mul]
  have at1 : ∀ P : rowSG Pr sel mu, muAtT Ch sel mu cst j.1 P ((LinearEquiv.det (γ.1 * fr P) : X.Eˣ) : X.E) =
      muAtT Ch sel mu cst j.1 P (z : X.E) * muAtT Ch sel mu cst j.1 P ((LinearEquiv.det (fr P) : X.Eˣ) : X.E) := fun P => by
    apply σ₀.injective
    rw [map_mul σ₀, muAtT_eq hX hPr hsel u hT hg ht hc hξ, muAtT_eq hX hPr hsel u hT hg ht hc hξ,
      muAtT_eq hX hPr hsel u hT hg ht hc hξ, map_mul, map_mul, mul_inv, Units.val_mul]
  have fin : (∏ v ∈ V, if B v then 1 else ((mUof Ch mu j.1 (sel v) ^ ordE (sel v) (z : X.E) : X.Kˣ) : X.K)) *
      ∏ P : rowSG Pr sel mu, muAtT Ch sel mu cst j.1 P (z : X.E) = ∏ τ, X.emb τ (z : X.E) ^ (-ez τ) := by
    apply σ₀.injective
    have a1 : σ₀ (∏ P : rowSG Pr sel mu, muAtT Ch sel mu cst j.1 P (z : X.E)) =
        ∏ v ∈ V, if B v then ((((m0 j * ξ).locK (rep v) z)⁻¹ : ℂˣ) : ℂ) else 1 := by
      rw [map_prod, Finset.prod_congr rfl fun P _ => muAtT_eq hX hPr hsel u hT hg ht hc hξ j P z,
        Finset.prod_coe_sort (rowSG Pr sel mu) fun P => ((((m0 j * ξ).locK P z)⁻¹ : ℂˣ) : ℂ), ← Finset.prod_filter]
      refine Finset.prod_nbij' (fun P => P.under (𝓞 X.F)) rep (fun P hP => ?_) (fun v hv => ?_) rep_mem (fun v hv => ?_)
        fun P hP => by rw [rep_mem P hP]
      · exact Finset.mem_filter.2 ⟨vB _ ⟨P, hP, rfl⟩, P, hP, rfl⟩
      · have h := (Finset.mem_filter.1 hv).2
        simp only [rep, dif_pos h]
        exact h.choose_spec.1
      · have h := (Finset.mem_filter.1 hv).2
        simp only [rep, dif_pos h]
        exact HeightOneSpectrum.ext h.choose_spec.2
    rw [map_mul, a1, map_prod, ← Finset.prod_mul_distrib, ← hinf, eq_inv_of_mul_eq_one_left key, ← Finset.prod_inv_distrib,
      Units.coe_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    by_cases h : B v
    · rw [if_pos h, if_pos h, map_one, one_mul]
    · have h' : ¬ B ((sel v).under (𝓞 X.F)) := by rwa [hsel']
      have o := unr_off hX hPr hsel hξ h'
      simp only [rep, dif_neg h, if_neg h]
      rw [mul_one, locK_eq_zpow (unr _ h'), Units.val_zpow_eq_zpow_val, map_zpow₀, mUof, dif_pos j.2, Units.val_mul, map_mul,
        Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, map_inv₀, map_inv₀, ht.muVal j _ o.1,
        (GlobalTheory.T.tame_character_values_eq_heckeChar_local_values X.F X.E X.K σ₀ _ ξ hξ (xi_tame hξ) _).1 o.2, HChar.val_mul, Units.val_inv_eq_inv_val,
        Units.val_zpow_eq_zpow_val, Units.val_mul, ← mul_inv, inv_zpow]
  rw [muInvDet, muInvDet, off, Finset.prod_congr rfl fun P _ => at1 P, Finset.prod_mul_distrib, ← fin]
  ring

end Mu

theorem even_rank (R : Ranks) (j : ℕ) : Even (R.N j) := R.k_even.add ((R.t_odd.add_one).mul_left j)

theorem weights {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (u : Pr.Word) {i : ℕ} (hi : i < R.m) (τ : X.Tau)
    {z : ℤ} (hz : (W.hc u τ).e ⟨i, hi⟩ = z) :
    (nuLast W u i τ : ℤ) - (W.lamTrue u i τ).detShift = z - ((R.N (i + 1) / 2 : ℕ) : ℤ) ∧
      (W.lamTrue u (i + 1) τ).detShift = ((R.N i / 2 : ℕ) : ℤ) - z := by
  have half : ∀ k, (((R.N k / 2 : ℕ) : ℤ) : ℚ) = (R.N k : ℚ) / 2 := fun k => by
    obtain ⟨c, hc⟩ := even_rank R k
    have : R.N k / 2 = c := by omega
    rw [this, hc]
    push_cast
    ring
  constructor
  · have h1 := GlobalTheory.GO.ChSrc.nuEnd_cast (W.hc u) hi τ
    rw [GlobalTheory.GO.ChSrc.nuEnd_eq W u hi, GlobalTheory.GO.ChSrc.trueWt_eq, GlobalTheory.GO.ChSrc.sS, dif_pos hi] at h1
    have h2 := GlobalTheory.GO.ChSrc.zOf_spec R _ ((W.hc u τ).e_int ⟨i, hi⟩) (i + 1)
    rw [h1, add_sub_cancel_left]
    apply Int.cast_injective (α := ℚ)
    rw [Int.cast_sub, half, ← hz]
    exact h2
  · have hN : R.N i < R.N (i + 1) := by unfold Ranks.N; rw [add_mul]; omega
    have h1 := W.lamTrue_new u hi τ ⟨R.N (i + 1) - 1, by omega⟩ (by show ¬ R.N (i + 1) - 1 < R.N i; omega)
    apply Int.cast_injective (α := ℚ)
    rw [DomWeight.detShift, dif_pos (R.N_pos _), h1, Int.cast_sub, half, ← hz, sExp, Nat.add_sub_cancel, neg_sub]

theorem ratStep : ∀ (Z : Dat) (H : D7) (s : Seam H Z.X) (cc : Ideal (𝓞 H.host.K)) (δ : ℂ) (B : Base H cc δ) (χ : TaylorLogMetric.IdE H → ℂ) (cD : H.what₂.Tau → ℂ) (sel : HeightOneSpectrum (𝓞 Z.X.F) → HeightOneSpectrum (𝓞 Z.X.E)) (S : Set ℕ) (mu : Tup Z.X.F Z.X.E Z.X.K S) (cst : LocCst Z.X (rowSG Z.Pr sel mu)) (u : Z.Pr.Word) (i : ℕ), i < Z.R.m → Hyp Z s cc δ χ cD sel S mu cst u → B.EqP χ → B.VecP χ → MuqTie Z.Ch sel mu cst → (∀ N N' c x, InRange (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) c N N' x → ∀ m : DVar Z.X.Tau (Z.R.N i) (Z.R.N (i + 1)) →₀ ℕ, (∀ τ, (GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.degAt m τ : ℤ) = GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.degNu (Z.W.lamTrue u i) (nuLast Z.W u i) τ) → ∃ k : Z.X.K, (ambOf s B χ cD).σ₀ k = ((ambOf s B χ cD).chiF _ _ N N')⁻¹ * jetC (ambOf s B χ cD).cD ((ambOf s B χ cD).thInd (Sall sel mu u) N N' c x) m) → RatStep Z.W Z.Ch sel mu cst (ambOf s B χ cD) u i (i + 1) := by
  intro Z H s cc δ B χ cD sel S mu cst u i hi h hE hv _ hJ γ γ' N fr N' fr' c x hR
  obtain ⟨hs, hσ, hcc, hδ, hχ, -⟩ := h.ana
  obtain ⟨m0, eta, ht, hc⟩ := h.tied
  have hX := h.ok.fields
  have hPr := h.ok.primes
  have ea := even_rank Z.R i
  have eb := even_rank Z.R (i + 1)
  obtain ⟨hL, hsm⟩ := GlobalTheory.T.normalisedFamily_latticeHyp_and_smooth H Z.X s cc δ B χ cD _ _ hX hs hcc hδ hv ea eb
  have bad := GlobalTheory.ThetaMove.BadPrimes.bad_primes Z.X Z.Pr sel S mu u hX hPr h.isSel h.T_mem h.g_mem
  have hL' : (ambOf s B χ cD).LaHyp (Z.R.N i) (Z.R.N (i + 1)) (Sall sel mu u) :=
    ⟨hL.1, hL.2.1, fun P hP => (bad P hP).1, fun P hP =>
      GlobalTheory.PeriodIdealUnit.locP_AA_eq_one Z.X H s cc δ B χ cD P (bad P hP).2.1 (bad P hP).2.2.1 (h.cop P hP), hL.2.2.2.2⟩
  have hth := GlobalTheory.Mem.Col2.IndEq.thIndEq_of_vacEq Z.X _ _ _ _ _ hX hL' (GlobalTheory.ThetaMove.SeamMoves.aa_ne_bot s B χ cD hcc.1)
    (modulus_pos sel mu cst u (hPr.T_prime u).pos)
    (GlobalTheory.Mem.Col2.JetEx.VacEqPf.vacEq_ambOf H Z.X s cc δ B χ cD _ _ hs hE ea eb) γ γ' N N' c x hR
  have hchi := GlobalTheory.Mem.Col2.ChiFacLaw.chiLaw_ambOf H Z.X s cc δ B χ cD (Z.R.N i) (Z.R.N (i + 1)) hs hχ γ γ' N N' hR.1 hR.2.1
  have hG := indSmooth_of _ _ _ _ _ hsm N N' c x hR
  set A := ambOf s B χ cD with hA
  have hgN : IsSdLat (gmap γ.1 N) := ⟨gmap_lattice _ _ hR.1.1, by rw [IsUnimodular, dual_gmap _ γ.2, hR.1.2]⟩
  have hgN' : IsSdLat (gmap γ'.1 N') := ⟨gmap_lattice _ _ hR.2.1.1, by rw [IsUnimodular, dual_gmap _ γ'.2, hR.2.1.2]⟩
  have hR' : InRange (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) c (gmap γ.1 N) (gmap γ'.1 N')
      (γ'.1.toLinearMap ∘ₗ x ∘ₗ γ.1.symm.toLinearMap) :=
    ⟨hgN, hgN', hR.2.2.1, hR.2.2.2.1, (divLat_gmap_iff _ _ _ _ _ _ _).2 hR.2.2.2.2⟩
  choose ez hez using fun τ => (Z.W.hc u τ).e_int ⟨i, hi⟩
  have hez' : ∀ τ, (Z.W.row τ).e ⟨i, hi⟩ = ez τ := fun τ => by rw [← h.ok.wts.hc_row u τ]; exact hez τ
  have hmu := fun n => muProdLaw h.ok.fieldsConditions hPr h.isSel u h.T_mem h.g_mem ht hc ⟨i, hi⟩ ez hez' n
  have hV : JetInVV Z.X.K (Z.W.lamTrue u i) (Z.W.lamTrue u (i + 1)) (nuLast Z.W u i) := by
    have := GlobalTheory.GO.ChSrc.jetInVV_trueWt (Z.W.hc u) hi
    rwa [GlobalTheory.GO.ChSrc.nuEnd_eq Z.W u hi, GlobalTheory.GO.ChSrc.trueWt_eq, GlobalTheory.GO.ChSrc.trueWt_eq] at this
  have h₁ := hJ _ _ _ _ hR'
  rw [funext hth] at h₁
  set d : Z.X.Tau → Z.X.K := fun τ => Z.X.emb τ ((LinearEquiv.det γ.1 : Z.X.Eˣ) : Z.X.E) with hd
  set d' : Z.X.Tau → Z.X.K := fun τ => Z.X.emb τ ((LinearEquiv.det γ'.1 : Z.X.Eˣ) : Z.X.E) with hd'
  have d0 : ∀ τ, d τ ≠ 0 := fun τ => (map_ne_zero _).2 (Units.ne_zero _)
  have d0' : ∀ τ, d' τ ≠ 0 := fun τ => (map_ne_zero _).2 (Units.ne_zero _)
  have key := jetOp_pull A _ _ _ hV γ γ' _ hG _ (A.chiF _ _ N N')⁻¹
    ((∏ τ, d τ ^ ((Z.R.N (i + 1) / 2 : ℕ) : ℤ)) * ∏ τ, d' τ ^ (-((Z.R.N i / 2 : ℕ) : ℤ))) (by
      rw [hchi, mul_inv, mul_inv, ← zpow_neg, ← zpow_neg, neg_neg, Finset.prod_zpow, Finset.prod_zpow, map_mul, map_zpow₀,
        map_zpow₀, map_prod, map_prod]
      rfl) h₁ (hJ _ _ _ _ hR)
  unfold stepT thDistC Amb.jetK
  rw [if_pos hR'.2.2.2, if_pos hR.2.2.2, funext hth, key, hmu _ γ N fr hR.1, hmu _ γ' N' fr' hR.2.1, smul_smul,
    LinearMap.smul_comp, LinearMap.comp_smul]
  congr 1
  have e1 : (∏ τ, d τ ^ (-ez τ)) * (∏ τ, d τ ^ ((Z.R.N (i + 1) / 2 : ℕ) : ℤ)) *
      ∏ τ, d τ ^ ((nuLast Z.W u i τ : ℤ) - (Z.W.lamTrue u i τ).detShift) = 1 := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [(weights Z.W u hi τ (hez τ)).1, ← zpow_add₀ (d0 τ), ← zpow_add₀ (d0 τ)]
    ring_nf
    exact zpow_zero _
  have e2 : (∏ τ, d' τ ^ (-ez τ))⁻¹ * (∏ τ, d' τ ^ (-((Z.R.N i / 2 : ℕ) : ℤ))) *
      ∏ τ, d' τ ^ (Z.W.lamTrue u (i + 1) τ).detShift = 1 := by
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [(weights Z.W u hi τ (hez τ)).2, ← zpow_neg, ← zpow_add₀ (d0' τ), ← zpow_add₀ (d0' τ)]
    ring_nf
    exact zpow_zero _
  rw [mul_inv]
  generalize muInvDet sel _ _ _ N fr = p
  generalize (muInvDet sel _ _ _ N' fr')⁻¹ = p'
  calc _ = ((∏ τ, d τ ^ (-ez τ)) * (∏ τ, d τ ^ ((Z.R.N (i + 1) / 2 : ℕ) : ℤ)) *
      ∏ τ, d τ ^ ((nuLast Z.W u i τ : ℤ) - (Z.W.lamTrue u i τ).detShift)) * ((∏ τ, d' τ ^ (-ez τ))⁻¹ *
        (∏ τ, d' τ ^ (-((Z.R.N i / 2 : ℕ) : ℤ))) * ∏ τ, d' τ ^ (Z.W.lamTrue u (i + 1) τ).detShift) * (p * p') := by ring
    _ = _ := by rw [e1, e2, one_mul, one_mul]

end GlobalTheory.KerT.RatLaw
