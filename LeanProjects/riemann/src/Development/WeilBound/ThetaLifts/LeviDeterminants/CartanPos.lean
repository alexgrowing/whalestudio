import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.AdaptC
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.MMPreservesHM
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.EqZeroOfPiInf
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.ExistsAdelePiInf
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DisjointSpanPerpLat
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.TrSumOf

noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace PositivityTheory.ThKF0

open PositivityTheory.Mix.Adapt GlobalTheory.CompanionTheory.Ar.RT.Lie

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem tr_evI (h : IsTotallyReal F) (a : AF F) : Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F a) =
    ∑ w : InfinitePlace F, (InfinitePlace.Completion.extensionEmbedding w (a.1 w)).re := by
  classical
  haveI : IsEmpty {w : InfinitePlace F // w.IsComplex} :=
    ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.2 w.2 (h.isReal w.1)⟩
  rw [evI, Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi, PI.ProdFormulaE.Tr.trace_pi,
    InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  refine (congrArg₂ HAdd.hAdd ?_ (Finset.sum_of_isEmpty _)).trans (add_zero _)
  refine Fintype.sum_equiv (Equiv.subtypeUnivEquiv h.isReal) _ _ fun w => ?_
  rw [Equiv.subtypeUnivEquiv_apply, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply w.2, Complex.ofReal_re]
  simp

theorem tr_tr (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (z : AE F E) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (Algebra.trace (AF F) (AE F E) z)) =
      ∑ w, 2 * (piInf (τ w) z).re := by
  rw [tr_evI h.1]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h1 : algebraMap (AF F) (AE F E) (Algebra.trace (AF F) (AE F E) z) = z + cA σ z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]; ring
    | tmul a e =>
      rw [← GlobalTheory.VacIndic.smul_inclR_eq, map_smul (Algebra.trace _ _), map_smul (cA σ), GlobalTheory.VacIndic.trace_inclR, GlobalTheory.VacIndic.cA_inclR, ← smul_add,
        ← map_add, ← GlobalTheory.SelfDualLatticeCompare.trace_field h, smul_eq_mul, map_mul, Algebra.smul_def]
      congr 1
      generalize Algebra.trace F E e = t
      show algebraMap F (AF F) t ⊗ₜ[F] (1 : E) = (1 : AF F) ⊗ₜ[F] algebraMap F E t
      rw [Algebra.algebraMap_eq_smul_one (A := AF F), Algebra.algebraMap_eq_smul_one (A := E), TensorProduct.smul_tmul]
  have h2 := congrArg (piInf (τ w)) h1
  rw [map_add, piInf_cA h, Complex.add_conj] at h2
  have h3 : piInf (τ w) (algebraMap (AF F) (AE F E) (Algebra.trace (AF F) (AE F E) z)) =
      InfinitePlace.Completion.extensionEmbedding w ((Algebra.trace (AF F) (AE F E) z).1 w) * (τ w).1 1 := rfl
  rw [h3, map_one, mul_one] at h2
  rw [h2, Complex.ofReal_re]

abbrev cj : ℂ →ₐ[ℝ] ℂ := Complex.conjAe

variable {n d : ℕ}

def omega (σ : E →ₐ[F] E) (X : Spc F E n) (W : Spc F E d) (u u' : Matrix (Fin n) (Fin d) (AE F E)) : ℝ :=
  Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J) u u'))

variable {X : Spc F E n} {W : Spc F E d} {B : Base F E} {r s r' s' : ℕ}

theorem omega_eq (hB : B.IsGood σ) (u u' : Matrix (Fin n) (Fin d) (AE F E)) : omega σ X W u u' =
    ∑ w, 2 * (-hTens cj (X.J.map (B.emb w).1) (W.J.map (B.emb w).1) (u.map (piInf (B.emb w))) (u'.map (piInf (B.emb w)))).re := by
  rw [omega, symp, tr_tr hB.cm B.emb]
  refine Finset.sum_congr rfl fun w _ => ?_
  congr 2
  simp only [hTens, neg_one_mul, map_neg, map_sum, map_mul, piInf_cA hB.cm, incM, Matrix.map_apply, piInf_inclR]
  rfl

def Rel (B : Base F E) (X : Spc F E n) (W : Spc F E d) (e : InfinitePlace F → ℤˣ) (u u' : Matrix (Fin n) (Fin d) (AE F E)) : Prop :=
  ∀ w, u'.map (piInf (B.emb w)) = (((e w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ)

variable {e : InfinitePlace F → ℤˣ} {u u' u₁ u₁' : Matrix (Fin n) (Fin d) (AE F E)}

theorem sq_sign (x : ℤˣ) : ((x : ℤ) : ℂ) * ((x : ℤ) : ℂ) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp

theorem Rel.add (h : Rel B X W e u u') (h₁ : Rel B X W e u₁ u₁') : Rel B X W e (u + u₁) (u' + u₁') := fun w => by
  rw [Matrix.map_add _ (map_add _), Matrix.map_add _ (map_add _), h w, h₁ w, Matrix.mul_add, Matrix.add_mul, smul_add]

theorem Rel.symm (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (h : Rel B X W e u u') : Rel B X W e u' (-u) := fun w => by
  have h2 : (W.θ w)ᵀ * (W.θ w)ᵀ = 1 := by rw [← Matrix.transpose_mul, (hW.cartan w).1, Matrix.transpose_one]
  rw [h w, Matrix.map_neg _ (map_neg _), Matrix.mul_smul, Matrix.smul_mul, smul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    (hX.cartan w).1, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one,
    show ((e w : ℤ) : ℂ) * Complex.I * (((e w : ℤ) : ℂ) * Complex.I) = -1 by
      linear_combination (Complex.I * Complex.I) * sq_sign (e w) + Complex.I_mul_I, neg_one_smul]

theorem at_ext {α β : Type} (hB : B.IsGood σ) {u u' : Matrix α β (AE F E)} (hu : At (evI F) u) (hu' : At (evI F) u')
    (h : ∀ w, u.map (piInf (B.emb w)) = u'.map (piInf (B.emb w))) : u = u' := by
  ext i j
  refine sub_eq_zero.1 (GlobalTheory.CompanionTheory.CMAdele.eq_zero_of_piInf σ hB.cm B.emb _ (fun t ht => ?_) fun w => ?_)
  · rw [smul_sub, show t • u i j = 0 from congrFun (congrFun (hu t ht) i) j,
      show t • u' i j = 0 from congrFun (congrFun (hu' t ht) i) j, sub_zero]
  · rw [map_sub, sub_eq_zero]
    exact congrFun (congrFun (h w) i) j

theorem Rel.unique (hB : B.IsGood σ) (h : Rel B X W e u u') (h₁ : Rel B X W e u u₁') (hu : At (evI F) u') (hu' : At (evI F) u₁') :
    u' = u₁' := at_ext hB hu hu' fun w => (h w).trans (h₁ w).symm

theorem exists_vec {α : Type} (hB : B.IsGood σ) (z : InfinitePlace F → α → ℂ) :
    ∃ a : α → AE F E, At (evI F) a ∧ ∀ w i, piInf (B.emb w) (a i) = z w i := by
  choose a ha using fun i => GlobalTheory.CompanionTheory.RealPlaceAdele.exists_adele_piInf σ hB.cm B.emb fun w => z w i
  exact ⟨a, fun t ht => funext fun i => (ha i).1 t ht, fun w i => (ha i).2 w⟩

theorem exists_rel (hB : B.IsGood σ) (X : Spc F E n) (W : Spc F E d) (e) (u : Matrix (Fin n) (Fin d) (AE F E)) :
    ∃ u', At (evI F) u' ∧ Rel B X W e u u' := by
  obtain ⟨a, h1, h2⟩ := exists_vec hB fun w (k : Fin n × Fin d) =>
    ((((e w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ)) k.1 k.2
  exact ⟨Matrix.of fun i j => a (i, j), fun t ht => Matrix.ext fun i j => congrFun (h1 t ht) (i, j),
    fun w => Matrix.ext fun i j => h2 w (i, j)⟩

theorem hTens_smul {α β : Type} [Fintype α] [Fintype β] (J : Matrix α α ℂ) (J' : Matrix β β ℂ) (a b : ℂ) (x y : Matrix α β ℂ) :
    hTens cj J J' (a • x) (b • y) = a * star b * hTens cj J J' x y := by
  simp only [hTens, Finset.mul_sum, Matrix.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => ?_
  change _ * (star b * _) = _
  ring

theorem omega_rel (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (h : Rel B X W e u u')
    (h₁ : Rel B X W e u₁ u₁') : omega σ X W u' u₁' = omega σ X W u u₁ := by
  rw [omega_eq hB, omega_eq hB]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h2 : (W.θ w)ᵀ * W.J.map (B.emb w).1 * (W.θ w).map cj = W.J.map (B.emb w).1 := by
    have := (hW.cartan w).2.1
    rw [Matrix.mul_smul, Matrix.smul_mul] at this
    exact smul_right_injective _ Complex.I_ne_zero this
  have h3 : (X.θ w)ᵀ * X.J.map (B.emb w).1 * (X.θ w).map cj = X.J.map (B.emb w).1 := (hX.cartan w).2.1
  rw [h w, h₁ w, hTens_smul, hTens_mul, h2, h3,
    show ((e w : ℤ) : ℂ) * Complex.I * star (((e w : ℤ) : ℂ) * Complex.I) = 1 by
      simp only [star_mul, Complex.star_def, Complex.conj_I, map_intCast]
      linear_combination (-Complex.I * Complex.I) * sq_sign (e w) - Complex.I_mul_I, one_mul]

theorem cartan_pos {M θ : Matrix (Fin n) (Fin n) ℂ} (h : IsCartan M θ) (hM : ∀ i j, star (M j i) = M i j) (a : Fin n → ℂ) :
    ∃ p : ℝ, a ⬝ᵥ M *ᵥ star (θ *ᵥ a) = p ∧ (a = 0 → p = 0) ∧ (a ≠ 0 → 0 < p) := by
  have hs : ∀ x, star (θ *ᵥ x) = θ.map star *ᵥ star x := fun x => funext fun i => by
    simp [Matrix.mulVec, dotProduct, mul_comm]
  have h1 : a ⬝ᵥ M *ᵥ star (θ *ᵥ a) = (θ *ᵥ a) ⬝ᵥ M *ᵥ star a := by
    conv_lhs => rw [← h.2.1, ← Matrix.mulVec_mulVec, ← hs, Matrix.mulVec_mulVec a, h.1, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have h2 : star (a ⬝ᵥ M *ᵥ star (θ *ᵥ a)) = (θ *ᵥ a) ⬝ᵥ M *ᵥ star a := by
    generalize θ *ᵥ a = b
    simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', Pi.star_apply, star_star, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hM]; ring
  refine ⟨(a ⬝ᵥ M *ᵥ star (θ *ᵥ a)).re, (Complex.conj_eq_iff_re.1 (h2.trans h1.symm)).symm, fun h0 => by simp [h0], fun h0 => ?_⟩
  rw [h1]
  exact h.2.2 a h0

theorem omega_pure (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (a : Fin n → AE F E) {b : Fin d → E}
    (hb : b ≠ 0) (h : Rel B X W e (Matrix.vecMulVec a (incV F b)) u') :
    ∃ p : InfinitePlace F → ℝ, omega σ X W (Matrix.vecMulVec a (incV F b)) u' = ∑ w, ((e w : ℤ) : ℝ) * p w ∧
      ∀ w, ((fun i => piInf (B.emb w) (a i)) = 0 → p w = 0) ∧ ((fun i => piInf (B.emb w) (a i)) ≠ 0 → 0 < p w) := by
  choose p hp using fun w => cartan_pos (hX.cartan w) (fun i j => by
    rw [Matrix.map_apply, Matrix.map_apply, ← hB.cm.2.2.2, hX.herm]) fun i => piInf (B.emb w) (a i)
  choose q hq using fun w => cartan_pos (hW.cartan w) (fun i j => by
    rw [Matrix.smul_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.map_apply, smul_eq_mul, star_mul', ← hB.cm.2.2.2, hW.skew]
    simp) fun i => (B.emb w).1 (b i)
  have hq' : ∀ w, 0 < q w := fun w => (hq w).2.2 fun h0 => hb (funext fun i => (B.emb w).1.injective
    ((congrFun h0 i).trans (map_zero _).symm))
  refine ⟨fun w => 2 * p w * q w, ?_, fun w => ⟨fun h0 => by simp [(hp w).2.1 h0],
    fun h0 => mul_pos (mul_pos two_pos ((hp w).2.2 h0)) (hq' w)⟩⟩
  rw [omega_eq hB]
  refine Finset.sum_congr rfl fun w _ => ?_
  have e1 : (Matrix.vecMulVec a (incV F b)).map (piInf (B.emb w)) =
      Matrix.vecMulVec (fun i => piInf (B.emb w) (a i)) fun i => (B.emb w).1 (b i) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.vecMulVec_apply, map_mul, incV, piInf_inclR]
  have e2 : ∀ (J : Matrix (Fin n) (Fin n) ℂ) (J' : Matrix (Fin d) (Fin d) ℂ) x x' y y',
      hTens cj J J' (Matrix.vecMulVec x y) (Matrix.vecMulVec x' y') = (x ⬝ᵥ J *ᵥ star x') * (y ⬝ᵥ J' *ᵥ star y') := by
    intro J J' x x' y y'
    simp only [hTens, dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply, map_mul, Pi.star_apply]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    change _ * (star _ * star _) = _
    ring
  have h1 := (hq w).1
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at h1
  rw [h w, e1, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_transpose, ← one_smul ℂ (Matrix.vecMulVec _ _),
    hTens_smul, e2, (hp w).1]
  generalize (fun i => (B.emb w).1 (b i)) ⬝ᵥ _ = t at h1
  have h4 : -(1 * star (((e w : ℤ) : ℂ) * Complex.I) * (p w * t)) = ((((e w : ℤ) : ℝ) * (p w * q w) : ℝ) : ℂ) := by
    simp only [star_mul, Complex.star_def, Complex.conj_I, map_intCast]
    push_cast
    rw [← h1]
    ring
  rw [h4, Complex.ofReal_re]
  ring

end PositivityTheory.ThKF0
