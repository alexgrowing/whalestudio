import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParamSubgroupTransposeGramLieAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodSplitPlaceTranslationActsThroughWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasArchimedeanCharExponentsConjOfHasInfExp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.LineAtPlace

variable {D : D7}

theorem emb_eq_or_conj (e₁ e₂ : D.host.E →+* ℂ)
    (h : ∀ a : D.host.F, e₁ (algebraMap D.host.F D.host.E a) = e₂ (algebraMap D.host.F D.host.E a)) :
    (∀ x, e₂ x = e₁ x) ∨ ∀ x, e₂ x = starRingEnd ℂ (e₁ x) := by
  have hconj : ∀ a : D.host.E, e₁ (star a) = starRingEnd ℂ (e₁ a) := D.sp.cm.cmUnram.2.1 e₁
  have hb := Eqv.star_alphaE D
  have hdec : ∀ y : D.host.E, ∃ p q : D.host.F,
      y = algebraMap D.host.F D.host.E p + algebraMap D.host.F D.host.E q * Eqv.alphaE D := by
    intro y
    refine ⟨(Eqv.basE D).repr y 0, (Eqv.basE D).repr y 1, ?_⟩
    conv_lhs => rw [← (Eqv.basE D).sum_repr y]
    rw [Fin.sum_univ_two, Eqv.basE_zero, Eqv.basE_one, Algebra.smul_def, Algebra.smul_def, mul_one]
  have hb2 : e₂ (Eqv.alphaE D) ^ 2 = e₁ (Eqv.alphaE D) ^ 2 := by
    have h1 : star (Eqv.alphaE D ^ 2) = Eqv.alphaE D ^ 2 := by rw [star_pow, hb]; ring
    obtain ⟨t, ht⟩ := (D.sp.cm.fixed _).1 h1
    rw [← map_pow, ← map_pow, ← ht, h]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hb2 with hc | hc
  · left
    intro y
    obtain ⟨p, q, rfl⟩ := hdec y
    rw [map_add, map_add, map_mul, map_mul, hc, h, h]
  · right
    intro y
    obtain ⟨p, q, rfl⟩ := hdec y
    rw [← hconj, star_add, star_mul, Eqv.star_algebraMapF, Eqv.star_algebraMapF, hb, map_add, map_add, map_mul, map_mul,
      map_neg, hc, h, h]
    ring

theorem exists_piInf (τ : D.what₂.Tau) (p : GlobalTheory.AdelicU.EmbOver D.host.E (Eqv.plW D τ)) :
    ∃ c : ℂ →+* ℂ, Continuous c ∧ (∀ (t : ℝ) z, c (t • z) = t • c z) ∧
      ∀ y : AE D, Eqv.psiT D τ y = c (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf p y) := by
  have key : ∀ c : ℂ →+* ℂ, (∀ t : ℝ, c t = t) → (∀ x, tauE D τ x = c (p.1 x)) →
      ∀ y : AE D, Eqv.psiT D τ y = c (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf p y) := by
    intro c hc hx y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add a b ha hb => rw [RingHom.map_add, RingHom.map_add, RingHom.map_add, ha, hb]
    | tmul a x =>
      have l1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf p (a ⊗ₜ[D.host.F] x) = Eqv.gW D (Eqv.plW D τ) (fstA D.host.F a) * p.1 x :=
        GlobalTheory.AdelicU.infEmb_tmul p _ x
      have l2 : Eqv.psiT D τ (a ⊗ₜ[D.host.F] x) = Eqv.gW D (Eqv.plW D τ) (fstA D.host.F a) * tauE D τ x :=
        Eqv.thetaC_tmul D τ _ x
      rw [l1, l2, map_mul, hx, Eqv.gW_real, hc]
  rcases emb_eq_or_conj p.1 (tauE D τ) (fun a => RingHom.congr_fun (p.2.trans (Eqv.plW_embedding D τ)) a) with h | h
  · exact ⟨RingHom.id ℂ, continuous_id, fun _ _ => rfl, key _ (fun _ => rfl) h⟩
  · exact ⟨starRingEnd ℂ, Complex.continuous_conj, fun t z => by simp, key _ Complex.conj_ofReal h⟩

theorem kapX_surj (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = D.host.xi0 • reindex e e X.gramᵀ) (k : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) : ∃ h, kapX X e hJ h = k := by
  subst hJ
  have h1 : (k.1.1)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D.host.xi0 • reindex e e X.gramᵀ) * (k.1.1).map (cA D) =
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D.host.xi0 • reindex e e X.gramᵀ) := k.2
  rw [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul] at h1
  have hx : D.host.xi0 ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  have h2 := congrArg (fun Y => ((incA D D.host.xi0⁻¹ • Y)ᵀ).submatrix e e) h1
  simp only [smul_smul, ← map_mul, inv_mul_cancel₀ hx, map_one, one_smul, transpose_mul,
    transpose_transpose, ← Matrix.mul_assoc] at h2
  rw [← submatrix_mul_equiv _ _ _ e, ← submatrix_mul_equiv _ _ _ e] at h2
  have e1 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (reindex e e X.gramᵀ))ᵀ.submatrix e e = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram := by
    ext i j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM]
  rw [e1] at h2
  refine ⟨⟨Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom k.1, h2⟩, Subtype.ext (Units.ext ?_)⟩
  show reindex e e (reindex e.symm e.symm k.1.1) = k.1.1
  simp

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

theorem lie_of_exp {n : ℕ} (Y H : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ t : ℝ, (NormedSpace.exp (t • Y))ᴴ * H * NormedSpace.exp (t • Y) = H) : Yᴴ * H + H * Y = 0 := by
  have h1 := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) Yᴴ (0 : ℝ)).mul_const H).fun_mul
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ))
  have h2 : (fun t : ℝ => NormedSpace.exp (t • Yᴴ) * H * NormedSpace.exp (t • Y)) = fun _ => H := by
    funext t
    have e : t • Yᴴ = (t • Y)ᴴ := by rw [Matrix.conjTranspose_smul, star_trivial]
    rw [e, Matrix.exp_conjTranspose]
    exact h t
  have h3 := (h1.congr_of_eventuallyEq (f₁ := fun _ => H)
    (Filter.Eventually.of_forall fun t => (congrFun h2 t).symm)).unique (hasDerivAt_const _ _)
  simpa using h3

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in

theorem exp_map {n d : ℕ} (e : Fin n ≃ Fin d) (c : ℂ →+* ℂ) (hc : Continuous c) (Z : Matrix (Fin d) (Fin d) ℂ) :
    ((NormedSpace.exp Z).map c).submatrix e e = NormedSpace.exp ((Z.map c).submatrix e e) :=
  NormedSpace.map_exp ((Matrix.reindexAlgEquiv ℂ ℂ e.symm).toRingHom.comp c.mapMatrix)
    ((continuous_id.matrix_map hc).matrix_submatrix e e) Z

end GlobalTheory.LineAtPlace

open GlobalTheory.LineAtPlace in
theorem GlobalTheory.LineAtPlace.exists_oneP : ∀ (D : D7) (θ : InfFam D) (X : HSp D), IsInfFam θ → ∀ {d : ℕ} (e : Fin X.rank ≃ Fin d)
    (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d) (hJ : Wd.J = D.host.xi0 • reindex e e X.gramᵀ)
    (emb : ∀ w : InfinitePlace D.host.F, GlobalTheory.AdelicU.EmbOver D.host.E w) (w : InfinitePlace D.host.F)
    (Z : Matrix (Fin d) (Fin d) ℂ) (γ : Multiplicative ℝ →* GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Wd.J),
    γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Wd →
    (∀ t : ℝ, (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t))).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (emb w)) =
      NormedSpace.exp (t • Z)) →
    (∀ (t : ℝ) (w' : InfinitePlace D.host.F), w' ≠ w →
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t))).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piInf (emb w')) = 1) →
    ∃ (τ : D.what₂.Tau) (Y : Matrix (Fin X.rank) (Fin X.rank) ℂ), Y ∈ lieAt X τ ∧
      ∀ t : ℝ, γ (Multiplicative.ofAdd t) = kapX X e hJ (oneP θ X τ Y t) := by
  intro D θ X hθ d e Wd hJ emb w Z γ hγ hw ho
  obtain rfl := Eqv.eq_thetaC D hθ
  obtain ⟨τ, rfl⟩ : ∃ τ, Eqv.plW D τ = w := ⟨_, Eqv.plW_symm D w⟩
  choose h hh using fun t : ℝ => kapX_surj X e hJ (γ (Multiplicative.ofAdd t))
  have hm : ∀ t, Eqv.matA D X (h t) = (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t))).submatrix e e := by
    intro t
    rw [← hh t]
    show _ = (reindex e e (Eqv.matA D X (h t))).submatrix e e
    simp
  obtain ⟨c, hc, hcs, hp⟩ := exists_piInf τ (emb _)
  have h1 : ∀ t : ℝ, infMat D.sp.cm.sig X.gram (Eqv.thetaC D τ) (h t) =
      NormedSpace.exp (t • (Z.map c).submatrix e e) := by
    intro t
    have e1 : t • (Z.map c).submatrix e e = ((t • Z).map c).submatrix e e := by
      ext i j
      exact (hcs t _).symm
    rw [Eqv.infMat_thetaC, hm, e1, ← exp_map e c hc, ← hw]
    ext i j
    exact hp _
  have hu : ∀ t : ℝ, (NormedSpace.exp (t • (Z.map c).submatrix e e))ᴴ * gramAt D X τ *
      NormedSpace.exp (t • (Z.map c).submatrix e e) = gramAt D X τ := by
    intro t
    rw [← h1]
    exact Eqv.infMat_unitary' D X (h t) τ
  refine ⟨τ, (Z.map c).submatrix e e, lie_of_exp _ _ hu, fun t => ?_⟩
  rw [← hh t, oneP, Eqv.atTau_eq D X τ _ (hu t)]
  congr 1
  apply Eqv.matA_inj D X
  rw [Eqv.matA_atH]
  refine Eqv.matA_of_isAtTau D X ⟨(Eqv.mem_GinfC D X _).2 ?_, h1 t, fun ρ hρ => ?_⟩
  · ext i j
    have k1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t)) (e i) (e j) - (1 : Matrix _ _ (AE D)) (e i) (e j)) :=
      fun u hu => congrFun (congrFun (hγ.2 _ u hu) (e i)) (e j)
    have k2 := GlobalTheory.ConjInfExp.finPart_eq_one
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat (γ (Multiplicative.ofAdd t)) (e i) (e j) - (1 : Matrix _ _ (AE D)) (e i) (e j) + 1)
      (by rwa [add_sub_cancel_right])
    rw [RingHom.map_add, RingHom.map_one, add_eq_right, RingHom.map_sub, sub_eq_zero] at k2
    rw [Matrix.map_apply, hm, submatrix_apply, k2]
    by_cases k : i = j
    · subst k; simp
    · simp [Matrix.one_apply_ne k, Matrix.one_apply_ne (e.injective.ne k)]
  · obtain ⟨c', -, -, hp'⟩ := exists_piInf ρ (emb _)
    have k1 : Eqv.plW D ρ ≠ Eqv.plW D τ := fun k => hρ (by rw [← Eqv.symm_plW D ρ, k, Eqv.symm_plW])
    rw [Eqv.infMat_thetaC, hm]
    ext i j
    have k2 := congrFun (congrFun (ho t _ k1) (e i)) (e j)
    rw [Matrix.map_apply] at k2
    rw [Matrix.map_apply, submatrix_apply, hp', k2]
    by_cases k : i = j
    · subst k; simp
    · simp [Matrix.one_apply_ne k, Matrix.one_apply_ne (e.injective.ne k)]

end
