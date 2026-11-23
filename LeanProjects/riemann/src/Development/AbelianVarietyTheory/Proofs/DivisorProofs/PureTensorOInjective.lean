import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRealPlaceSymplecticFormPositiveComplexStru
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsHeisenbergDerivativeLinearOperators
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HeisenbergDerivativeCommutatorRelation

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockVecInj

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis

theorem injective_of_pderiv {ι M : Type} [AddCommGroup M] [Module ℂ M] (E : MvPolynomial ι ℂ →ₗ[ℂ] M) (h1 : E 1 ≠ 0)
    (hd : ∀ i Q, E Q = 0 → E (MvPolynomial.pderiv i Q) = 0) : Function.Injective E := by
  have key : ∀ n : ℕ, ∀ Q, E Q = 0 → (∀ k : ι →₀ ℕ, n ≤ k.degree → Q.coeff k = 0) → Q = 0 := by
    intro n
    induction n with
    | zero => intro Q _ h; ext k; exact h k (Nat.zero_le _)
    | succ n ih =>
      intro Q hQ h
      have h2 : ∀ i, MvPolynomial.pderiv i Q = 0 := fun i => ih _ (hd i Q hQ) fun k hk => by
        rw [MvPolynomial.coeff_pderiv, h _ (by rw [map_add, Finsupp.degree_single]; omega), zero_mul]
      have h3 : Q = Q.coeff 0 • (1 : MvPolynomial ι ℂ) := by
        ext k
        rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_one]
        split_ifs with hk
        · rw [← hk, smul_eq_mul, mul_one]
        · obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
            by_contra hc
            exact hk (Finsupp.ext fun i => by simpa using (not_not.1 fun hi => hc ⟨i, hi⟩).symm)
          have e : k - Finsupp.single i 1 + Finsupp.single i 1 = k :=
            tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hi))
          have h4 := MvPolynomial.coeff_pderiv (i := i) Q (k - Finsupp.single i 1)
          rw [h2, e, MvPolynomial.coeff_zero] at h4
          rw [smul_zero]
          exact (mul_eq_zero.1 h4.symm).resolve_right (Nat.cast_add_one_ne_zero _)
      rw [h3, map_smul] at hQ
      rw [h3, (smul_eq_zero.1 hQ).resolve_right h1, zero_smul]
  refine (injective_iff_map_eq_zero E).2 fun Q hQ => key (Q.totalDegree + 1) Q hQ fun k hk => ?_
  exact MvPolynomial.coeff_eq_zero_of_totalDegree_lt hk

theorem injective_of_canonicalCommutation {ι X : Type} (M : Submodule ℂ (X → ℂ)) (A : ι → (X → ℂ) → (X → ℂ))
    (a b : ι → Module.End ℂ M) (c : ι → ℂ) (hA : ∀ i (g : M), A i g = a i g)
    (haa : ∀ i j g, a i (a j g) = a j (a i g))
    (hba : ∀ i j g, b i (a j g) = a j (b i g) + (if i = j then c i else 0) • g) (hc : ∀ i, c i ≠ 0)
    (f : M) (hf : ∀ i, b i f = 0) (h0 : f ≠ 0) : Function.Injective (pureTensorL A (f : X → ℂ)) := by
  let E : MvPolynomial ι ℂ →ₗ[ℂ] M := (MvPolynomial.basisMonomials ι ℂ).constr ℂ
    fun k : ι →₀ ℕ => (Multiset.toList (Finsupp.toMultiset k)).foldr (fun i g => a i g) f
  have hm : ∀ k r, E (MvPolynomial.monomial k r) =
      r • (Multiset.toList (Finsupp.toMultiset k)).foldr (fun i g => a i g) f := fun k r => by
    have e : MvPolynomial.monomial k r = r • MvPolynomial.basisMonomials ι ℂ k := by
      rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [e, map_smul, Module.Basis.constr_basis]
  have hE : pureTensorL A (f : X → ℂ) = M.subtype ∘ₗ E := by
    refine (MvPolynomial.basisMonomials ι ℂ).ext fun k => ?_
    rw [LinearMap.comp_apply, pureTensorL, Module.Basis.constr_basis, Module.Basis.constr_basis, opPow]
    induction (Finsupp.toMultiset k).toList with
    | nil => rfl
    | cons i l ih => rw [List.foldr_cons, List.foldr_cons, ih]; exact hA _ _
  have h1 : E 1 = f := by
    rw [MvPolynomial.one_def, hm, one_smul]
    simp
  haveI : LeftCommutative fun (i : ι) (g : M) => a i g := ⟨haa⟩
  have hX : ∀ Q v, E (Q * MvPolynomial.X v) = a v (E Q) := by
    intro Q v
    induction Q using MvPolynomial.induction_on' with
    | monomial k r =>
      rw [MvPolynomial.X, MvPolynomial.monomial_mul, mul_one, hm, hm, map_smul]
      congr 1
      refine List.Perm.foldr_eq (l₂ := v :: (Finsupp.toMultiset k).toList) ?_ f
      rw [← Multiset.coe_eq_coe, ← Multiset.cons_coe, Multiset.coe_toList, Multiset.coe_toList, map_add,
        Finsupp.toMultiset_single, one_smul, add_comm, Multiset.singleton_add]
    | add p q hp hq => rw [add_mul, map_add, map_add, hp, hq, map_add]
  have hb : ∀ i Q, b i (E Q) = c i • E (MvPolynomial.pderiv i Q) := by
    intro i Q
    induction Q using MvPolynomial.induction_on with
    | C r =>
      rw [MvPolynomial.pderiv_C, map_zero, smul_zero, MvPolynomial.C_eq_smul_one, map_smul, map_smul, h1, hf, smul_zero]
    | add p q hp hq => simp only [map_add, hp, hq, smul_add]
    | mul_X p j hp =>
      rw [hX, hba, hp, MvPolynomial.pderiv_mul, map_add, hX, map_smul, smul_add]
      congr 1
      split_ifs with h
      · rw [h, MvPolynomial.pderiv_X_self, mul_one]
      · rw [MvPolynomial.pderiv_X_of_ne (Ne.symm h), mul_zero, map_zero, smul_zero, zero_smul]
  rw [hE]
  refine M.injective_subtype.comp (injective_of_pderiv E (h1 ▸ h0) fun i Q hQ => ?_)
  have := hb i Q
  rw [hQ, map_zero] at this
  exact (smul_eq_zero.1 this.symm).resolve_left (hc i)

theorem cplxO_unitMap {m n : ℕ} {s B : Matrix (Fin n) (Fin n) ℂ} {s' B' : Matrix (Fin m) (Fin m) ℂ} {ε : Fin n → ℂ}
    {ε' : Fin m → ℂ} (hB : IsUnit B.det) (h : s * B = B * diagonal ε) (h' : s' * B' = B' * diagonal ε') (i j) :
    cplxO s s' (unitMap B B' i j) = (I * (ε' i * ε j)) • unitMap B B' i j := by
  have e : B⁻¹ * s = diagonal ε * B⁻¹ := by
    calc B⁻¹ * s = B⁻¹ * (s * B) * B⁻¹ := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB, Matrix.mul_one]
      _ = _ := by rw [h, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hB, Matrix.one_mul]
  have e2 : diagonal ε' * Matrix.single i j (1 : ℂ) * diagonal ε = (ε' i * ε j) • Matrix.single i j (1 : ℂ) := by
    ext a b
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply]
    split_ifs with hh
    · rw [hh.1, hh.2]; simp
    · simp
  unfold cplxO unitMap
  rw [mul_smul, ← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.mul_smul B' (ε' i * ε j), ← e2,
    Matrix.smul_mul, Matrix.smul_mul]
  congr 1
  calc s' * (B' * Matrix.single i j (1 : ℂ) * B⁻¹) * s = (s' * B') * Matrix.single i j (1 : ℂ) * (B⁻¹ * s) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h', e]; simp only [Matrix.mul_assoc]

theorem trace_unitMap {m n : ℕ} {G B : Matrix (Fin n) (Fin n) ℂ} {G' B' : Matrix (Fin m) (Fin m) ℂ} {ε : Fin n → ℂ}
    {ε' : Fin m → ℂ} (hε : ∀ a, ε a * ε a = 1) (h : Bᴴ * G * B = diagonal ε) (h' : B'ᴴ * G' * B' = diagonal ε')
    (i j k l) : (G⁻¹ * (unitMap B B' k l)ᴴ * G' * unitMap B B' i j).trace =
      if i = k ∧ j = l then ε' i * ε j else 0 := by
  have e : B⁻¹ * G⁻¹ * B⁻¹ᴴ = diagonal ε := by
    rw [Matrix.conjTranspose_nonsing_inv, ← Matrix.mul_inv_rev, ← Matrix.mul_inv_rev, ← Matrix.mul_assoc, h]
    apply Matrix.inv_eq_left_inv
    rw [Matrix.diagonal_mul_diagonal]
    simp only [hε, Matrix.diagonal_one]
  have e2 : G⁻¹ * (unitMap B B' k l)ᴴ * G' * unitMap B B' i j =
      (G⁻¹ * B⁻¹ᴴ * (Matrix.single k l (1 : ℂ))ᴴ * (B'ᴴ * G' * B') * Matrix.single i j (1 : ℂ)) * B⁻¹ := by
    simp only [unitMap, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e2, Matrix.trace_mul_comm, h', ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e,
    Matrix.trace_mul_single, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, Matrix.single_apply]
  split_ifs with h1 h2 h2
  · simp [mul_comm]
  · exact (h2 ⟨h1.1.symm, h1.2.symm⟩).elim
  · exact (h1 ⟨h2.1.symm, h2.2.symm⟩).elim
  · simp

theorem ccr_of_comm {M R : Type} [AddCommGroup M] [Module ℂ M] (Dop : R → Module.End ℂ M) (w : R → R → ℂ)
    (h : ∀ u v g, Dop u (Dop v g) = Dop v (Dop u g) + w u v • g) (u u' v v' : R) (r r' : ℂ) (g : M) :
    ((r • (Dop u - I • Dop u')) ((r' • (Dop v - I • Dop v')) g) =
      (r' • (Dop v - I • Dop v')) ((r • (Dop u - I • Dop u')) g) +
        (r * r' * (w u v - w u' v' - I * (w u v' + w u' v))) • g) ∧
    (Dop u + I • Dop u') ((r' • (Dop v - I • Dop v')) g) =
      (r' • (Dop v - I • Dop v')) ((Dop u + I • Dop u') g) +
        (r' * (w u v + w u' v' + I * (w u' v - w u v'))) • g := by
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.add_apply, map_smul, map_sub, map_add]
  rw [h u v, h u v', h u' v, h u' v']
  constructor <;> match_scalars <;> first | ring1 | (ring_nf; simp only [I_sq]; ring1)

variable {D : D7}

theorem omO_single (S T : HSp D) (τ τ' : D.what₂.Tau) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    omO S T (Pi.single τ x : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ)
        (Pi.single τ' y : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) =
      if τ = τ' then 2 * (tauE D τ D.host.xi0 * ((gramAt D S τ)⁻¹ * yᴴ * gramAt D T τ * x).trace).re else 0 := by
  show ∑ ρ, formAt S T ρ ((Pi.single τ x : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) ρ)
    ((Pi.single τ' y : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) ρ) = _
  simp only [GlobalTheory.OrientedRealForm.formAt_eq]
  rw [Finset.sum_eq_single τ (fun ρ _ hρ => by simp [Pi.single_eq_of_ne hρ]) (by simp), Pi.single_eq_same]
  split_ifs with h
  · rw [h, Pi.single_eq_same]
  · simp [Pi.single_eq_of_ne h]

theorem pi_lineAt {S T : HSp D} {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    piW θ T S (lineAt θ τ z 1) = (Pi.single τ z : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ) := by
  funext τ'
  refine ((isLineAt_lineAt hθ τ z).2.2 1 τ').trans ?_
  rw [Pi.single_apply, Complex.ofReal_one, one_smul]

theorem pureTensorO_injective : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (sV BV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (s BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (pV pW : D.what₂.Tau → ℕ), (∀ τ, IsCartanInv (gramAt D V τ) (sV τ)) → (∀ τ, IsCartanInv (gramAt D W τ) (s τ)) → (∀ τ, IsONBasis (gramAt D V τ) (sV τ) (BV τ) (pV τ)) → (∀ τ, IsONBasis (gramAt D W τ) (s τ) (BW τ) (pW τ)) → V.SigOK → W.SigOK → ∀ f, IsThetaFunO ψ V W f → (∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (sV τ) (s τ)) f) → f ≠ 0 → Function.Injective (pureTensorO ψ θ V W sV s BV BW f) := by
  intro D ψ θ V W hψ hθ sV BV s BW pV pW _ _ hBV hBW _ _ f hf hvac hf0
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  choose ε hε hG hs using hBV
  choose ε' hε' hG' hs' using hBW
  have sq : ∀ τ a, (ε τ a : ℂ) * ε τ a = 1 := fun τ a => by
    rcases hε τ a with h | h <;> simp [h.1]
  have sq' : ∀ τ a, (ε' τ a : ℂ) * ε' τ a = 1 := fun τ a => by
    rcases hε' τ a with h | h <;> simp [h.1]
  have hdet : ∀ τ, IsUnit (BV τ).det := fun τ => by
    have e : (diagonal (fun a => (ε τ a : ℂ)) * ((BV τ)ᴴ * gramAt D V τ)) * BV τ = 1 := by
      rw [Matrix.mul_assoc, hG, Matrix.diagonal_mul_diagonal]
      simp only [sq, Matrix.diagonal_one]
    exact Matrix.isUnit_det_of_left_inverse e
  have hE : ∀ τ z g, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z g = hD (iotaW σ W V) (piW θ W V) (omO V W)
      (Pi.single τ z : D.what₂.Tau → Matrix (Fin W.rank) (Fin V.rank) ℂ) g := fun τ z g => by
    rw [← pi_lineAt hθ]
    exact dLine_eq_hD h hψ (isRealDir_lineAt hθ τ z) g
  let M : Submodule ℂ (WO V W → ℂ) :=
    { carrier := {g | Sm (iotaW σ W V) g}
      add_mem' := fun ha hb w => (ha w).add (hb w)
      zero_mem' := fun w => contDiff_const
      smul_mem' := fun c g hg w => contDiff_const.mul (hg w) }
  have hform := fun g hg u w => hD_eq_fderiv (iotaW σ W V) (piW θ W V) (omO V W) g hg u w
  obtain ⟨Dop, hD1, -⟩ := exists_heisenberg_operators _ _ (iotaW σ W V) (piW θ W V) (omO V W) (h.pi_iota W V) hform M
    (fun _ hg => hg) fun u g hg => (hD_formula_smooth _ _ _ _ _ (h.pi_iota W V) g hg u).2
  have sk : ∀ u v, omO V W v u = -omO V W u v := fun u v => by
    have h1 := omO_self h (S := V) (T := W) (u + v)
    simp only [LinearMap.map_add, LinearMap.add_apply, omO_self h] at h1
    linarith
  have hcomm : ∀ u v g, Dop u (Dop v g) = Dop v (Dop u g) + (-(2 * Real.pi * I) * (omO V W u v : ℝ)) • g := fun u v g => by
    apply Subtype.ext
    rw [Submodule.coe_add, Submodule.coe_smul, hD1, hD1, hD1, hD1]
    exact eq_add_of_sub_eq' (heisenberg_derivative_commutator _ _ _ _ _ (h.pi_iota W V) hform sk g g.2 u v)
  let η : FVar D W.rank V.rank → ℝ := fun k => ε' k.1 k.2.1 * ε k.1 k.2.2
  have hη : ∀ k, η k = 1 ∨ η k = -1 := fun k => by
    rcases hε k.1 k.2.2 with h | h <;> rcases hε' k.1 k.2.1 with h' | h' <;> simp [η, h.1, h'.1]
  let u : ℂ → FVar D W.rank V.rank → RW W V := fun c k =>
    (Pi.single k.1 (c • unitMap (BV k.1) (BW k.1) k.2.1 k.2.2) : D.what₂.Tau → Matrix (Fin W.rank) (Fin V.rank) ℂ)
  have hom : ∀ c c' k l, omO V W (u c k) (u c' l) =
      if k = l then 2 * (tauE D k.1 D.host.xi0 * (c * conj c' * η k)).re else 0 := by
    rintro c c' ⟨τ, i, j⟩ ⟨τ', k, l⟩
    refine (omO_single V W τ τ' _ _).trans ?_
    by_cases hτ : τ = τ'
    · subst hτ
      rw [if_pos rfl, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul,
        Matrix.trace_smul, Matrix.trace_smul, trace_unitMap (sq τ) (hG τ) (hG' τ)]
      by_cases hk : i = k ∧ j = l
      · rw [if_pos hk, if_pos (by rw [hk.1, hk.2])]
        simp only [η, smul_eq_mul, Complex.ofReal_mul, mul_assoc]
        rfl
      · rw [if_neg hk, if_neg (by simpa using hk)]
        simp
    · rw [if_neg hτ, if_neg fun hh => hτ (congrArg Prod.fst hh)]
  have hJ : ∀ k : FVar D W.rank V.rank, cplxO (sV k.1) (s k.1) (unitMap (BV k.1) (BW k.1) k.2.1 k.2.2) =
      (I * η k) • unitMap (BV k.1) (BW k.1) k.2.1 k.2.2 := fun k => by
    rw [cplxO_unitMap (hdet _) (hs _) (hs' _)]
    simp only [η, Complex.ofReal_mul]
  have h1 : ∀ k : FVar D W.rank V.rank, u 1 k = (Pi.single k.1 (unitMap (BV k.1) (BW k.1) k.2.1 k.2.2) :
      D.what₂.Tau → Matrix (Fin W.rank) (Fin V.rank) ℂ) := fun k => congrArg (Pi.single k.1) (one_smul _ _)
  have hξ : ∀ τ, tauE D τ D.host.xi0 ≠ 0 := fun τ => (_root_.map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
  have hre := fun τ => GlobalTheory.OrientedRealForm.realPlace_imaginaryGenerator_re_eq_zero (D := D) τ
  have him : ∀ τ, (tauE D τ D.host.xi0).im ≠ 0 := fun τ hh => hξ τ (Complex.ext (hre τ) hh)
  have hsc : ∀ τ, (fockScale D τ : ℂ) ≠ 0 := fun τ => by
    have := norm_pos_iff.2 (hξ τ)
    have h2 : 0 < fockScale D τ := by unfold fockScale; positivity
    exact Complex.ofReal_ne_zero.2 h2.ne'
  refine injective_of_canonicalCommutation M _ (fun k => (fockScale D k.1 : ℂ)⁻¹ • (Dop (u 1 k) - I • Dop (u (I * η k) k)))
    (fun k => Dop (u 1 k) + I • Dop (u (I * η k) k))
    (fun k => (fockScale D k.1 : ℂ)⁻¹ * (-8 * Real.pi * (tauE D k.1 D.host.xi0).im)) (fun k g => ?_) (fun k l g => ?_)
    (fun k l g => ?_) (fun k => ?_) ⟨f, theta_sm h hf⟩ (fun k => ?_) (fun hh => hf0 (congrArg Subtype.val hh))
  · simp only [aPlusAll, aPlus, crea, LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub,
      hD1, hE, hJ]
    rw [h1]
  · rw [(ccr_of_comm Dop _ hcomm _ _ _ _ _ _ g).1]
    refine add_eq_left.2 (smul_eq_zero.2 (Or.inl ?_))
    simp only [hom]
    split_ifs with hh
    · subst hh
      rcases hη k with e | e <;> simp [e, hre]
    · simp
  · rw [(ccr_of_comm Dop _ hcomm _ _ _ _ 0 _ g).2]
    refine congrArg (fun c : ℂ => _ + c • g) ?_
    by_cases hh : k = l
    · subst hh
      simp only [hom, if_true]
      refine congrArg _ ?_
      rcases hη k with e | e <;> simp [e, hre] <;> ring_nf <;> simp only [I_sq] <;> ring1
    · simp [hom, hh]
  · exact mul_ne_zero (inv_ne_zero (hsc _)) (mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)) (Complex.ofReal_ne_zero.2 (him _)))
  · apply Subtype.ext
    have := hvac k.1 (unitMap (BV k.1) (BW k.1) k.2.1 k.2.2)
    simp only [annih, hE, hJ] at this
    simp only [LinearMap.smul_apply, LinearMap.add_apply, Submodule.coe_smul, Submodule.coe_add, hD1]
    rw [h1]
    exact this

end GlobalTheory.FockVecInj

end
