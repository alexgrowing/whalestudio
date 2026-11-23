import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonsplitCentraliserNormElement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjSelfReciprocalOfDvdEllipticPolynomial
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct ComplexOrder ComplexConjugate
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.PosDefNorm

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem norm_value_pos {r : ℕ} (Q : SelfRecip E r) (ρ : Fld Q →+* ℂ) (hn : ‖ρ (alpha Q)‖ = 1) (y : Fld Q)
    (hz : ∀ u : InfinitePlace (maximalRealSubfield E), ∃ z : (u.Completion ⊗[maximalRealSubfield E] Fld Q)ˣ,
      (z : u.Completion ⊗[maximalRealSubfield E] Fld Q) *
        involBase Q u.Completion (z : u.Completion ⊗[maximalRealSubfield E] Fld Q) = 1 ⊗ₜ y) :
    0 < ρ y := by
  have hinv : ∀ x, ρ (invol Q x) = conj (ρ x) := by
    have h : (ρ.comp (invol Q : Fld Q →+* Fld Q)) = (starRingEnd ℂ).comp ρ := by
      refine AdjoinRoot.ringHom_ext (RingHom.ext fun e => ?_) ?_
      · change ρ (invol Q (algebraMap E (Fld Q) e)) = conj (ρ (algebraMap E (Fld Q) e))
        rw [invol_algebraMap]
        exact IsCMField.complexEmbedding_complexConj E (ρ.comp (algebraMap E (Fld Q))) e
      · change ρ (invol Q (alpha Q)) = conj (ρ (alpha Q))
        rw [invol_alpha, map_inv₀]
        exact Complex.inv_eq_conj hn
    exact fun x => DFunLike.congr_fun h x
  let ρF : maximalRealSubfield E →+* ℂ := ρ.comp (algebraMap (maximalRealSubfield E) (Fld Q))
  let w := InfinitePlace.mk ρF
  have hw : w.IsReal := IsTotallyReal.isReal w
  letI : Algebra (maximalRealSubfield E) ℂ := ρF.toAlgebra
  let g : w.Completion →ₐ[maximalRealSubfield E] ℂ :=
    ⟨InfinitePlace.Completion.extensionEmbedding w, fun a =>
      (InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ a)).trans
        (DFunLike.congr_fun (InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 hw)) a)⟩
  have hg : ∀ a, conj (g a) = g a := fun a => by
    have : g a = (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw a : ℂ) :=
      (InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw a).symm
    rw [this, Complex.conj_ofReal]
  let f := (Algebra.TensorProduct.productMap g
    (⟨ρ, fun _ => rfl⟩ : Fld Q →ₐ[maximalRealSubfield E] ℂ)).toRingHom
  have hf : ∀ a e, f (a ⊗ₜ e) = g a * ρ e := fun _ _ => rfl
  have hfi : ∀ t, f (involBase Q w.Completion t) = conj (f t) := fun t => by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      rw [involBase, Algebra.TensorProduct.map_tmul, hf, hf, map_mul, hg]
      exact congrArg _ (hinv e)
    | add a b ha hb => simp only [map_add, ha, hb]
  obtain ⟨z, hz⟩ := hz w
  have h1 := congrArg f hz
  rw [map_mul, hfi, hf, map_one, one_mul, Complex.mul_conj] at h1
  have h2 : f (z : w.Completion ⊗[maximalRealSubfield E] Fld Q) ≠ 0 := (z.isUnit.map f).ne_zero
  rw [← h1]
  exact_mod_cast Complex.normSq_pos.2 h2

theorem exists_irreducible_factor (P : E[X]) (hP : P.Monic) (τ : E →+* ℂ) (μ : ℂ) (h : eval₂ τ μ P = 0) :
    ∃ R : E[X], R.Monic ∧ Irreducible R ∧ R ∣ P ∧ eval₂ τ μ R = 0 := by
  letI : Algebra E ℂ := τ.toAlgebra
  have hi : IsIntegral E μ := ⟨P, hP, h⟩
  exact ⟨minpoly E μ, minpoly.monic hi, minpoly.irreducible hi, minpoly.dvd E μ h, minpoly.aeval E μ⟩

theorem aeval_units_conj {n : ℕ} (u : (Matrix (Fin n) (Fin n) ℂ)ˣ) (A : Matrix (Fin n) (Fin n) ℂ) (p : ℂ[X]) :
    aeval ((u : Matrix (Fin n) (Fin n) ℂ) * A * ((u⁻¹ : _ˣ) : Matrix (Fin n) (Fin n) ℂ)) p =
      (u : Matrix (Fin n) (Fin n) ℂ) * aeval A p * ((u⁻¹ : _ˣ) : Matrix (Fin n) (Fin n) ℂ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, hp, hq, mul_add, add_mul]
  | monomial k a =>
    rw [aeval_monomial, aeval_monomial, Units.conj_pow]
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, mul_smul_comm]

theorem posDef_aeval {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU : Uᴴ * U = 1) (hs : U.charpoly.Separable)
    (hn : ∀ μ : ℂ, U.charpoly.IsRoot μ → ‖μ‖ = 1) (p : ℂ[X])
    (hp : ∀ μ : ℂ, U.charpoly.IsRoot μ → 0 < p.eval μ) : (aeval U p).PosDef := by
  have hU' : U * Uᴴ = 1 := mul_eq_one_comm.1 hU
  obtain ⟨r, hr⟩ := GlobalTheory.BCT.ClsFin.exists_aeval_of_comm U Uᴴ hs (hU'.trans hU.symm)
  have hdiv : U.charpoly ∣ X * r - 1 := by
    refine GlobalTheory.ClassParam.charpoly_dvd_of_aeval U hs _ ?_
    rw [map_sub, map_mul, aeval_X, ← hr, hU', map_one, sub_self]
  have hrv : ∀ μ : ℂ, U.charpoly.IsRoot μ → r.eval μ = conj μ := fun μ hμ => by
    obtain ⟨t, ht⟩ := hdiv
    have h1 := congrArg (eval μ) ht
    have h0 : eval μ U.charpoly = 0 := hμ
    rw [eval_mul, h0, zero_mul, eval_sub, eval_mul, eval_X, eval_one, sub_eq_zero] at h1
    rw [← Complex.inv_eq_conj (hn μ hμ)]
    exact eq_inv_of_mul_eq_one_right h1
  have hcT : (aeval U p)ᴴ = aeval U ((p.map (starRingEnd ℂ)).comp r) := by
    have h1 := GlobalTheory.NormInert.cT_aeval (starRingEnd ℂ) U p
    have h2 : ∀ M : Matrix (Fin n) (Fin n) ℂ, cT (starRingEnd ℂ) M = Mᴴ := fun M => rfl
    rw [h2, h2, hr, ← aeval_comp] at h1
    exact h1
  have hzero : aeval U (p - (p.map (starRingEnd ℂ)).comp r) = 0 := by
    by_cases h0 : p - (p.map (starRingEnd ℂ)).comp r = 0
    · rw [h0, map_zero]
    have hd : U.charpoly ∣ p - (p.map (starRingEnd ℂ)).comp r := by
      refine (IsAlgClosed.splits _).dvd_of_roots_le_roots U.charpoly_monic.ne_zero ?_
      rw [Multiset.le_iff_subset (nodup_roots hs)]
      intro μ hμ
      have hμ' := isRoot_of_mem_roots hμ
      rw [mem_roots h0, IsRoot.def, eval_sub, eval_comp, hrv μ hμ', sub_eq_zero, eval_map]
      have h3 : eval₂ (starRingEnd ℂ) (conj μ) p = conj (eval μ p) := by
        rw [eval, Polynomial.hom_eval₂, RingHom.comp_id]
      rw [h3]
      exact (Complex.conj_eq_iff_im.2 (Complex.pos_iff.1 (hp μ hμ')).2.symm).symm
    obtain ⟨t, ht⟩ := hd
    rw [ht, map_mul, Matrix.aeval_self_charpoly, zero_mul]
  have hH : (aeval U p).IsHermitian := by
    rw [Matrix.IsHermitian, hcT]
    rw [map_sub, sub_eq_zero] at hzero
    exact hzero.symm
  rw [hH.posDef_iff_eigenvalues_pos]
  intro i
  haveI : Nonempty (Fin n) := ⟨i⟩
  have h1 : ((hH.eigenvalues i : ℝ) : ℂ) ∈ spectrum ℂ (aeval U p) := by
    have := hH.eigenvalues_mem_spectrum_real i
    rw [← spectrum.preimage_algebraMap ℂ] at this
    exact this
  rw [spectrum.map_polynomial_aeval_of_nonempty _ _ (spectrum.nonempty_of_isAlgClosed_of_finiteDimensional ℂ U)] at h1
  obtain ⟨μ, hμ, e⟩ := h1
  have h2 := hp μ (Matrix.mem_spectrum_iff_isRoot_charpoly.1 hμ)
  rw [show eval μ p = ((hH.eigenvalues i : ℝ) : ℂ) from e] at h2
  exact_mod_cast h2

open scoped MatrixOrder Matrix.Norms.L2Operator in
theorem exists_factor {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ} (hT : T.PosSemidef) :
    ∃ S : Matrix (Fin n) (Fin n) ℂ, T = Sᴴ * S := by
  obtain ⟨y, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hT.nonneg
  exact ⟨y, rfl⟩

theorem map_aeval {n : ℕ} (τ : E →+* ℂ) (A : Matrix (Fin n) (Fin n) E) (p : E[X]) :
    (aeval A p).map τ = aeval (A.map τ) (p.map τ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, Polynomial.map_add, map_add, ← hp, ← hq]
    ext i j
    simp
  | monomial k a =>
    rw [aeval_monomial, Polynomial.map_monomial, aeval_monomial]
    have e : (A.map τ) ^ k = (A ^ k).map τ := by rw [Matrix.map_pow]
    rw [e]
    ext i j
    simp [Algebra.algebraMap_eq_smul_one]

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → ∀ m : E[X], (∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → invol Q (AdjoinRoot.mk Q.1 m : Fld Q) = (AdjoinRoot.mk Q.1 m : Fld Q)) → (∀ (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∀ u : InfinitePlace (maximalRealSubfield E), ∃ z : (u.Completion ⊗[(maximalRealSubfield E)] Fld Q)ˣ, (z : u.Completion ⊗[(maximalRealSubfield E)] Fld Q) * involBase Q u.Completion (z : u.Completion ⊗[(maximalRealSubfield E)] Fld Q) = 1 ⊗ₜ (AdjoinRoot.mk Q.1 m : Fld Q)) → ∀ τ : E →+* ℂ, ∃ Q' : Matrix (Fin n) (Fin n) ℂ, Q'.det ≠ 0 ∧ (H₀ * aeval γ₀.val m).map τ = cT (starRingEnd ℂ) Q' * Q' := by
  intro E _ _ _ n γ₀ hell H₀ _ _ hiso hdef m _ hz τ
  obtain ⟨Q, hQ, hHQ⟩ := hdef τ
  have h2 : ∀ M : Matrix (Fin n) (Fin n) ℂ, cT (starRingEnd ℂ) M = Mᴴ := fun M => rfl
  rw [h2] at hHQ
  set A := γ₀.val.map τ with hA
  have hiso' : Aᴴ * (Qᴴ * Q) * A = Qᴴ * Q := by
    have h := congrArg (fun M => M.map τ) hiso
    simp only [Matrix.map_mul] at h
    have e : (cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val).map τ = Aᴴ := by
      ext i j
      exact IsCMField.complexEmbedding_complexConj E τ (γ₀.val j i)
    rw [e, hHQ] at h
    exact h
  let u : (Matrix (Fin n) (Fin n) ℂ)ˣ := ((Matrix.isUnit_iff_isUnit_det Q).2 (isUnit_iff_ne_zero.2 hQ)).unit
  have hu : (u : Matrix (Fin n) (Fin n) ℂ) = Q := rfl
  obtain ⟨Qi, hQi⟩ : ∃ Qi : Matrix (Fin n) (Fin n) ℂ, Qi = ((u⁻¹ : _ˣ) : Matrix (Fin n) (Fin n) ℂ) := ⟨_, rfl⟩
  have e1 : Q * Qi = 1 := by rw [hQi, ← hu]; exact u.mul_inv
  have e2 : Qi * Q = 1 := by rw [hQi, ← hu]; exact u.inv_mul
  have hconj := aeval_units_conj u A (m.map τ)
  have hchar := Matrix.charpoly_units_conj u A
  rw [← Matrix.coe_units_inv] at hchar
  rw [hu, ← hQi] at hconj hchar
  have hAc : A.charpoly = γ₀.val.charpoly.map τ := Matrix.charpoly_map _ _
  obtain ⟨U, hUd⟩ : ∃ U, U = Q * A * Qi := ⟨_, rfl⟩
  rw [← hUd] at hconj hchar
  have hU : Uᴴ * U = 1 := by
    have e3 : Qiᴴ * Qᴴ = 1 := by rw [← conjTranspose_mul, e1, conjTranspose_one]
    calc Uᴴ * U = Qiᴴ * (Aᴴ * (Qᴴ * Q) * A) * Qi := by
          simp only [hUd, conjTranspose_mul, Matrix.mul_assoc]
      _ = (Qiᴴ * Qᴴ) * (Q * Qi) := by rw [hiso']; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e1, e3, Matrix.mul_one]
  have hroot : ∀ μ : ℂ, U.charpoly.IsRoot μ → (γ₀.val.charpoly.map τ).IsRoot μ := fun μ h => by
    rwa [hchar, hAc] at h
  have hnorm : ∀ μ : ℂ, U.charpoly.IsRoot μ → ‖μ‖ = 1 := fun μ h =>
    hell.2.2.2 τ μ ((mem_roots (Polynomial.map_ne_zero hell.1.ne_zero)).2 (hroot μ h))
  have hsep : U.charpoly.Separable := by
    rw [hchar, hAc]
    exact hell.2.2.1.map
  have hp : ∀ μ : ℂ, U.charpoly.IsRoot μ → 0 < (m.map τ).eval μ := fun μ h => by
    have h0 : eval₂ τ μ γ₀.val.charpoly = 0 := by
      rw [← eval_map]
      exact hroot μ h
    obtain ⟨R, Rm, Ri, Rd, Re⟩ := exists_irreducible_factor _ hell.1 τ μ h0
    let S : SelfRecip E R.natDegree := ⟨R, GlobalTheory.SelfRecipFactor.isSelfRecip_of_dvd_ell E n _ hell R Rm Ri Rd⟩
    let ρ : Fld S →+* ℂ := AdjoinRoot.lift τ μ Re
    have hα : ρ (alpha S) = μ := AdjoinRoot.lift_root Re
    have hm : ρ (AdjoinRoot.mk S.1 m : Fld S) = eval₂ τ μ m := AdjoinRoot.lift_mk Re m
    have := norm_value_pos S ρ (by rw [hα]; exact hnorm μ h) _ (hz _ S Rd)
    rwa [hm, ← eval_map] at this
  have hT := posDef_aeval U hU hsep hnorm (m.map τ) hp
  obtain ⟨S, hS⟩ := exists_factor hT.posSemidef
  have hdetS : S.det ≠ 0 := fun h => by
    have := hT.det_pos
    rw [hS, Matrix.det_mul, h, mul_zero] at this
    exact lt_irrefl _ this
  refine ⟨S * Q, by rw [Matrix.det_mul]; exact mul_ne_zero hdetS hQ, ?_⟩
  have e4 : Q * aeval A (m.map τ) = (Sᴴ * S) * Q := by
    rw [← hS, hconj, Matrix.mul_assoc, e2, Matrix.mul_one]
  rw [Matrix.map_mul, hHQ, map_aeval, h2, conjTranspose_mul, Matrix.mul_assoc, e4]
  simp only [Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.PosDefNorm
end
