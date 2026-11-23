import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LetAct
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLetterEquivConjugate
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowHighestLeSpanColWordComplex

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameRead

open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.Harm
open scoped Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw : Datum H) {n : ℕ}

def invTranspose {K : Type} [Field K] (g : GL (Fin n) K) : GL (Fin n) K :=
  ⟨((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).transpose, (g : Matrix (Fin n) (Fin n) K).transpose,
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩

theorem rename_letAct_invTranspose_eq_colAct {Ix : Type} [Fintype Ix] {pl : Ix → (E →+* ℂ)} (hpl : IsEnum H pl) (K : Type) [Field K]
    (g : {τ : E →+* ℂ // InPsi H τ} → GL (Fin n) K) (P : MvPolynomial (LtN Dw n) K) :
    rename (thetaLetterEquiv Dw n) (letAct Dw pl K (fun t => invTranspose (g ⟨pl t, (hpl.2 _).2 ⟨t, rfl⟩⟩)) P) =
      colAct K _ Dw.p Dw.q (Fin n) g (rename (thetaLetterEquiv Dw n) P) := by
  rw [colAct_apply]
  refine DFunLike.congr_fun (?_ : (rename (thetaLetterEquiv Dw n)).comp
    (letAct Dw pl K (fun t => invTranspose (g ⟨pl t, (hpl.2 _).2 ⟨t, rfl⟩⟩))) =
    (colSubst (fun t => (((g t)⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (fun t => g t)).comp
      (rename (thetaLetterEquiv Dw n))) P
  refine MvPolynomial.algHom_ext fun ⟨τ, i, b⟩ => ?_
  rw [AlgHom.comp_apply, AlgHom.comp_apply, rename_X, letAct, aeval_X]
  rcases half_cases (Ψ := InPsi H) (ComplexEmbedding.involutive_conjugate E)
    (not_mem_hostType_iff H) τ with h | ⟨τ, h, rfl⟩
  · have h₁ : ∃ t, pl t = τ := (hpl.2 τ).1 h
    rw [dif_pos h₁, thetaLetterEquiv_of_mem Dw h, colSubst_X_xVar, xForm_apply, map_sum]
    have e : (⟨pl h₁.choose, (hpl.2 _).2 ⟨_, rfl⟩⟩ : {τ : E →+* ℂ // InPsi H τ}) = ⟨τ, h⟩ :=
      Subtype.ext h₁.choose_spec
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, rename_C, rename_X, thetaLetterEquiv_of_mem Dw h]
    simp only [e]
    rfl
  · have h₀ : ¬ ∃ t, pl t = ComplexEmbedding.conjugate τ := fun hh => by
      have h₂ : InPsi H (ComplexEmbedding.conjugate τ) := (hpl.2 _).2 hh
      exact (not_mem_hostType_iff H τ).2 h₂ h
    have h₁ : ∃ t, ComplexEmbedding.conjugate (pl t) = ComplexEmbedding.conjugate τ := by
      obtain ⟨t, ht⟩ := (hpl.2 τ).1 h
      exact ⟨t, by rw [ht]⟩
    rw [dif_neg h₀, dif_pos h₁, thetaLetterEquiv_conjugate Dw h, colSubst_X_yVar, yForm_apply, map_sum]
    have e : (⟨pl h₁.choose, (hpl.2 _).2 ⟨_, rfl⟩⟩ : {τ : E →+* ℂ // InPsi H τ}) = ⟨τ, h⟩ :=
      Subtype.ext ((ComplexEmbedding.involutive_conjugate E).injective h₁.choose_spec)
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, rename_C, rename_X, thetaLetterEquiv_conjugate Dw h]
    simp only [e]
    rfl

variable {l : Level H} (c : Coeff l)

theorem rename_minorP_of_mem (hn : Dw.p + Dw.q ≤ n) {τ : E →+* ℂ} (h : InPsi H τ) (i : Fin Dw.p)
    (hi : i.val < Dw.mult τ) (hi' : i.val + 1 ≤ n) :
    rename (thetaLetterEquiv Dw n) (minorPolynomial (Dw := Dw) c τ i.val hi (Fin.castLE hi')) =
      xMinor ⟨τ, h⟩ i (baseCovec c.F hn) := by
  rw [minorPolynomial, xMinor, AlgHom.map_det]
  congr 1
  ext1 s b
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X, baseCovec, xForm_single]
  rw [thetaLetterEquiv_of_mem Dw h]
  rfl

theorem rename_minorP_conjugate (hn : Dw.p + Dw.q ≤ n) {τ : E →+* ℂ} (h : InPsi H τ) (i : Fin Dw.q)
    (hi : i.val < Dw.mult (ComplexEmbedding.conjugate τ)) (hi' : n - (i.val + 1) + (i.val + 1) = n) :
    rename (thetaLetterEquiv Dw n) (minorPolynomial (Dw := Dw) c (ComplexEmbedding.conjugate τ) i.val hi
      (fun b => Fin.cast hi' (Fin.natAdd (n - (i.val + 1)) b))) =
      ((Equiv.Perm.sign (Fin.revPerm (n := i.val + 1)) : ℤ) : Poly c.F _ Dw.p Dw.q (Fin n)) *
        yMinor ⟨τ, h⟩ i (baseVec c.F hn) := by
  rw [minorPolynomial, yMinor, AlgHom.map_det, ← Matrix.det_permute']
  congr 1
  ext1 s b
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, rename_X, baseVec, yForm_single,
    Matrix.submatrix_apply, id]
  rw [thetaLetterEquiv_conjugate Dw h]
  refine congrArg X (Prod.ext rfl (Prod.ext rfl (Fin.ext ?_)))
  have := b.isLt
  simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_rev, Fin.val_castLE, Fin.revPerm_apply]
  omega

theorem rename_pG [Fintype {τ : E →+* ℂ // InPsi H τ}] (hn : Dw.p + Dw.q ≤ n) (a : (E →+* ℂ) × ℕ → ℕ) :
    ∃ u : ℤˣ, rename (thetaLetterEquiv Dw n) (pG (Dw := Dw) c a n) =
      ((u : ℤ) : Poly c.F _ Dw.p Dw.q (Fin n)) *
        basePoly c.F hn (fun t : {τ : E →+* ℂ // InPsi H τ} => diffOf fun i : Fin Dw.p => a (t.1, i))
          (fun t => diffOf fun i : Fin Dw.q => a (ComplexEmbedding.conjugate t.1, i)) := by
  refine ⟨∏ t : {τ : E →+* ℂ // InPsi H τ}, ∏ i : Fin Dw.q, Equiv.Perm.sign (Fin.revPerm (n := i.val + 1)) ^
    diffOf (fun i : Fin Dw.q => a (ComplexEmbedding.conjugate t.1, i)) i, ?_⟩
  rw [pG, ← Fintype.prod_sigma', ← (halfRowEquiv (Ψ := InPsi H) (ComplexEmbedding.involutive_conjugate E)
    (not_mem_hostType_iff H) (fun _ => mult_of_mem Dw) (fun _ => mult_conjEmb_of_mem Dw)).symm.prod_comp,
    Fintype.prod_prod_type, basePoly, minorProd, map_prod]
  push_cast
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [Fintype.prod_sum_type, map_mul, mul_left_comm, ← Finset.prod_mul_distrib, map_prod, map_prod]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hi' : i.val + 1 ≤ n := by have := i.isLt; omega
    have hi : i.val < Dw.mult t.1 := by rw [mult_of_mem Dw t.2]; exact i.isLt
    change rename _ ((if h : i.val + 1 ≤ n then
      (if InPsi H t.1 then minorPolynomial c t.1 i.val hi (Fin.castLE h)
        else minorPolynomial c t.1 i.val hi (fun b => Fin.cast (by omega) (Fin.natAdd (n - (i.val + 1)) b)))
      else 0) ^ aStep Dw a t.1 i.val) = _
    rw [dif_pos hi', if_pos t.2, map_pow, rename_minorP_of_mem Dw c hn t.2]
    congr 1
    rw [aStep, diffOf, mult_of_mem Dw t.2]
    split_ifs <;> rfl
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hi' : i.val + 1 ≤ n := by have := i.isLt; omega
    have hi : i.val < Dw.mult (ComplexEmbedding.conjugate t.1) :=
      i.isLt.trans_eq (mult_conjEmb_of_mem Dw t.2).symm
    have h₀ : ¬ InPsi H (ComplexEmbedding.conjugate t.1) := fun h₂ => (not_mem_hostType_iff H t.1).2 h₂ t.2
    change rename _ ((if h : i.val + 1 ≤ n then
      (if InPsi H (ComplexEmbedding.conjugate t.1) then
        minorPolynomial c (ComplexEmbedding.conjugate t.1) i.val hi (Fin.castLE h)
        else minorPolynomial c (ComplexEmbedding.conjugate t.1) i.val hi
          (fun b => Fin.cast (by omega) (Fin.natAdd (n - (i.val + 1)) b)))
      else 0) ^ aStep Dw a (ComplexEmbedding.conjugate t.1) i.val) = _
    rw [dif_pos hi', if_neg h₀, map_pow, rename_minorP_conjugate Dw c hn t.2, ← mul_pow]
    congr 1
    have hq : Dw.mult (ComplexEmbedding.conjugate t.1) = Dw.q := mult_conjEmb_of_mem Dw t.2
    rw [aStep, diffOf, hq]
    split_ifs <;> rfl

theorem pG_mem_ne_zero_generates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (n : ℕ) (Ix : Type) [Fintype Ix] (pl : Ix → (E →+* ℂ)), IsEnum H pl → Dw.p + Dw.q ≤ n → ∀ (l : Level H) (c : Coeff l) (a : (E →+* ℂ) × ℕ → ℕ), (∀ τ, Antitone fun i => a (τ, i)) → pG (Dw := Dw) c a n ∈ harmA (Dw := Dw) c a n ∧ pG (Dw := Dw) c a n ≠ 0 ∧ ∀ P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)), P ∈ Submodule.span c.F (Set.range fun g : Ix → GL (Fin n) c.F => letAct Dw pl c.F g (pG (Dw := Dw) c a n)) := by
  intro E _ _ _ H Dw n Ix _ pl hpl hn l c a ha
  obtain ⟨u, hu⟩ := rename_pG Dw c hn a
  set k := fun t : {τ : E →+* ℂ // InPsi H τ} => diffOf fun i : Fin Dw.p => a (t.1, i) with hk
  set k' := fun t : {τ : E →+* ℂ // InPsi H τ} =>
    diffOf fun i : Fin Dw.q => a (ComplexEmbedding.conjugate t.1, i) with hk'
  have hx (t : {τ : E →+* ℂ // InPsi H τ}) : partOf (k t) = fun i : Fin Dw.p => a (t.1, i) :=
    partOf_diffOf fun i j hij => ha t.1 hij
  have hy (t : {τ : E →+* ℂ // InPsi H τ}) :
      partOf (k' t) = fun i : Fin Dw.q => a (ComplexEmbedding.conjugate t.1, i) :=
    partOf_diffOf fun i j hij => ha _ hij
  have hmem (P : MvPolynomial (LtN Dw n) c.F) :
      P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) ↔
        rename (thetaLetterEquiv Dw n) P ∈ orbitSpan c.F hn k k' := by
    rw [← (rowHighest_orbitSpan_main hn k k' c.F).2.1, mem_rowHighest_iff_rowAdd]
    simp only [hx, hy]
    exact mem_HHa_iff_rename (Ψ := InPsi H) (ComplexEmbedding.involutive_conjugate E) (not_mem_hostType_iff H)
      (fun _ => mult_of_mem Dw) (fun _ => mult_conjEmb_of_mem Dw) _ P
  rw [← zsmul_eq_mul] at hu
  have hu' : basePoly c.F hn k k' = (u : ℤ) • rename (thetaLetterEquiv Dw n) (pG (Dw := Dw) c a n) := by
    rw [hu, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]
  have hinj := (thetaLetterEquiv Dw n).injective
  refine ⟨⟨(hmem _).2 ?_, fun m => ?_⟩, fun h0 => ?_, fun P hP => ?_⟩
  · rw [hu]
    exact zsmul_mem (basePoly_mem hn k k') _
  · rw [← coeff_rename_mapDomain _ hinj, hu, ← map_basePoly hn k k' (Int.castRingHom c.F), ← map_zsmul, coeff_map]
    exact intCast_mem _ _
  · rw [h0, map_zero, smul_zero] at hu'
    exact basePoly_ne_zero hn k k' hu'
  · have key : orbitSpan c.F hn k k' ≤ (Submodule.span c.F (Set.range fun g : Ix → GL (Fin n) c.F =>
        letAct Dw pl c.F g (pG (Dw := Dw) c a n))).map (rename (thetaLetterEquiv Dw n)).toLinearMap := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, rfl⟩
      simp only [hu', map_zsmul, ← rename_letAct_invTranspose_eq_colAct Dw hpl]
      exact zsmul_mem (Submodule.mem_map_of_mem (Submodule.subset_span (Set.mem_range_self _))) _
    obtain ⟨Q, hQ, e⟩ := key ((hmem P).1 hP)
    rwa [← rename_injective _ hinj e]

end GlobalTheory.FrameRead
