import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.CoefFieldEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.Thorne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformModel
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.CocycleCoefficients.PetAdjQuot

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N GlobalTheory.GalOfCusp GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published.Kato UpperTheory.V.Lit CongruenceSubgroup
open scoped Matrix MatrixGroups ModularForm ComplexConjugate

noncomputable section

namespace UpperTheory.V.Lit.KT

open UpperHalfPlane ModularForm
open scoped Manifold

private structure Good (H : Subgroup SL(2, ℤ)) (k : ℤ) (F : ℍ → ℂ) : Prop where
  hol : MDiff F
  bd : ∃ C : ℝ, ∀ z, ‖petersson k F F z‖ ≤ C
  inv : ∀ γ ∈ H, F ∣[k] γ = F

variable {H : Subgroup SL(2, ℤ)} {k : ℤ} {F G : ℍ → ℂ}

private theorem Good.cont (hF : Good H k F) (hG : Good H k G) : Continuous (petersson k F G) :=
  petersson_continuous k hF.hol.continuous hG.hol.continuous

private theorem Good.pbd (hF : Good H k F) (hG : Good H k G) : ∃ C : ℝ, ∀ z, ‖petersson k F G z‖ ≤ C := by
  obtain ⟨A, hA⟩ := hF.bd
  obtain ⟨B, hB⟩ := hG.bd
  refine ⟨A + B, fun z => le_trans ?_ (add_le_add (hA z) (hB z))⟩
  simp only [petersson, norm_mul, Complex.norm_conj]
  rw [← add_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  nlinarith [sq_nonneg (‖F z‖ - ‖G z‖), norm_nonneg (F z), norm_nonneg (G z)]

private theorem Good.pinv (hF : Good H k F) (hG : Good H k G) : ∀ γ ∈ H, ∀ z, petersson k F G (γ • z) = petersson k F G z :=
  fun γ hγ z => by rw [← petersson_slash_SL, hF.inv γ hγ, hG.inv γ hγ]

private theorem Good.slash {K : Subgroup SL(2, ℤ)} (hF : Good K k F) (α : GL (Fin 2) ℝ) (h : H ≤ conjGL K α) :
    Good H k (F ∣[k] α) := by
  obtain ⟨A, hA⟩ := hF.bd
  refine ⟨hF.hol.slash k α, ⟨‖((|α.det.val| : ℝ) : ℂ) ^ (k - 2)‖ * A, fun z => ?_⟩, fun γ hγ => ?_⟩
  · rw [petersson_slash, norm_mul, norm_σ]
    exact mul_le_mul_of_nonneg_left (hA _) (norm_nonneg _)
  · obtain ⟨y, hy, e⟩ := mem_conjGL.1 (h hγ)
    have e' : α * (γ : GL (Fin 2) ℝ) = (y : GL (Fin 2) ℝ) * α := by rw [e]; group
    rw [SL_slash, ← SlashAction.slash_mul, e', SlashAction.slash_mul, ← SL_slash, hF.inv y hy]

private theorem le_conj [hN : H.Normal] (γ : SL(2, ℤ)) : H ≤ conjGL H (γ : GL (Fin 2) ℝ) := fun x hx =>
  mem_conjGL.2 ⟨_, hN.conj_mem x hx γ, by simp⟩

private theorem Good.slashSL [H.Normal] (hF : Good H k F) (γ : SL(2, ℤ)) : Good H k (F ∣[k] γ) :=
  hF.slash _ (le_conj γ)

private theorem B_slash [H.FiniteIndex] {α : GL (Fin 2) ℝ} (hα : 0 < α.det.val) (h1 : (conjGL H α).FiniteIndex)
    (h2 : (conjGL H α⁻¹).FiniteIndex) (hF : Good H k F) (hG : Good H k G) (hF' : Good H k (F ∣[k] α))
    (hG' : Good H k (G ∣[k] α)) :
    quotInt H (petersson k (F ∣[k] α) (G ∣[k] α)) = (α.det.val : ℂ) ^ (k - 2) * quotInt H (petersson k F G) := by
  have e : ∀ z, petersson k (F ∣[k] α) (G ∣[k] α) z = (α.det.val : ℂ) ^ (k - 2) * petersson k F G (α • z) := fun z => by
    rw [petersson_slash, σ, if_pos hα, abs_of_pos hα]; rfl
  have h0 : (α.det.val : ℂ) ^ (k - 2) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast hα.ne')
  obtain ⟨C, hC⟩ := hF.pbd hG
  rw [funext e, quotInt_mul, quotInt_conj H α h1 h2 (hF.cont hG) hC (hF.pinv hG) fun γ hγ z => ?_]
  refine mul_left_cancel₀ h0 ?_
  rw [← e, ← e, hF'.pinv hG' γ hγ]

private theorem B_slashSL [H.FiniteIndex] [H.Normal] (γ : SL(2, ℤ)) (hF : Good H k F) (hG : Good H k G) :
    quotInt H (petersson k (F ∣[k] γ) (G ∣[k] γ)) = quotInt H (petersson k F G) := by
  have hd : (γ : GL (Fin 2) ℝ).det.val = 1 := by simp
  have h2 : (conjGL H (γ : GL (Fin 2) ℝ)⁻¹).FiniteIndex := by
    have := Subgroup.finiteIndex_of_le (le_conj (H := H) γ⁻¹)
    rwa [map_inv, map_inv] at this
  have := B_slash (α := (γ : GL (Fin 2) ℝ)) (by rw [hd]; exact one_pos) (Subgroup.finiteIndex_of_le (le_conj γ)) h2 hF hG
    (hF.slashSL γ) (hG.slashSL γ)
  rw [hd, Complex.ofReal_one, one_zpow, one_mul] at this
  exact this

private theorem B_smul_left [H.FiniteIndex] (c : ℂ) :
    quotInt H (petersson k (c • F) G) = conj c * quotInt H (petersson k F G) := by
  rw [← quotInt_mul]; congr 1; funext z; simp [petersson]; ring

private theorem B_smul_right [H.FiniteIndex] (c : ℂ) :
    quotInt H (petersson k F (c • G)) = c * quotInt H (petersson k F G) := by
  rw [← quotInt_mul]; congr 1; funext z; simp [petersson]; ring

private theorem Good.smul (hF : Good H k F) (c : ℂ) : Good H k (c • F) := by
  obtain ⟨A, hA⟩ := hF.bd
  refine ⟨hF.hol.const_smul c, ⟨‖c‖ ^ 2 * A, fun z => ?_⟩, fun γ hγ => by rw [SL_smul_slash, hF.inv γ hγ]⟩
  refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left (hA z) (by positivity))
  simp [petersson]; ring

private theorem B_adj [H.FiniteIndex] {α β : GL (Fin 2) ℝ} {p : ℕ} (hp : 0 < p) (hβ : β.det.val = p)
    (h1 : (conjGL H β).FiniteIndex) (h2 : (conjGL H β⁻¹).FiniteIndex) (hF : Good H k F) (hG : Good H k G)
    (hF' : Good H k (F ∣[k] α)) (hG' : Good H k (G ∣[k] β)) (e : (F ∣[k] α) ∣[k] β = (p : ℂ) ^ (k - 2) • F) :
    quotInt H (petersson k F (G ∣[k] β)) = quotInt H (petersson k (F ∣[k] α) G) := by
  have h := B_slash (by rw [hβ]; exact_mod_cast hp) h1 h2 hF' hG (e ▸ hF.smul _) hG'
  rw [e, B_smul_left, hβ, map_zpow₀, map_natCast, Complex.ofReal_natCast] at h
  exact mul_left_cancel₀ (zpow_ne_zero _ (by exact_mod_cast hp.ne')) h

private def dg (m n : ℕ) (h : m * n ≠ 0) : GL (Fin 2) ℝ :=
  (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(m : ℚ), 0; 0, (n : ℚ)]
    (by rw [Matrix.det_fin_two_of, mul_zero, sub_zero]; exact_mod_cast h)).map (Rat.castHom ℝ)

private theorem dg_val (m n : ℕ) (h : m * n ≠ 0) : (dg m n h).1 = !![(m : ℝ), 0; 0, (n : ℝ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg]

private theorem dg_det (m n : ℕ) (h : m * n ≠ 0) : (dg m n h).det.val = (m * n : ℕ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, dg_val]; simp

private theorem dg_fin (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] (m n : ℕ) (h : m * n ≠ 0) :
    (conjGL H (dg m n h)).FiniteIndex := finiteIndex_conjGL_rat H _

private theorem dg_fin' (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] (m n : ℕ) (h : m * n ≠ 0) :
    (conjGL H (dg m n h)⁻¹).FiniteIndex := by
  rw [dg, ← map_inv]; exact finiteIndex_conjGL_rat H _

private theorem dg_slash (m n : ℕ) (h : m * n ≠ 0) (k : ℤ) (F : ℍ → ℂ) (z : ℍ) :
    (F ∣[k] dg m n h) z = ((m * n : ℕ) : ℂ) ^ (k - 1) * (n : ℂ) ^ (-k) * F (ofComplex (m * (z : ℂ) / n)) := by
  have hpos : 0 < (dg m n h).det.val := by rw [dg_det]; exact_mod_cast Nat.pos_of_ne_zero h
  rw [slash_apply, σ, if_pos hpos, dg_det, ← ofComplex_apply (dg m n h • z), coe_smul_of_det_pos hpos]
  simp [num, denom, dg_val]
  ring

private theorem dg_mul (m n : ℕ) (h : m * n ≠ 0) (h' : n * m ≠ 0) (k : ℤ) (F : ℍ → ℂ) :
    (F ∣[k] dg m n h) ∣[k] dg n m h' = ((m * n : ℕ) : ℂ) ^ (k - 2) • F := by
  have e : dg m n h * dg n m h' = dg (m * n) (m * n) (mul_ne_zero h h) := by
    apply Units.ext
    simp [dg_val, mul_comm]
  have h0 : ((m * n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast h
  funext z
  rw [← SlashAction.slash_mul, e, dg_slash, mul_div_cancel_left₀ _ h0, ofComplex_apply, Nat.cast_mul (m * n), mul_zpow,
    ← zpow_add₀ h0, ← zpow_add₀ h0, Pi.smul_apply, smul_eq_mul]
  congr 2
  ring

private theorem T_exp {M k : ℕ} [NeZero M] (hk : 1 ≤ k) {p : ℕ} (hp : p.Prime) (c : ℂ) (f Tf : CuspForm (Gamma1 M) (k : ℤ))
    (h : ∀ n, 1 ≤ n → coef Tf n = coef f (p * n) + c * (p : ℂ) ^ (k - 1) * (if p ∣ n then coef f (n / p) else 0))
    (ha : p * 1 ≠ 0) (hb : 1 * p ≠ 0) (z : ℍ) :
    Tf z = c * (⇑f ∣[(k : ℤ)] dg p 1 ha) z +
      ∑ u ∈ Finset.range p, ((⇑f ∣[(k : ℤ)] dg 1 p hb) ∣[(k : ℤ)] (ModularGroup.T ^ (u : ℤ))) z := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℂ) - 1 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hp.ne_one)
  have h1 : (1 : ℝ) ∈ (Gamma1 M : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  have hsum : ∀ (f : CuspForm (Gamma1 M) (k : ℤ)) (τ : ℍ),
      HasSum (fun m => coef f m • Function.Periodic.qParam 1 τ ^ m) (f τ) := fun f τ =>
    hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f h1) f.holo'
      (ModularFormClass.bdd_at_infty f) τ
  have h0 : ∀ f : CuspForm (Gamma1 M) (k : ℤ), coef f 0 = 0 := fun f => CuspFormClass.qExpansion_coeff_zero f one_pos h1
  have a1 := hasSum_heckeOne 1 hp.pos (hsum f) z
  have a2 := hasSum_heckeOne 2 hp.pos (hsum f) z
  have a3 := a1.add ((a2.sub a1).mul_left ((c * (p : ℂ) ^ (k - 1) - 1) / (p - 1)))
  have e := (hsum Tf z).unique (cast (congrArg (HasSum · _) (funext fun m => ?_)) a3)
  · have e1 : ∀ u : ℕ, ((⇑f ∣[(k : ℤ)] dg 1 p hb) ∣[(k : ℤ)] (ModularGroup.T ^ (u : ℤ))) z =
        (p : ℂ)⁻¹ * f (ofComplex (((z : ℂ) + u) / p)) := fun u => by
      have hd : denom (ModularGroup.T ^ (u : ℤ) : SL(2, ℤ)) z = 1 := by
        rw [ModularGroup.denom_apply, ModularGroup.coe_T_zpow]; simp
      rw [SL_slash_apply, dg_slash, ModularGroup.coe_T_zpow_smul_eq, hd]
      simp [zpow_sub₀ hp0]
      left
      field_simp
    rw [e, dg_slash]
    simp only [e1, heckeOne, ← Finset.mul_sum]
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp
    field_simp
    ring
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [h0]
    · rw [h m hm]
      simp only [smul_eq_mul]
      field_simp
      ring

private theorem B_symm [H.FiniteIndex] : quotInt H (petersson k G F) = conj (quotInt H (petersson k F G)) := by
  haveI : Fintype (SL(2, ℤ) ⧸ H) := Fintype.ofFinite _
  simp only [quotInt, finsum_eq_sum_of_fintype, map_sum, ← integral_conj, ← petersson_symm]

private theorem quotInt_petersson_eq_add_of_hecke_sum [H.FiniteIndex] [H.Normal] {p : ℕ} {c : ℂ} {A B TF : ℍ → ℂ} (hF : Good H k F) (hA : Good H k A)
    (hB : Good H k B) (hT : ∀ u : ℤ, F ∣[k] (ModularGroup.T ^ u) = F)
    (e : ∀ z, TF z = c * A z + ∑ u ∈ Finset.range p, (B ∣[k] (ModularGroup.T ^ (u : ℤ))) z) :
    quotInt H (petersson k F TF) = c * quotInt H (petersson k F A) + p * quotInt H (petersson k F B) := by
  have e1 : petersson k F TF = fun z => petersson k F (c • A) z +
      ∑ u ∈ Finset.range p, petersson k F (B ∣[k] (ModularGroup.T ^ (u : ℤ))) z := by
    funext z
    simp only [petersson, e, Pi.smul_apply, smul_eq_mul, mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
  have hc := fun u : ℕ => hF.cont (hB.slashSL (ModularGroup.T ^ (u : ℤ)))
  have hb := fun u : ℕ => hF.pbd (hB.slashSL (ModularGroup.T ^ (u : ℤ)))
  choose C hC using hb
  obtain ⟨D, hD⟩ := hF.pbd (hA.smul c)
  rw [e1, quotInt_add H (hF.cont (hA.smul c)) hD (continuous_finset_sum _ fun u _ => hc u)
    (C' := ∑ u ∈ Finset.range p, C u) fun z => (norm_sum_le _ _).trans (Finset.sum_le_sum fun u _ => hC u z),
    quotInt_sum H _ hc fun u => ⟨_, hC u⟩, B_smul_right]
  congr 1
  rw [Finset.sum_congr rfl (g := fun _ => quotInt H (petersson k F B)) fun u _ => ?_]
  · simp
  · rw [← B_slashSL (ModularGroup.T ^ (u : ℤ)) hF hB, hT]

private theorem good_cusp {M k : ℕ} [NeZero M] (f : CuspForm (Gamma1 M) (k : ℤ)) (h : H ≤ Gamma1 M) : Good H k f :=
  ⟨f.holo', CuspFormClass.petersson_bounded_left (k : ℤ) (Gamma1 M) f f,
    fun γ hγ => f.slash_action_eq' _ ⟨γ, h hγ, rfl⟩⟩

private theorem dg_swap {M p : ℕ} (hc : p.Coprime M) (ha : p * 1 ≠ 0) (hb : 1 * p ≠ 0) :
    ∃ δ ∈ Gamma0 M, ∃ γ ∈ Gamma1 M, δ 1 1 = p ∧ dg p 1 ha * (δ : GL (Fin 2) ℝ) = (γ : GL (Fin 2) ℝ) * dg 1 p hb := by
  obtain ⟨r, s, h⟩ : IsCoprime (p : ℤ) (M : ℤ) := Nat.isCoprime_iff_coprime.2 hc
  obtain ⟨δ, hδ⟩ : ∃ δ : SL(2, ℤ), δ.1 = !![r, -s; M, p] :=
    ⟨⟨_, by rw [Matrix.det_fin_two_of]; linear_combination h⟩, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ γ : SL(2, ℤ), γ.1 = !![p * r, -s; M, 1] :=
    ⟨⟨_, by rw [Matrix.det_fin_two_of]; linear_combination h⟩, rfl⟩
  refine ⟨δ, by simp [Gamma0_mem, hδ], γ, ?_, by simp [hδ], ?_⟩
  · have := congrArg (Int.cast : ℤ → ZMod M) h
    rw [Gamma1_mem]
    simpa [mul_comm, hγ] using this
  · apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dg_val, Matrix.mul_apply, Fin.sum_univ_two, mul_comm, hδ, hγ]

end UpperTheory.V.Lit.KT

open UpperHalfPlane ModularForm UpperTheory.V.Lit.KT in
theorem UpperTheory.V.Lit.KT.petAdj :
    ∀ (M k : ℕ), 0 < M → 1 ≤ k → ∀ (χ : DirichletCharacter ℂ M) (p : ℕ), p.Prime → ¬ p ∣ M → ∀ f g Tf Tg : CuspForm (Gamma1 M) (k : ℤ), HasChar k χ f → HasChar k χ g →
    (∀ n, 1 ≤ n → coef Tf n = coef f (p * n) + χ (p : ZMod M) * (p : ℂ) ^ (k - 1) * (if p ∣ n then coef f (n / p) else 0)) →
    (∀ n, 1 ≤ n → coef Tg n = coef g (p * n) + χ (p : ZMod M) * (p : ℂ) ^ (k - 1) * (if p ∣ n then coef g (n / p) else 0)) →
    pet M k f Tg = χ (p : ZMod M) * pet M k Tf g := by
  intro M k hM hk χ p hp hpM f g Tf Tg _ hg hTf hTg
  haveI : NeZero M := ⟨hM.ne'⟩
  have hc : p.Coprime M := (Nat.Prime.coprime_iff_not_dvd hp).2 hpM
  have ha : p * 1 ≠ 0 := by simpa using hp.ne_zero
  have hb : 1 * p ≠ 0 := by simpa using hp.ne_zero
  haveI := dg_fin (Gamma1 M) p 1 ha
  haveI := dg_fin (Gamma1 M) 1 p hb
  set H := (Gamma1 M ⊓ conjGL (Gamma1 M) (dg p 1 ha) ⊓ conjGL (Gamma1 M) (dg 1 p hb)).normalCore with hH
  have hle := (Gamma1 M ⊓ conjGL (Gamma1 M) (dg p 1 ha) ⊓ conjGL (Gamma1 M) (dg 1 p hb)).normalCore_le
  rw [← hH, le_inf_iff, le_inf_iff] at hle
  obtain ⟨⟨l1, la⟩, lb⟩ := hle
  have G0 := fun f : CuspForm (Gamma1 M) (k : ℤ) => good_cusp f l1
  have G1 := fun f : CuspForm (Gamma1 M) (k : ℤ) => good_cusp f le_rfl
  have Ga := fun f : CuspForm (Gamma1 M) (k : ℤ) => (G1 f).slash _ la
  have Gb := fun f : CuspForm (Gamma1 M) (k : ℤ) => (G1 f).slash _ lb
  have hT : ∀ (f : CuspForm (Gamma1 M) (k : ℤ)) (u : ℤ), ⇑f ∣[(k : ℤ)] (ModularGroup.T ^ u) = f := fun f u =>
    (G1 f).inv _ (by rw [Gamma1_mem]; simp [ModularGroup.coe_T_zpow])
  have tow : ∀ f g : CuspForm (Gamma1 M) (k : ℤ),
      quotInt H (petersson k f g) = (H.relIndex (Gamma1 M) : ℂ) * pet M k f g := fun f g =>
    quotInt_tower l1 _ ((G1 f).pinv (G1 g))
  have e1 := quotInt_petersson_eq_add_of_hecke_sum (G0 f) (Ga g) (Gb g) (hT f) (T_exp hk hp _ g Tg hTg ha hb)
  have e2 := congrArg conj (quotInt_petersson_eq_add_of_hecke_sum (G0 g) (Ga f) (Gb f) (hT g) (T_exp hk hp _ f Tf hTf ha hb))
  rw [map_add, map_mul, map_mul, ← B_symm, ← B_symm, ← B_symm, Complex.conj_natCast] at e2
  have e3 := B_adj hp.pos (by rw [dg_det, one_mul]) (dg_fin H 1 p hb) (dg_fin' H 1 p hb) (G0 f) (G0 g) (Ga f) (Gb g)
    (by rw [dg_mul, mul_one])
  have e4 := B_adj hp.pos (by rw [dg_det, mul_one]) (dg_fin H p 1 ha) (dg_fin' H p 1 ha) (G0 f) (G0 g) (Gb f) (Ga g)
    (by rw [dg_mul, one_mul])
  obtain ⟨δ, hδ, γ, hγ, h11, hm⟩ := dg_swap hc ha hb
  have e5 := B_slashSL δ (Ga f) (G0 g)
  rw [hg δ hδ, h11, Int.cast_natCast, B_smul_right, SL_slash, ← SlashAction.slash_mul, hm, SlashAction.slash_mul,
    ← SL_slash, (G1 f).inv γ hγ] at e5
  have e6 : χ (p : ZMod M) * conj (χ (p : ZMod M)) = 1 := by
    have := χ.unit_norm_eq_one (ZMod.unitOfCoprime p hc)
    rw [ZMod.coe_unitOfCoprime] at this
    rw [Complex.mul_conj', this]; simp
  refine mul_left_cancel₀ (a := (H.relIndex (Gamma1 M) : ℂ)) (Nat.cast_ne_zero.2 Subgroup.FiniteIndex.index_ne_zero) ?_
  rw [mul_left_comm, ← tow, ← tow, e1, e2, e3, e4, ← e5]
  linear_combination (-(χ (p : ZMod M)) * quotInt H (petersson k (⇑f ∣[(k : ℤ)] dg 1 p hb) g)) * e6
