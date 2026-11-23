import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondOperatorOfMatrixCuspFormGamma1InterGamma0Statement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeTOperatorExplicitCuspFormStatement
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.CocycleCoefficients.PetAdjQuot

noncomputable section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold ComplexConjugate

namespace GlobalTheory.Hk.PetAdjT

open UpperTheory.V.Lit.KT (quotInt quotInt_tower quotInt_conj finiteIndex_conjGL_rat quotInt_add quotInt_sum quotInt_mul)

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

private theorem Good.mono {K : Subgroup SL(2, ℤ)} (hF : Good K k F) (h : H ≤ K) : Good H k F :=
  ⟨hF.hol, hF.bd, fun γ hγ => hF.inv γ (h hγ)⟩

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

private theorem isDia_N {N l : ℕ} {d : ℤ} {s : SL(2, ℤ)} (h : IsDia N l d s) :
    ((s 1 0 : ℤ) : ZMod N) = 0 := by
  have := congrArg (ZMod.castHom (dvd_mul_right N l) (ZMod N)) h.1
  simpa using this

private theorem isDia_l {N l : ℕ} {d : ℤ} {s : SL(2, ℤ)} (h : IsDia N l d s) :
    ((s 1 0 : ℤ) : ZMod l) = 0 := by
  have := congrArg (ZMod.castHom (dvd_mul_left l N) (ZMod l)) h.1
  simpa using this

private theorem det_SL (s : SL(2, ℤ)) : s 0 0 * s 1 1 - s 0 1 * s 1 0 = 1 := by
  have := s.2
  rw [Matrix.det_fin_two] at this
  exact this

private theorem isDia_mul_inv_mem {N l : ℕ} {d : ℤ} {s t : SL(2, ℤ)} (hs : IsDia N l d s) (ht : IsDia N l d t) :
    s * t⁻¹ ∈ lev N l := by
  have ds := det_SL s
  have dt := det_SL t
  have cs := isDia_N hs
  have ct := isDia_N ht
  have e1 := hs.2
  have e2 := ht.2
  have ls := isDia_l hs
  have lt := isDia_l ht
  have e00 : (s * t⁻¹) 0 0 = s 0 0 * t 1 1 - s 0 1 * t 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two] <;> ring
  have e11 : (s * t⁻¹) 1 1 = - s 1 0 * t 0 1 + s 1 1 * t 0 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two] <;> ring
  have e10 : (s * t⁻¹) 1 0 = s 1 0 * t 1 1 - s 1 1 * t 1 0 := by
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two] <;> ring
  have ds' := congrArg (Int.cast : ℤ → ZMod N) ds
  have dt' := congrArg (Int.cast : ℤ → ZMod N) dt
  push_cast at ds' dt'
  refine ⟨(Gamma1_mem _ _).2 ⟨?_, ?_, ?_⟩, Gamma0_mem.2 ?_⟩
  · rw [e00]; push_cast
    linear_combination ds' + ((s 0 0 : ℤ) : ZMod N) * (e2 - e1) + ((s 0 1 : ℤ) : ZMod N) * cs - ((s 0 1 : ℤ) : ZMod N) * ct
  · rw [e11]; push_cast
    linear_combination dt' + ((t 0 0 : ℤ) : ZMod N) * (e1 - e2) - ((t 0 1 : ℤ) : ZMod N) * cs + ((t 0 1 : ℤ) : ZMod N) * ct
  · rw [e10]; push_cast
    linear_combination ((t 1 1 : ℤ) : ZMod N) * cs - ((s 1 1 : ℤ) : ZMod N) * ct
  · rw [e10]; push_cast
    linear_combination ((t 1 1 : ℤ) : ZMod l) * ls - ((s 1 1 : ℤ) : ZMod l) * lt

private theorem slash_isDia {N l : ℕ} {d : ℤ} {s t : SL(2, ℤ)} (hs : IsDia N l d s) (ht : IsDia N l d t)
    {k : ℤ} {F : ℍ → ℂ} (hF : ∀ γ ∈ lev N l, F ∣[k] γ = F) : F ∣[k] s = F ∣[k] t := by
  have e : s = (s * t⁻¹) * t := by group
  rw [e, SlashAction.slash_mul, hF _ (isDia_mul_inv_mem hs ht)]

private theorem isDia_one_mem {N l : ℕ} {s : SL(2, ℤ)} (hs : IsDia N l 1 s) : s ∈ lev N l := by
  have h1 : IsDia N l 1 (1 : SL(2, ℤ)) := ⟨by simp, by simp⟩
  simpa using isDia_mul_inv_mem hs h1

private theorem isDia_mul {N l : ℕ} {d e : ℤ} {s t : SL(2, ℤ)} (hs : IsDia N l d s) (ht : IsDia N l e t) :
    IsDia N l (d * e) (s * t) := by
  have cs := isDia_N hs
  have e10 : (s * t) 1 0 = s 1 0 * t 0 0 + s 1 1 * t 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (s * t) 1 1 = s 1 0 * t 0 1 + s 1 1 * t 1 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hs1 := hs.1
  have ht1 := ht.1
  have hs2 := hs.2
  have ht2 := ht.2
  refine ⟨?_, ?_⟩
  · rw [e10]; push_cast
    linear_combination ((t 0 0 : ℤ) : ZMod (N * l)) * hs1 + ((s 1 1 : ℤ) : ZMod (N * l)) * ht1
  · rw [e11]; push_cast
    linear_combination ((t 0 1 : ℤ) : ZMod N) * cs + ((t 1 1 : ℤ) : ZMod N) * hs2 + (d : ZMod N) * ht2

private theorem isDia_congr {N l : ℕ} {d e : ℤ} {s : SL(2, ℤ)} (hs : IsDia N l d s) (h : (d : ZMod N) = e) :
    IsDia N l e s := ⟨hs.1, hs.2.trans h⟩

private theorem levFin (N l : ℕ) [NeZero N] [NeZero l] : (lev N l).FiniteIndex := by
  unfold lev; infer_instance

private theorem T_mem {N l : ℕ} (u : ℤ) : ModularGroup.T ^ u ∈ lev N l :=
  Subgroup.mem_inf.2 ⟨(Gamma1_mem _ _).2 (by simp [ModularGroup.coe_T_zpow]), Gamma0_mem.2 (by simp [ModularGroup.coe_T_zpow])⟩

private theorem good_cusp {N l : ℕ} [NeZero N] [NeZero l] {k : ℤ} (f : CuspForm (lev N l) k)
    {H : Subgroup SL(2, ℤ)} (h : H ≤ lev N l) : Good H k f :=
  haveI := levFin N l
  ⟨f.holo', CuspFormClass.petersson_bounded_left k (lev N l) f f,
    fun γ hγ => f.slash_action_eq' _ ⟨γ, h hγ, rfl⟩⟩

private theorem swap (q : ℕ) (hq : q ≠ 0) (x y z w : ℤ) (h : q * x * w - y * z = 1) :
    ∃ X Y : SL(2, ℤ), X 1 0 = z ∧ X 1 1 = w ∧ Y 1 0 = z ∧ Y 1 1 = q * w ∧
      dg q 1 (by simpa using hq) * (Y : GL (Fin 2) ℝ) = (X : GL (Fin 2) ℝ) * dg 1 q (by simpa using hq) := by
  obtain ⟨X, hX⟩ : ∃ X : SL(2, ℤ), X.1 = !![q * x, y; z, w] :=
    ⟨⟨_, by rw [Matrix.det_fin_two_of]; linear_combination h⟩, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : SL(2, ℤ), Y.1 = !![x, y; z, q * w] :=
    ⟨⟨_, by rw [Matrix.det_fin_two_of]; linear_combination h⟩, rfl⟩
  refine ⟨X, Y, by simp [hX], by simp [hX], by simp [hY], by simp [hY], ?_⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg_val, Matrix.mul_apply, Fin.sum_univ_two, mul_comm, hX, hY]

private theorem slash_swap {k : ℤ} (F : ℍ → ℂ) {α β : GL (Fin 2) ℝ} {X Y : SL(2, ℤ)}
    (h : α * (Y : GL (Fin 2) ℝ) = (X : GL (Fin 2) ℝ) * β) : (F ∣[k] α) ∣[k] Y = (F ∣[k] X) ∣[k] β := by
  rw [SL_slash, ← SlashAction.slash_mul, h, SlashAction.slash_mul, ← SL_slash]

private theorem heckeT_eq (q : ℕ) (hq : q ≠ 0) (k : ℤ) (s : SL(2, ℤ)) (F : ℍ → ℂ) (z : ℍ) :
    heckeT k q s F z = 1 * ((F ∣[k] s) ∣[k] dg q 1 (by simpa using hq)) z +
      ∑ u ∈ Finset.range q, ((F ∣[k] dg 1 q (by simpa using hq)) ∣[k] (ModularGroup.T ^ (u : ℤ))) z := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have e1 : ∀ u : ℕ, ((F ∣[k] dg 1 q (by simpa using hq)) ∣[k] (ModularGroup.T ^ (u : ℤ))) z =
      (q : ℂ)⁻¹ * F (ofComplex (((z : ℂ) + u) / q)) := fun u => by
    have hd : denom (ModularGroup.T ^ (u : ℤ) : SL(2, ℤ)) z = 1 := by
      rw [ModularGroup.denom_apply, ModularGroup.coe_T_zpow]; simp
    rw [SL_slash_apply, dg_slash, ModularGroup.coe_T_zpow_smul_eq, hd]
    simp [zpow_sub₀ hq0, zpow_neg]
    left
    field_simp
  rw [heckeT, Pi.add_apply, Pi.smul_apply, uOp, vOp, dg_slash]
  simp only [e1, ← Finset.mul_sum]
  simp
  ring

end GlobalTheory.Hk.PetAdjT

namespace GlobalTheory.Hk

open UpperTheory.V.Lit.KT (quotInt quotInt_tower)
open PetAdjT

theorem pet_heckeT_adj : ∀ (N l q : ℕ) (k : ℤ) (σ σ' : SL(2, ℤ)), 0 < N → 0 < l → q.Prime → ¬ q ∣ N * l →
    IsDia N l q σ → IsDia N l q σ' → ∀ f g : CuspForm (lev N l) k,
    pet (lev N l) k (heckeT k q σ ⇑f) (dia k σ' ⇑g) = pet (lev N l) k ⇑f (heckeT k q σ ⇑g) := by
  intro N l q k s s' hN hl hq hqNl hs hs' f g
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  have hq0 : q ≠ 0 := hq.ne_zero
  have ha : q * 1 ≠ 0 := by simpa using hq0
  have hb : 1 * q ≠ 0 := by simpa using hq0
  haveI : (lev N l).FiniteIndex := levFin N l
  haveI := dg_fin (lev N l) q 1 ha
  haveI := dg_fin (lev N l) 1 q hb
  set H := (lev N l ⊓ conjGL (lev N l) (dg q 1 ha) ⊓ conjGL (lev N l) (dg 1 q hb)).normalCore with hH
  have hle := (lev N l ⊓ conjGL (lev N l) (dg q 1 ha) ⊓ conjGL (lev N l) (dg 1 q hb)).normalCore_le
  rw [← hH, le_inf_iff, le_inf_iff] at hle
  obtain ⟨⟨l1, la⟩, lb⟩ := hle
  obtain ⟨fs, hfs⟩ := GlobalTheory.T.diamondOperatorOfMatrix_cuspForm_gamma1InterGamma0 N l k q s hN hs f
  obtain ⟨gs, hgs⟩ := GlobalTheory.T.diamondOperatorOfMatrix_cuspForm_gamma1InterGamma0 N l k q s hN hs g
  obtain ⟨gs', hgs'⟩ := GlobalTheory.T.diamondOperatorOfMatrix_cuspForm_gamma1InterGamma0 N l k q s' hN hs' g
  obtain ⟨Tf, hTf⟩ := GlobalTheory.T.heckeTOperatorExplicit_cuspForm N l q k s hN hq hqNl hs f
  obtain ⟨Tg, hTg⟩ := GlobalTheory.T.heckeTOperatorExplicit_cuspForm N l q k s hN hq hqNl hs g
  have G1 := fun f : CuspForm (lev N l) k => good_cusp f (le_refl (lev N l))
  have G0 := fun f : CuspForm (lev N l) k => good_cusp f l1
  have Ga := fun f : CuspForm (lev N l) k => (G1 f).slash _ la
  have Gb := fun f : CuspForm (lev N l) k => (G1 f).slash _ lb
  have hT : ∀ (f : CuspForm (lev N l) k) (u : ℤ), ⇑f ∣[k] (ModularGroup.T ^ u) = f := fun f u =>
    (G1 f).inv _ (T_mem u)
  have tow : ∀ f g : CuspForm (lev N l) k,
      quotInt H (petersson k f g) = (H.relIndex (lev N l) : ℂ) * pet (lev N l) k f g := fun f g =>
    quotInt_tower l1 _ ((G1 f).pinv (G1 g))
  have hfs' : ⇑f ∣[k] s = ⇑fs := hfs.symm
  have hgs1 : ⇑g ∣[k] s = ⇑gs := hgs.symm
  have hgs2 : ⇑g ∣[k] s' = ⇑gs' := hgs'.symm
  have eTf : ∀ z, (Tf : ℍ → ℂ) z = 1 * ((fs : ℍ → ℂ) ∣[k] dg q 1 ha) z +
      ∑ u ∈ Finset.range q, (((f : ℍ → ℂ) ∣[k] dg 1 q hb) ∣[k] (ModularGroup.T ^ (u : ℤ))) z := by
    intro z; rw [hTf, heckeT_eq q hq0, hfs']
  have eTg : ∀ z, (Tg : ℍ → ℂ) z = 1 * ((gs : ℍ → ℂ) ∣[k] dg q 1 ha) z +
      ∑ u ∈ Finset.range q, (((g : ℍ → ℂ) ∣[k] dg 1 q hb) ∣[k] (ModularGroup.T ^ (u : ℤ))) z := by
    intro z; rw [hTg, heckeT_eq q hq0, hgs1]
  have e1 := quotInt_petersson_eq_add_of_hecke_sum (G0 gs') (Ga fs) (Gb f) (hT gs') eTf
  have e2 := quotInt_petersson_eq_add_of_hecke_sum (G0 f) (Ga gs) (Gb g) (hT f) eTg
  have e1' := congrArg conj e1
  rw [map_add, map_mul, map_mul, ← B_symm, ← B_symm, ← B_symm, Complex.conj_natCast, map_one] at e1'
  have a1 := B_adj (H := H) hq.pos (by rw [dg_det, one_mul]) (dg_fin H 1 q hb) (dg_fin' H 1 q hb) (G0 f) (G0 g)
    (Ga f) (Gb g) (by rw [dg_mul, mul_one])
  have a2 := B_adj (H := H) hq.pos (by rw [dg_det, mul_one]) (dg_fin H q 1 ha) (dg_fin' H q 1 ha) (G0 f) (G0 gs)
    (Gb f) (Ga gs) (by rw [dg_mul, one_mul])
  obtain ⟨r, t, hrt⟩ : IsCoprime (q : ℤ) ((N * l : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hq).2 hqNl)
  obtain ⟨X1, Y1, x10, x11, y10, y11, hm1⟩ := swap q hq0 r (-t) ((N * l : ℕ) : ℤ) 1 (by linear_combination hrt)
  obtain ⟨X2, Y2, x20, x21, y20, y21, hm2⟩ := swap q hq0 1 (-t) ((N * l : ℕ) : ℤ) r (by linear_combination hrt)
  have hrt' : (q : ZMod N) * (r : ZMod N) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod N) hrt
    push_cast at this
    rw [ZMod.natCast_self] at this
    linear_combination this
  have dX1 : IsDia N l 1 X1 := ⟨by rw [x10, Int.cast_natCast, ZMod.natCast_self], by rw [x11]⟩
  have dY1 : IsDia N l q Y1 := ⟨by rw [y10, Int.cast_natCast, ZMod.natCast_self], by rw [y11, mul_one]⟩
  have dX2 : IsDia N l r X2 := ⟨by rw [x20, Int.cast_natCast, ZMod.natCast_self], by rw [x21]⟩
  have dY2 : IsDia N l 1 Y2 := ⟨by rw [y20, Int.cast_natCast, ZMod.natCast_self], by rw [y21]; push_cast; exact hrt'⟩
  have d1 : IsDia N l 1 (1 : SL(2, ℤ)) := ⟨by simp, by simp⟩
  have b1 := B_slashSL Y1 (Ga f) (G0 g)
  rw [slash_swap _ hm1, (G1 f).inv _ (isDia_one_mem dX1), slash_isDia dY1 hs' (G1 g).inv, hgs2] at b1
  have b2 := B_slashSL Y2 (Ga fs) (G0 gs')
  rw [slash_swap _ hm2, ← hfs', ← SlashAction.slash_mul,
    slash_isDia (isDia_congr (isDia_mul hs dX2) (by push_cast; exact hrt')) d1 (G1 f).inv, SlashAction.slash_one,
    ← hgs2, ← SlashAction.slash_mul, slash_isDia (isDia_congr (isDia_mul hs' dY2) (by simp)) hs (G1 g).inv,
    hgs1, hfs', hgs2] at b2
  rw [← hTf, show dia k s' ⇑g = ⇑gs' from hgs2, ← hTg]
  refine mul_left_cancel₀ (a := (H.relIndex (lev N l) : ℂ)) (Nat.cast_ne_zero.2 Subgroup.FiniteIndex.index_ne_zero) ?_
  rw [← tow, ← tow, e1', e2, a1, a2, ← b1, ← b2]

end GlobalTheory.Hk
