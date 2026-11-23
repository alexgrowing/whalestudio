import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagGrassSteps
import GroundTheory.HeightsAndTheta.Heights.Intersections.PfAtZero
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem isSmoothHerm_fsHerm {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (a : K → ℤ) :
    IsSmoothHerm (fsHerm ι a) := by
  unfold IsSmoothHerm
  have hfun : (fsHerm ι a).h = fun z => ∏ k, (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ ((a k : ℝ) / 2) := rfl
  rw [hfun]
  refine contDiffOn_prod fun k _ => ContDiffOn.rpow_const_of_ne ?_ fun z hz => ?_
  · exact (ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp
      (contDiff_apply ℝ ℂ (⟨k, i⟩ : Σ k, ι k))).contDiffOn
  · obtain ⟨i, hi⟩ := hz k
    exact (Finset.sum_pos' (fun j _ => sq_nonneg ‖z ⟨k, j⟩‖)
      ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩).ne'

theorem plToIncr_injective {j m N s : ℕ} (hs : s = j) (hN : j + m = N) :
    Function.Injective (plToIncr (m := m) hs hN) := by
  intro I I' h
  have h1 : ∀ a, I.1.orderEmbOfFin I.2 a = I'.1.orderEmbOfFin I'.2 a := by
    intro a
    have := congrArg (fun A : PlueckerData.Incr s N => A.1 (Fin.cast hs.symm a)) h
    simp only [plToIncr, Fin.cast_cast, Fin.cast_eq_self] at this
    exact Fin.cast_injective hN this
  apply Subtype.ext
  apply Finset.coe_injective
  rw [← Finset.range_orderEmbOfFin I.1 I.2, ← Finset.range_orderEmbOfFin I'.1 I'.2]
  exact congrArg Set.range (funext h1)

theorem plToIncr_surjective {j m N s : ℕ} (hs : s = j) (hN : j + m = N) :
    Function.Surjective (plToIncr (m := m) hs hN) := by
  intro A
  let g : Fin j → Fin (j + m) := fun a => Fin.cast hN.symm (A.1 (Fin.cast hs.symm a))
  have hg : StrictMono g := fun a b hab => by
    simp only [g, Fin.lt_def, Fin.val_cast]
    exact A.2 (by rw [Fin.lt_def] at hab ⊢; simpa using hab)
  have hcard : (Finset.univ.map ⟨g, hg.injective⟩).card = j := by simp
  refine ⟨⟨_, hcard⟩, ?_⟩
  have hu : g = (Finset.univ.map ⟨g, hg.injective⟩).orderEmbOfFin hcard :=
    Finset.orderEmbOfFin_unique hcard (fun x => by simp) hg
  apply Subtype.ext
  funext a
  show Fin.cast hN ((Finset.univ.map ⟨g, hg.injective⟩).orderEmbOfFin hcard (Fin.cast hs a)) = A.1 a
  rw [← hu]
  simp [g]

def plIncrEquiv {j m N s : ℕ} (hs : s = j) (hN : j + m = N) : PlIdx j m ≃ PlueckerData.Incr s N :=
  Equiv.ofBijective _ ⟨plToIncr_injective hs hN, plToIncr_surjective hs hN⟩

section Proj

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

omit [DecidableEq Ψ] in
theorem isBlockMap_grFl (hj : 1 ≤ j) (hjN : j ≤ N - 1) :
    IsBlockMap (grFlKappa Ψ N j hj hjN) (grFlV Ψ N j hj hjN) := by
  have hκ : Function.Injective (grFlKappa Ψ N j hj hjN) := fun t t' h =>
    (Fintype.equivFin Ψ).symm.injective (congrArg Prod.fst h)
  refine ⟨hκ, ?_, fun _ => rfl, ?_⟩
  · rintro ⟨t, I⟩ ⟨t', I'⟩ h
    simp only [grFlV, Sigma.mk.inj_iff] at h
    obtain ⟨h1, h2⟩ := h
    obtain rfl := hκ h1
    obtain rfl := plToIncr_injective _ _ (eq_of_heq h2)
    rfl
  · rintro ⟨q, A⟩ ⟨t, rfl⟩
    obtain ⟨I, hI⟩ := plToIncr_surjective (m := N - j) (N := N)
      (s := ((grFlKappa Ψ N j hj hjN t).2 : ℕ) + 1) (by show j - 1 + 1 = j; omega) (by omega) A
    exact ⟨⟨t, I⟩, congrArg (Sigma.mk _) hI⟩

theorem linDeg_muForm_apply (τ : Ψ) (i : Fin (N - 1)) :
    linDeg Ψ N (muForm Ψ N j) (τ, i) = if (i : ℕ) + 1 = j then -1 else 0 := by
  have hi := i.isLt
  unfold linDeg
  rw [Fintype.sum_prod_type, Fintype.sum_eq_single τ (fun τ' hτ' => by
    refine Finset.sum_eq_zero fun a _ => ?_
    simp [xDeg, Ne.symm hτ'])]
  simp only [xDeg, if_true, mul_sub]
  rw [Finset.sum_sub_distrib]
  have h1 : ∑ a : Fin N, muForm Ψ N j (τ, a) * (if (i : ℕ) = a then 1 else 0) =
      if (i : ℕ) < j then 0 else 1 := by
    rw [Fintype.sum_eq_single ⟨i, by omega⟩]
    · simp [muForm]
    · intro a ha
      have : (i : ℕ) ≠ a := fun h => ha (Fin.ext h.symm)
      simp [this]
  have h2 : ∑ a : Fin N, muForm Ψ N j (τ, a) * (if (i : ℕ) + 1 = a then 1 else 0) =
      if (i : ℕ) + 1 < j then 0 else 1 := by
    rw [Fintype.sum_eq_single ⟨(i : ℕ) + 1, by omega⟩]
    · simp [muForm]
    · intro a ha
      have : (i : ℕ) + 1 ≠ a := fun h => ha (Fin.ext h.symm)
      simp [this]
  rw [h1, h2]
  split_ifs <;> omega

theorem linDeg_muForm (hj : 1 ≤ j) (hjN : j ≤ N - 1) :
    linDeg Ψ N (muForm Ψ N j) = pullDeg (grFlKappa Ψ N j hj hjN) (fun _ => -1) := by
  have hκ : Function.Injective (grFlKappa Ψ N j hj hjN) := (isBlockMap_grFl hj hjN).1
  funext ⟨τ, i⟩
  rw [linDeg_muForm_apply]
  unfold pullDeg
  by_cases h : (i : ℕ) + 1 = j
  · have hq : (τ, i) = grFlKappa Ψ N j hj hjN (Fintype.equivFin Ψ τ) := by
      simp only [grFlKappa, Equiv.symm_apply_apply, Prod.mk.injEq, true_and]
      exact Fin.ext (by simp; omega)
    rw [if_pos h, hq, hκ.extend_apply]
  · rw [if_neg h, Function.extend_apply']
    · rfl
    · rintro ⟨t, ht⟩
      apply h
      have := congrArg (fun q : FlBlock Ψ N => (q.2 : ℕ)) ht
      simp only [grFlKappa] at this
      omega

theorem isPullHerm_mu (hj : 1 ≤ j) (hjN : j ≤ N - 1) :
    IsPullHerm (grFlKappa Ψ N j hj hjN) (grFlV Ψ N j hj hjN)
      (fsHerm (plBlocks (Fintype.card Ψ) j (N - j)) (fun _ => -1)) (linLine Ψ N (muForm Ψ N j)) := by
  refine ⟨linDeg_muForm hj hjN, fun z => ?_⟩
  show refNorm (linDeg Ψ N (muForm Ψ N j)) z = refNorm (fun _ => (-1 : ℤ)) (fun p => z (grFlV Ψ N j hj hjN p))
  unfold refNorm
  rw [Fintype.prod_prod_type]
  refine (Equiv.prod_comp (Fintype.equivFin Ψ).symm _).symm.trans (Finset.prod_congr rfl fun t _ => ?_)
  have hlt : j - 1 < N - 1 := by omega
  rw [Fintype.prod_eq_single ⟨j - 1, hlt⟩ (fun i hi => by
    rw [linDeg_muForm_apply, if_neg (fun h => hi (Fin.ext (by simp; omega)))]
    simp)]
  rw [linDeg_muForm_apply, if_pos (by simp; omega)]
  congr 1
  exact (Equiv.sum_comp (plIncrEquiv (m := N - j) (N := N) (s := j - 1 + 1) (by omega) (by omega))
    (fun A => ‖z ⟨((Fintype.equivFin Ψ).symm t, ⟨j - 1, hlt⟩), A⟩‖ ^ 2)).symm

end Proj

section Forms

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ)

omit [DecidableEq Ψ] in
theorem linForm_muForm : linForm Ψ N (muForm Ψ N j) = muPoly Ψ N j := by
  unfold linForm muPoly muForm
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs <;> simp

theorem linForm_vandForm (t : VandPair Ψ N j) :
    linForm Ψ N (vandForm Ψ N j t) = X (t.1.1, t.1.2.1) - X (t.1.1, t.1.2.2) := by
  simp only [linForm, vandForm, Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero, sub_smul,
    Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

def vandPairEquiv :
    Ψ × {ab : Fin N × Fin N // ab.1 < ab.2 ∧ ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j)} ≃ VandPair Ψ N j where
  toFun x := ⟨(x.1, x.2.1), x.2.2⟩
  invFun t := (t.1.1, ⟨t.1.2, t.2⟩)
  left_inv _ := rfl
  right_inv _ := rfl

theorem prod_vandForm :
    ∏ i : Fin (vandCount Ψ N j), linForm Ψ N (vandForm Ψ N j ((Fintype.equivFin (VandPair Ψ N j)).symm i)) =
      vandBlocks Ψ N j := by
  refine (Equiv.prod_comp (Fintype.equivFin (VandPair Ψ N j)).symm
    (fun t => linForm Ψ N (vandForm Ψ N j t))).trans ?_
  have hB : ∏ x : Ψ × {ab : Fin N × Fin N // ab.1 < ab.2 ∧ ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j)},
      (X (x.1, x.2.1.1) - X (x.1, x.2.1.2) : RootPoly Ψ N) =
      ∏ t : VandPair Ψ N j, linForm Ψ N (vandForm Ψ N j t) :=
    Fintype.prod_equiv (vandPairEquiv Ψ N j) _ (fun t => linForm Ψ N (vandForm Ψ N j t))
      (fun x => (linForm_vandForm Ψ N j (vandPairEquiv Ψ N j x)).symm)
  rw [← hB]
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Finset.prod_subtype (p := fun ab : Fin N × Fin N => ab.1 < ab.2 ∧ ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j))
    (Finset.univ.filter (fun ab : Fin N × Fin N => ab.1 < ab.2 ∧ ((ab.1 : ℕ) < j ↔ (ab.2 : ℕ) < j)))
    (fun ab => by simp) (fun ab => (X (τ, ab.1) - X (τ, ab.2) : RootPoly Ψ N))]

def faForms : Fin (dimN Ψ N j + 1 + vandCount Ψ N j) → Ψ × Fin N → ℤ :=
  Fin.append (fun _ => muForm Ψ N j) (fun i => vandForm Ψ N j ((Fintype.equivFin (VandPair Ψ N j)).symm i))

theorem FA_eq_prod (cf : ℚ) : FA Ψ N j cf = C cf * ∏ i, linForm Ψ N (faForms Ψ N j i) := by
  rw [Fin.prod_univ_add]
  simp only [faForms, Fin.append_left, Fin.append_right, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    linForm_muForm, prod_vandForm]
  unfold FA fib
  ring

theorem linLine_faForms :
    (fun i => linLine Ψ N (faForms Ψ N j i)) =
      Fin.append (fun _ : Fin (dimN Ψ N j + 1) => linLine Ψ N (muForm Ψ N j)) (vandLine Ψ N j) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [faForms]
  · simp [faForms, vandLine]

theorem flagInt_C_mul (c : ℚ) (P : RootPoly Ψ N) : flagInt Ψ N (C c * P) = c * flagInt Ψ N P := by
  have h : antisym Ψ N (C c * P) = C c * antisym Ψ N P := by
    unfold antisym
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [map_mul, rename_C, mul_smul_comm]
  unfold flagInt
  rw [h, coeff_C_mul]

end Forms

theorem FlagGrassPush.proof (hAI3 : Inter.PushforwardArithIntersection.Statement) (hStep : Inter.PFStep.Statement)
    (hGr : GroundTheory.Heights₂.Heights.GrassArithVar.Statement) (hAr : FlagArithVar.Statement)
    (hIm : FlagImageGrass.Statement) (hCnt : VandCount.Statement) (hProd : HFlProdLinear.Statement)
    (hInv : FsInvPow.Statement) (hFib : FlagGrassFibreDeg.Statement) (hDeg : GrassDegFlagInt.Statement) :
    FlagGrassPush.Statement := by
  intro II Ψ _ _ _ N j cf hII hN hj hjN
  have hcnt : dimN Ψ N j + vandCount Ψ N j = dimFl Ψ N := hCnt Ψ N j (by omega)
  have hArFl : IsArithVar (PFl Ψ N) (dimN Ψ N j + 1 + vandCount Ψ N j) := by
    have h := hAr Ψ N hN
    rwa [show dimFl Ψ N + 1 = dimN Ψ N j + 1 + vandCount Ψ N j by omega] at h
  have hArGr : IsArithVar (grassIdeal (Fintype.card Ψ) j (N - j)) (dimN Ψ N j + 1) :=
    hGr (Fintype.card Ψ) j (N - j) Fintype.card_pos
  have hArIm : IsArithVar (imageZ (grFlV Ψ N j hj hjN) (PFl Ψ N)) (dimN Ψ N j + 1) := by
    rw [hIm Ψ N j hj hjN]
    exact hArGr
  obtain ⟨G, J, hJ, hJval⟩ := hFib Ψ N j hj hjN
  have hPF := Inter.PushforwardProjLineFlag.proof hAI3 hStep II hII (Fin (Fintype.card Ψ)) (plBlocks (Fintype.card Ψ) j (N - j))
    (FlBlock Ψ N) (FlIdx Ψ N) (grFlKappa Ψ N j hj hjN) (grFlV Ψ N j hj hjN) (PFl Ψ N) (dimN Ψ N j + 1)
    (vandCount Ψ N j) G J (fun _ => fsHerm (plBlocks (Fintype.card Ψ) j (N - j)) (fun _ => -1))
    (fun _ => linLine Ψ N (muForm Ψ N j)) (vandLine Ψ N j) (isBlockMap_grFl hj hjN) hArFl hArIm hJ
    (fun _ => isSmoothHerm_fsHerm _) (fun _ => isPullHerm_mu hj hjN) (fun _ => isSmoothHerm_fsHerm _)
  rw [hIm Ψ N j hj hjN] at hPF
  have hprod := hProd II Ψ N (dimN Ψ N j + 1 + vandCount Ψ N j) cf (faForms Ψ N j) hII hN (by omega)
  rw [linLine_faForms Ψ N j, hPF, ← FA_eq_prod] at hprod
  have hinv := hInv II (Fin (Fintype.card Ψ)) (plBlocks (Fintype.card Ψ) j (N - j))
    (grassIdeal (Fintype.card Ψ) j (N - j)) (dimN Ψ N j + 1) hII hArGr
  have hJr : ((J (fibreIdeal (grFlKappa Ψ N j hj hjN) G) (vandCount Ψ N j)
      (fun i => fibreDeg (grFlKappa Ψ N j hj hjN) (vandLine Ψ N j i).a) : ℤ) : ℝ) = (fdeg Ψ N j : ℝ) := by
    rw [← hJval]
    push_cast
    rfl
  have hJint : (Jint Ψ N j cf : ℝ) =
      (cf : ℝ) * ((flagInt Ψ N (muPoly Ψ N j ^ dimN Ψ N j * vandBlocks Ψ N j) : ℚ) : ℝ) := by
    unfold Jint fib
    rw [show muPoly Ψ N j ^ dimN Ψ N j * (C cf * vandBlocks Ψ N j) =
      C cf * (muPoly Ψ N j ^ dimN Ψ N j * vandBlocks Ψ N j) by ring, flagInt_C_mul]
    push_cast
    rfl
  rw [hprod, hinv, hJr, hJint, hDeg Ψ N j hN hj hjN]
  ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
