import Mathlib
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagGrassPush
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFlagGrassPush
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHFlProdLinear
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFsInvPow
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFlagArithVar
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PFlagImageGrass
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVandCount
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Assembly
import GroundTheory.HeightsAndTheta.Heights.Intersections.PConsequences
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ExistsUnique
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ChangeOfModel
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsPermAppendSnoc
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPointsIntegralProductFormulaStatement
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Giv.Push

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

section Multilinear

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} {P : Ideal (MRing ι)} {n : ℕ}

theorem snoc_update_fsHerm (c : HermLine ι) (v : Fin n → K → ℤ) (j : Fin n) (d : K → ℤ) :
    (Fin.snoc (α := fun _ => HermLine ι) (fun i => fsHerm ι (Function.update v j d i)) c) =
      Function.update (Fin.snoc (α := fun _ => HermLine ι) (fun i => fsHerm ι (v i)) c) j.castSucc
        (fsHerm ι d) := by
  rw [← Fin.snoc_update]
  congr 1
  funext i
  rcases eq_or_ne i j with rfl | h
  · simp
  · simp [Function.update_of_ne h]

theorem isSmooth_snoc_fsHerm {c : HermLine ι} (hc : IsSmoothHerm c) (v : Fin n → K → ℤ)
    (i : Fin (n + 1)) :
    IsSmoothHerm ((Fin.snoc (α := fun _ => HermLine ι) (fun i => fsHerm ι (v i)) c) i) := by
  induction i using Fin.lastCases with
  | last => rw [Fin.snoc_last]; exact hc
  | cast i => rw [Fin.snoc_castSucc]; exact FsInvPow.isSmoothHerm_fsHerm _

theorem snoc_update_add (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) {c : HermLine ι}
    (hc : IsSmoothHerm c) (v : Fin n → K → ℤ) (j : Fin n) (a b : K → ℤ) :
    I P (n + 1) (Fin.snoc (α := fun _ => HermLine ι) (fun i => fsHerm ι (Function.update v j (a + b) i)) c) =
      I P (n + 1) (Fin.snoc (α := fun _ => HermLine ι) (fun i => fsHerm ι (Function.update v j a i)) c) +
        I P (n + 1) (Fin.snoc (α := fun _ => HermLine ι) (fun i => fsHerm ι (Function.update v j b i)) c) := by
  have hL := isSmooth_snoc_fsHerm hc v
  rw [snoc_update_fsHerm, snoc_update_fsHerm, snoc_update_fsHerm,
    Inter.fam_update_eq_snoc hI hP _ hL _ (FsInvPow.isSmoothHerm_fsHerm _),
    Inter.fam_update_eq_snoc hI hP _ hL _ (FsInvPow.isSmoothHerm_fsHerm _),
    Inter.fam_update_eq_snoc hI hP _ hL _ (FsInvPow.isSmoothHerm_fsHerm _)]
  exact FlagHeightMultilinear.I_snoc_fsHerm_add hI hP _ (fun i => hL _) a b

def snocMultilin (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) {c : HermLine ι}
    (hc : IsSmoothHerm c) : MultilinearMap ℤ (fun _ : Fin n => K → ℤ) ℝ where
  toFun v := I P (n + 1) (Fin.snoc (α := fun _ => HermLine ι) (fun i => fsHerm ι (v i)) c)
  map_update_add' := by
    intro inst v j a b
    have e : inst = instDecidableEqFin n := Subsingleton.elim _ _
    subst e
    exact snoc_update_add hI hP hc v j a b
  map_update_smul' := by
    intro inst v j t a
    have e : inst = instDecidableEqFin n := Subsingleton.elim _ _
    subst e
    let g : (K → ℤ) →+ ℝ := AddMonoidHom.mk'
      (fun a => I P (n + 1) (Fin.snoc (α := fun _ => HermLine ι) (fun i => fsHerm ι (Function.update v j a i)) c))
      (fun a b => snoc_update_add hI hP hc v j a b)
    exact map_zsmul g t a

theorem snocMultilin_apply (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) (v : Fin n → K → ℤ) :
    snocMultilin hI hP (isSmoothHerm_constLine (-Real.log ((2 : ℕ) : ℝ))) v =
      Real.log ((2 : ℕ) : ℝ) * ptsIntegral P (pot fun i => fsHerm ι (v i)) (fun _ => 1) :=
  (Inter.Conservation.proof K ι I hI P n (fun i => fsHerm ι (v i)) 2 hP
    (fun _ => FsInvPow.isSmoothHerm_fsHerm _) Nat.prime_two).2

theorem log_two_ne : Real.log ((2 : ℕ) : ℝ) ≠ 0 :=
  (Real.log_pos (by norm_num)).ne'

theorem pts_fsHerm_sum (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) {α : Type} [Fintype α]
    (ℓ : Fin n → α → ℤ) (x : α → K → ℤ) :
    ptsIntegral P (pot fun i => fsHerm ι (∑ p, ℓ i p • x p)) (fun _ => 1) =
      ∑ r : Fin n → α, (∏ i, (ℓ i (r i) : ℝ)) *
        ptsIntegral P (pot fun i => fsHerm ι (x (r i))) (fun _ => 1) := by
  refine mul_left_cancel₀ log_two_ne ?_
  rw [← snocMultilin_apply hI hP, MultilinearMap.map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [MultilinearMap.map_smul_univ _ (fun i => ℓ i (r i)) (fun i => x (r i)), snocMultilin_apply hI hP,
    zsmul_eq_mul, Int.cast_prod]
  ring

theorem pts_neg_eq (hI : IsIntersectionFamily I) (hP : IsArithVar P (n + 1)) :
    ptsIntegral P (pot fun _ : Fin n => fsHerm ι fun _ => -1) (fun _ => 1) =
      (-1) ^ n * geomDeg P (fsMulti ι) n := by
  have hg : geomDeg P (fsMulti ι) n =
      ptsIntegral P (pot fun _ : Fin n => fsHerm ι fun _ => 1) (fun _ => 1) := by
    unfold geomDeg
    congr 1
    funext _ z
    show Real.log ((fsMulti ι).h z) = Real.log ((fsHerm ι fun _ => 1).h z)
    rw [FsInvPow.fsHerm_h_eq]
    rfl
  rw [hg]
  refine mul_left_cancel₀ log_two_ne ?_
  have e : (fun _ : Fin n => (fun _ => -1 : K → ℤ)) =
      fun i => (fun _ : Fin n => (-1 : ℤ)) i • (fun _ : Fin n => (fun _ => 1 : K → ℤ)) i := by
    funext _ _
    simp
  rw [← snocMultilin_apply hI hP, e, MultilinearMap.map_smul_univ, snocMultilin_apply hI hP]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, zsmul_eq_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one]
  ring

end Multilinear

section Forms

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)

def flagIntAdd : RootPoly Ψ N →+ ℚ :=
  AddMonoidHom.mk' (flagInt Ψ N) fun a b => by
    unfold flagInt LowerBoundFree.antisym
    simp only [map_add, smul_add, Finset.sum_add_distrib, coeff_add]

theorem flagInt_prod_linForm {d : ℕ} (ℓ : Fin d → Ψ × Fin N → ℤ) :
    flagInt Ψ N (∏ i, LowerBoundFree.linForm Ψ N (ℓ i)) =
      ∑ r : Fin d → Ψ × Fin N, (∏ i, (ℓ i (r i) : ℚ)) * flagInt Ψ N (∏ i, X (r i)) := by
  have h : ∏ i, LowerBoundFree.linForm Ψ N (ℓ i) =
      ∑ r : Fin d → Ψ × Fin N, C (∏ i, (ℓ i (r i) : ℚ)) * ∏ i, (X (r i) : RootPoly Ψ N) := by
    unfold LowerBoundFree.linForm
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [smul_eq_C_mul, Finset.prod_mul_distrib, map_prod]
  rw [h]
  refine (map_sum (flagIntAdd Ψ N) _ _).trans (Finset.sum_congr rfl fun r _ => ?_)
  exact flagInt_C_mul Ψ N _ _

theorem pts_linForms [Nonempty Ψ] (II : IntersectionSystem) (hII : IsIntersectionSystem II) (hN : 2 ≤ N)
    (hB : ∀ w : Fin (dimFl Ψ N) → Ψ × Fin N,
      ptsIntegral (PFl Ψ N) (pot fun r => xLine Ψ N (w r)) (fun _ => 1) =
        ((flagInt Ψ N (∏ r, X (w r)) : ℚ) : ℝ))
    (d : ℕ) (hd : d = dimFl Ψ N) (ℓ : Fin d → Ψ × Fin N → ℤ) :
    ptsIntegral (PFl Ψ N) (pot fun i => linLine Ψ N (ℓ i)) (fun _ => 1) =
      ((flagInt Ψ N (∏ i, LowerBoundFree.linForm Ψ N (ℓ i)) : ℚ) : ℝ) := by
  subst hd
  have hP := FlagArithVar.proof Ψ N hN
  have hI := hII (FlBlock Ψ N) (FlIdx Ψ N)
  have hlin : (fun i => linLine Ψ N (ℓ i)) =
      fun i => fsHerm (FlIdx Ψ N) (∑ p, ℓ i p • xDeg Ψ N p) := by
    funext i
    unfold linLine linDeg
    congr 1
    funext q
    simp [Finset.sum_apply]
  rw [hlin, pts_fsHerm_sum hI hP, flagInt_prod_linForm]
  push_cast
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← hB r]
  rfl

variable (j : ℕ)

def jForms : Fin (dimN Ψ N j + vandCount Ψ N j) → Ψ × Fin N → ℤ :=
  Fin.append (fun _ => muForm Ψ N j) (fun i => vandForm Ψ N j ((Fintype.equivFin (VandPair Ψ N j)).symm i))

theorem prod_jForms :
    ∏ i, LowerBoundFree.linForm Ψ N (jForms Ψ N j i) = muPoly Ψ N j ^ dimN Ψ N j * vandBlocks Ψ N j := by
  rw [Fin.prod_univ_add]
  simp only [jForms, Fin.append_left, Fin.append_right, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    linForm_muForm, prod_vandForm]

theorem linLine_jForms :
    (fun i => linLine Ψ N (jForms Ψ N j i)) =
      Fin.append (fun _ : Fin (dimN Ψ N j) => linLine Ψ N (muForm Ψ N j)) (vandLine Ψ N j) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [jForms]
  · simp [jForms, vandLine]

end Forms

end GlobalTheory.CompanionTheory.Ar.Giv.Push

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar.Giv.Push

theorem flagGrassPush : GlobalTheory.CompanionTheory.Ar.PB.Inputs → ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement →
    GroundTheory.Heights₂.Heights.LowerBoundFree.FlagGrassPush.Statement := by
  intro hIn hSys II Ψ _ _ _ N j cf hII hN hj hjN
  have hcnt : dimN Ψ N j + vandCount Ψ N j = dimFl Ψ N := VandCount.proof Ψ N j (by omega)
  have hAr0 : IsArithVar (PFl Ψ N) (dimFl Ψ N + 1) := FlagArithVar.proof Ψ N hN
  have hArFl : IsArithVar (PFl Ψ N) (dimN Ψ N j + 1 + vandCount Ψ N j) := by
    rwa [show dimFl Ψ N + 1 = dimN Ψ N j + 1 + vandCount Ψ N j by omega] at hAr0
  have hArFl' : IsArithVar (PFl Ψ N) (dimN Ψ N j + vandCount Ψ N j + 1) := by
    rwa [show dimN Ψ N j + 1 + vandCount Ψ N j = dimN Ψ N j + vandCount Ψ N j + 1 by omega] at hArFl
  have hArGr : IsArithVar (grassIdeal (Fintype.card Ψ) j (N - j)) (dimN Ψ N j + 1) :=
    GrassArithVar.full (Fintype.card Ψ) j (N - j) Fintype.card_pos
  have hIm := FlagImageGrass.proof Ψ N j hj hjN
  have hArIm : IsArithVar (imageZ (grFlV Ψ N j hj hjN) (PFl Ψ N)) (dimN Ψ N j + 1) := by
    rw [hIm]
    exact hArGr
  have hb := isBlockMap_grFl (Ψ := Ψ) (N := N) (j := j) hj hjN
  obtain ⟨G⟩ := Targets.genFibreExists _ _ _ _ _ _ (PFl Ψ N) _ hb hArFl
  obtain ⟨J, hJ, -⟩ := Targets.ExistsUnique.full G.Φ (fibreIdx (FlIdx Ψ N) (grFlKappa Ψ N j hj hjN))

  have hPF := hIn.projFormula II hII (Fin (Fintype.card Ψ)) (plBlocks (Fintype.card Ψ) j (N - j))
    (FlBlock Ψ N) (FlIdx Ψ N) (grFlKappa Ψ N j hj hjN) (grFlV Ψ N j hj hjN) (PFl Ψ N) (dimN Ψ N j + 1)
    (vandCount Ψ N j) G J (fun _ => fsHerm (plBlocks (Fintype.card Ψ) j (N - j)) (fun _ => -1))
    (fun _ => linLine Ψ N (muForm Ψ N j)) (vandLine Ψ N j) hb hArFl hArIm hJ
    (fun _ => isSmoothHerm_fsHerm _) (fun _ => isPullHerm_mu hj hjN) (fun _ => isSmoothHerm_fsHerm _)
  rw [hIm] at hPF
  have hprod := HFlProdLinear.proof FlagArithVar.proof II Ψ N (dimN Ψ N j + 1 + vandCount Ψ N j) cf
    (faForms Ψ N j) hII hN (by omega)
  rw [linLine_faForms Ψ N j, hPF, ← FA_eq_prod] at hprod
  have hinv := FsInvPow.proof II (Fin (Fintype.card Ψ)) (plBlocks (Fintype.card Ψ) j (N - j))
    (grassIdeal (Fintype.card Ψ) j (N - j)) (dimN Ψ N j + 1) hII hArGr

  have hgeo := ptsIntegral_projection hIn.projFormula ⟨II, hII⟩ (Fin (Fintype.card Ψ))
    (plBlocks (Fintype.card Ψ) j (N - j)) (FlBlock Ψ N) (FlIdx Ψ N) (grFlKappa Ψ N j hj hjN)
    (grFlV Ψ N j hj hjN) (PFl Ψ N) (dimN Ψ N j) (vandCount Ψ N j) G J
    (fun _ => fsHerm (plBlocks (Fintype.card Ψ) j (N - j)) (fun _ => -1))
    (fun _ => linLine Ψ N (muForm Ψ N j)) (vandLine Ψ N j) hb hArFl' hArIm hJ
    (fun _ => isSmoothHerm_fsHerm _) (fun _ => isPullHerm_mu hj hjN) (fun _ => isSmoothHerm_fsHerm _)
  rw [hIm, pts_neg_eq (hII _ _) hArGr, ← linLine_jForms,
    pts_linForms Ψ N II hII hN (fun w => GlobalTheory.T.flag_points_integral_product_formula hIn hSys Ψ N w hN) _ hcnt, prod_jForms] at hgeo
  have hJint : (Jint Ψ N j cf : ℝ) =
      (cf : ℝ) * ((flagInt Ψ N (muPoly Ψ N j ^ dimN Ψ N j * vandBlocks Ψ N j) : ℚ) : ℝ) := by
    unfold Jint fib
    rw [show muPoly Ψ N j ^ dimN Ψ N j * (C cf * vandBlocks Ψ N j) =
      C cf * (muPoly Ψ N j ^ dimN Ψ N j * vandBlocks Ψ N j) by ring, flagInt_C_mul]
    push_cast
    rfl
  rw [hprod, hinv, hJint, hgeo]
  ring

end GlobalTheory.CompanionTheory.Ar.Giv
