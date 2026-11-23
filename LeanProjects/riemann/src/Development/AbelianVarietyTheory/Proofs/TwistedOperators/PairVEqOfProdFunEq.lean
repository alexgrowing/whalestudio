import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColMapEqColMapV
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultilinearSumEqOfFunctionProductSumsEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedKernelOfVectorAdd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmPureTensorOOfFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsEqSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ExpansionInvariance

theorem chainTo_congr_lt {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    {k k' : ∀ j, V j →ₗ[ℂ] V (j + 1)} : ∀ n, (∀ j, j < n → k j = k' j) → chainTo k n = chainTo k' n
  | 0, _ => rfl
  | n + 1, h => by
    show k n ∘ₗ chainTo k n = k' n ∘ₗ chainTo k' n
    rw [h n n.lt_succ_self, chainTo_congr_lt n fun j hj => h j (by omega)]

theorem chainTo_add_at {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    {k₁ k₂ k₃ : ∀ j, V j →ₗ[ℂ] V (j + 1)} (j₀ : ℕ) (h₂ : ∀ j, j ≠ j₀ → k₂ j = k₁ j) (h₃ : ∀ j, j ≠ j₀ → k₃ j = k₁ j)
    (h : k₁ j₀ = k₂ j₀ + k₃ j₀) : ∀ n, j₀ < n → chainTo k₁ n = chainTo k₂ n + chainTo k₃ n
  | 0, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, hn => by
    show k₁ n ∘ₗ chainTo k₁ n = k₂ n ∘ₗ chainTo k₂ n + k₃ n ∘ₗ chainTo k₃ n
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h' | h'
    · rw [chainTo_add_at j₀ h₂ h₃ h n h', h₂ n (by omega), h₃ n (by omega), LinearMap.comp_add]
    · subst h'
      rw [chainTo_congr_lt (k := k₂) (k' := k₁) j₀ (fun j hj => h₂ j (by omega)),
        chainTo_congr_lt (k := k₃) (k' := k₁) j₀ (fun j hj => h₃ j (by omega)), h, LinearMap.add_comp]

theorem chainTo_smul_at {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]
    {k₁ k₂ : ∀ j, V j →ₗ[ℂ] V (j + 1)} (j₀ : ℕ) (a : ℂ) (h₂ : ∀ j, j ≠ j₀ → k₂ j = k₁ j)
    (h : k₁ j₀ = a • k₂ j₀) : ∀ n, j₀ < n → chainTo k₁ n = a • chainTo k₂ n
  | 0, hn => absurd hn (Nat.not_lt_zero _)
  | n + 1, hn => by
    show k₁ n ∘ₗ chainTo k₁ n = a • (k₂ n ∘ₗ chainTo k₂ n)
    rcases Nat.lt_succ_iff_lt_or_eq.mp hn with h' | h'
    · rw [chainTo_smul_at j₀ a h₂ h n h', h₂ n (by omega), LinearMap.comp_smul]
    · subst h'
      rw [chainTo_congr_lt (k := k₂) (k' := k₁) j₀ (fun j hj => h₂ j (by omega)), h, LinearMap.smul_comp]

theorem jetOp_mul_tab {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ} (lam : ι → DomWeight a)
    (lam' : ι → DomWeight b) (c : K) (J : (Formalism.L2.Ker.DVar ι a b →₀ ℕ) → K) (n : ι → ℕ) :
    Formalism.L2.Ker.jetOp lam lam' (fun k => c * J k) n = c • Formalism.L2.Ker.jetOp lam lam' J n := by
  have e : Formalism.L2.Ker.jetLin (fun k => c * J k) = c • Formalism.L2.Ker.jetLin J := by
    refine (MvPolynomial.basisMonomials ((ι × Fin b × Fin b) ⊕ Formalism.L2.Ker.DVar ι a b) K).ext fun m => ?_
    simp only [Formalism.L2.Ker.jetLin, LinearMap.smul_apply, Module.Basis.constr_basis, MvPolynomial.smul_monomial,
      smul_eq_mul]
  ext1 P
  simp only [Formalism.L2.Ker.jetOp, Formalism.L2.Ker.jetMap, e, LinearMap.comp_apply, LinearMap.smul_apply, map_smul]

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem kkVec_smul (S : GridChoice W U) (p : Pair T) (a : ℂ) (f : WO (G.pS p) (G.pT p) → ℂ) (x : FinPt G p.small)
    (y : FinPt G p.big) : GlobalTheory.TopZeroInv.kkVec S p (a • f) x y = a • GlobalTheory.TopZeroInv.kkVec S p f x y := by
  have hJ : ∀ x' y', jetTab W S.N.frC p (a • f) x' y' = fun k => a * jetTab W S.N.frC p f x' y' k := by
    intro x' y'
    funext k
    simp only [jetTab, kerFin, fockIn, GlobalTheory.FiniteFock.pureTensorO_smul, GridData.Weil.ker, thetaKO, map_smul,
      Pi.smul_apply, smul_eq_mul]
  unfold GlobalTheory.TopZeroInv.kkVec fockComp
  rw [hJ, jetOp_mul_tab, smul_comm]

def colML (S : GridChoice W U) (t : T) (x : ∀ j, FinPt G (.top j)) :
    MultilinearMap ℂ (fun j : Fin D.R.m => ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))))
      (VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (wt G (.top D.R.m))) where
  toFun cc := colMapV S t (fun j => (cc j : WO _ _ → ℂ)) x
  map_update_add' := by
    intro _ cc j₀ a b
    unfold colMapV
    rw [← LinearMap.add_comp]
    congr 1
    refine chainTo_add_at j₀.1 ?_ ?_ ?_ D.R.m j₀.2
    · intro j hj
      dsimp only
      split_ifs with h
      · have hne : (⟨j, h⟩ : Fin D.R.m) ≠ j₀ := fun e => hj (congrArg Fin.val e)
        simp only [Function.update_of_ne hne]
      · rfl
    · intro j hj
      dsimp only
      split_ifs with h
      · have hne : (⟨j, h⟩ : Fin D.R.m) ≠ j₀ := fun e => hj (congrArg Fin.val e)
        simp only [Function.update_of_ne hne]
      · rfl
    · simp only [dif_pos j₀.2, Fin.eta, Function.update_self, Submodule.coe_add]
      exact GlobalTheory.TopZeroInv.kkVec_add S _ a.2 b.2 _ _
  map_update_smul' := by
    intro _ cc j₀ c a
    unfold colMapV
    rw [← LinearMap.smul_comp]
    congr 1
    refine chainTo_smul_at j₀.1 c ?_ ?_ D.R.m j₀.2
    · intro j hj
      dsimp only
      split_ifs with h
      · have hne : (⟨j, h⟩ : Fin D.R.m) ≠ j₀ := fun e => hj (congrArg Fin.val e)
        simp only [Function.update_of_ne hne]
      · rfl
    · simp only [dif_pos j₀.2, Fin.eta, Function.update_self, Submodule.coe_smul]
      exact kkVec_smul S _ c _ _ _

def rowML (S : GridChoice W U) (t : T) (y : ∀ i, FinPt G (.grid i D.R.m)) :
    MultilinearMap ℂ (fun i : Fin D.R.m => ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))))
      (VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] VV ℂ (wt G (.grid D.R.m D.R.m))) where
  toFun rr := rowMapV S (fun i => (rr i : WO _ _ → ℂ)) y
  map_update_add' := by
    intro _ rr i₀ a b
    unfold rowMapV
    rw [← LinearMap.add_comp]
    congr 1
    refine chainTo_add_at i₀.1 ?_ ?_ ?_ D.R.m i₀.2
    · intro i hi
      dsimp only
      split_ifs with h
      · have hne : (⟨i, h⟩ : Fin D.R.m) ≠ i₀ := fun e => hi (congrArg Fin.val e)
        simp only [Function.update_of_ne hne]
      · rfl
    · intro i hi
      dsimp only
      split_ifs with h
      · have hne : (⟨i, h⟩ : Fin D.R.m) ≠ i₀ := fun e => hi (congrArg Fin.val e)
        simp only [Function.update_of_ne hne]
      · rfl
    · simp only [dif_pos i₀.2, Fin.eta, Function.update_self, Submodule.coe_add]
      exact GlobalTheory.TopZeroInv.kkVec_add S _ a.2 b.2 _ _
  map_update_smul' := by
    intro _ rr i₀ c a
    unfold rowMapV
    rw [← LinearMap.smul_comp]
    congr 1
    refine chainTo_smul_at i₀.1 c ?_ ?_ D.R.m i₀.2
    · intro i hi
      dsimp only
      split_ifs with h
      · have hne : (⟨i, h⟩ : Fin D.R.m) ≠ i₀ := fun e => hi (congrArg Fin.val e)
        simp only [Function.update_of_ne hne]
      · rfl
    · simp only [dif_pos i₀.2, Fin.eta, Function.update_self, Submodule.coe_smul]
      exact kkVec_smul S _ c _ _ _

def pairRowL (S : GridChoice W U) (t : T) (y : ∀ i, FinPt G (.grid i D.R.m)) (u : VV ℂ (wt G (.top 0)))
    (v : VV ℂ (listedWt G (.grid 0 D.R.m))) :
    (VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (wt G (.top D.R.m))) →ₗ[ℂ]
      MultilinearMap ℂ (fun i : Fin D.R.m => ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)))) ℂ where
  toFun A := ((brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m)) (A u)).comp
    (LinearMap.applyₗ v)).compMultilinearMap (rowML S t y)
  map_add' A B := by
    ext rr
    simp only [LinearMap.add_apply, map_add, LinearMap.add_comp, MultilinearMap.add_apply]
    rfl
  map_smul' c A := by
    ext rr
    simp only [LinearMap.smul_apply, map_smul, LinearMap.smul_comp, MultilinearMap.smul_apply, RingHom.id_apply]
    rfl

def pairML (S : GridChoice W U) (t : T) (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m))
    (u : VV ℂ (wt G (.top 0))) (v : VV ℂ (listedWt G (.grid 0 D.R.m))) :
    MultilinearMap ℂ (fun j : Fin D.R.m => ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))))
      (MultilinearMap ℂ (fun i : Fin D.R.m => ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)))) ℂ) :=
  (pairRowL S t y u v).compMultilinearMap (colML S t x)

theorem pairML_apply (S : GridChoice W U) (t : T) (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m))
    (u : VV ℂ (wt G (.top 0))) (v : VV ℂ (listedWt G (.grid 0 D.R.m))) (cc rr) :
    pairML S t x y u v cc rr = (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))).compl₁₂
      (colMapV S t (fun j => (cc j : WO _ _ → ℂ)) x) (rowMapV S (fun i => (rr i : WO _ _ → ℂ)) y) u v := rfl

theorem pairV_eq_of_prodFun_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) (t : T)
    {δ : Type} (τ : δ →₀ ℂ) (c c' : δ → ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ)
    (r r' : δ → ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ),
    (∀ d ∈ τ.support, ∀ j : Fin D.R.m, IsThetaFunO W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) (c d j) ∧
      IsThetaFunO W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) (c' d j)) →
    (∀ d ∈ τ.support, ∀ i : Fin D.R.m, IsThetaFunO W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (r d i) ∧
      IsThetaFunO W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (r' d i)) →
    (∀ (w : ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)))
      (z : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      (τ.sum fun d a => a * (∏ j, c d j (w j)) * ∏ i, r d i (z i)) = τ.sum fun d a => a * (∏ j, c' d j (w j)) * ∏ i, r' d i (z i)) →
    ∀ x y, pairV S t τ c r x y = pairV S t τ c' r' x y := by
  intro D T L sc G W U S t δ τ c c' r r' hc hr hprod x y
  classical
  refine LinearMap.ext fun u => LinearMap.ext fun v => ?_
  let f : δ → ∀ j : Fin D.R.m, ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))) :=
    fun d j => if h : d ∈ τ.support then ⟨c d j, (hc d h j).1⟩ else 0
  let f' : δ → ∀ j : Fin D.R.m, ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))) :=
    fun d j => if h : d ∈ τ.support then ⟨c' d j, (hc d h j).2⟩ else 0
  let g : δ → ∀ i : Fin D.R.m, ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) :=
    fun d i => if h : d ∈ τ.support then ⟨r d i, (hr d h i).1⟩ else 0
  let g' : δ → ∀ i : Fin D.R.m, ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) :=
    fun d i => if h : d ∈ τ.support then ⟨r' d i, (hr d h i).2⟩ else 0
  have ef : ∀ d ∈ τ.support, (fun j => (f d j : WO _ _ → ℂ)) = c d := fun d hd => funext fun j => by simp only [f, dif_pos hd]
  have ef' : ∀ d ∈ τ.support, (fun j => (f' d j : WO _ _ → ℂ)) = c' d := fun d hd => funext fun j => by simp only [f', dif_pos hd]
  have eg : ∀ d ∈ τ.support, (fun i => (g d i : WO _ _ → ℂ)) = r d := fun d hd => funext fun i => by simp only [g, dif_pos hd]
  have eg' : ∀ d ∈ τ.support, (fun i => (g' d i : WO _ _ → ℂ)) = r' d := fun d hd => funext fun i => by simp only [g', dif_pos hd]
  have key := GlobalTheory.funProd_multilinear_sum_eq (pairML S t x y u v) τ f f' g g' (fun w z => by
    rw [Finsupp.sum, Finsupp.sum]
    have h1 := hprod w z
    rw [Finsupp.sum, Finsupp.sum] at h1
    refine (Finset.sum_congr rfl fun d hd => ?_).trans (h1.trans (Finset.sum_congr rfl fun d hd => ?_))
    · rw [← ef d hd, ← eg d hd]
    · rw [← ef' d hd, ← eg' d hd])
  have hL : ∀ (cc : δ → ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ)
      (rr : δ → ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)
      (F : δ → ∀ j : Fin D.R.m, ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))))
      (H : δ → ∀ i : Fin D.R.m, ↥(GlobalTheory.RowVertexInv.thetaSub W.ψ (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)))),
      (∀ d ∈ τ.support, (fun j => (F d j : WO _ _ → ℂ)) = cc d) → (∀ d ∈ τ.support, (fun i => (H d i : WO _ _ → ℂ)) = rr d) →
      pairV S t τ cc rr x y u v = τ.sum fun d a => a * pairML S t x y u v (F d) (H d) := by
    intro cc rr F H hF hH
    unfold pairV
    rw [Finsupp.sum, Finsupp.sum, LinearMap.sum_apply, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, pairML_apply, hF d hd, hH d hd]
  rw [hL c r f g ef eg, hL c' r' f' g' ef' eg']
  exact key

end GlobalTheory.ExpansionInvariance

end
