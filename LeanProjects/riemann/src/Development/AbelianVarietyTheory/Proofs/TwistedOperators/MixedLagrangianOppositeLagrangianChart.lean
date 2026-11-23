import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrientedHermitianFormQuadSumEqTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AtWAtPlSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfPartAlgebraMapLiftV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesSplitIdempotentSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianActionColumnBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.FlipMatch.ChartOpp

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (blk blk_mul blk_transpose blk_one blk_map)

theorem chart_algebra {K : Type} [Field K] {n p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d)
    (Bp : GL (Fin n) K) (C cc : GL (Fin d) K) (G₁ : Matrix (Fin n) (Fin n) K) (hG₁ : G₁.det ≠ 0)
    (β₁ : GL (Fin n) K) (βV : GL (Fin p) K) (βV₁ : GL (Fin q) K)
    (GV : Matrix (Fin p) (Fin p) K) (GV₁ : Matrix (Fin q) (Fin q) K) (ξ : K) (hξ : ξ ≠ 0)
    (hC : C.val * cc.val = blk e βV.val (-βV₁.val)) :
    ∃ g : GL (Fin n) K, ∀ U Ub : Matrix (Fin n) (Fin d) K,
      g.val * (-(Bp.valᵀ * (-G₁) * Ub * (ξ • blk e GV GV₁) * C.val)) * cc.val =
          (β₁⁻¹).val * Ub * blk e (GV * βV.val) (-(GV₁ * βV₁.val)) ∧
      ξ⁻¹ • ((invT g).val * ((Bp⁻¹).val * U * ((C⁻¹).val)ᵀ) * (invT cc).val) =
          β₁.valᵀ * G₁ᵀ * U * blk e ((βV⁻¹).val)ᵀ (-((βV₁⁻¹).val)ᵀ) := by
  have hdet : (ξ • (Bp.valᵀ * G₁ * β₁.val)).det ≠ 0 := by
    rw [det_smul, det_mul, det_mul, det_transpose]
    exact mul_ne_zero (pow_ne_zero _ hξ) (mul_ne_zero (mul_ne_zero (Matrix.isUnits_det_units Bp).ne_zero hG₁)
      (Matrix.isUnits_det_units β₁).ne_zero)
  obtain ⟨Q, hQ⟩ : IsUnit (ξ • (Bp.valᵀ * G₁ * β₁.val)) :=
    (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
  have hinv : (cc⁻¹).val * (C⁻¹).val = blk e (βV⁻¹).val (-(βV₁⁻¹).val) := by
    have h1 : (C.val * cc.val) * blk e (βV⁻¹).val (-(βV₁⁻¹).val) = 1 := by
      rw [hC, blk_mul, Units.mul_inv, neg_mul_neg, Units.mul_inv, blk_one]
    calc (cc⁻¹).val * (C⁻¹).val
        = (cc⁻¹).val * (C⁻¹).val * ((C.val * cc.val) * blk e (βV⁻¹).val (-(βV₁⁻¹).val)) := by
          rw [h1, Matrix.mul_one]
      _ = blk e (βV⁻¹).val (-(βV₁⁻¹).val) := by
          simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left]
  refine ⟨Q⁻¹, fun U Ub => ⟨?_, ?_⟩⟩
  · have e1 : -(Bp.valᵀ * (-G₁) * Ub * (ξ • blk e GV GV₁) * C.val) =
        Q.val * ((β₁⁻¹).val * (Ub * (blk e GV GV₁ * C.val))) := by
      rw [hQ]
      simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, smul_neg]
      rw [← Matrix.mul_assoc (β₁ : Matrix (Fin n) (Fin n) K) ((β₁⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
        Units.mul_inv, Matrix.one_mul]
    rw [e1]
    simp only [Matrix.mul_assoc]
    rw [hC, blk_mul, Matrix.mul_neg, ← Matrix.mul_assoc ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      (Q : Matrix (Fin n) (Fin n) K), Units.inv_mul, Matrix.one_mul]
  · have e2 : ((C⁻¹).val)ᵀ * ((cc⁻¹).val)ᵀ = blk e ((βV⁻¹).val)ᵀ (-((βV₁⁻¹).val)ᵀ) := by
      rw [← transpose_mul, hinv, blk_transpose, transpose_neg]
    show ξ⁻¹ • ((((Q⁻¹)⁻¹ : GL (Fin n) K)).valᵀ * ((Bp⁻¹).val * U * ((C⁻¹).val)ᵀ) * ((cc⁻¹).val)ᵀ) = _
    rw [inv_inv, hQ, transpose_smul, transpose_mul, transpose_mul, transpose_transpose]
    simp only [Matrix.smul_mul, Matrix.mul_assoc, smul_smul, inv_mul_cancel₀ hξ, one_smul]
    rw [← Matrix.mul_assoc (Bp : Matrix (Fin n) (Fin n) K) ((Bp⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K),
      Units.mul_inv, Matrix.one_mul, e2]

end GlobalTheory.FlipMatch.ChartOpp

namespace GlobalTheory.FlipMatch.ChartOpp

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (blk blk_mul blk_transpose blk_one blk_map)

theorem map_mul_equiv {K K' : Type} [Field K] [Field K'] (f : K ≃+* K') {a b c : Type} [Fintype b] (P : Matrix a b K)
    (Q : Matrix b c K) : (P * Q).map f = P.map f * Q.map f :=
  Matrix.map_mul (f := (f : K →+* K'))

variable {D : D7}

theorem isHalf_of_mulG (S : HSp D) {m : ℕ} {b : AE D} {y : Matrix (Fin m) (Fin S.rank) (AE D)}
    (h : IsHalf b (mulG S y)) : IsHalf b y := by
  have k : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram⁻¹ = 1 := mul_eq_one_comm.mp (GlobalTheory.RouteCoords.inv_mul_gram S)
  have hy : mulG S y * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram⁻¹ = y := by
    unfold mulG
    rw [Matrix.mul_assoc, k, Matrix.mul_one]
  have h2 : b • mulG S y = mulG S y := Matrix.ext fun a c => h a c
  have h3 : b • y = y := by
    calc b • y = b • (mulG S y * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram⁻¹) := by rw [hy]
      _ = (b • mulG S y) * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM S.gram⁻¹ := (Matrix.smul_mul _ _ _).symm
      _ = y := by rw [h2, hy]
  intro a c
  exact congrFun₂ h3 a c

theorem isHalf_cA_of_adjV₁ {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ} (e : Num G i j)
    {m : ℕ} {b : AE D} {u : Matrix (Fin m) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)}
    (h : IsHalf b (adjV₁ e u)) : IsHalf (cA D b) (u.submatrix id fun k => e (.inr k)) := by
  have h1 : IsHalf b (mulG (spV₁ G i j) ((u.submatrix id fun k => e (.inr k)).map (cA D))) := fun a c => by
    have := h a c
    simp only [adjV₁, Matrix.neg_apply, mul_neg, neg_inj] at this
    exact this
  have h2 := isHalf_of_mulG _ h1
  intro a c
  have := congrArg (cA D) (h2 a c)
  rw [map_mul, Matrix.map_apply, Formalism.L2.Theta.cA_cA] at this
  exact this

end GlobalTheory.FlipMatch.ChartOpp

namespace GlobalTheory.FlipMatch.ChartOpp

section Blocks

variable {K R C : Type} [Field K] {n p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (eA : Fin n ≃ R) (eC : Fin d ≃ C)

theorem entry_inl (x : Matrix (Fin n) (Fin n) K) (Z : Matrix (Fin n) (Fin d) K) (P : Matrix (Fin p) (Fin p) K)
    (Q : Matrix (Fin q) (Fin q) K) (a : Fin n) (k : Fin p) :
    reindex eA eC (x * Z * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e P Q) (eA a) (eC (e (.inl k))) =
      (x * (Z.submatrix id fun k => e (.inl k)) * P) a k := by
  rw [← GlobalTheory.RouteCoords.mul_submatrix_cols, ← GlobalTheory.RouteCoords.submatrix_mul_blk_inl e _ P Q]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]

theorem entry_inr (x : Matrix (Fin n) (Fin n) K) (Z : Matrix (Fin n) (Fin d) K) (P : Matrix (Fin p) (Fin p) K)
    (Q : Matrix (Fin q) (Fin q) K) (a : Fin n) (k : Fin q) :
    reindex eA eC (x * Z * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e P Q) (eA a) (eC (e (.inr k))) =
      (x * (Z.submatrix id fun k => e (.inr k)) * Q) a k := by
  rw [← GlobalTheory.RouteCoords.mul_submatrix_cols, ← GlobalTheory.RouteCoords.submatrix_mul_blk_inr e _ P Q]
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]

theorem zero_inl (S : Finset C) (hS : ∀ k, eC (e (.inr k)) ∉ S) (x : Matrix (Fin n) (Fin n) K)
    (Z : Matrix (Fin n) (Fin d) K) (P : Matrix (Fin p) (Fin p) K) (Q : Matrix (Fin q) (Fin q) K)
    (hZ : (Z.submatrix id fun k => e (.inl k)) = 0) :
    ∀ r, ∀ s ∈ S, reindex eA eC (x * Z * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e P Q) r s = 0 := by
  intro r s hs
  obtain ⟨a, rfl⟩ := eA.surjective r
  obtain ⟨z, rfl⟩ := (e.trans eC).surjective s
  rcases z with k | k
  · exact (entry_inl e eA eC x Z P Q a k).trans (by rw [hZ, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply])
  · exact absurd hs (hS k)

theorem zero_inr (S : Finset C) (hS : ∀ k, eC (e (.inl k)) ∈ S) (x : Matrix (Fin n) (Fin n) K)
    (Z : Matrix (Fin n) (Fin d) K) (P : Matrix (Fin p) (Fin p) K) (Q : Matrix (Fin q) (Fin q) K)
    (hZ : (Z.submatrix id fun k => e (.inr k)) = 0) :
    ∀ r, ∀ s ∉ S, reindex eA eC (x * Z * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e P Q) r s = 0 := by
  intro r s hs
  obtain ⟨a, rfl⟩ := eA.surjective r
  obtain ⟨z, rfl⟩ := (e.trans eC).surjective s
  rcases z with k | k
  · exact absurd (hS k) hs
  · exact (entry_inr e eA eC x Z P Q a k).trans (by rw [hZ, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply])

theorem eq_add_of_blocks (co : Matrix R C K) (x y : Matrix (Fin n) (Fin n) K) (Z U : Matrix (Fin n) (Fin d) K)
    (P P' : Matrix (Fin p) (Fin p) K) (Q Q' : Matrix (Fin q) (Fin q) K)
    (hZ : (Z.submatrix id fun k => e (.inl k)) = 0) (hU : (U.submatrix id fun k => e (.inr k)) = 0)
    (h₁ : ∀ a k, co (eA a) (eC (e (.inl k))) = (y * (U.submatrix id fun k => e (.inl k)) * P') a k)
    (h₂ : ∀ a k, co (eA a) (eC (e (.inr k))) = (x * (Z.submatrix id fun k => e (.inr k)) * Q) a k) :
    co = reindex eA eC (x * Z * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e P Q) + reindex eA eC (y * U * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e P' Q') := by
  ext r s
  obtain ⟨a, rfl⟩ := eA.surjective r
  obtain ⟨z, rfl⟩ := (e.trans eC).surjective s
  rcases z with k | k
  · rw [Equiv.trans_apply, Matrix.add_apply, entry_inl, entry_inl, h₁, hZ, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.zero_apply, zero_add]
  · rw [Equiv.trans_apply, Matrix.add_apply, entry_inr, entry_inr, h₂, hU, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.zero_apply, add_zero]

end Blocks

section Grid

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T) {i j : Fin D.R.m} (e : Num G i j)
  (w : Pl D.host.E)

theorem colsEq_inl (k : Fin (spV G i j).rank) :
    colsEq t e w (e (.inl k)) = .inl (finCongr (rank_vertex G t w (X := (i, j + 1)) ⟨i.2.le, j.2⟩).symm k) := by
  unfold colsEq
  rw [Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

theorem colsEq_inr (k : Fin (spV₁ G i j).rank) :
    colsEq t e w (e (.inr k)) = .inr (finCongr (rank_vertex G t w (X := (i + 1, j)) ⟨i.2, j.2.le⟩).symm k) := by
  unfold colsEq
  rw [Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

variable (B : Frames G) (κ : D.host.E →+* Kw w) (hinc : ∀ x : D.host.E, cpt w (toEAf D (inclR (AF D.host.F) x)) = κ x)
  (u : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D))
include hinc

theorem mixCoS_inl (a : Fin (spW₁ G i j).rank) (k : Fin (spV G i j).rank) :
    mixCoS B t e w u (finCongr (rankW₁ G t i j w) a) (colsEq t e w (e (.inl k))) =
      ((loc w (B.β i j)).valᵀ * ((spW₁ G i j).gram.map κ)ᵀ *
        ((u.map fun a => cpt w (toEAf D a)).submatrix id fun k => e (.inl k)) *
        (((loc w (B.β i (j + 1)))⁻¹).val)ᵀ) a k := by
  have hx : (mulG (spW₁ G i j) (colV e u)ᵀ).map (fun a => cpt w (toEAf D a)) =
      ((u.map fun a => cpt w (toEAf D a)).submatrix id fun k => e (.inl k))ᵀ * (spW₁ G i j).gram.map κ := by
    ext a b
    simp [mulG, Matrix.mul_apply, map_sum, map_mul, colV, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, hinc]
  have key : ∀ {n p : ℕ} (b : Matrix (Fin p) (Fin p) (Kw w)) (U : Matrix (Fin n) (Fin p) (Kw w))
      (g c : Matrix (Fin n) (Fin n) (Kw w)) (a : Fin n) (k : Fin p), (b * (Uᵀ * g) * c) k a = (cᵀ * gᵀ * U * bᵀ) a k :=
    fun b U g c a k => by
      have : (b * (Uᵀ * g) * c)ᵀ = cᵀ * gᵀ * U * bᵀ := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      exact congrFun₂ this a k
  rw [colsEq_inl, ← key, ← hx]
  rfl

theorem mixCoS_inr (a : Fin (spW₁ G i j).rank) (k : Fin (spV₁ G i j).rank) :
    mixCoS B t e w u (finCongr (rankW₁ G t i j w) a) (colsEq t e w (e (.inr k))) =
      (((loc w (B.β i j))⁻¹).val * ((u.map fun a => cpt w (toEAf D (cA D a))).submatrix id fun k => e (.inr k)) *
        (-((spV₁ G i j).gram.map κ * (loc w (B.β (i + 1) j)).val))) a k := by
  have hx : (adjV₁ e u).map (fun a => cpt w (toEAf D a)) =
      -(((u.map fun a => cpt w (toEAf D (cA D a))).submatrix id fun k => e (.inr k)) * (spV₁ G i j).gram.map κ) := by
    ext a b
    simp [adjV₁, mulG, Matrix.mul_apply, map_sum, map_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM, hinc]
  have key : ∀ {n p : ℕ} (b : Matrix (Fin n) (Fin n) (Kw w)) (U : Matrix (Fin n) (Fin p) (Kw w))
      (g c : Matrix (Fin p) (Fin p) (Kw w)), b * -(U * g) * c = b * U * -(g * c) := fun b U g c => by
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  rw [colsEq_inr, ← key, ← hx]
  rfl

end Grid

end GlobalTheory.FlipMatch.ChartOpp

namespace GlobalTheory.FlipMatch

open ChartOpp

theorem chartOpp_isMixChart : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G) (e : Num G i j) (Bs : Base D.host.F D.host.E)
    (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E), IsTripleOf W M t i j e Bs Γ X →
    ∀ (v : Bs.P) (w : Pl D.host.E), splitPrime (Bs.τ v) = w → ∀ jj : Fv D.host.F v ≃+* Kw w, IsPlaceIso (Bs.τ v) w jj →
    ∀ cc : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Kw w), (Γ.W.bas v).val.map jj * cc.val = basCols B e w →
    ∃ g : GL (Fin (spW₁ G i j).rank) (Kw w),
      IsMixChart v.1 (mixHalfS e (atPl w 1)) (mixHalfS e (cA D (atPl w 1))) (mixCoS B t e w)
        (fun u => chart jj (finCongr (rankW₁ G t i j w)) (colsEq t e w) g cc
          (coY D.sp.cm.sig Γ.V' Γ.W (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u))
        (fun u => (xiAt w)⁻¹ • chart jj (finCongr (rankW₁ G t i j w)) (colsEq t e w) (invT g) (invT cc)
          (coX (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u))
        (Assignment.one.block _ _) := by
  intro D T L sc G μ₀ hL W B t i j M e Bs Γ X h v w hw jj hjj cc hcc
  classical

  have hε : atPl w 1 = GlobalTheory.EmbChart.idem (Bs.τ v) :=
    (GlobalTheory.IdemAtPl.eq_atPl_of_isIdemAt (hw ▸ GlobalTheory.EmbChart.isIdemAt_idem (Bs.τ v))).symm
  have hsum : GlobalTheory.EmbChart.idem (Bs.τ v) + cA D (GlobalTheory.EmbChart.idem (Bs.τ v)) =
      algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v.1 1) := by
    rw [GlobalTheory.EmbChart.cA_idem, GlobalTheory.EmbChart.idem, ← LinearMap.map_add, add_sub_cancel]; rfl
  have hii := GlobalTheory.SrcHalfOne.idem_mul_self (Bs.τ v)
  have hic : GlobalTheory.EmbChart.idem (Bs.τ v) * cA D (GlobalTheory.EmbChart.idem (Bs.τ v)) = 0 :=
    (GlobalTheory.EmbChart.isSplitIdem_idem (Bs.τ v)).2.1
  have hcc' : cA D (GlobalTheory.EmbChart.idem (Bs.τ v)) * cA D (GlobalTheory.EmbChart.idem (Bs.τ v)) =
      cA D (GlobalTheory.EmbChart.idem (Bs.τ v)) := by rw [← map_mul, hii]
  have hb₁ : GlobalTheory.EmbChart.idem (Bs.τ v) * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v.1 1) =
      GlobalTheory.EmbChart.idem (Bs.τ v) := by rw [← hsum, mul_add, hii, hic, add_zero]
  have hb₂ : cA D (GlobalTheory.EmbChart.idem (Bs.τ v)) * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v.1 1) =
      cA D (GlobalTheory.EmbChart.idem (Bs.τ v)) := by
    rw [← hsum, mul_add, mul_comm (cA D _) (GlobalTheory.EmbChart.idem _), hic, zero_add, hcc']
  rw [hε]

  have hzero : cpt w (toEAf D (cA D (GlobalTheory.EmbChart.idem (Bs.τ v)))) = 0 := by
    rw [← hjj]
    exact (congrArg jj (GlobalTheory.SrcHalfOne.piW_cA_idem (Bs.τ v))).trans (map_zero jj)
  have hE : ∀ x : D.host.E, jj (Bs.τ v x) = algebraMap D.host.E (Kw w) x := fun x => by
    rw [← GlobalTheory.FunObj.Good.cpt_incA w x, ← hjj]
    exact congrArg jj (GlobalTheory.LocFrame.piW_incA (Bs.τ v) x).symm
  have hcA : ∀ a, jj (piW ((Bs.τ v).comp D.sp.cm.sig) a) = cpt w (toEAf D (cA D a)) := fun a => by
    rw [← hjj]
    exact congrArg jj (GlobalTheory.SrcHalfOne.piW_cA (Bs.τ v) a).symm

  obtain ⟨κ, hκ⟩ : ∃ κ : D.host.E →+* Kw w, κ = algebraMap D.host.E (Kw w) := ⟨_, rfl⟩
  obtain ⟨Bp, hBp⟩ : ∃ Bp : GL (Fin (spW₁ G i j).rank) (Kw w),
    Bp = Matrix.GeneralLinearGroup.map (jj : Fv D.host.F v.1 →+* Kw w) (Γ.V'.bas v) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Kw w),
    C = Matrix.GeneralLinearGroup.map (jj : Fv D.host.F v.1 →+* Kw w) (Γ.W.bas v) := ⟨_, rfl⟩
  have hG₁ : ((spW₁ G i j).gram.map κ).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero κ).2 (GlobalTheory.RouteCoords.gram_det_ne _)
  have hξ : xiAt w ≠ 0 := (map_ne_zero _).2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hCc : C.val * cc.val = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (loc w (B.β i (j + 1))).val (-(loc w (B.β (i + 1) j)).val) := by
    rw [hC]; exact hcc
  obtain ⟨g, hg⟩ := chart_algebra e Bp C cc _ hG₁ (loc w (B.β i j)) (loc w (B.β i (j + 1))) (loc w (B.β (i + 1) j))
    ((spV G i j).gram.map κ) ((spV₁ G i j).gram.map κ) (xiAt w) hξ hCc
  refine ⟨g, ?_⟩

  have hκm : ∀ {a b : Type} (Z : Matrix a b D.host.E), (Z.map (Bs.τ v)).map jj = Z.map κ := fun Z =>
    Matrix.ext fun _ _ => by rw [hκ]; exact hE _
  have hX : ∀ u, (coX (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u).map jj =
      (Bp⁻¹).val * u.map (fun a => cpt w (toEAf D a)) * ((C⁻¹).val)ᵀ := fun u => by
    unfold coX
    rw [map_mul_equiv, map_mul_equiv, Matrix.transpose_map, Matrix.map_map]
    have : u.map (⇑jj ∘ ⇑(piW (Bs.τ v))) = u.map (fun a => cpt w (toEAf D a)) := Matrix.ext fun _ _ => hjj _
    rw [this, hBp, hC]
    rfl
  have hJ1 : (Γ.V'.J.map (Bs.τ v)).map jj = -((spW₁ G i j).gram.map κ) := by
    rw [hκm, h.JW₁]
    ext a b
    simp
  have hJ2 : ((Γ.W.J.map (Bs.τ v))ᵀ).map jj = xiAt w • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e ((spV G i j).gram.map κ) ((spV₁ G i j).gram.map κ) := by
    rw [Matrix.transpose_map, hκm, h.JWW, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram]
    ext a b
    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk,
      Matrix.reindex_apply, Matrix.submatrix_apply]
    rcases e.symm a with a | a <;> rcases e.symm b with b | b <;> simp [xiAt, hκ]
  have hY : ∀ u, (coY D.sp.cm.sig Γ.V' Γ.W (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u).map jj =
      -(Bp.valᵀ * (-((spW₁ G i j).gram.map κ)) * u.map (fun a => cpt w (toEAf D (cA D a))) *
        (xiAt w • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e ((spV G i j).gram.map κ) ((spV₁ G i j).gram.map κ)) * C.val) := fun u => by
    unfold coY
    rw [Matrix.map_neg _ (map_neg jj), map_mul_equiv, map_mul_equiv, map_mul_equiv, map_mul_equiv, hJ1, hJ2,
      Matrix.map_map]
    have : u.map (⇑jj ∘ ⇑(piW ((Bs.τ v).comp D.sp.cm.sig))) = u.map (fun a => cpt w (toEAf D (cA D a))) :=
      Matrix.ext fun _ _ => hcA _
    rw [this, Matrix.transpose_map, hBp, hC]
    rfl

  have htr : ∀ u, chart jj (finCongr (rankW₁ G t i j w)) (colsEq t e w) g cc
      (coY D.sp.cm.sig Γ.V' Γ.W (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u) =
      reindex (finCongr (rankW₁ G t i j w)) (colsEq t e w) (((loc w (B.β i j))⁻¹).val *
        u.map (fun a => cpt w (toEAf D (cA D a))) *
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e ((spV G i j).gram.map κ * (loc w (B.β i (j + 1))).val)
          (-((spV₁ G i j).gram.map κ * (loc w (B.β (i + 1) j)).val))) := fun u => by
    unfold chart
    rw [hY, (hg 0 _).1]
  have hmu : ∀ u, (xiAt w)⁻¹ • chart jj (finCongr (rankW₁ G t i j w)) (colsEq t e w) (invT g) (invT cc)
      (coX (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u) =
      reindex (finCongr (rankW₁ G t i j w)) (colsEq t e w) ((loc w (B.β i j)).valᵀ * ((spW₁ G i j).gram.map κ)ᵀ *
        u.map (fun a => cpt w (toEAf D a)) *
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (((loc w (B.β i (j + 1)))⁻¹).val)ᵀ (-(((loc w (B.β (i + 1) j))⁻¹).val)ᵀ)) := fun u => by
    unfold chart
    rw [hX, ← (hg (u.map fun a => cpt w (toEAf D a)) 0).2]
    rfl
  have hinc : ∀ x : D.host.E, cpt w (toEAf D (inclR (AF D.host.F) x)) = κ x := fun x => by
    rw [hκ]; exact GlobalTheory.FunObj.Good.cpt_incA w x
  have hPl : ∀ k, colsEq t e w (e (.inl k)) ∈ Assignment.one.block _ _ := fun k => by
    rw [colsEq_inl]; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩
  have hPr : ∀ k, colsEq t e w (e (.inr k)) ∉ Assignment.one.block _ _ := fun k hk => by
    rw [colsEq_inr] at hk; exact Bool.false_ne_true (Finset.mem_filter.1 hk).2

  have z₁ : ∀ z : AE D, GlobalTheory.EmbChart.idem (Bs.τ v) * z = z → cpt w (toEAf D (cA D z)) = 0 := fun z hz => by
    rw [← hz, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, hzero, zero_mul]
  have z₂ : ∀ z : AE D, cA D (GlobalTheory.EmbChart.idem (Bs.τ v)) * z = z → cpt w (toEAf D z) = 0 := fun z hz => by
    rw [← hz, RingHom.map_mul, RingHom.map_mul, hzero, zero_mul]
  have hat : ∀ (u : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) (b b' : AE D),
      b * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v.1 1) = b →
      b' * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v.1 1) = b' →
      IsHalf b (u.submatrix id fun k => e (.inl k)) → IsHalf b' (u.submatrix id fun k => e (.inr k)) →
      At (evFin D.host.F v.1) u := fun u b b' hb hb' h1 h2 c hc => by
    have k1 := GlobalTheory.BigDat.smul_eq_zero_of_isHalf v.1 hb h1 c hc
    have k2 := GlobalTheory.BigDat.smul_eq_zero_of_isHalf v.1 hb' h2 c hc
    refine Matrix.ext fun a s => ?_
    obtain ⟨z, rfl⟩ := e.surjective s
    rcases z with k | k
    · exact congrFun₂ k1 a k
    · exact congrFun₂ k2 a k
  unfold IsMixChart
  simp only [htr, hmu]
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · have h1 : IsHalf (GlobalTheory.EmbChart.idem (Bs.τ v)) (u.submatrix id fun k => e (.inl k)) := fun a c =>
      isHalf_of_mulG _ hu.1 c a
    have h2 := isHalf_cA_of_adjV₁ e hu.2
    have hZ : ((u.map fun a => cpt w (toEAf D (cA D a))).submatrix id fun k => e (.inl k)) = 0 :=
      Matrix.ext fun a k => z₁ _ (h1 a k)
    have hU : ((u.map fun a => cpt w (toEAf D a)).submatrix id fun k => e (.inr k)) = 0 :=
      Matrix.ext fun a k => z₂ _ (h2 a k)
    exact ⟨hat u _ _ hb₁ hb₂ h1 h2, zero_inl e _ _ _ hPr _ _ _ _ hZ, zero_inr e _ _ _ hPl _ _ _ _ hU,
      eq_add_of_blocks e _ _ _ _ _ _ _ _ _ _ _ hZ hU (mixCoS_inl t e w B κ hinc u) (mixCoS_inr t e w B κ hinc u)⟩
  · have h1 : IsHalf (cA D (GlobalTheory.EmbChart.idem (Bs.τ v))) (u.submatrix id fun k => e (.inl k)) := fun a c =>
      isHalf_of_mulG _ hu.1 c a
    have h2 := isHalf_cA_of_adjV₁ e hu.2
    rw [Formalism.L2.Theta.cA_cA] at h2
    have hZ : ((u.map fun a => cpt w (toEAf D (cA D a))).submatrix id fun k => e (.inr k)) = 0 :=
      Matrix.ext fun a k => z₁ _ (h2 a k)
    have hU : ((u.map fun a => cpt w (toEAf D a)).submatrix id fun k => e (.inl k)) = 0 :=
      Matrix.ext fun a k => z₂ _ (h1 a k)
    exact ⟨hat u _ _ hb₂ hb₁ h1 h2, zero_inr e _ _ _ hPl _ _ _ _ hZ, zero_inl e _ _ _ hPr _ _ _ _ hU⟩

end GlobalTheory.FlipMatch
