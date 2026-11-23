import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DependenceFixed
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

noncomputable section

namespace GlobalTheory.TopFlip.StdLoc

open GlobalTheory.StdPairCone GlobalTheory.LFun GlobalTheory.FunObj.Comparison₂
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

variable {D : D7}

theorem cpt_locIdele (w Q : Pl D.host.E) (y : (Kw w)ˣ) :
    cpt (D := D) Q (toEAf D (locIdele D.host.F w y : AE D)) = (Neutral.B1.finiteSingle D.host.E w (y : Kw w)) Q := by
  rw [GlobalTheory.DepthFix.cpt_eq_finAd]
  exact congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z Q) (finTens_locIdele (F := D.host.F) w y)

def prodId (S : Finset (Pl D.host.E)) (y : ∀ w : S, (Kw w.1)ˣ) : (AE D)ˣ := ∏ w : S, locIdele D.host.F w.1 (y w)

theorem infPart_prodId (S : Finset (Pl D.host.E)) (y : ∀ w : S, (Kw w.1)ˣ) : infPart D (prodId S y : AE D) = 1 := by
  rw [prodId, Units.coe_prod, map_prod]
  exact Finset.prod_eq_one fun w _ => infTens_locIdele (F := D.host.F) w.1 _

theorem cpt_prodId_mem (S : Finset (Pl D.host.E)) (y : ∀ w : S, (Kw w.1)ˣ) (Q : S) :
    cpt (D := D) Q.1 (toEAf D (prodId S y : AE D)) = y Q := by
  classical
  rw [prodId, Units.coe_prod, map_prod, map_prod, Finset.prod_eq_single Q]
  · rw [cpt_locIdele, finSingle_self]
  · intro b _ hb
    rw [cpt_locIdele]
    exact finSingle_ne (fun h => hb (Subtype.ext h.symm)) _
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem cpt_prodId_notMem (S : Finset (Pl D.host.E)) (y : ∀ w : S, (Kw w.1)ˣ) {Q : Pl D.host.E} (hQ : Q ∉ S) :
    cpt (D := D) Q (toEAf D (prodId S y : AE D)) = 1 := by
  rw [prodId, Units.coe_prod, map_prod, map_prod]
  refine Finset.prod_eq_one fun w _ => ?_
  rw [cpt_locIdele]
  exact finSingle_ne (fun h => hQ (by rw [h]; exact w.2)) _

theorem prodId_inv (S : Finset (Pl D.host.E)) (y : ∀ w : S, (Kw w.1)ˣ) : (prodId S y)⁻¹ = prodId S fun w => (y w)⁻¹ := by
  simp only [prodId, map_inv, Finset.prod_inv_distrib]

theorem int_iff (w : Pl D.host.E) (y : Kw w) :
    y ∈ w.adicCompletionIntegers D.host.E ↔ ValuativeRel.valuation (Kw w) y ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).trans (vEq w).le_one_iff_le_one.symm

theorem cpt_twist_mem {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) (z : EAf D) {w : Pl D.host.E} (hw : w ∈ S) :
    cpt (D := D) w (1 - toEAf D e + toEAf D e * z) = cpt (D := D) w z := by
  rw [RingHom.map_add, RingHom.map_sub, RingHom.map_mul, RingHom.map_one, (cpt_idemSum he).2.1 w hw, sub_self, zero_add, one_mul]

theorem cpt_twist_notMem {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) (z : EAf D) {w : Pl D.host.E} (hw : w ∉ S) :
    cpt (D := D) w (1 - toEAf D e + toEAf D e * z) = 1 := by
  rw [RingHom.map_add, RingHom.map_sub, RingHom.map_mul, RingHom.map_one, (cpt_idemSum he).2.2 w hw, sub_zero, zero_mul, add_zero]

theorem cpt_mul_inv (w : Pl D.host.E) (x : (AE D)ˣ) :
    cpt (D := D) w (toEAf D (x : AE D)) * cpt (D := D) w (toEAf D ((x⁻¹ : (AE D)ˣ) : AE D)) = 1 := by
  have h : toEAf D (x : AE D) * toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := by
    rw [← RingHom.map_mul, Units.mul_inv, RingHom.map_one]
  rw [← RingHom.map_mul, h, RingHom.map_one]

theorem unit_of_isUnitDet {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) {k : ℕ}
    {N : Matrix (Fin k) (Fin k) (EAf D)} {x : (AE D)ˣ} (hx : IsUnitDet e N x) {w : Pl D.host.E} (hw : w ∈ S)
    (hN : ValuativeRel.valuation (Kw w) (cpt (D := D) w N.det) ≤ 1) :
    cpt (D := D) w N.det ≠ 0 ∧ ValuativeRel.valuation (Kw w) (cpt (D := D) w N.det) = 1 := by
  obtain ⟨-, h2, h3⟩ := hx
  have h4 := (int_iff w _).1 ((mem_OA_iff _).1 h3 w)
  have h5 := cpt_mul_inv w x
  rw [h2, cpt_twist_mem he _ hw] at h5
  refine ⟨left_ne_zero_of_mul_eq_one h5, le_antisymm hN ?_⟩
  have h6 := congrArg (ValuativeRel.valuation (Kw w)) h5
  rw [map_mul, map_one] at h6
  exact h6.ge.trans (mul_le_of_le_one_right' h4)

theorem unitChar_eq_prod (ν : (AE D)ˣ →* Circle) {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) {k : ℕ}
    (N : Matrix (Fin k) (Fin k) (EAf D)) (hN : ∀ w ∈ S, ValuativeRel.valuation (Kw w) (cpt (D := D) w N.det) ≤ 1) :
    unitChar ν e N = ∏ w ∈ S, unitInd (locChar ν w) (cpt (D := D) w N.det) := by
  classical
  by_cases h : ∀ w ∈ S, cpt (D := D) w N.det ≠ 0 ∧ ValuativeRel.valuation (Kw w) (cpt (D := D) w N.det) = 1
  · let y : ∀ w : S, (Kw w.1)ˣ := fun w => Units.mk0 _ (h w.1 w.2).1
    have k1 : ∀ Q, cpt (D := D) Q (toEAf D (prodId S y : AE D)) = cpt (D := D) Q (1 - toEAf D e + toEAf D e * N.det) :=
      fun Q => by
        by_cases hQ : Q ∈ S
        · exact (cpt_prodId_mem S y ⟨Q, hQ⟩).trans (cpt_twist_mem he _ hQ).symm
        · exact (cpt_prodId_notMem S y hQ).trans (cpt_twist_notMem he _ hQ).symm
    have hx : ∃ x, IsUnitDet e N x := by
      refine ⟨prodId S y, infPart_prodId S y, cpt_ext k1, (mem_OA_iff _).2 fun Q => ?_⟩
      rw [prodId_inv]
      by_cases hQ : Q ∈ S
      · rw [cpt_prodId_mem S _ ⟨Q, hQ⟩, int_iff, Units.val_inv_eq_inv_val, map_inv₀]
        exact le_of_eq (inv_eq_one.2 (h Q hQ).2)
      · rw [cpt_prodId_notMem S _ hQ]
        exact one_mem _
    have hc : hx.choose = prodId S y := Units.ext (GlobalTheory.FunObj.ae_ext (hx.choose_spec.1.trans (infPart_prodId S y).symm)
      fun Q => by rw [hx.choose_spec.2.1, k1])
    rw [unitChar, dif_pos hx, hc, ← Finset.prod_coe_sort, prodId, map_prod, ← Finset.prod_inv_distrib]
    refine (map_prod Circle.coeHom _ _).trans (Finset.prod_congr rfl fun w _ => ?_)
    rw [unitInd, dif_pos (h w.1 w.2)]
    rfl
  · rw [unitChar, dif_neg fun ⟨x, hx⟩ => h fun w hw => unit_of_isUnitDet he hx hw (hN w hw)]
    push Not at h
    obtain ⟨w, hw, h⟩ := h
    exact (Finset.prod_eq_zero hw (by rw [unitInd, dif_neg fun h' => h h'.1 h'.2])).symm

theorem mem_cball_iff (w : Pl D.host.E) (c : ℕ) (y : Kw w) :
    y ∈ cball (unifAt w ^ c) ↔ Valued.v y ≤ WithZero.exp (-(c : ℤ)) := by
  have h : Valued.v (unifAt w : Kw w) = WithZero.exp (-1 : ℤ) := Formalism.L2.Host.unif_spec w
  refine (vEq w _ _).trans ?_
  rw [Units.val_pow_eq_pow_val, map_pow, h, ← WithZero.exp_nsmul]
  simp

theorem inId_iff (S : Finset (Pl D.host.E)) (c : Pl D.host.E → ℕ) {z : EAf D} (hz : z ∈ OA D) :
    InId (∏ w ∈ S, w.asIdeal ^ c w) z ↔ ∀ w ∈ S, cpt (D := D) w z ∈ cball (unifAt w ^ c w) := by
  have h : ∏ w ∈ S, w.asIdeal ^ c w = S.inf fun w => w.asIdeal ^ c w :=
    (HeightOneSpectrum.inf_pow_eq_prod S c (fun w => w) fun _ _ _ _ hne => hne).symm
  have h0 : ∏ w ∈ S, w.asIdeal ^ c w ≠ ⊥ := Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot
  simp only [mem_cball_iff]
  constructor
  · rintro ⟨h1, h2⟩ w hw
    exact v_le_of_mem_idS (s := ⟨z, h1⟩) (h.le.trans (Finset.inf_le hw)) h2
  · intro H
    exact ⟨hz, mem_idS_of_v_le (w := fun w => w) h0 h (s := ⟨z, hz⟩) H⟩

open Classical in

theorem stdA_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ν : kˣ →* ℂˣ) (ϖ : kˣ) (hϖ : ValuativeRel.valuation k (ϖ : k) ≤ 1) (c : ℕ) {a b a₁ a₂ : ℕ} (ha : a = a₁) (hb : b = a₁ + a₂)
    (N : Matrix (Fin b) (Fin a) k) (M : Matrix (Fin a₁) (Fin (a₁ + a₂)) k)
    (hM : ∀ r s, M r s = N (Fin.cast hb.symm s) (Fin.cast ha.symm r)) :
    stdA ν ϖ c a₁ a₂ M =
      if (∀ i j, ValuativeRel.valuation k (N i j) ≤ 1) ∧ ∀ i j, a ≤ i.1 → N i j ∈ cball (ϖ ^ c) then
        unitInd ν (topL a N).det else 0 := by
  subst ha hb
  have hM' : ∀ r s, M r s = N s r := hM
  have e1 : blk₁ M = (topL a N)ᵀ := by
    ext r s
    rw [blk₁, of_apply, hM', transpose_apply, topL, dif_pos ⟨by omega, r.2⟩]
    rfl
  have e2 : (blk₁ M).det = (topL a N).det := by rw [e1, det_transpose]
  have e3 : (∀ i j, blk₂ M i j ∈ cball (ϖ ^ c)) ↔ ∀ i j, a ≤ i.1 → N i j ∈ cball (ϖ ^ c) := by
    refine ⟨fun H i j hi => ?_, fun H i j => ?_⟩
    · have := H j ⟨i.1 - a, by omega⟩
      rw [blk₂, of_apply, hM'] at this
      convert this using 2
      ext
      simp only [Fin.natAdd_mk]
      omega
    · rw [blk₂, of_apply, hM']
      exact H _ _ (by simp)
  have e4 : ∀ y ∈ cball (ϖ ^ c), ValuativeRel.valuation k y ≤ 1 := fun y hy => by
    refine le_trans (show ValuativeRel.valuation k y ≤ ValuativeRel.valuation k ((ϖ ^ c : kˣ) : k) from hy) ?_
    rw [Units.val_pow_eq_pow_val, map_pow]
    exact pow_le_one' hϖ c
  unfold stdA
  split_ifs with h1 h2 h2
  · rw [unitInd, dif_pos ⟨e2 ▸ h1.1, e2 ▸ h1.2.1.2⟩]
    simp only [e2]
  · refine absurd ⟨fun i j => ?_, e3.1 h1.2.2⟩ h2
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [← hM']
      exact h1.2.1.1 j i
    · exact e4 _ (e3.1 h1.2.2 _ _ (by simp))
  · rw [unitInd, dif_neg]
    intro h3
    refine h1 ⟨e2 ▸ h3.1, ⟨fun i j => ?_, e2 ▸ h3.2⟩, e3.2 h2.2⟩
    rw [blk₁, of_apply, hM']
    exact h2.1 _ _
  · rfl

theorem valuation_det_le {k : Type} [Field k] [ValuativeRel k] {n : ℕ} {M : Matrix (Fin n) (Fin n) k}
    (h : ∀ i j, ValuativeRel.valuation k (M i j) ≤ 1) : ValuativeRel.valuation k M.det ≤ 1 := by
  let A : Matrix (Fin n) (Fin n) (ValuativeRel.valuation k).integer := fun i j => ⟨M i j, h i j⟩
  have e : M.det = ((A.det : (ValuativeRel.valuation k).integer) : k) :=
    (RingHom.map_det (ValuativeRel.valuation k).integer.subtype A).symm
  rw [e]
  exact A.det.2

theorem topL_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') {b a : ℕ} (n : ℕ) (N : Matrix (Fin b) (Fin a) R) :
    f (topL n N).det = (topL n (N.map f)).det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, map_apply, topL]
  split_ifs
  · rfl
  · exact map_zero f

theorem valuation_unifAt_le (w : Pl D.host.E) : ValuativeRel.valuation (Kw w) (unifAt w : Kw w) ≤ 1 := by
  have h : Valued.v (unifAt w : Kw w) = WithZero.exp (-1 : ℤ) := Formalism.L2.Host.unif_spec w
  rw [(vEq w).le_one_iff_le_one, h, ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

open Classical in

theorem std_eq_prod (ν : (AE D)ˣ →* Circle) {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) (c : Pl D.host.E → ℕ)
    {a b : ℕ} (N : Matrix (Fin b) (Fin a) (EAf D)) (h0 : ∀ w ∉ S, ∀ i j, cpt (D := D) w (N i j) = 0) :
    (if IsIntM N ∧ ∀ i j, a ≤ i.1 → InId (∏ w ∈ S, w.asIdeal ^ c w) (N i j) then unitChar ν e (topL a N) else 0) =
      ∏ w ∈ S, if (∀ i j, ValuativeRel.valuation (Kw w) (N.map (cpt (D := D) w) i j) ≤ 1) ∧
          ∀ i j, a ≤ i.1 → N.map (cpt (D := D) w) i j ∈ cball (unifAt w ^ c w) then
        unitInd (locChar ν w) (topL a (N.map (cpt (D := D) w))).det else 0 := by
  have e1 : IsIntM N ↔ ∀ w ∈ S, ∀ i j, ValuativeRel.valuation (Kw w) (cpt (D := D) w (N i j)) ≤ 1 := by
    refine ⟨fun H w _ i j => (int_iff w _).1 ((mem_OA_iff _).1 (H i j) w), fun H i j => (mem_OA_iff _).2 fun w => ?_⟩
    by_cases hw : w ∈ S
    · exact (int_iff w _).2 (H w hw i j)
    · rw [h0 w hw]
      exact zero_mem _
  rw [Finset.prod_ite_zero]
  split_ifs with h1 h2 h2
  · rw [unitChar_eq_prod ν he _ fun w hw => ?_]
    · exact Finset.prod_congr rfl fun w _ => by rw [topL_map]
    · rw [topL_map]
      refine valuation_det_le fun i j => ?_
      unfold topL
      split_ifs
      · exact (h2 w hw).1 _ _
      · rw [map_zero]
        exact zero_le_one
  · exact absurd (fun w hw => ⟨e1.1 h1.1 w hw, fun i j hi => (inId_iff S c (h1.1 i j)).1 (h1.2 i j hi) w hw⟩) h2
  · have h3 := e1.2 fun w hw => (h2 w hw).1
    exact absurd ⟨h3, fun i j hi => (inId_iff S c (h3 i j)).2 fun w hw => (h2 w hw).2 i j hi⟩ h1
  · rfl

theorem cpt_frMapO_eq_zero {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S) (A WW : HSp D)
    (βA : GL (Fin A.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)) {x : WO A WW} (hx : IsHalf e x) {w : Pl D.host.E} (hw : w ∉ S)
    (i : Fin WW.rank) (j : Fin A.rank) : cpt (D := D) w (frMapO A WW βA βW x i j) = 0 := by
  have h : ((x : Matrix (Fin WW.rank) (Fin A.rank) (AE D)).map (toEAf D)).map (cpt (D := D) w) = 0 := by
    refine Matrix.ext fun r s => ?_
    change cpt (D := D) w (toEAf D (x r s)) = 0
    rw [← hx r s, RingHom.map_mul, RingHom.map_mul, (cpt_idemSum he).2.2 w hw, zero_mul]
  change (frMapO A WW βA βW x).map (cpt (D := D) w) i j = 0
  rw [frMapO, Matrix.map_mul, Matrix.map_mul, h, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply]

theorem change_eq {k : Type} [Field k] {a d a' d' : Type} [Fintype a] [DecidableEq a] [Fintype d] [DecidableEq d]
    [Fintype a'] [DecidableEq a'] [Fintype d'] [DecidableEq d'] (ea : a ≃ a') (ed : d ≃ d') (β β' : GL a k) (γ γ' : GL d k)
    (x : Matrix d a k) :
    (GlobalTheory.StepData.reGL ea (invT (β⁻¹ * β'))).val * reindex ea ed ((γ'⁻¹).val * x * β'.val)ᵀ *
      (invT (GlobalTheory.StepData.reGL ed (γ'⁻¹ * γ))).val = reindex ea ed ((γ⁻¹).val * x * β.val)ᵀ := by
  have h1 : (invT (GlobalTheory.StepData.reGL ed (γ'⁻¹ * γ))).val = (((γ⁻¹ * γ').val)ᵀ).submatrix ed.symm ed.symm := by
    change ((GlobalTheory.StepData.reGL ed (γ'⁻¹ * γ))⁻¹).valᵀ = _
    rw [← map_inv, GlobalTheory.StepData.reGL_val, _root_.mul_inv_rev, inv_inv, transpose_submatrix]
  have h2 : (invT (β⁻¹ * β')).val = ((β'⁻¹ * β).val)ᵀ := by
    change ((β⁻¹ * β')⁻¹).valᵀ = _
    rw [_root_.mul_inv_rev, inv_inv]
  rw [h1, GlobalTheory.StepData.reGL_val, h2, reindex_apply, reindex_apply, submatrix_mul_equiv, submatrix_mul_equiv, ← transpose_mul,
    ← transpose_mul]
  congr 2
  simp only [Units.val_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc β'.val, ← Matrix.mul_assoc γ'.val, Units.mul_inv, Units.mul_inv, Matrix.one_mul, Matrix.one_mul]

variable {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc}

theorem locChar_nu {μ₀ : T} (hL : L.Is μ₀) (t : T) (i j : Fin D.R.m) (w : Pl D.host.E) :
    locChar (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) w = (locGrid G t w).nu i j := by
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j = G.nu t i (j + 1) :=
    mul_div_mul_right_eq_div _ _ _
  rw [e1, locChar_eq_of_chrEq (SqNum.chrEq_nu G t i j hL)]
  have hj : (j : ℕ) < D.R.m := j.2
  ext x
  simp only [SqNum.nuH, Grid.nu, locGrid, muBase, dif_pos hj, MonoidHom.div_apply, Formalism.L2.Host.HChar.loc_mul,
    Formalism.L2.Host.HChar.loc_inv, div_eq_mul_inv]
  rfl

theorem ordX_colX_val (t : T) (i j : Fin D.R.m) (w : Pl D.host.E) (s : Fin (spX G i j).rank) :
    (ordX G t i j w (colX G t i j w s)).val = s.val := by
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective s
  simp only [ordX, colX, SplitFlip.stdSplit, Equiv.trans_apply, Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
    Equiv.symm_apply_apply]
  rcases s with s | s
  · rfl
  · simp only [Equiv.sumCongr_apply, Sum.map_inr, finSumFinEquiv_apply_right, finCongr_symm, finCongr_apply, Fin.val_cast,
      Fin.val_natAdd]
    congr 1
    exact rank_vertex G t w (X := (i, j + 1)) ⟨i.2.le, j.2⟩

end GlobalTheory.TopFlip.StdLoc

namespace GlobalTheory.TopFlip

open GlobalTheory.TopFlip.StdLoc

theorem stdFst_eq_prodA : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (B : Frames G) (t : T) (i j : Fin D.R.m) (X : TriG G i j) (ε : AE D), IsIdemSum ε (locPl G t) →
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) ε (X.ideal (locPl G) t)
        (spW G i j) (spX G i j) X.rA.β X.rW.β = prodA B t i j ε (locFst B t X) := by
  intro D T L sc G μ₀ hL B t i j X ε he
  classical
  funext x
  unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst prodA
  by_cases hx : IsHalf ε x
  · simp only [hx, true_and, if_true]
    refine (std_eq_prod _ he (X.c t) _ fun w hw => cpt_frMapO_eq_zero he _ _ _ _ hx hw).trans
      (Finset.prod_congr rfl fun w _ => ?_)
    have hb : (spX G i j).rank = (locGrid G t w).rank (i + 1, j + 1) + (locGrid G t w).rank (i, j) := by
      simpa using Fintype.card_congr ((colX G t i j w).trans (ordX G t i j w))
    rw [locChar_nu hL]
    refine (stdA_eq _ _ (valuation_unifAt_le w) _ (rankW G t i j w) hb _ _ fun r s => ?_).symm
    have h1 := change_eq (finCongr (rankW G t i j w)) (colX G t i j w) (loc w X.rA.β) (loc w (B.β (i + 1) (j + 1)))
      (loc w X.rW.β) (loc w (frX B i j))
      (((x : Matrix (Fin (spX G i j).rank) (Fin (spW G i j).rank) (AE D)).map (toEAf D)).map (cpt (D := D) w))
    have h2 : ∀ (β : GL (Fin (spW G i j).rank) (EAf D)) (γ : GL (Fin (spX G i j).rank) (EAf D)),
        (frMapO (spW G i j) (spX G i j) β γ x).map (cpt (D := D) w) = ((loc w γ)⁻¹).val *
          ((x : Matrix (Fin (spX G i j).rank) (Fin (spW G i j).rank) (AE D)).map (toEAf D)).map (cpt (D := D) w) *
            (loc w β).val := fun β γ => by
      rw [frMapO, Matrix.map_mul, Matrix.map_mul, ← map_inv]
      rfl
    rw [← h2, ← h2] at h1
    have h3 : (chA B t X w).val * linA B t i j w x * (invT (chX B t X w)).val = _ := h1
    rw [h3]
    have h4 : (colX G t i j w).symm ((ordX G t i j w).symm s) = Fin.cast hb.symm s := by
      refine Fin.ext ((ordX_colX_val t i j w _).symm.trans ?_)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      rfl
    simp only [reindex_apply, submatrix_apply, transpose_apply, h4]
    rfl
  · rw [if_neg hx, if_neg fun h => hx h.1]

end GlobalTheory.TopFlip

end
