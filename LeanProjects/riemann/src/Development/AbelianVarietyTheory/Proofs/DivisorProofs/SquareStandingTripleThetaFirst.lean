import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedLagrangianOppositeLagrangianChart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.TopFlip.ChartB

theorem reindex_blocks {K C : Type} [Field K] {n p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (ρ : Fin p ⊕ Fin q ≃ C)
    (x : Matrix (Fin n) (Fin n) K) (Z : Matrix (Fin n) (Fin d) K) (P R : Matrix (Fin p) (Fin p) K)
    (Q S : Matrix (Fin q) (Fin q) K) (r : Fin n) (c : C) :
    (x * (Z.submatrix id (e.symm.trans finSumFinEquiv).symm * GlobalTheory.Doubling.blkMat finSumFinEquiv P Q) *
      GlobalTheory.Doubling.blkMat finSumFinEquiv R (-S)) r ((finSumFinEquiv.symm.trans ρ).symm c) =
    (x * Z * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (P * R) (-(Q * S))) r ((e.symm.trans ρ).symm c) := by
  have h : Z.submatrix id (e.symm.trans finSumFinEquiv).symm * GlobalTheory.Doubling.blkMat finSumFinEquiv P Q *
      GlobalTheory.Doubling.blkMat finSumFinEquiv R (-S) =
      (Z * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (P * R) (-(Q * S))).submatrix id (e.symm.trans finSumFinEquiv).symm := by
    have h1 : GlobalTheory.Doubling.blkMat finSumFinEquiv P Q * GlobalTheory.Doubling.blkMat finSumFinEquiv R (-S) =
        (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (P * R) (-(Q * S))).submatrix (e.symm.trans finSumFinEquiv).symm
          (e.symm.trans finSumFinEquiv).symm := by
      unfold GlobalTheory.Doubling.blkMat GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk
      rw [submatrix_mul_equiv, fromBlocks_multiply]
      ext a b
      simp
    rw [Matrix.mul_assoc, h1, submatrix_mul_equiv]
  rw [Matrix.mul_assoc, h, Matrix.mul_assoc]
  simp [Matrix.mul_apply]

variable {D : D7}

theorem adj_coord (S X : HSp D) (y : Matrix (Fin S.rank) (Fin X.rank) (AE D)) :
    (S.gram⁻¹).map (incA D) * ((HMul.hMul yᵀ (incM S.gram) : Matrix (Fin X.rank) (Fin S.rank) (AE D)).map (cA D))ᵀ =
      y.map (cA D) := by
  have e0 : ((incM S.gram).map (cA D))ᵀ = S.gram.map (incA D) := by
    ext a b
    exact congrArg (incA D) (show star (S.gram b a) = S.gram a b from S.herm.eq (S.frame b) (S.frame a))
  rw [Matrix.map_mul, Matrix.transpose_mul, e0, ← Matrix.mul_assoc, GlobalTheory.RouteCoords.inv_mul_gram, Matrix.one_mul]
  rfl

theorem linB_ptB {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} (B : Frames G) (t : T)
    {i j : Fin D.R.m} (e : Num G i j) (w : Pl D.host.E)
    (u : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    linB B t i j w (ptB e u) =
      reindex (finCongr (rankW₁ G t i j w)) (colsEq t e w) (((loc w (B.β i j))⁻¹).val *
        u.map (fun a => cpt w (toEAf D (cA D a))) *
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e ((spV G i j).gram.map (algebraMap D.host.E (Kw w)) * (loc w (B.β i (j + 1))).val)
          (-((spV₁ G i j).gram.map (algebraMap D.host.E (Kw w)) * (loc w (B.β (i + 1) j)).val))) := by
  have h1 := adj_coord (spW₁ G i j) (spX G i j) (u.submatrix id (e.symm.trans finSumFinEquiv).symm)
  have h2 : (((spX G i j).gram.map (incA D)).map (toEAf D)).map (cpt w) = GlobalTheory.Doubling.blkMat finSumFinEquiv
      ((spV G i j).gram.map (algebraMap D.host.E (Kw w))) ((spV₁ G i j).gram.map (algebraMap D.host.E (Kw w))) := by
    rw [GlobalTheory.Doubling.gram_hsum]
    refine Matrix.ext fun a b => ?_
    refine (GlobalTheory.FunObj.Good.cpt_incA w _).trans ?_
    obtain ⟨a | a, rfl⟩ := finSumFinEquiv.surjective a <;> obtain ⟨b | b, rfl⟩ := finSumFinEquiv.surjective b <;>
      simp [GlobalTheory.Doubling.blkMat, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]
  have h3 : (frX B i j).val.map (cpt w) = GlobalTheory.Doubling.blkMat finSumFinEquiv (loc w (B.β i (j + 1))).val
      (-(loc w (B.β (i + 1) j)).val) := by
    refine Matrix.ext fun a b => ?_
    change cpt w (GlobalTheory.Doubling.blkMat finSumFinEquiv (B.β i (j + 1)).val (-(B.β (i + 1) j).val) a b) = _
    obtain ⟨a | a, rfl⟩ := finSumFinEquiv.surjective a <;> obtain ⟨b | b, rfl⟩ := finSumFinEquiv.surjective b <;>
      simp [GlobalTheory.Doubling.blkMat, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]
  have h4 : (frMapAdj (spW₁ G i j) (spX G i j) (B.β i j) (frX B i j) (ptB e u)).map (cpt w) =
      ((loc w (B.β i j))⁻¹).val * ((u.map (fun a => cpt w (toEAf D (cA D a)))).submatrix id
        (e.symm.trans finSumFinEquiv).symm * GlobalTheory.Doubling.blkMat finSumFinEquiv
      ((spV G i j).gram.map (algebraMap D.host.E (Kw w))) ((spV₁ G i j).gram.map (algebraMap D.host.E (Kw w)))) *
      GlobalTheory.Doubling.blkMat finSumFinEquiv (loc w (B.β i (j + 1))).val (-(loc w (B.β (i + 1) j)).val) := by
    rw [← h2, ← h3]
    unfold frMapAdj
    erw [h1]
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul]
    rfl
  refine Matrix.ext fun r c => ?_
  unfold linB
  rw [h4]
  exact reindex_blocks e _ _ _ _ _ _ _ _ c

open GlobalTheory.FlipMatch.ChartOpp hiding isHalf_of_mulG in

theorem exists_mixChart_linB : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G), SquareStanding G t →
    ∀ (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
      (om : Rep D.sp.cm.sig Γ.V Γ.W) (om' : Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' → IsDoublyCompatible t i j e Bs Γ X →
    ∀ (v : Bs.P) (w : Pl D.host.E), splitPrime (Bs.τ v) = w → ∀ jj : Fv D.host.F v ≃+* Kw w, IsPlaceIso (Bs.τ v) w jj → IsLocIso jj →
    ∀ cc : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Kw w), (Γ.W.bas v).val.map jj * cc.val = basCols B e w →
    ∃ g : GL (Fin (spW₁ G i j).rank) (Kw w),
      IsMixChart v.1 (mixHalfS e (atPl w 1)) (mixHalfS e (cA D (atPl w 1))) (mixCoS B t e w)
        (fun u => chart jj (finCongr (rankW₁ G t i j w)) (colsEq t e w) g cc
          (coY D.sp.cm.sig Γ.V' Γ.W (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u))
        (fun u => (xiAt w)⁻¹ • chart jj (finCongr (rankW₁ G t i j w)) (colsEq t e w) (invT g) (invT cc)
          (coX (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u))
        (Assignment.one.block _ _) ∧
      ∀ u, chart jj (finCongr (rankW₁ G t i j w)) (colsEq t e w) g cc
          (coY D.sp.cm.sig Γ.V' Γ.W (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u) = linB B t i j w (ptB e u) := by
  intro D T L sc G μ₀ _ W B t i j M _ e Bs Γ X _ _ h _ _ v w hw jj hjj _ cc hcc
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
  refine ⟨?_, fun u => by rw [htr, linB_ptB, hκ]⟩
  unfold IsMixChart
  simp only [htr, hmu]
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · have h1 : IsHalf (GlobalTheory.EmbChart.idem (Bs.τ v)) (u.submatrix id fun k => e (.inl k)) := fun a c =>
      GlobalTheory.FlipMatch.ChartOpp.isHalf_of_mulG _ hu.1 c a
    have h2 := isHalf_cA_of_adjV₁ e hu.2
    have hZ : ((u.map fun a => cpt w (toEAf D (cA D a))).submatrix id fun k => e (.inl k)) = 0 :=
      Matrix.ext fun a k => z₁ _ (h1 a k)
    have hU : ((u.map fun a => cpt w (toEAf D a)).submatrix id fun k => e (.inr k)) = 0 :=
      Matrix.ext fun a k => z₂ _ (h2 a k)
    exact ⟨hat u _ _ hb₁ hb₂ h1 h2, zero_inl e _ _ _ hPr _ _ _ _ hZ, zero_inr e _ _ _ hPl _ _ _ _ hU,
      eq_add_of_blocks e _ _ _ _ _ _ _ _ _ _ _ hZ hU (mixCoS_inl t e w B κ hinc u) (mixCoS_inr t e w B κ hinc u)⟩
  · have h1 : IsHalf (cA D (GlobalTheory.EmbChart.idem (Bs.τ v))) (u.submatrix id fun k => e (.inl k)) := fun a c =>
      GlobalTheory.FlipMatch.ChartOpp.isHalf_of_mulG _ hu.1 c a
    have h2 := isHalf_cA_of_adjV₁ e hu.2
    rw [Formalism.L2.Theta.cA_cA] at h2
    have hZ : ((u.map fun a => cpt w (toEAf D (cA D a))).submatrix id fun k => e (.inr k)) = 0 :=
      Matrix.ext fun a k => z₁ _ (h2 a k)
    have hU : ((u.map fun a => cpt w (toEAf D a)).submatrix id fun k => e (.inl k)) = 0 :=
      Matrix.ext fun a k => z₂ _ (h1 a k)
    exact ⟨hat u _ _ hb₂ hb₁ h1 h2, zero_inr e _ _ _ hPl _ _ _ _ hZ, zero_inl e _ _ _ hPr _ _ _ _ hU⟩

end GlobalTheory.TopFlip.ChartB
