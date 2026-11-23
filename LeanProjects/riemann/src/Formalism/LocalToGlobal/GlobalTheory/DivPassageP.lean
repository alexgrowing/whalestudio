import Formalism.LocalToGlobal.GlobalTheory.DivPassage
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Transfer
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.MapScale
import Lemmata.GeneralBFactThirdAlt.Imports

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.DivPassage

open Formalism.L2.Indef

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K]

theorem ok_smul_eq {n : ℕ} (c : 𝓞 K) (x : Fin n → K) : c • x = (algebraMap (𝓞 K) K c) • x :=
  (algebraMap_smul K c x).symm

theorem exists_smul_mem {n : ℕ} (R : Submodule (𝓞 K) (Fin n → K)) (x : Fin n → K)
    (hx : x ∈ Submodule.span K (R : Set (Fin n → K))) : ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ R := by
  first | exact Bl.general_b_fact_third_alt.goal1 .. | (apply Bl.general_b_fact_third_alt.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_third_alt.goal1 <;> assumption)

namespace LevelAmb

variable [StarRing K] {D0 D1 : ℕ} (A : LevelAmb K D0 D1)

theorem partLat_le (e : Matrix (Fin A.Dg) (Fin A.Dg) K) : A.partLat e ≤ A.Rg := inf_le_left

theorem mem_range_of_partLat {e : Matrix (Fin A.Dg) (Fin A.Dg) K} {y : Fin A.Dg → K} (hy : y ∈ A.partLat e) :
    y ∈ LinearMap.range e.mulVecLin := hy.2

theorem span_partLat (hL : A.LatG) (e : Matrix (Fin A.Dg) (Fin A.Dg) K) :
    Submodule.span K (A.partLat e : Set (Fin A.Dg → K)) = LinearMap.range e.mulVecLin := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro y hy
    exact hy.2
  · intro w hw
    have hw' : w ∈ Submodule.span K (A.Rg : Set (Fin A.Dg → K)) := by
      rw [hL.span_eq_top]; exact Submodule.mem_top
    obtain ⟨d, hd, hm⟩ := exists_smul_mem A.Rg w hw'
    have hdK : algebraMap (𝓞 K) K d ≠ 0 := by
      rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective (𝓞 K) K)]; exact hd
    have hmem : d • w ∈ A.partLat e := by
      refine ⟨hm, ?_⟩
      show d • w ∈ LinearMap.range e.mulVecLin
      rw [ok_smul_eq]
      exact Submodule.smul_mem _ _ hw
    have : w = (algebraMap (𝓞 K) K d)⁻¹ • (d • w) := by
      rw [ok_smul_eq, smul_smul, inv_mul_cancel₀ hdK, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem partLat_fg (hL : A.LatG) (e : Matrix (Fin A.Dg) (Fin A.Dg) K) : (A.partLat e).FG := by
  have : IsNoetherian (𝓞 K) A.Rg := isNoetherian_of_fg_of_noetherian A.Rg hL.fg
  exact Submodule.FG.of_le_of_isNoetherian (A.partLat_le e)

theorem nat_smul_ne_zero {n : ℕ} {h : ℕ} (hh : 0 < h) {y : Fin n → K} (hy : y ≠ 0) : (h : 𝓞 K) • y ≠ 0 := by
  rw [Nat.cast_smul_eq_nsmul]
  exact smul_ne_zero (Nat.pos_iff_ne_zero.mp hh) hy

theorem frame_scale_unit (h : ℕ) (hh : 0 < h) (hF : A.FramesG) (v : InfinitePlace K) :
    IsUnit ((Formalism.BranchingDeterminantCap.scaleFrame (Real.sqrt h) A.Xg) v).det := by
  unfold Formalism.BranchingDeterminantCap.scaleFrame
  rw [Matrix.det_smul]
  refine IsUnit.mul ?_ (hF v)
  refine IsUnit.pow _ (isUnit_iff_ne_zero.mpr ?_)
  have : (0 : ℝ) < Real.sqrt h := Real.sqrt_pos.mpr (by exact_mod_cast hh)
  exact_mod_cast this.ne'

theorem levelFacts [IsTotallyComplex K] {D : ℕ} (ι : Matrix (Fin A.Dg) (Fin D) K) (ep : Matrix (Fin A.Dg) (Fin A.Dg) K)
    (h : ℕ) (XE : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ) (RR : Submodule (𝓞 K) (Fin D → K))
    (hF : A.FramesG) (hL : A.LatG) (hE : A.EmbAt ι ep h XE) (hS : A.SandAt ι ep h RR) (hh : 0 < h)
    (hne : A.partLat ep ≠ ⊥) :
    A.img ι RR ≠ ⊥ ∧
    Formalism.HN.muDef (Pi.basisFun K (Fin D)) XE RR =
      Formalism.HN.muDef (Pi.basisFun K (Fin A.Dg)) (Formalism.BranchingDeterminantCap.scaleFrame (Real.sqrt h) A.Xg) (A.img ι RR) ∧
    Formalism.HN.muMaxDef (Pi.basisFun K (Fin D)) XE RR =
      Formalism.HN.muMaxDef (Pi.basisFun K (Fin A.Dg)) (Formalism.BranchingDeterminantCap.scaleFrame (Real.sqrt h) A.Xg) (A.img ι RR) ∧
    Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame XE) (Formalism.HN.dualLat RR) =
      - Formalism.HN.muDef (Pi.basisFun K (Fin D)) XE RR := by
  obtain ⟨hinj, hrange, hmaj⟩ := hE
  obtain ⟨hle, hsm⟩ := hS

  have himg : A.img ι RR ≠ ⊥ := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    intro hb
    have := hsm y hy
    rw [hb, Submodule.mem_bot] at this
    exact nat_smul_ne_zero hh hy0 this

  have hfgI : (A.img ι RR).FG := by
    have : IsNoetherian (𝓞 K) A.Rg := isNoetherian_of_fg_of_noetherian A.Rg hL.fg
    exact Submodule.FG.of_le_of_isNoetherian (le_trans hle (A.partLat_le ep))
  have hinj' : Function.Injective (ι.mulVecLin.restrictScalars (𝓞 K)) := hinj
  have hfg : RR.FG := Submodule.fg_of_fg_map_injective _ hinj' hfgI

  have hspan : Submodule.span K (RR : Set (Fin D → K)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have h1 : ι *ᵥ x ∈ Submodule.span K (A.partLat ep : Set (Fin A.Dg → K)) := by
      rw [A.span_partLat hL ep, ← hrange]; exact ⟨x, rfl⟩
    have h2 : Submodule.span K (A.partLat ep : Set (Fin A.Dg → K)) ≤
        Submodule.span K (A.img ι RR : Set (Fin A.Dg → K)) := by
      rw [Submodule.span_le]
      intro y hy
      have hyy := hsm y hy
      have hhK : (h : K) ≠ 0 := by exact_mod_cast hh.ne'
      have : y = (h : K)⁻¹ • ((h : 𝓞 K) • y) := by
        rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hhK, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hyy)
    have h3 := h2 h1
    have himgset : (A.img ι RR : Set (Fin A.Dg → K)) = ι.mulVecLin '' (RR : Set (Fin D → K)) := by
      unfold img; rw [Submodule.map_coe]; rfl
    rw [himgset, Submodule.span_image] at h3
    obtain ⟨z, hz, hzx⟩ := h3
    have : z = x := hinj hzx
    rw [← this]; exact hz

  let B : Formalism.BasicNotions.HLat K :=
    { V := Fin A.Dg → K, ι := Fin A.Dg, b := Pi.basisFun K (Fin A.Dg),
      X := Formalism.BranchingDeterminantCap.scaleFrame (Real.sqrt h) A.Xg, L := ⊥ }
  let C : Formalism.BasicNotions.HLat K :=
    { V := Fin D → K, ι := Fin D, b := Pi.basisFun K (Fin D), X := XE, L := RR }
  have hB : HLatOps.FrameOK B := A.frame_scale_unit h hh hF
  have hn : ∀ v x, Formalism.HermitianLatticesTheory.normAt C.b C.X v x = Formalism.HermitianLatticesTheory.normAt B.b B.X v (ι.mulVecLin x) := by
    intro v x
    rw [HLatOps.normAt_eq_sqrt, HLatOps.normAt_eq_sqrt]
    show Real.sqrt (Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin D)) XE v x x).re =
      Real.sqrt (Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin A.Dg)) (Formalism.BranchingDeterminantCap.scaleFrame (Real.sqrt h) A.Xg) v
        (ι *ᵥ x) (ι *ᵥ x)).re
    rw [hmaj v x x]
  obtain ⟨hCf, hnum⟩ := HLatOps.emb_numbers K C B ι.mulVecLin hB hinj hn
  obtain ⟨-, hnum2⟩ := hnum RR
  obtain ⟨hmu, hmax, _hmin, _hlcv⟩ := hnum2 hfg

  have hgood : C.Good := ⟨hCf, hfg, hspan⟩
  have hrk : 0 < C.rank := by
    show 0 < Formalism.HN.rkK RR
    unfold Formalism.HN.rkK
    rw [hspan, finrank_top, Module.finrank_fin_fun]
    rcases Nat.eq_zero_or_pos D with hD | hD
    · exfalso
      subst hD
      apply himg
      rw [eq_bot_iff]
      rintro y ⟨x, -, rfl⟩
      have : x = 0 := Subsingleton.elim _ _
      rw [this, map_zero]; exact Submodule.zero_mem _
    · exact hD
  obtain ⟨hdual, -, -⟩ := HLatOps.dual_numbers K C hgood hrk
  exact ⟨himg, hmu, hmax, hdual⟩

end LevelAmb

end SlopeTestRemainingChoices

theorem passage_from_levels : PassageFromLevels := by
  intro K _ _ _ _ Bs Df0 Df1 N S0 S1 A hFr hLat hE0 hE1 hS0 hS1 hSz hRk hD0 hD1 hMx hMu hRows
  obtain ⟨h0p, h0G, h1p, h1G, hla⟩ := hSz
  obtain ⟨hne0, hne1⟩ := hRows
  obtain ⟨hI0, hmu0, hmax0, hdual0⟩ :=
    A.levelFacts A.ι0 A.ep0 A.h0 S0.XE S0.RR hFr hLat hE0 hS0 h0p hne0
  obtain ⟨hI1, hmu1, hmax1, hdual1⟩ :=
    A.levelFacts A.ι1 A.ep1 A.h1 S1.XE S1.RR hFr hLat hE1 hS1 h1p hne1
  have hfg0 : A.latticeAtBaseLevel.FG := A.partLat_fg hLat A.ep0
  have hfg1 : A.latticeAtSharpLevel.FG := A.partLat_fg hLat A.ep1

  have hG1 : (1 : ℝ) ≤ (A.G : ℝ) := by exact_mod_cast le_trans h0p h0G
  have hlogG : 0 ≤ Real.log A.G := Real.log_nonneg hG1
  have hlog0 : Real.log A.h0 ≤ Real.log A.G :=
    Real.log_le_log (by exact_mod_cast h0p) (by exact_mod_cast h0G)
  have hlog1 : Real.log A.h1 ≤ Real.log A.G :=
    Real.log_le_log (by exact_mod_cast h1p) (by exact_mod_cast h1G)

  have hLC0 := Formalism.BranchingDeterminantCap.levelCompare_statement K (Fin A.Dg → K) (Fin A.Dg) (Pi.basisFun K (Fin A.Dg)) A.Xg hFr
    A.latticeAtBaseLevel (A.img A.ι0 S0.RR) A.h0 hfg0 hI0 h0p hS0.1 hS0.2
  have hLC1 := Formalism.BranchingDeterminantCap.levelCompare_statement K (Fin A.Dg → K) (Fin A.Dg) (Pi.basisFun K (Fin A.Dg)) A.Xg hFr
    A.latticeAtSharpLevel (A.img A.ι1 S1.RR) A.h1 hfg1 hI1 h1p hS1.1 hS1.2
  unfold Passage
  intro hde0 hde3 HH0 hHH
  have hmaxRR0 : S0.muMaxRR = Formalism.HN.muMaxDef (Pi.basisFun K (Fin A.Dg))
      (Formalism.BranchingDeterminantCap.scaleFrame (Real.sqrt A.h0) A.Xg) (A.img A.ι0 S0.RR) := hmax0
  have hmaxRR1 : S1.muMaxRR = Formalism.HN.muMaxDef (Pi.basisFun K (Fin A.Dg))
      (Formalism.BranchingDeterminantCap.scaleFrame (Real.sqrt A.h1) A.Xg) (A.img A.ι1 S1.RR) := hmax1
  have hcc0 : S0.muCC = - Formalism.HN.muDef (Pi.basisFun K (Fin A.Dg))
      (Formalism.BranchingDeterminantCap.scaleFrame (Real.sqrt A.h0) A.Xg) (A.img A.ι0 S0.RR) := by
    show Formalism.HN.muDef _ _ _ = _
    rw [hdual0, hmu0]
  have hcc1 : S1.muCC = - Formalism.HN.muDef (Pi.basisFun K (Fin A.Dg))
      (Formalism.BranchingDeterminantCap.scaleFrame (Real.sqrt A.h1) A.Xg) (A.img A.ι1 S1.RR) := by
    show Formalism.HN.muDef _ _ _ = _
    rw [hdual1, hmu1]
  constructor
  ·
    have a1 := (abs_le.mp hLC1.2).2
    have a0 := (abs_le.mp hLC0.2).1
    unfold LevelAmb.MaxT at hMx
    unfold LevelAmb.latticeAtBaseLevel LevelAmb.latticeAtSharpLevel at *
    rw [hmaxRR1]
    rw [hmaxRR0] at hHH
    nlinarith
  ·
    have hRs : ∀ s, A.Rs s ≤ A.latticeAtBaseLevel := by
      intro s y hy
      refine ⟨hy.1, ?_⟩
      obtain ⟨x, hx⟩ := hy.2
      refine ⟨A.es s *ᵥ x, ?_⟩
      show A.ep0 *ᵥ (A.es s *ᵥ x) = y
      rw [Matrix.mulVec_mulVec]; exact hx
    obtain ⟨hr0, hr1⟩ := hRk
    have hr0' : (Formalism.HN.rkK A.latticeAtBaseLevel : ℝ) = ∑ s, (Formalism.HN.rkK (A.Rs s) : ℝ) := by rw [hr0]; push_cast; rfl
    have hr1' : (Formalism.HN.rkK A.latticeAtSharpLevel : ℝ) = ∑ s, (A.nS s : ℝ) * (Formalism.HN.rkK (A.Rs s) : ℝ) := by
      rw [hr1]; push_cast; rfl
    have hP := Formalism.BranchingDeterminantCap.passageLat_of Formalism.BranchingDeterminantCap.levelCompare_statement K (Fin A.Dg → K) (Fin A.Dg)
      (Pi.basisFun K (Fin A.Dg)) A.Xg hFr A.S A.Rs A.nS A.latticeAtBaseLevel A.latticeAtSharpLevel (A.img A.ι0 S0.RR) (A.img A.ι1 S1.RR)
      A.G A.h0 A.h1 A.nbar N.de HH0 hfg0 hfg1 hI0 hI1 h0p h0G h1p h1G hS0.1 hS0.2 hS1.1 hS1.2 hRs hr0' hr1'
      hD1 hD0 hMu.1 hde0 hde3 hMu.2 (hmaxRR0 ▸ hHH)
    rw [hcc0, hcc1]
    have hb : 3 * N.de * (4 * Real.log A.G) ≤ 3 * N.de * (28 * N.la) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      linarith
    nlinarith

theorem passage_base_sharp_levels : PassageAtBaseSharpLevels := by
  intro K _ _ _ _ E _ _ Pg r k _ Pl0 T J _ F ψ Zs N S0 S1 A
  exact passage_from_levels K F.base _ _ N S0 S1 A

section Trivial

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {Df : DefSide Bs}

def trivAmb (S : IndefData Df) : LevelAmb K S.D S.D where
  Dg := S.D
  Xg := S.XE
  Rg := S.RR
  ep0 := 1
  ep1 := 1
  S := Unit
  fS := inferInstance
  es := fun _ => 1
  nS := fun _ => 1
  nbar := 1
  G := 1
  h0 := 1
  h1 := 1
  ι0 := 1
  ι1 := 1

theorem trivAmb_partLat (S : IndefData Df) : (trivAmb S).partLat (trivAmb S).ep0 = S.RR := by
  apply le_antisymm inf_le_left
  intro y hy
  refine ⟨hy, y, ?_⟩
  show (1 : Matrix (Fin S.D) (Fin S.D) K) *ᵥ y = y
  exact Matrix.one_mulVec y

theorem trivAmb_img (S : IndefData Df) : (trivAmb S).img (trivAmb S).ι0 S.RR = S.RR := by
  unfold LevelAmb.img
  ext y
  constructor
  · intro h
    obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.mp h
    rw [← hxy]
    show (1 : Matrix (Fin S.D) (Fin S.D) K) *ᵥ x ∈ S.RR
    rwa [Matrix.one_mulVec]
  · intro hy
    refine Submodule.mem_map.mpr ⟨y, hy, ?_⟩
    show (1 : Matrix (Fin S.D) (Fin S.D) K) *ᵥ y = y
    exact Matrix.one_mulVec y

theorem trivAmb_hyps (S : IndefData Df) (N : IndefNum Bs) (hX : ∀ v, IsUnit (S.XE v).det)
    (hL : Submodule.IsLattice K S.RR) (hne : S.RR ≠ ⊥) (hla : 0 ≤ N.la) (hde : 0 ≤ N.de) :
    (trivAmb S).FramesG ∧ (trivAmb S).LatG ∧
    (trivAmb S).EmbAt (trivAmb S).ι0 (trivAmb S).ep0 (trivAmb S).h0 S.XE ∧
    (trivAmb S).EmbAt (trivAmb S).ι1 (trivAmb S).ep1 (trivAmb S).h1 S.XE ∧
    (trivAmb S).SandAt (trivAmb S).ι0 (trivAmb S).ep0 (trivAmb S).h0 S.RR ∧
    (trivAmb S).SandAt (trivAmb S).ι1 (trivAmb S).ep1 (trivAmb S).h1 S.RR ∧
    (trivAmb S).Sizes N.la ∧ (trivAmb S).Ranks ∧ (trivAmb S).Deg0 ∧ (trivAmb S).Deg1 ∧ (trivAmb S).MaxT ∧
    (trivAmb S).Mult N.de ∧ (trivAmb S).RowsG := by
  letI : Unique (trivAmb S).S := inferInstanceAs (Unique Unit)
  have hP1 : (trivAmb S).partLat (trivAmb S).ep0 = S.RR := trivAmb_partLat S
  have hRP0 : (trivAmb S).latticeAtBaseLevel = S.RR := hP1
  have hRP1 : (trivAmb S).latticeAtSharpLevel = S.RR := hP1
  have hRs : ∀ s, (trivAmb S).Rs s = S.RR := by
    intro s
    have : (trivAmb S).ep0 * (trivAmb S).es s = (trivAmb S).ep0 := by
      exact mul_one _
    unfold LevelAmb.Rs; rw [this]; exact hP1
  have hsc : Formalism.BranchingDeterminantCap.scaleFrame (Real.sqrt (((trivAmb S).h0 : ℕ) : ℝ)) (trivAmb S).Xg = S.XE := by
    funext v
    show ((Real.sqrt ((1 : ℕ) : ℝ) : ℝ) : ℂ) • S.XE v = S.XE v
    rw [Nat.cast_one, Real.sqrt_one, Complex.ofReal_one, one_smul]
  have hemb : (trivAmb S).EmbAt (trivAmb S).ι0 (trivAmb S).ep0 (trivAmb S).h0 S.XE := by
    refine ⟨fun x y h => ?_, rfl, fun v x y => ?_⟩
    · change (1 : Matrix (Fin S.D) (Fin S.D) K) *ᵥ x = (1 : Matrix (Fin S.D) (Fin S.D) K) *ᵥ y at h
      rwa [Matrix.one_mulVec, Matrix.one_mulVec] at h
    · rw [hsc]
      show _ = Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin S.D)) S.XE v ((1 : Matrix (Fin S.D) (Fin S.D) K) *ᵥ x)
        ((1 : Matrix (Fin S.D) (Fin S.D) K) *ᵥ y)
      rw [Matrix.one_mulVec, Matrix.one_mulVec]
  have hsand : (trivAmb S).SandAt (trivAmb S).ι0 (trivAmb S).ep0 (trivAmb S).h0 S.RR := by
    refine ⟨?_, fun y hy => ?_⟩
    · rw [trivAmb_img, hP1]
      exact le_rfl
    · rw [trivAmb_img]; rw [hP1] at hy
      show ((1 : ℕ) : 𝓞 K) • y ∈ S.RR
      rwa [Nat.cast_one, one_smul]
  have hG : Real.log ((trivAmb S).G : ℝ) = 0 := by
    show Real.log ((1 : ℕ) : ℝ) = 0
    rw [Nat.cast_one, Real.log_one]
  refine ⟨hX, hL, hemb, hemb, hsand, hsand, ⟨one_pos, le_rfl, one_pos, le_rfl, by rw [hG]; exact hla⟩,
    ⟨?_, ?_⟩, ?_, ?_, ?_, ⟨one_pos, fun _ => ⟨?_, ?_⟩⟩, ⟨?_, ?_⟩⟩
  · rw [hRP0, Fintype.sum_unique, hRs]
  · rw [hRP1, Fintype.sum_unique, hRs]
    show Formalism.HN.rkK S.RR = 1 * Formalism.HN.rkK S.RR
    rw [one_mul]
  · unfold LevelAmb.Deg0; rw [hRP0, Fintype.sum_unique, hRs, hG]; simp
  · unfold LevelAmb.Deg1; rw [hRP1, Fintype.sum_unique, hRs, hG]
    show ((1 : ℕ) : ℝ) * _ - _ ≤ _
    simp
  · unfold LevelAmb.MaxT; rw [hRP0, hRP1, hG]; simp
  · show (1 - N.de) * (1 : ℝ) ≤ ((1 : ℕ) : ℝ)
    push_cast; linarith
  · show ((1 : ℕ) : ℝ) ≤ (1 + N.de) * (1 : ℝ)
    push_cast; linarith
  · rw [hRP0]; exact hne
  · rw [hRP1]; exact hne

end Trivial

end Formalism.L2.GlobalTheoryTheory.DivPassage
