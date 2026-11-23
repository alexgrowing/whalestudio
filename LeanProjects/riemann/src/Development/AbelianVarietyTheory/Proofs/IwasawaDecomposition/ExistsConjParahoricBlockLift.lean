import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CenterEqSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompOfOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockDiagonalWithIdentity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeCongruenceInLevelCharacterOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev

noncomputable section

namespace GlobalTheory.ParahLift

section Core

variable {K : Type} [CommRing K]

theorem pl_blkDiag_mem {m r : ℕ} {x : GL (Fin r) K} {M : GL (Fin m) K} (hM : GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity x M) :
    M ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
  intro i j hij
  have hj : j.val < r := by
    unfold Formalism.L2.DIV.blk2 at hij; split_ifs at hij with h1 h2 <;> omega
  have hi : ¬ i.val < r := by
    unfold Formalism.L2.DIV.blk2 at hij; split_ifs at hij with h1 h2 <;> omega
  have hne : i ≠ j := fun h => hi (h ▸ hj)
  show M.val i j = 0
  rw [hM i j, dif_neg (fun h => hi h.1), if_neg hne]

theorem pl_blkOf_eq {m r t : ℕ} (hm : m = r + t) (a : Fin m) :
    Formalism.L2.DIV.blkOf r t a = Formalism.L2.DIV.blk2 r a := by
  have ha := a.2
  unfold Formalism.L2.DIV.blkOf Formalism.L2.DIV.blk2
  split_ifs with h
  · rfl
  · have : (a.val - r) / t = 0 := Nat.div_eq_of_lt (by omega)
    omega

theorem pl_blockTri_eq {m r t : ℕ} (hm : m = r + t) :
    Formalism.L2.DIV.blockTri (κ := K) (n := m) (Formalism.L2.DIV.blkOf r t) = Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
  have : (Formalism.L2.DIV.blkOf r t : Fin m → ℕ) = Formalism.L2.DIV.blk2 r := funext (pl_blkOf_eq hm)
  rw [this]

theorem pl_core {m r t : ℕ} (hm : m = r + t) (hr : r ≤ m) {b M : GL (Fin m) K} {x : GL (Fin r) K}
    (hb : b ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) (hM : GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity x M) :
    b * M * b⁻¹ ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ∧
    Formalism.L2.DIV.upperLeftBlock hr (b * M * b⁻¹) = Formalism.L2.DIV.upperLeftBlock hr b * x * (Formalism.L2.DIV.upperLeftBlock hr b)⁻¹ ∧
    Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) 1 (b * M * b⁻¹) = 1 := by
  have hM2 := pl_blkDiag_mem hM
  have hbinv := (Formalism.L2.DIV.blockTri (κ := K) (Formalism.L2.DIV.blk2 r)).inv_mem hb
  have hbM := (Formalism.L2.DIV.blockTri (κ := K) (Formalism.L2.DIV.blk2 r)).mul_mem hb hM2
  have hall := (Formalism.L2.DIV.blockTri (κ := K) (Formalism.L2.DIV.blk2 r)).mul_mem hbM hbinv
  have hE := pl_blockTri_eq (K := K) hm
  refine ⟨hE ▸ hall, ?_, ?_⟩
  · have hMr : Formalism.L2.DIV.upperLeftBlock hr M = x := by
      apply Units.ext
      ext i j
      rw [Formalism.L2.DIV.upper_block_val_submatrix hr hM2, Matrix.submatrix_apply, hM, dif_pos ⟨i.2, j.2⟩]
      rfl
    unfold Formalism.L2.DIV.upperLeftBlock at hMr ⊢
    rw [Formalism.L2.DIV.extendMatrixByIdentityAlongIndices_mul _ hbM hbinv, Formalism.L2.DIV.extendMatrixByIdentityAlongIndices_mul _ hb hM2, Formalism.L2.DIV.extendOne_inv _ hb, hMr]
  · have hb' : b ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) := hE ▸ hb
    have hM' : M ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) := hE ▸ hM2
    have hbinv' : b⁻¹ ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) := hE ▸ hbinv
    have hbM' := (Formalism.L2.DIV.blockTri (κ := K) (Formalism.L2.DIV.blkOf r t)).mul_mem hb' hM'
    have hdM : Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) 1 M = 1 := by
      apply Units.ext
      rw [Formalism.L2.DIV.diag_block_det_val 1 hM', Units.val_one]
      have hsub : (M.val.submatrix (Subtype.val : {a : Fin m // Formalism.L2.DIV.blkOf r t a = 1} → Fin m) (Subtype.val : {a : Fin m // Formalism.L2.DIV.blkOf r t a = 1} → Fin m)) = 1 := by
        ext a c
        have ha : ¬ a.1.val < r := fun h => by
          have h2 := a.2
          simp [Formalism.L2.DIV.blkOf, h] at h2
        rw [Matrix.submatrix_apply, hM, dif_neg (fun h => ha h.1), Matrix.one_apply]
        by_cases hac : a = c
        · subst hac; simp
        · rw [if_neg hac, if_neg (fun h => hac (Subtype.ext h))]
      show (M.val.submatrix (Subtype.val : {a : Fin m // Formalism.L2.DIV.blkOf r t a = 1} → Fin m) (Subtype.val : {a : Fin m // Formalism.L2.DIV.blkOf r t a = 1} → Fin m)).det = 1
      rw [hsub, Matrix.det_one]
    rw [Formalism.L2.DIV.diag_block_det_mul hbM' hbinv', Formalism.L2.DIV.diag_block_det_mul hb' hM', hdM, mul_one]
    unfold Formalism.L2.DIV.dBlk
    rw [Formalism.L2.DIV.extendOne_inv _ hb', mul_inv_cancel]

theorem pl_core_cast {n m r t : ℕ} (hn : n = m) (hm : m = r + t) (hr : r ≤ m) (hr' : r ≤ n) {b M : GL (Fin m) K}
    {X : GL (Fin n) K} {x : GL (Fin r) K}
    (hb : b ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) (hM : GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity x M)
    (hX : ∀ a c : Fin m, X.val (Fin.cast hn.symm a) (Fin.cast hn.symm c) = (b * M * b⁻¹).val a c) :
    X ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ∧
    Formalism.L2.DIV.upperLeftBlock hr' X = Formalism.L2.DIV.upperLeftBlock hr b * x * (Formalism.L2.DIV.upperLeftBlock hr b)⁻¹ ∧
    Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) 1 X = 1 := by
  subst hn
  have hXe : X = b * M * b⁻¹ := Units.ext (Matrix.ext fun a c => hX a c)
  subst hXe
  exact pl_core hm hr hb hM

theorem pl_one_cast {n m : ℕ} (hn : n = m) {b Y : GL (Fin m) K} {X : GL (Fin n) K} (hY : Y = 1)
    (hX : ∀ a c : Fin m, X.val (Fin.cast hn.symm a) (Fin.cast hn.symm c) = (b * Y * b⁻¹).val a c) : X = 1 := by
  subst hn; subst hY
  apply Units.ext
  ext a c
  have h := hX a c
  rw [mul_one, mul_inv_cancel] at h
  exact h

end Core

end GlobalTheory.ParahLift

namespace GlobalTheory.ParahLift

section LevFn

open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
  {LL : Type} [CommRing LL]

theorem pl_levFn_eq_one (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Ld : Formalism.L2.DIV.LevDat E LL n)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hP : Ld.P.chi = 1)
    (hg : ∀ PP ∈ Ld.Pg, ∀ c ∈ Finset.range Ld.s,
      Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf Ld.r Ld.t) (c + 1) (Formalism.L2.DIV.redFn β PP x) = 1)
    (hq : ∀ PP ∈ Ld.Q, Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 Ld.r) 1 (Formalism.L2.DIV.redFn β PP x) = 1) :
    Formalism.L2.DIV.levFn β Ld x = 1 := by
  unfold Formalism.L2.DIV.levFn
  rw [Finset.prod_eq_one (fun PP hPP => Finset.prod_eq_one (fun c hc => by rw [hg PP hPP c hc, map_one])),
    Finset.prod_eq_one (fun PP hPP => by rw [hq PP hPP, map_one])]
  have h1 : Formalism.L2.DIV.ext1 Ld.P.H Ld.P.chi (Formalism.L2.DIV.rTup β Ld x) = 1 := by
    unfold Formalism.L2.DIV.ext1
    split_ifs
    · rw [hP]; rfl
    · rfl
  rw [h1, mul_one, mul_one]

end LevFn

theorem exists_conj_parahoric_lift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (k : Fin D.R.m) (s : T)
  (P : Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc D k) D.R.nV) (L : G0g D.nd → Formalism.AUTREP.GAf D.host.E D.R.nV),
  (∀ g, L g ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV) →
  (∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV, Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc D k) (P.ψ κ) ∈ Formalism.L2.DIV.St (R.βV k)) →
  (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q s → ∃ (s' : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w)
      (b : GL (Fin D.R.nV) (Formalism.L2.DIV.kP s'.w)), s'.w = PP ∧ GlobalTheory.CenFrame.IsResidue s' φ ∧
        GlobalTheory.CenFrame.FrameRed (GlobalTheory.FrameBlockDiagonal.rankV D k) P (R.βV k) s' φ b ∧ (PP ∈ R.Pg → b ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 D.R.r))) →
  (∀ g (s' : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w), GlobalTheory.CenFrame.IsResidue s' φ →
      (s'.w ∈ R.Q s → ∃ y, GlobalTheory.CenFrame.IsCompOf s' (L g) y ∧ Matrix.GeneralLinearGroup.map φ y = 1) ∧
      ∀ hP : s'.w ∈ R.Pg, ∃ y, GlobalTheory.CenFrame.IsCompOf s' (L g) y ∧
        GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity (R.eG ((R.eG.trans cG).symm g) ⟨s'.w, hP⟩) (Matrix.GeneralLinearGroup.map φ y)) →
  ∃ c : G, ∀ g : G,
    Formalism.IndefR.Lev.IsLevelLift (Formalism.IndefR.Links.Vc D k) (R.βV k) (R.datVt k s) (R.eG g) (P.ψ (L ((R.eG.trans cG) (c * g * c⁻¹)))) ∧
    Formalism.IndefR.Lev.levChi (Formalism.IndefR.Links.Vc D k) (R.βV k) (Formalism.IndefR.Lev.flagL (R.datVt k s)) (P.ψ (L ((R.eG.trans cG) (c * g * c⁻¹)))) = 1 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R cG k s P L H1 H2 H3 H4
  have hn : (Formalism.IndefR.Links.Vc D k).rank = D.R.nV := GlobalTheory.FrameBlockDiagonal.rankV D k
  have hm : D.R.nV = D.R.r + D.R.t := rfl
  have hr : D.R.r ≤ D.R.nV := Nat.le_add_right _ _
  have hr' : D.R.r ≤ (Formalism.IndefR.Links.Vc D k).rank := hn ▸ hr
  have hA : ∀ PP : ↥R.Pg, ∃ b : GL (Fin D.R.nV) (Formalism.L2.DIV.kP PP.1), b ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 D.R.r) ∧
      ∀ h : G0g D.nd, ∃ M : GL (Fin D.R.nV) (Formalism.L2.DIV.kP PP.1),
        GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity (R.eG ((R.eG.trans cG).symm h) PP) M ∧
        ∀ a c, (Formalism.L2.DIV.redFn (R.βV k) PP.1 (Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc D k) (P.ψ (L h)))).val
          (Fin.cast hn.symm a) (Fin.cast hn.symm c) = (b * M * b⁻¹).val a c := by
    rintro ⟨PP, hPP⟩
    obtain ⟨s', φ, b, hw, hres, hfr, hb⟩ := H3 PP (Or.inl hPP)
    subst hw
    refine ⟨b, hb hPP, fun h => ?_⟩
    obtain ⟨y, hy, hbd⟩ := (H4 h s' φ hres).2 hPP
    exact ⟨_, hbd, hfr (L h) (H1 h) y hy⟩
  have hB : ∀ PP ∈ R.Q s, ∀ h : G0g D.nd,
      Formalism.L2.DIV.redFn (R.βV k) PP (Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc D k) (P.ψ (L h))) = 1 := by
    intro PP hPP h
    obtain ⟨s', φ, b, hw, hres, hfr, -⟩ := H3 PP (Or.inr hPP)
    subst hw
    obtain ⟨y, hy, h1⟩ := (H4 h s' φ hres).1 hPP
    exact pl_one_cast hn h1 (hfr (L h) (H1 h) y hy)
  choose bf hbf Mf hMd hMe using hA
  refine ⟨R.eG.symm (fun PP => (Formalism.L2.DIV.upperLeftBlock hr (bf PP))⁻¹), fun g => ?_⟩
  set c := R.eG.symm (fun PP => (Formalism.L2.DIV.upperLeftBlock hr (bf PP))⁻¹) with hc
  set h := (R.eG.trans cG) (c * g * c⁻¹) with hh
  have hsymm : (R.eG.trans cG).symm h = c * g * c⁻¹ := MulEquiv.symm_apply_apply _ _
  have hx : ∀ PP : ↥R.Pg, R.eG ((R.eG.trans cG).symm h) PP =
      (Formalism.L2.DIV.upperLeftBlock hr (bf PP))⁻¹ * R.eG g PP * Formalism.L2.DIV.upperLeftBlock hr (bf PP) := by
    intro PP
    rw [hsymm, map_mul, map_mul, map_inv, hc, MulEquiv.apply_symm_apply]
    simp only [Pi.mul_apply, Pi.inv_apply, inv_inv]
  have hcore : ∀ PP : ↥R.Pg,
      Formalism.L2.DIV.redFn (R.βV k) PP.1 (Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc D k) (P.ψ (L h))) ∈
        Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf D.R.r D.R.t) ∧
      Formalism.L2.DIV.upperLeftBlock hr' (Formalism.L2.DIV.redFn (R.βV k) PP.1 (Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc D k) (P.ψ (L h)))) =
        R.eG g PP ∧
      Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf D.R.r D.R.t) 1
        (Formalism.L2.DIV.redFn (R.βV k) PP.1 (Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc D k) (P.ψ (L h)))) = 1 := by
    intro PP
    obtain ⟨h1, h2, h3⟩ := pl_core_cast hn hm hr hr' (hbf PP) (hMd PP h) (hMe PP h)
    refine ⟨h1, ?_, h3⟩
    rw [h2, hx PP]
    group
  have hSt := H2 (L h) (H1 h)
  refine ⟨⟨P.into _, Formalism.L2.DIV.mem_parLev.2 ⟨GlobalTheory.LevFinCong.finE_mem_UA _ _, hSt, fun PP hPP => (hcore ⟨PP, hPP⟩).1,
    fun PP hPP => ?_⟩, ?_⟩, ?_⟩
  · rw [hB PP hPP h]; exact Subgroup.one_mem _
  · funext PP
    exact (hcore PP).2.1
  · unfold Formalism.IndefR.Lev.levChi
    rw [pl_levFn_eq_one _ _ _ rfl, Units.val_one]
    · intro PP hPP c' hc'
      have hc0 : c' = 0 := by
        have : c' < 1 := Finset.mem_range.1 hc'
        omega
      subst hc0
      exact (hcore ⟨PP, hPP⟩).2.2
    · intro PP hPP
      rw [hB PP hPP h]
      exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _

end GlobalTheory.ParahLift
