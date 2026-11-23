import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NVNeZero
import Formalism.LocalToGlobal.IndefiniteReal.BridgeColPts
import Formalism.LocalToGlobal.Columns.InputsGenus
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockTriangularBlockIndexOfIffColBlockUTTwoBlockStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopBlockEqOneIffMemColHKStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SecondBlockDetEqBlockDetOfSumPartitionsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftLevelCharacterTypePrimeEqColumnCharacterStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftResidueTwistCharacterEqResCharStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePrimesDisjointTwistChosenPrimesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.Mem.LevPres
open Formalism.L2.DIV

theorem castGL_rfl' {R : Type} [CommRing R] {m : ℕ} (x : GL (Fin m) R) : LiftBrg.castGL (rfl : m = m) x = x :=
  Units.ext (Matrix.ext fun _ _ => rfl)

theorem castGL_castGL_symm' {R : Type} [CommRing R] {m n : ℕ} (h : m = n) (y : GL (Fin n) R) :
    LiftBrg.castGL h (LiftBrg.castGL h.symm y) = y := by
  subst h; rw [castGL_rfl', castGL_rfl']

theorem castGL_St {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m n : ℕ}
    (h : m = n) (x : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    LiftBrg.castGL h x ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ↔ x ∈ St (1 : GL (Fin m) _) := by
  subst h; rw [castGL_rfl']

theorem castGL_redFn {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m n : ℕ}
    (h : m = n) (x : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Pl E) :
    redFn (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) PP (LiftBrg.castGL h x) = LiftBrg.castGL h (redFn 1 PP x) := by
  subst h; rw [castGL_rfl', castGL_rfl']

theorem castGL_blkOf {κ : Type} [CommRing κ] {m n : ℕ} (h : m = n) (r t : ℕ) (g : GL (Fin m) κ) :
    LiftBrg.castGL h g ∈ blockTri (blkOf r t) ↔ g ∈ blockTri (blkOf r t) := by
  subst h; rw [castGL_rfl']

theorem generalLinearGroupCastOfEq_mem_twoBlockTri_iff {κ : Type} [CommRing κ] {m n : ℕ} (h : m = n) (r : ℕ) (g : GL (Fin m) κ) :
    LiftBrg.castGL h g ∈ blockTri (blk2 r) ↔ g ∈ blockTri (blk2 r) := by
  subst h; rw [castGL_rfl']

theorem generalLinearGroupCastOfEq_rowBlock_eq {κ : Type} [CommRing κ] {m n r : ℕ} (h : m = n) (hr : r ≤ n) (hr' : r ≤ m) (g : GL (Fin m) κ) :
    upperLeftBlock hr (LiftBrg.castGL h g) = upperLeftBlock hr' g := by
  subst h; rw [castGL_rfl']

theorem generalLinearGroupCastOfEq_diagBlock_eq {κ : Type} [CommRing κ] {m n : ℕ} (h : m = n) (r t : ℕ) (g : GL (Fin m) κ) :
    dBlk (blkOf r t) 1 (LiftBrg.castGL h g) = dBlk (blkOf r t) 1 g := by
  subst h; rw [castGL_rfl']

theorem generalLinearGroupCastOfEq_twoBlock_diagBlock_eq {κ : Type} [CommRing κ] {m n : ℕ} (h : m = n) (r : ℕ) (g : GL (Fin m) κ) :
    dBlk (blk2 r) 1 (LiftBrg.castGL h g) = dBlk (blk2 r) 1 g := by
  subst h; rw [castGL_rfl']

section StdSide'

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (SG : Finset (Pl E)) (H : Subgroup (Formalism.L2.Col.GLG E n SG))

theorem mem_J0_empty (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) :
    x ∈ Formalism.L2.Col.J0 hc n ∅ ↔ x ∈ Formalism.L2.Col.UAd hc n ∧ x ∈ St (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
  unfold Formalism.L2.Col.J0
  simp only [Subgroup.mem_inf, Subgroup.mem_iInf]
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, fun P hP => absurd hP (Finset.notMem_empty P)⟩

theorem mem_colJ_iff (x : Formalism.L2.Col.UAd hc n) :
    x ∈ Bridge.colJ hc n ∅ SG H ↔
      ∃ hx : (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) ∈ Formalism.L2.Col.J0 hc n ∅, Formalism.L2.Col.redG hc n ∅ SG ⟨x, hx⟩ ∈ H := by
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m.2, hm⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

theorem redG_apply' (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hx : x ∈ Formalism.L2.Col.J0 hc n ∅) (w : SG) :
    Formalism.L2.Col.redG hc n ∅ SG ⟨x, hx⟩ w = redFn 1 w.1 x := by
  unfold redFn
  rw [extendOne_of_mem _ (Formalism.L2.Col.congruence_subgroup_le_stabilizer hc n ∅ hx)]
  rfl

theorem redH_apply' (m : Formalism.L2.Col.JH hc n ∅ SG H) (w : SG) :
    ((Formalism.L2.Col.redH hc n ∅ SG H m : H) : Formalism.L2.Col.GLG E n SG) w =
      redFn (1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) w.1 ((m : Formalism.L2.Col.J0 hc n ∅) : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) := by
  show Formalism.L2.Col.redG hc n ∅ SG (m : Formalism.L2.Col.J0 hc n ∅) w = _
  exact redG_apply' hc n SG _ (m : Formalism.L2.Col.J0 hc n ∅).2 w

end StdSide'

theorem lev_eq_of_eq {κ K : Type} [CommRing κ] [Field K] {n : ℕ} {l₁ l₂ : Formalism.L2.Col.Lev κ K n} (e : l₁ = l₂)
    (g : GL (Fin n) κ) (h₁ : g ∈ l₁.H) (h₂ : g ∈ l₂.H) : l₁.lam ⟨g, h₁⟩ = l₂.lam ⟨g, h₂⟩ := by
  subst e; rfl

theorem mem_levEnvJ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (y : Bridge.Gf V) :
    y ∈ (levEnv V β L).J ↔ Formalism.UG.bc (swapAE D) (y : GL (Fin V.rank) _) ∈ lev D.sp.cm V.gram β (flag1L L) := Iff.rfl

theorem levEnv_chi {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (y : Bridge.Gf V)
    (hy : y ∈ (levEnv V β L).J) :
    (levEnv V β L).χ ⟨y, hy⟩ = levFn β (flag1L L) (Formalism.UG.bc (swapAE D) (y : GL (Fin V.rank) _)) := rfl

theorem levFn_datVt (X : Stages) {T : Type} (L : Formalism.IndefR.Links.LevCh X.toD7 T) (i : Fin X.toD7.R.m) (t : T)
    (M : GL (Fin (Vc X.toD7 i).rank) (LiftBrg.EA X)) :
    levFn 1 (flag1L (L.datVt i t)) M =
      (∏ PP ∈ L.Pg, (L.chi ((i : ℕ) + 1) PP)⁻¹ (dBlk (blkOf X.toD7.R.r X.toD7.R.t) 1 (redFn 1 PP M))) *
        ∏ PP ∈ L.Q t, L.xiR t PP (dBlk (blk2 X.toD7.R.r) 1 (redFn 1 PP M)) := by
  have h0 : ext1 (flag1L (L.datVt i t)).P.H (flag1L (L.datVt i t)).P.chi (rTup 1 (flag1L (L.datVt i t)) M) = 1 :=
    Formalism.IndefR.Lev.subgroupCharExtension_one_apply _ _
  unfold levFn
  rw [h0, one_mul]
  congr 1
  refine Finset.prod_congr rfl fun PP _ => ?_
  exact Finset.prod_range_one _

theorem chr_eq_one {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} {SG : Finset (HeightOneSpectrum (𝓞 E))}
    (Λ : Formalism.L2.Col.LevFam E K n SG) (h : Λ.grp) (e : h.1 = 1) : Λ.chr h = 1 := by
  have e' : h = 1 := Subtype.ext e
  rw [e', map_one]

theorem prod_glue {E : Type} [Field E] [NumberField E] (A' B' A B : Finset (HeightOneSpectrum (𝓞 E))) (hA : A' = A) (hB : B' = B)
    (hd : Disjoint A B) (a b φ : HeightOneSpectrum (𝓞 E) → ℂˣ) (ha : ∀ P ∈ A, φ P = (a P)⁻¹) (hb : ∀ P ∈ B, φ P = (b P)⁻¹) :
    ((∏ P ∈ A', a P) * ∏ P ∈ B', b P)⁻¹ = ∏ w : Formalism.L2.Col.uSG A B, φ w.1 := by
  classical
  subst hA hB
  rw [Finset.prod_coe_sort (Formalism.L2.Col.uSG A' B') φ, mul_inv, ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib,
    ← Finset.prod_congr rfl ha, ← Finset.prod_congr rfl hb]
  convert (Finset.prod_union hd).symm

theorem lev_type_eq : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → ValsIn I → LevOf X I U L →
    ∀ (i : Fin X.toD7.R.m) (t : TupU I U) (eG : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV ≃* Bridge.Gf (Vc X.toD7 i)),
    (∀ x, LiftBrg.castGL (LiftBrg.rkEq X i).symm (Formalism.UG.bc (swapAE X.toD7)
          ((eG x : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af X.toD7.host.F ⊗[X.toD7.host.F] X.toD7.host.E))) =
        (x : GL (Fin X.B.R.nV) (LiftBrg.EA X))) →
    ∃ hJ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J =
        (Bridge.colJ X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t)
          (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp).map eG.toMonoidHom,
      ∀ (k : Bridge.colJ X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp)
        (hk : eG (k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) ∈ (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J),
        (((levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).χ ⟨eG k, hk⟩)⁻¹ : ℂˣ) =
          Units.map X.toD7.what₂.embLL.toMonoidHom ((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.chr
            (Formalism.L2.Col.redH X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) _
              ((Bridge.colJEquiv X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) _).symm k))) ∧
        ((k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) ∈ Bridge.principalCongruenceSubgroup X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) →
          (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).χ ⟨eG k, hk⟩ = 1) := by
  intro X px I U L hI hV hL i t eG heG
  classical
  have hβ : L.βV i = 1 := hL.beta.1 i
  have hPg : L.Pg = (X.B.primes px).vGs := hL.Pg
  have hQ : L.Q t = Formalism.L2.Col.QE I.sel t.1 := by rw [hL.Q t, ← tup_ixOf I t]
  have hdisj := GlobalTheory.T.typePrimes_disjoint_twistChosenPrimes X px I U L hI hV hL t
  have hrk := LiftBrg.rkEq X i
  have hnV : X.B.R.nV = X.B.R.r + X.B.R.t := rfl
  have hM : ∀ x : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV,
      Formalism.UG.bc (swapAE X.toD7) ((eG x : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _) =
        LiftBrg.castGL hrk (x : GL (Fin X.B.R.nV) (LiftBrg.EA X)) := by
    intro x
    rw [← heG x]
    exact (castGL_castGL_symm' _ _).symm
  have hUA : ∀ y : Bridge.Gf (Vc X.toD7 i),
      Formalism.UG.bc (swapAE X.toD7) (y : GL (Fin (Vc X.toD7 i).rank) _) ∈ UA X.toD7.sp.cm (Vc X.toD7 i).gram := by
    rintro ⟨_, g, rfl⟩
    exact GlobalTheory.LevSplit.finE_mem_UA _ g

  have hHv : ∀ (w : LiftBrg.sgL X I U t) (hw : w.1 ∈ (X.B.primes px).vGs) (g : GL (Fin X.B.R.nV) (𝓞 X.B.fields.E ⧸ w.1.asIdeal)),
      g ∈ ((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv w).H ↔ g ∈ Formalism.L2.Col.HK X.B.R.nV _ X.B.R.r [X.B.R.t] := by
    intro w hw g
    show g ∈ (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1) w).H ↔ _
    have e : Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1) w = Formalism.L2.Col.mtTyK I.Ch ((i : ℕ) + 1) ⟨w.1, hw⟩ :=
      Formalism.L2.Col.LevFam.glue_of_mem _ _ w hw
    rw [e]
    rfl
  have hHq : ∀ (w : LiftBrg.sgL X I U t) (hw : w.1 ∉ (X.B.primes px).vGs) (g : GL (Fin X.B.R.nV) (𝓞 X.B.fields.E ⧸ w.1.asIdeal)),
      g ∈ ((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv w).H ↔ g ∈ Formalism.L2.Col.blockUT X.B.R.nV _ X.B.R.r [X.B.R.t] := by
    intro w hw g
    show g ∈ (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1) w).H ↔ _
    have e : Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1) w =
        Formalism.L2.Col.mtTyQ X.B.R (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K) (Formalism.L2.Col.QE I.sel t.1)
          ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩ :=
      Formalism.L2.Col.LevFam.glue_of_not _ _ w hw
    rw [e]
    rfl

  have hmem : ∀ x : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV,
      eG x ∈ (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J ↔
        x ∈ Bridge.colJ X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t)
          (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp := by
    intro x
    have hx0 := hUA (eG x)
    rw [hM x] at hx0
    have hcr : ∀ PP : Pl X.toD7.host.E,
        LiftBrg.castGL hrk (redFn (1 : GL (Fin X.B.R.nV) (LiftBrg.EA X)) PP (x : GL (Fin X.B.R.nV) (LiftBrg.EA X))) =
          redFn (1 : GL (Fin (Vc X.toD7 i).rank) (LiftBrg.EA X)) PP
            (LiftBrg.castGL hrk (x : GL (Fin X.B.R.nV) (LiftBrg.EA X))) :=
      fun PP => (castGL_redFn hrk _ PP).symm
    rw [mem_levEnvJ, hM x, hβ, mem_lev, mem_parLev, castGL_St]
    refine Iff.trans ?_ (mem_colJ_iff X.toD7.sp.cm X.B.R.nV (LiftBrg.sgL X I U t) _ x).symm
    constructor
    · rintro ⟨⟨-, hSt, hg, hq⟩, hr⟩
      have hr' : rTup 1 (flag1L (L.datVt i t)) (LiftBrg.castGL hrk (x : GL (Fin X.B.R.nV) (LiftBrg.EA X))) = 1 :=
        Subgroup.mem_bot.1 hr
      have hx : (x : GL (Fin X.B.R.nV) (LiftBrg.EA X)) ∈ Formalism.L2.Col.J0 X.toD7.sp.cm X.B.R.nV ∅ :=
        (mem_J0_empty _ _ _).2 ⟨x.2, hSt⟩
      refine ⟨hx, (Subgroup.mem_pi _).2 fun w _ => ?_⟩
      show Formalism.L2.Col.redG X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) ⟨_, hx⟩ w ∈
        ((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv w).H
      rw [show Formalism.L2.Col.redG X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) ⟨_, hx⟩ w =
        redFn (1 : GL (Fin X.B.R.nV) (LiftBrg.EA X)) (w.1 : Pl X.toD7.host.E) (x : GL (Fin X.B.R.nV) (LiftBrg.EA X))
          from redG_apply' _ _ _ _ hx w]
      by_cases hw : w.1 ∈ (X.B.primes px).vGs
      · rw [hHv w hw]
        have hPP : w.1 ∈ (flag1L (L.datVt i t)).Pg := by
          show w.1 ∈ L.Pg
          rw [hPg]; exact hw
        have h1 : LiftBrg.castGL hrk (redFn (1 : GL (Fin X.B.R.nV) (LiftBrg.EA X)) (w.1 : Pl X.toD7.host.E)
            (x : GL (Fin X.B.R.nV) (LiftBrg.EA X))) ∈ blockTri (blkOf X.B.R.r X.B.R.t) := by
          convert hg w.1 hPP using 2
          all_goals first | rfl | exact hcr _
        rw [castGL_blkOf] at h1
        have h2 := ((GlobalTheory.T.mem_blockTri_blkOf_and_blk2_iff_mem_blockUT hnV _).1).1 h1
        refine (GlobalTheory.T.upperLeftBlock_eq_one_iff_mem_HK hnV (Formalism.L2.Col.r_le_nV X.B.R) _ h2).1 ?_
        have h3 : upperLeftBlock (flag1L (L.datVt i t)).hr (LiftBrg.castGL hrk (redFn (1 : GL (Fin X.B.R.nV) (LiftBrg.EA X))
            (w.1 : Pl X.toD7.host.E) (x : GL (Fin X.B.R.nV) (LiftBrg.EA X)))) = 1 := by
          have h3' : upperLeftBlock (flag1L (L.datVt i t)).hr (redFn (1 : GL (Fin (Vc X.toD7 i).rank) (LiftBrg.EA X)) (w.1 : Pl X.toD7.host.E)
              (LiftBrg.castGL hrk (x : GL (Fin X.B.R.nV) (LiftBrg.EA X)))) = 1 := congrFun hr' ⟨w.1, hPP⟩
          convert h3' using 2
          all_goals first | rfl | exact hcr _
        rw [generalLinearGroupCastOfEq_rowBlock_eq hrk (flag1L (L.datVt i t)).hr (Formalism.L2.Col.r_le_nV X.B.R)] at h3
        exact h3
      · rw [hHq w hw]
        have hq' : w.1 ∈ Formalism.L2.Col.QE I.sel t.1 := (Finset.mem_union.mp w.2).resolve_left hw
        have hPP : w.1 ∈ (flag1L (L.datVt i t)).Q := by
          show w.1 ∈ L.Q t
          rw [hQ]; exact hq'
        have h1 : LiftBrg.castGL hrk (redFn (1 : GL (Fin X.B.R.nV) (LiftBrg.EA X)) (w.1 : Pl X.toD7.host.E)
            (x : GL (Fin X.B.R.nV) (LiftBrg.EA X))) ∈ blockTri (blk2 X.B.R.r) := by
          convert hq w.1 hPP using 2
          all_goals first | rfl | exact hcr _
        rw [generalLinearGroupCastOfEq_mem_twoBlockTri_iff] at h1
        exact ((GlobalTheory.T.mem_blockTri_blkOf_and_blk2_iff_mem_blockUT hnV _).2).1 h1
    · rintro ⟨hx, hH⟩
      have hSt := ((mem_J0_empty _ _ _).1 hx).2
      have hw' : ∀ w : LiftBrg.sgL X I U t, redFn (1 : GL (Fin X.B.R.nV) (LiftBrg.EA X)) (w.1 : Pl X.toD7.host.E)
          (x : GL (Fin X.B.R.nV) (LiftBrg.EA X)) ∈ ((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv w).H := fun w => by
        rw [show redFn (1 : GL (Fin X.B.R.nV) (LiftBrg.EA X)) (w.1 : Pl X.toD7.host.E) (x : GL (Fin X.B.R.nV) (LiftBrg.EA X)) =
          Formalism.L2.Col.redG X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) ⟨_, hx⟩ w from (redG_apply' _ _ _ _ hx w).symm]
        exact (Subgroup.mem_pi _).1 hH w (Set.mem_univ _)
      refine ⟨⟨hx0, hSt, fun PP hPP => ?_, fun PP hPP => ?_⟩, ?_⟩
      · have hv : PP ∈ (X.B.primes px).vGs := by rw [← hPg]; exact hPP
        have hk := (hHv ⟨PP, Finset.mem_union_left _ hv⟩ hv _).1 (hw' ⟨PP, Finset.mem_union_left _ hv⟩)
        rw [← hcr, castGL_blkOf]
        exact ((GlobalTheory.T.mem_blockTri_blkOf_and_blk2_iff_mem_blockUT hnV _).1).2 (Formalism.L2.Col.HK_le_blockUT _ _ _ _ hk)
      · have hq' : PP ∈ Formalism.L2.Col.QE I.sel t.1 := by rw [← hQ]; exact hPP
        have hb : redFn (1 : GL (Fin X.B.R.nV) (LiftBrg.EA X)) PP (x : GL (Fin X.B.R.nV) (LiftBrg.EA X)) ∈
            Formalism.L2.Col.blockUT X.B.R.nV _ X.B.R.r [X.B.R.t] := by
          by_cases hv : PP ∈ (X.B.primes px).vGs
          · exact Formalism.L2.Col.HK_le_blockUT _ _ _ _
              ((hHv ⟨PP, Finset.mem_union_right _ hq'⟩ hv _).1 (hw' ⟨PP, Finset.mem_union_right _ hq'⟩))
          · exact (hHq ⟨PP, Finset.mem_union_right _ hq'⟩ hv _).1 (hw' ⟨PP, Finset.mem_union_right _ hq'⟩)
        rw [← hcr, generalLinearGroupCastOfEq_mem_twoBlockTri_iff]
        exact ((GlobalTheory.T.mem_blockTri_blkOf_and_blk2_iff_mem_blockUT hnV _).2).2 hb
      · refine Subgroup.mem_bot.2 ?_
        funext PP
        have hv : PP.1 ∈ (X.B.primes px).vGs := by rw [← hPg]; exact PP.2
        have hk := (hHv ⟨PP.1, Finset.mem_union_left _ hv⟩ hv _).1 (hw' ⟨PP.1, Finset.mem_union_left _ hv⟩)
        show upperLeftBlock (L.datVt i t).hr (redFn 1 PP.1 (LiftBrg.castGL hrk (x : GL (Fin X.B.R.nV) (LiftBrg.EA X)))) = 1
        rw [← hcr, generalLinearGroupCastOfEq_rowBlock_eq hrk (L.datVt i t).hr (Formalism.L2.Col.r_le_nV X.B.R)]
        exact (GlobalTheory.T.upperLeftBlock_eq_one_iff_mem_HK hnV _ _ (Formalism.L2.Col.HK_le_blockUT _ _ _ _ hk)).2 hk

  have hJ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).J =
      (Bridge.colJ X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t)
        (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp).map eG.toMonoidHom := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · intro hy
      refine ⟨eG.symm y, (hmem _).1 (by rwa [eG.apply_symm_apply]), eG.apply_symm_apply y⟩
    · rintro ⟨x, hx, rfl⟩
      exact (hmem x).2 hx
  refine ⟨hJ, fun k hk => ?_⟩
  have hm1 := Bridge.colJEquiv_symm_coe X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t)
    (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp k
  have hxk : ((((Bridge.colJEquiv X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t)
      (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp).symm k : Formalism.L2.Col.JH _ _ _ _ _) :
        Formalism.L2.Col.J0 X.toD7.sp.cm X.B.R.nV ∅) : GL (Fin X.B.R.nV) (LiftBrg.EA X)) =
      ((k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (LiftBrg.EA X)) := congrArg Subtype.val hm1
  have hredw : ∀ w : LiftBrg.sgL X I U t,
      ((Formalism.L2.Col.redH X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) _
        ((Bridge.colJEquiv X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t)
          (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp).symm k) : _) : Formalism.L2.Col.GLG _ _ _) w =
        redFn (1 : GL (Fin X.B.R.nV) (LiftBrg.EA X)) (w.1 : Pl X.toD7.host.E)
          ((k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (LiftBrg.EA X)) := by
    intro w
    exact (redH_apply' _ _ _ _ _ w).trans (congrArg _ hxk)
  have hcrk : ∀ PP : Pl X.toD7.host.E,
      redFn (1 : GL (Fin (Vc X.toD7 i).rank) (LiftBrg.EA X)) PP
          (LiftBrg.castGL hrk ((k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (LiftBrg.EA X))) =
        LiftBrg.castGL hrk (redFn (1 : GL (Fin X.B.R.nV) (LiftBrg.EA X)) PP
          ((k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (LiftBrg.EA X))) :=
    fun PP => castGL_redFn hrk _ PP
  have perw : ∀ (w : LiftBrg.sgL X I U t) (g : GL (Fin X.B.R.nV) (𝓞 X.B.fields.E ⧸ w.1.asIdeal))
      (hg : g ∈ ((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv w).H),
      g = redFn (1 : GL (Fin X.B.R.nV) (LiftBrg.EA X)) (w.1 : Pl X.toD7.host.E)
          ((k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (LiftBrg.EA X)) →
      Units.map X.toD7.what₂.embLL.toMonoidHom (((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv w).lam ⟨g, hg⟩) =
        if (w.1 : Pl X.toD7.host.E) ∈ (X.B.primes px).vGs then
          L.chi ((i : ℕ) + 1) w.1 (dBlk (blkOf X.toD7.R.r X.toD7.R.t) 1 (redFn (1 : GL (Fin (Vc X.toD7 i).rank) (LiftBrg.EA X)) w.1
            (LiftBrg.castGL hrk ((k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (LiftBrg.EA X)))))
        else (L.xiR t w.1 (dBlk (blk2 X.toD7.R.r) 1 (redFn (1 : GL (Fin (Vc X.toD7 i).rank) (LiftBrg.EA X)) w.1
            (LiftBrg.castGL hrk ((k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (LiftBrg.EA X))))))⁻¹ := by
    intro w g hg hgw
    by_cases hv : (w.1 : Pl X.toD7.host.E) ∈ (X.B.primes px).vGs
    · rw [if_pos hv]
      have hg' : g ∈ Formalism.L2.Col.HK X.B.R.nV _ X.B.R.r [X.B.R.t] := (hHv w hv g).1 hg
      have hb := Formalism.L2.Col.HK_le_blockUT _ _ _ _ hg'
      have e : Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1) w = Formalism.L2.Col.mtTyK I.Ch ((i : ℕ) + 1) ⟨w.1, hv⟩ :=
        Formalism.L2.Col.LevFam.glue_of_mem _ _ w hv
      have l1 : ((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv w).lam ⟨g, hg⟩ =
          ((Formalism.L2.Col.mtTyK I.Ch ((i : ℕ) + 1) ⟨w.1, hv⟩).lam ⟨g, hg'⟩)⁻¹ := by
        show ((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1) w).lam⁻¹) ⟨g, hg⟩ = _
        rw [MonoidHom.inv_apply, lev_eq_of_eq e g hg hg']
      have l2 : (Formalism.L2.Col.mtTyK I.Ch ((i : ℕ) + 1) ⟨w.1, hv⟩).lam ⟨g, hg'⟩ =
          (Formalism.L2.Col.chiAt I.Ch ⟨w.1, hv⟩ (i : ℕ))⁻¹
            (Formalism.L2.Col.blkDet X.B.R.nV _ (Formalism.L2.Col.coarse X.B.R.r [X.B.R.t]) 1 ⟨g, hb⟩) := by
        show Formalism.L2.Col.lamKV (Formalism.L2.Col.chiAt I.Ch ⟨w.1, hv⟩ ((i : ℕ) + 1 - 1)) X.B.R.nV X.B.R.r X.B.R.t ⟨g, hg'⟩ = _
        rw [Nat.add_sub_cancel]
        unfold Formalism.L2.Col.lamKV Formalism.L2.Col.lamK
        rw [MonoidHom.comp_apply, Formalism.L2.Col.detChar_apply]
        simp only [List.length_singleton, Finset.prod_range_one]
        rfl
      have d1 : dBlk (blkOf X.B.R.r X.B.R.t) 1 g =
          Formalism.L2.Col.blkDet X.B.R.nV _ (Formalism.L2.Col.coarse X.B.R.r [X.B.R.t]) 1 ⟨g, hb⟩ := (GlobalTheory.T.dBlk_eq_blkDet_coarse hnV g hb).1
      have d2 : dBlk (blkOf X.toD7.R.r X.toD7.R.t) 1 (redFn (1 : GL (Fin (Vc X.toD7 i).rank) (LiftBrg.EA X)) w.1
            (LiftBrg.castGL hrk ((k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (LiftBrg.EA X)))) =
          dBlk (blkOf X.B.R.r X.B.R.t) 1 g :=
        (congrArg _ (hcrk w.1)).trans ((generalLinearGroupCastOfEq_diagBlock_eq hrk _ _ _).trans (congrArg _ hgw.symm))
      rw [l1, l2, MonoidHom.inv_apply, inv_inv]
      refine (GlobalTheory.T.liftLevelCharacter_typePrime_eq_columnCharacter X px I U L hI hL i ⟨w.1, hv⟩ _).symm.trans ?_
      exact congrArg _ (d2.trans d1).symm

    · rw [if_neg hv]
      have hq' : (w.1 : Pl X.toD7.host.E) ∈ Formalism.L2.Col.QE I.sel t.1 := (Finset.mem_union.mp w.2).resolve_left hv
      have hb : g ∈ Formalism.L2.Col.blockUT X.B.R.nV _ X.B.R.r [X.B.R.t] := (hHq w hv g).1 hg
      have e : Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1) w =
          Formalism.L2.Col.mtTyQ X.B.R (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K) (Formalism.L2.Col.QE I.sel t.1)
            ⟨w.1, hq'⟩ := Formalism.L2.Col.LevFam.glue_of_not _ _ w hv
      have l1 : ((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv w).lam ⟨g, hg⟩ =
          ((Formalism.L2.Col.mtTyQ X.B.R (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K) (Formalism.L2.Col.QE I.sel t.1)
            ⟨w.1, hq'⟩).lam ⟨g, hb⟩)⁻¹ := by
        show ((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1) w).lam⁻¹) ⟨g, hg⟩ = _
        rw [MonoidHom.inv_apply, lev_eq_of_eq e g hg hb]
      have l2 : (Formalism.L2.Col.mtTyQ X.B.R (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K) (Formalism.L2.Col.QE I.sel t.1)
            ⟨w.1, hq'⟩).lam ⟨g, hb⟩ =
          Formalism.L2.DIV.resChar (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K) w.1
            (Formalism.L2.Col.blkDet X.B.R.nV _ (Formalism.L2.Col.coarse X.B.R.r [X.B.R.t]) 1 ⟨g, hb⟩) := by
        show Formalism.L2.Col.lamQP (t.1 : Formalism.L2.DIV.Chr X.B.fields.F X.B.fields.E X.B.fields.K) w.1 X.B.R.nV X.B.R.r X.B.R.t ⟨g, hb⟩ = _
        unfold Formalism.L2.Col.lamQP Formalism.L2.Col.lamQ
        rw [Formalism.L2.Col.detChar_apply]
        simp only [List.length_singleton, Finset.prod_range_one]
      have d1 : dBlk (blk2 X.B.R.r) 1 g =
          Formalism.L2.Col.blkDet X.B.R.nV _ (Formalism.L2.Col.coarse X.B.R.r [X.B.R.t]) 1 ⟨g, hb⟩ := (GlobalTheory.T.dBlk_eq_blkDet_coarse hnV g hb).2
      have d2 : dBlk (blk2 X.toD7.R.r) 1 (redFn (1 : GL (Fin (Vc X.toD7 i).rank) (LiftBrg.EA X)) w.1
            (LiftBrg.castGL hrk ((k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (LiftBrg.EA X)))) =
          dBlk (blk2 X.B.R.r) 1 g :=
        (congrArg _ (hcrk w.1)).trans ((generalLinearGroupCastOfEq_twoBlock_diagBlock_eq hrk _ _).trans (congrArg _ hgw.symm))
      rw [l1, l2]
      refine (map_inv (Units.map X.toD7.what₂.embLL.toMonoidHom) _).trans ?_
      congr 1
      refine (GlobalTheory.T.liftResidueTwistCharacter_eq_resChar X px I U L hI hV hL t w.1 hq' _).symm.trans ?_
      exact congrArg _ (d2.trans d1).symm

  obtain ⟨φ, hφ⟩ : ∃ φ : Pl X.toD7.host.E → ℂˣ, ∀ PP, φ PP =
      if PP ∈ (X.B.primes px).vGs then
        L.chi ((i : ℕ) + 1) PP (dBlk (blkOf X.toD7.R.r X.toD7.R.t) 1 (redFn (1 : GL (Fin (Vc X.toD7 i).rank) (LiftBrg.EA X)) PP
          (LiftBrg.castGL hrk ((k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (LiftBrg.EA X)))))
      else (L.xiR t PP (dBlk (blk2 X.toD7.R.r) 1 (redFn (1 : GL (Fin (Vc X.toD7 i).rank) (LiftBrg.EA X)) PP
          (LiftBrg.castGL hrk ((k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (LiftBrg.EA X))))))⁻¹ :=
    ⟨_, fun _ => rfl⟩
  have e1 : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).χ ⟨eG k, hk⟩ =
      levFn 1 (flag1L (L.datVt i t))
        (LiftBrg.castGL hrk ((k : Formalism.L2.Col.UAd X.toD7.sp.cm X.B.R.nV) : GL (Fin X.B.R.nV) (LiftBrg.EA X))) := by
    refine (levEnv_chi _ _ _ _ hk).trans ?_
    rw [hM k, hβ]
  have hch : (((levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).χ ⟨eG k, hk⟩)⁻¹ : ℂˣ) =
      Units.map X.toD7.what₂.embLL.toMonoidHom ((Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.chr
        (Formalism.L2.Col.redH X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t) _
          ((Bridge.colJEquiv X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t)
            (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp).symm k))) := by
    refine (congrArg (·⁻¹) e1).trans ?_
    refine Eq.trans ?_ (congrArg (Units.map X.toD7.what₂.embLL.toMonoidHom)
      (Formalism.L2.Col.LevFam.chr_apply (X := X.B.fields) (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv _).symm)
    refine Eq.trans ?_ (map_prod _ _ _).symm
    refine Eq.trans ?_ (Finset.prod_congr rfl fun w _ => ((perw w _ _ (hredw w)).trans (hφ w.1).symm).symm)
    refine (congrArg (·⁻¹) (levFn_datVt X L i t _)).trans ?_
    refine prod_glue (E := X.toD7.host.E) L.Pg (L.Q t) _ _ hPg hQ hdisj _ _ φ (fun PP hP => ?_) (fun PP hP => ?_)
    · exact (hφ PP).trans ((if_pos hP).trans (inv_inv _).symm)
    · exact (hφ PP).trans (if_neg (Finset.disjoint_right.1 hdisj hP))
  refine ⟨hch, fun hk1 => ?_⟩
  have hred1 := (Bridge.mem_principal_congruence_iff X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t)
    (((Bridge.colJEquiv X.toD7.sp.cm X.B.R.nV ∅ (LiftBrg.sgL X I U t)
      (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv.grp).symm k : Formalism.L2.Col.JH _ _ _ _ _) :
        Formalism.L2.Col.J0 X.toD7.sp.cm X.B.R.nV ∅)).1 (by rw [hm1]; exact hk1)
  refine inv_eq_one.mp (hch.trans ?_)
  refine (congrArg (Units.map X.toD7.what₂.embLL.toMonoidHom)
    (chr_eq_one (Formalism.L2.Col.mtTyKK I.Ch I.sel t.1 ((i : ℕ) + 1)).inv _ hred1)).trans ?_
  exact map_one _

end GlobalTheory.Mem.LevPres
