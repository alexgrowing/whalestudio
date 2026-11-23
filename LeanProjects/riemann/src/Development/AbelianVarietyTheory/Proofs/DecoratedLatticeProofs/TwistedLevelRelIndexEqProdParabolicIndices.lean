import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NotIsConjPlOfIdemSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemBlockUpperTriangularTwoIffLowerLeftZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.TwistIndex

open Classical

theorem index_pi_univ {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i)) :
    (Subgroup.pi Set.univ H).index = ∏ i, (H i).index := by
  simp_rw [Subgroup.index, ← Nat.card_pi]
  refine Nat.card_congr ((Quotient.congrRight (fun x y ↦ ?_)).trans (Setoid.piQuotientEquiv _).symm)
  rw [QuotientGroup.leftRel_pi]

theorem restrictedBlock_self_apply {κ : Type} [CommRing κ] {n : ℕ} (g : GL (Fin n) κ) : Formalism.L2.DIV.upperLeftBlock (le_refl n) g = g := by
  have hg : g ∈ (Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 n) : Subgroup (GL (Fin n) κ)) := by
    show (g : Matrix (Fin n) (Fin n) κ).BlockTriangular _
    intro i j hij
    simp [Formalism.L2.DIV.blk2] at hij
  apply Units.ext
  rw [Formalism.L2.DIV.upper_block_val_submatrix _ hg]
  ext i j
  simp [Fin.castLE]

variable {D : D7}

theorem mem_datY_iff (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) {r t j : ℕ} (hr hr' : r ≤ V.rank) (Pg Q : Finset (Pl D.host.E))
    (χ χ' : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (x : GL (Fin V.rank) (Lev.EAf D)) :
    x ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.datY V.rank r t j hr Pg Q (LevelP.triv _ _ _) χ ξ Lev.Frm.B) ↔
      x ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (Lev.datY V.rank r t j hr' Pg ∅ (LevelP.triv _ _ _) χ' ξ' Lev.Frm.B) ∧
        ∀ PP ∈ Q, Formalism.L2.DIV.redFn β PP x ∈ (Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) : Subgroup (GL (Fin V.rank) (kP PP))) := by
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    refine ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩, h5⟩, fun PP hP => ?_⟩
    · exact Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => absurd hP (Finset.notMem_empty _)
    · exact (Formalism.L2.DIV.mem_parah.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h4 PP) hP)).2
  · rintro ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, -⟩, h5⟩, h6⟩
    refine ⟨⟨⟨⟨h1, h2⟩, h3⟩, ?_⟩, h5⟩
    exact Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => Formalism.L2.DIV.mem_parah.2 ⟨h2, h6 PP hP⟩

theorem relIndex_twist : ∀ (D : D7) (c : Com D) (w : Twist D) (j : ℕ) (s : PiLocalization₂ D), w.Is c → j ≤ D.R.m → IsStage c w j s → ∀ hr χ ξ, Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L ≤ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β (Lev.datY s.V.rank D.R.r D.R.t j hr w.Pg ∅ (LevelP.triv _ _ _) χ ξ Lev.Frm.B) ∧ (((Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L).relIndex (Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β (Lev.datY s.V.rank D.R.r D.R.t j hr w.Pg ∅ (LevelP.triv _ _ _) χ ξ Lev.Frm.B)) : ℕ) : ℝ) = ∏ PP ∈ w.Q, idxQ PP j := by
  intro D c w j s hw _ hs hr' χ ξ
  obtain ⟨hr, hL, hflat⟩ := hs
  rw [hL]
  have hmem := fun x => mem_datY_iff s.V s.β hr hr' w.Pg w.Q w.chi χ w.ξ ξ (r := D.R.r) (t := D.R.t) (j := j) x
  refine ⟨fun x hx => ((hmem x).1 hx).1, ?_⟩
  have hSt : Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β (Lev.datY s.V.rank D.R.r D.R.t j hr' w.Pg ∅ (LevelP.triv _ _ _) χ ξ Lev.Frm.B) ≤
      Formalism.L2.DIV.St s.β := fun x hx => Formalism.L2.DIV.parLev_St hx.1
  let φ : Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β (Lev.datY s.V.rank D.R.r D.R.t j hr' w.Pg ∅ (LevelP.triv _ _ _) χ ξ Lev.Frm.B) →*
      (∀ PP : w.Q, GL (Fin s.V.rank) (kP PP.1)) :=
    MonoidHom.pi fun PP => (Formalism.L2.DIV.redAt s.β PP.1).comp (Subgroup.inclusion hSt)
  have hφ : ∀ x PP, φ x PP = Formalism.L2.DIV.redFn s.β PP.1 x.1 := by
    intro x PP
    unfold Formalism.L2.DIV.redFn
    rw [Formalism.L2.DIV.extendOne_of_mem _ (hSt x.2)]
    rfl
  have hcomap : (Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β (Lev.datY s.V.rank D.R.r D.R.t j hr w.Pg w.Q (LevelP.triv _ _ _) w.chi w.ξ Lev.Frm.B)).subgroupOf
      (Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β (Lev.datY s.V.rank D.R.r D.R.t j hr' w.Pg ∅ (LevelP.triv _ _ _) χ ξ Lev.Frm.B)) =
      (Subgroup.pi Set.univ fun PP : w.Q =>
        (Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 D.R.r) : Subgroup (GL (Fin s.V.rank) (kP PP.1)))).comap φ := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi, hmem]
    simp only [hφ]
    constructor
    · rintro ⟨-, h⟩ PP -
      exact h PP.1 PP.2
    · intro h
      exact ⟨x.2, fun PP hP => h ⟨PP, hP⟩ (Set.mem_univ _)⟩
  have hsurj : Function.Surjective φ := by
    intro g
    obtain ⟨N, hN, -⟩ := hflat.base
    obtain ⟨e, he⟩ := hw.com.split
    have hnc := GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum he
    let L' : LevDat D.host.E ℂ s.V.rank := Lev.datW s.V.rank c.Pg (LevelP.triv c.Pg s.V.rank ℂ) Lev.Frm.B
    have hlift : Lev.LiftsExist s.V s.β L' :=
      GlobalTheory.ParahoricLift.liftsExist s.V s.β L' s.Λ N hN (fun PP hP PP' hP' => by
        rcases hP' with h | h
        · exact hnc PP hP PP' h
        · exact absurd h (Finset.notMem_empty _)) (Finset.disjoint_empty_right _)
    let g0 : Formalism.L2.DIV.G0 L'.Pg L'.r := fun PP => if h : PP.1 ∈ w.Q then g ⟨PP.1, h⟩ else 1
    have h0 := hlift g0
    have hκ := h0.choose_spec
    have hκ1 : Lev.finE s.V h0.choose ∈ Formalism.L2.DIV.parLev D.sp.cm s.V.gram s.β L' := hκ.2.1
    have hκ2 : Formalism.L2.DIV.rTup s.β L' (Lev.finE s.V h0.choose) = g0 := hκ.2.2
    have hred : ∀ PP (h : PP ∈ c.Pg), Formalism.L2.DIV.redFn s.β PP (Lev.finE s.V h0.choose) = g0 ⟨PP, h⟩ := by
      intro PP h
      exact (restrictedBlock_self_apply _).symm.trans (congrFun hκ2 ⟨PP, h⟩)
    have hPg : ∀ PP ∈ w.Pg, Formalism.L2.DIV.redFn s.β PP (Lev.finE s.V h0.choose) = 1 := by
      intro PP hP
      have hc : PP ∈ c.Pg := by rw [hw.union]; exact Finset.mem_union_left _ hP
      rw [hred PP hc]
      have hq : PP ∉ w.Q := Finset.disjoint_left.1 hw.disj hP
      show (if h : PP ∈ w.Q then g ⟨PP, h⟩ else (1 : GL (Fin s.V.rank) (kP PP))) = 1
      exact dif_neg hq
    have hSt' := Formalism.L2.DIV.parLev_St hκ1
    have hxbig : Lev.finE s.V h0.choose ∈
        Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β (Lev.datY s.V.rank D.R.r D.R.t j hr' w.Pg ∅ (LevelP.triv _ _ _) χ ξ Lev.Frm.B) := by
      refine ⟨⟨⟨⟨Formalism.L2.DIV.parLev_UA hκ1, hSt'⟩, ?_⟩, ?_⟩, ?_⟩
      · exact Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP =>
          Formalism.L2.DIV.mem_parah.2 ⟨hSt', by rw [hPg PP hP]; exact Subgroup.one_mem _⟩
      · exact Subgroup.mem_iInf.2 fun PP => Subgroup.mem_iInf.2 fun hP => absurd hP (Finset.notMem_empty _)
      · show Formalism.L2.DIV.rTup s.β (Lev.datY s.V.rank D.R.r D.R.t j hr' w.Pg ∅ (LevelP.triv _ _ _) χ ξ Lev.Frm.B) (Lev.finE s.V h0.choose) ∈
          (⊥ : Subgroup (Formalism.L2.DIV.G0 w.Pg D.R.r))
        refine Subgroup.mem_bot.2 (funext fun PP => ?_)
        show Formalism.L2.DIV.upperLeftBlock hr' (Formalism.L2.DIV.redFn s.β PP.1 (Lev.finE s.V h0.choose)) = 1
        rw [hPg PP.1 PP.2]
        exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
    refine ⟨⟨_, hxbig⟩, funext fun PP => ?_⟩
    rw [hφ]
    have hc : PP.1 ∈ c.Pg := by rw [hw.union]; exact Finset.mem_union_right _ PP.2
    rw [hred PP.1 hc]
    show (if h : PP.1 ∈ w.Q then g ⟨PP.1, h⟩ else 1) = g PP
    rw [dif_pos PP.2]
  have hn : s.V.rank = D.R.r + j * D.R.t := hflat.rank
  rw [Subgroup.relIndex, hcomap, Subgroup.index_comap_of_surjective _ hsurj, index_pi_univ, Nat.cast_prod]
  refine Eq.trans ?_ (Finset.prod_coe_sort w.Q (fun PP => idxQ PP j))
  refine Finset.prod_congr rfl fun PP _ => ?_
  refine (GlobalTheory.ParabIndex.index_maxParabolic_GL_finiteField (kP PP.1) s.V.rank D.R.r (j * D.R.t) hn).trans ?_
  have hq : Nat.card (kP PP.1) = Ideal.absNorm PP.1.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hq, hn]
  rfl

end GlobalTheory.TwistIndex

end
