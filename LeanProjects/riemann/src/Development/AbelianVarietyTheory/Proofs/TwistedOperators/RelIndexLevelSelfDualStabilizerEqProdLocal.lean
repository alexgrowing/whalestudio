import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LiftsGen
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMemProjEqOnFinset
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockPartitionOfEqTwoBlock
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelPlacesUnionTwistPlacesSplitDisjointStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeLevelEqUnitaryInfFrameStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardBlockUpperTriangularSubgroupOfTopBlockStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
open Formalism.L2.DIV (kP Pl LevelP)

noncomputable section

namespace GlobalTheory.ParIndex

theorem gram_herm (D : D7) (V : HSp D) : Formalism.UG.IsHerm (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := by
  refine Matrix.ext fun i j => ?_
  show (D.sp.cm.sig : D.host.E →+* D.host.E) (V.gram j i) = V.gram i j
  exact V.herm.eq (V.frame j) (V.frame i)

theorem gram_det_ne (D : D7) (V : HSp D) : V.gram.det ≠ 0 :=
  ((GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V).2

theorem hermitianSpace_standard_lattice_span_eq_top (D : D7) (V : HSp D) :
    Submodule.span D.host.E (L0c D V) = ⊤ := by
  let f := V.frame.equivFun.toLinearMap
  let L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := V.L0.map (f.restrictScalars (𝓞 D.host.E))
  have hL : (L : Set (Fin V.rank → D.host.E)) = L0c D V := by
    ext v
    constructor
    · rintro ⟨x, hx, rfl⟩
      change ∑ i, V.frame.equivFun x i • V.frame i ∈ V.L0
      rwa [V.frame.sum_equivFun]
    · intro hv
      refine ⟨V.frame.equivFun.symm v, ?_, V.frame.equivFun.apply_symm_apply v⟩
      rw [Module.Basis.equivFun_symm_apply]
      exact hv
  rw [← hL, eq_top_iff]
  intro v _
  obtain ⟨x, rfl⟩ := V.frame.equivFun.surjective v
  have hx : x ∈ Submodule.span D.host.E (V.L0 : Set V.V) := by
    rw [V.standardTuple_isLattice.span_eq_top]; trivial
  have := Submodule.mem_map_of_mem (f := f) hx
  rw [Submodule.map_span] at this
  exact this

theorem relIndex_levV_latLev : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Hl : ∀ PP : ↥R.Pg, Subgroup (GL (Fin D.R.r) (kP PP.1))) (cl : ∀ PP : ↥R.Pg, Hl PP →* ℂˣ), GlobalTheory.Hk3.Core R F → P = LevelP.ofLocal Hl cl → (((GlobalTheory.AdelicScalar.levV R i t P m).relIndex (GlobalTheory.Mass.Levels.latLev (Vc D i)) : ℕ) : ℝ) = (∏ PP ∈ R.Pg.attach, (Nat.card (GL (Fin (Vc D i).rank) (kP PP.1)) : ℝ) / ((Nat.card (Hl PP) : ℝ) * (Nat.card (GL (Fin D.R.t) (kP PP.1)) : ℝ) * (Nat.card (kP PP.1) : ℝ) ^ (D.R.r * D.R.t))) * ∏ PP ∈ R.Q t, (Nat.card (GL (Fin (Vc D i).rank) (kP PP)) : ℝ) / ((Nat.card (GL (Fin D.R.r) (kP PP)) : ℝ) * (Nat.card (GL (Fin D.R.t) (kP PP)) : ℝ) * (Nat.card (kP PP) : ℝ) ^ (D.R.r * D.R.t)) := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R F i t P m Hl cl hC hP
  obtain ⟨c, hB⟩ := hC.lev.βV i
  rw [one_pow] at hB
  have hK := GlobalTheory.T.latticeLevel_eq_unitary_inf_frame_stabilizer D (Vc D i) (R.βV i) _ hB
  obtain ⟨hsplit, hdis⟩ := GlobalTheory.T.levelPlaces_union_twistPlaces_split_disjoint R F hC t
  have hspan : Submodule.span D.host.E ((R.ΛV i : Submodule (𝓞 D.host.E) _) : Set (Fin (Vc D i).rank → D.host.E)) = ⊤ := by
    rw [eq_top_iff, ← hermitianSpace_standard_lattice_span_eq_top D (Vc D i)]
    refine Submodule.span_mono fun x hx => ?_
    have := hB.2.2.2.1 x hx
    rwa [Nat.cast_one, one_smul] at this
  have hdual : dualSet (D.sp.cm.sig : D.host.E →+* D.host.E) (Vc D i).gram (R.ΛV i) = ((R.ΛV i : Submodule (𝓞 D.host.E) _) : Set (Fin (Vc D i).rank → D.host.E)) := by
    have e := Formalism.IndefR.Fin.Lifts.span_dualSet_eq (D.sp.cm.sig : D.host.E →+* D.host.E) (Vc D i).gram (R.ΛV i)
    have h := hB.2.1
    unfold Formalism.L2.Herm.dualL at h
    rw [h] at e
    exact e.symm
  have hn : (Vc D i).rank = D.R.r + D.R.t := by
    rw [D.sp.V_rank _ (Nat.le_add_left _ _) i.2]; rfl
  have hSt : ∀ x ∈ GlobalTheory.Mass.Levels.latLev (Vc D i), x ∈ Formalism.L2.DIV.St (R.βV i) := by
    intro x hx; rw [hK] at hx; exact hx.2
  set Ts := R.Pg ∪ R.Q t with hTs
  let φ : GlobalTheory.Mass.Levels.latLev (Vc D i) →* (∀ PP : ↥Ts, GL (Fin (Vc D i).rank) (kP PP.1)) :=
    { toFun := fun x PP => redFn (R.βV i) PP.1 x
      map_one' := by funext PP; exact redFn_one _
      map_mul' := fun x y => by funext PP; exact redFn_mul (hSt _ x.2) (hSt _ y.2) _ }
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx, hred⟩ := Formalism.IndefR.Fin.Lifts.redSurj_sd D.sp.cm Ts (gram_herm D (Vc D i))
      (isUnit_iff_ne_zero.2 (gram_det_ne D (Vc D i))) hspan hdual hB.1 hsplit y
    exact ⟨⟨x, by rw [hK]; exact hx⟩, funext hred⟩
  let Bl : ∀ PP : ↥Ts, Subgroup (GL (Fin (Vc D i).rank) (kP PP.1)) := fun PP =>
    if h : PP.1 ∈ R.Pg then parSub (r_le_V i) (Hl ⟨PP.1, h⟩) else blockTri (blk2 D.R.r)
  have hBp : ∀ (PP : ↥Ts) (h : PP.1 ∈ R.Pg), Bl PP = parSub (r_le_V i) (Hl ⟨PP.1, h⟩) := fun PP h => dif_pos h
  have hBn : ∀ (PP : ↥Ts), PP.1 ∉ R.Pg → Bl PP = blockTri (blk2 D.R.r) := fun PP h => dif_neg h
  have hcomap : (GlobalTheory.AdelicScalar.levV R i t P m).subgroupOf (GlobalTheory.Mass.Levels.latLev (Vc D i)) =
      (Subgroup.pi Set.univ Bl).comap φ := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_pi]
    have hxK : (x : GL (Fin (Vc D i).rank) (Lev.EAf D)) ∈ Formalism.L2.DIV.UA D.sp.cm (Vc D i).gram ⊓ Formalism.L2.DIV.St (R.βV i) := by
      rw [← hK]; exact x.2
    subst hP
    constructor
    · intro hx PP _
      have hx' := (mem_lev.1 hx)
      obtain ⟨-, -, hg, hq⟩ := mem_parLev.1 hx'.1
      show redFn (R.βV i) PP.1 x ∈ Bl PP
      by_cases h : PP.1 ∈ R.Pg
      · rw [hBp PP h]
        refine ⟨?_, ?_⟩
        · have := hg PP.1 h
          change redFn (R.βV i) PP.1 x ∈ blockTri (blkOf D.R.r D.R.t) at this
          rwa [blockTri_blkOf_eq hn] at this
        · exact hx'.2 ⟨PP.1, h⟩ (Set.mem_univ _)
      · rw [hBn PP h]
        have hQ : PP.1 ∈ R.Q t := by
          rcases Finset.mem_union.1 PP.2 with h' | h'
          · exact absurd h' h
          · exact h'
        exact hq PP.1 hQ
    · intro hx
      have hx1 : ∀ PP (h : PP ∈ Ts), redFn (R.βV i) PP x ∈ Bl ⟨PP, h⟩ := fun PP h => hx ⟨PP, h⟩ (Set.mem_univ _)
      refine mem_lev.2 ⟨mem_parLev.2 ⟨hxK.1, hxK.2, fun PP hPP => ?_, fun PP hPP => ?_⟩, ?_⟩
      · have := hx1 PP (Finset.mem_union_left _ hPP)
        rw [hBp ⟨PP, Finset.mem_union_left _ hPP⟩ hPP] at this
        show _ ∈ blockTri (blkOf D.R.r D.R.t)
        rw [blockTri_blkOf_eq hn]
        exact this.1
      · have := hx1 PP (Finset.mem_union_right _ hPP)
        by_cases h : PP ∈ R.Pg
        · rw [hBp ⟨PP, Finset.mem_union_right _ hPP⟩ h] at this
          exact this.1
        · rw [hBn ⟨PP, Finset.mem_union_right _ hPP⟩ h] at this
          exact this
      · intro PP _
        have := hx1 PP.1 (Finset.mem_union_left _ PP.2)
        rw [hBp ⟨PP.1, Finset.mem_union_left _ PP.2⟩ PP.2] at this
        exact this.2

  have hidx : (((GlobalTheory.AdelicScalar.levV R i t P m).relIndex (GlobalTheory.Mass.Levels.latLev (Vc D i)) : ℕ) : ℝ) =
      ∏ PP : ↥Ts, (((Bl PP).index : ℕ) : ℝ) := by
    rw [Subgroup.relIndex, hcomap, Subgroup.index_comap_of_surjective _ hφ, GlobalTheory.index_pi_univ_dep, Nat.cast_prod]
  let g : Pl D.host.E → ℝ := fun PP =>
    if h : PP ∈ R.Pg then (Nat.card (GL (Fin (Vc D i).rank) (kP PP)) : ℝ) / ((Nat.card (Hl ⟨PP, h⟩) : ℝ) *
      (Nat.card (GL (Fin D.R.t) (kP PP)) : ℝ) * (Nat.card (kP PP) : ℝ) ^ (D.R.r * D.R.t))
    else (Nat.card (GL (Fin (Vc D i).rank) (kP PP)) : ℝ) / ((Nat.card (GL (Fin D.R.r) (kP PP)) : ℝ) *
      (Nat.card (GL (Fin D.R.t) (kP PP)) : ℝ) * (Nat.card (kP PP) : ℝ) ^ (D.R.r * D.R.t))
  have hloc : ∀ PP : ↥Ts, (((Bl PP).index : ℕ) : ℝ) = g PP.1 := by
    intro PP
    haveI : PP.1.asIdeal.IsMaximal := PP.1.isMaximal
    letI : Field (kP PP.1) := Ideal.Quotient.field _
    have hc := Subgroup.card_mul_index (Bl PP)
    have hpos : (Nat.card (Bl PP) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := Bl PP)).ne'
    have e1 : (((Bl PP).index : ℕ) : ℝ) = (Nat.card (GL (Fin (Vc D i).rank) (kP PP.1)) : ℝ) / (Nat.card (Bl PP) : ℝ) := by
      rw [eq_div_iff hpos, mul_comm]
      exact_mod_cast hc
    rw [e1]
    by_cases h : PP.1 ∈ R.Pg
    · have e2 : Bl PP = parSub (r_le_V i) (Hl ⟨PP.1, h⟩) := hBp PP h
      simp only [g, dif_pos h]
      rw [e2, GlobalTheory.T.card_blockUpperTriangularSubgroupOfTopBlock (kP PP.1) _ _ _ (r_le_V i) hn]
      push_cast; ring
    · have e2 : Bl PP = parSub (r_le_V i) ⊤ := by
        rw [hBn PP h]
        ext x
        simp [mem_parSub]
      simp only [g, dif_neg h]
      rw [e2, GlobalTheory.T.card_blockUpperTriangularSubgroupOfTopBlock (kP PP.1) _ _ _ (r_le_V i) hn, Subgroup.card_top]
      push_cast; ring
  rw [hidx, Finset.prod_congr rfl (fun PP _ => hloc PP), Finset.prod_coe_sort Ts g, hTs, Finset.prod_union hdis]
  congr 1
  · rw [← Finset.prod_attach R.Pg g]
    refine Finset.prod_congr rfl fun PP _ => ?_
    simp only [g, dif_pos PP.2]
  · refine Finset.prod_congr rfl fun PP hPP => ?_
    have h : PP ∉ R.Pg := Finset.disjoint_right.1 hdis hPP
    simp only [g, dif_neg h]

end GlobalTheory.ParIndex

end
