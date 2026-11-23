import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGAnalytic
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.DataInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsComplementUnitaryMulActionLocalInnerDatum
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TsumTransversalEqTsumOrbitQuotientGeneral
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryComplementMovesHermitianTermsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TsumInvStabilizerEqTsumMulFiberStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedLatticesLocalDataUnimodularStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalLatticesCountEqProdLocalCountsBadPlacesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TsumRationalClassesEqProdLocalSumsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsometryFixingSpanPreservesGluedLatticesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteRationalStabiliserGluedLatticeLocalDataStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GlueCount

theorem mem_isometriesFixingBothFrames_iff_unitriangular : ∀ (D : D7) {T T' : D.host.E} (F G : LFlag (VS D) D.R.rS T) (F' G' : LFlag (VS D) D.R.rS T'), Tri D.host.E (frame F) (frame G) → Tri D.host.E (frame F') (frame G') → ∀ g : GV D, g ∈ H0 F F' ↔ g ∈ Formalism.L2.SG.Pf.Cnt.isomFix (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D G.fl G') := by
  intro D T T' F G F' G' hG hG' g

  have fwd : ∀ {f h : Fin (D.R.rS + 1) → (VS D).V}, Tri D.host.E f h → (∀ a, g (f a) = f a) → ∀ a, g (h a) = h a := by
    rintro f h ⟨A, -, hC⟩ hf a
    rw [hC a, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, hf b]
  have bwd : ∀ {f h : Fin (D.R.rS + 1) → (VS D).V}, Tri D.host.E f h → (∀ a, g (h a) = h a) → ∀ a, g (f a) = f a := by
    rintro f h ⟨A, ⟨hlow, hdiag⟩, hC⟩ hh a
    induction a using WellFoundedLT.induction with
    | _ a ih =>
      have hsplit : h a = f a + ∑ b ∈ Finset.univ.filter (fun b => b < a), A b a • f b := by
        rw [hC a, ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun b => b < a)]
        have hrest : ∑ b ∈ Finset.univ.filter (fun b => ¬ b < a), A b a • f b = f a := by
          rw [Finset.sum_eq_single_of_mem a (by simp)]
          · rw [hdiag, one_smul]
          · intro b hb hba
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hb
            rw [hlow b a (lt_of_le_of_ne hb (Ne.symm hba)), zero_smul]
        rw [hrest, add_comm]
      have h1 := hh a
      rw [hsplit, map_add, map_sum] at h1
      have h2 : ∑ b ∈ Finset.univ.filter (fun b => b < a), g (A b a • f b) =
          ∑ b ∈ Finset.univ.filter (fun b => b < a), A b a • f b := by
        refine Finset.sum_congr rfl fun b hb => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
        rw [map_smul, ih b hb]
      rw [h2] at h1
      exact add_right_cancel h1
  constructor
  · rintro ⟨hiso, hF, hF'⟩
    refine ⟨hiso, fun x hx => ?_⟩
    have hle : Formalism.L2.SG.Pf.Cnt.UPair D G.fl G' ≤ LinearMap.ker ((g : (VS D).V →ₗ[D.host.E] (VS D).V) - LinearMap.id) := by
      unfold Formalism.L2.SG.Pf.Cnt.UPair
      rw [Submodule.span_le]
      rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
      · simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, sub_eq_zero]
        exact fwd hG hF a
      · simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, sub_eq_zero]
        exact fwd hG' hF' a
    have := hle hx
    simpa [sub_eq_zero] using this
  · rintro ⟨hiso, hU⟩
    have hG1 : ∀ a, g (frame G a) = frame G a := fun a =>
      hU _ (Submodule.subset_span (Or.inl ⟨a, rfl⟩))
    have hG2 : ∀ a, g (frame G' a) = frame G' a := fun a =>
      hU _ (Submodule.subset_span (Or.inr ⟨a, rfl⟩))
    exact ⟨hiso, bwd hG hG1, bwd hG' hG2⟩

theorem glue_stable : ∀ (D : D7) (U : Submodule D.host.E (VS D).V) (M : Submodule (𝓞 D.host.E) (VS D).V), ∀ g ∈ Formalism.L2.SG.Pf.Cnt.isomFix (VS D).hT U, ∀ Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT U M, Formalism.HermitianLatticesTheory.gmap g Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT U M :=
  GlobalTheory.T.isometryFixingSpan_preserves_gluedLattices

theorem loc_ext : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)), Based Z FP (Tu D u) (Tu D u') F F' → ∀ g ∈ H0 F F', ∀ p, ∃ g', GlobalTheory.Unfold.Ext p g g' ∧ GlobalTheory.InnerDatumAct.InU (FP p) g' ∧ ∀ g'', GlobalTheory.Unfold.Ext p g g'' → g'' = g' := by
  intro D Z FP u u' F F' hB g hg p
  obtain ⟨g', hE, hU, huniq, -, -⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D Z p g hg.1
  refine ⟨g', hE, ⟨⟨hU, fun b => ?_⟩, ⟨hU, fun b => ?_⟩⟩, fun g'' h'' => huniq g'' h''⟩
  · rw [(hB p).1]
    show g' (frFac Z.δ p b • baseChange₂ D p (frame F b)) = frFac Z.δ p b • baseChange₂ D p (frame F b)
    rw [map_smul, hE, hg.2.1 b]
  · rw [(hB p).2.1]
    show g' (frFac Z.δ p b • baseChange₂ D p (frame F' b)) = frFac Z.δ p b • baseChange₂ D p (frame F' b)
    rw [map_smul, hE, hg.2.2 b]

theorem stab_finite : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F G : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' G' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (P : Finset (PlF D)) (d0 : Dat Z FP), 4 * D.R.rS + 7 ≤ D.R.k → BaseOK (Tu D u) (Tu D u') F F' P d0 → StdOff Z P F G F' G' → TotPos (Gval F F') → ∀ (Λ : LV D) (y : Dat Z FP), Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D G.fl G') (Formalism.L2.SG.Pf.Cnt.MMof D G.fl G') → Λ ∈ globSet G G' y → (stabY F F' y).Finite :=
  GlobalTheory.T.finite_rationalStabiliser_gluedLattice_localData

theorem rank_Vp' (D : D7) (p : PlF D) : Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have h1 := D.R.r_eq
  have h2 : 2 * D.R.rS + 2 = D.R.m := by
    have hm2 := D.R.two_le_m
    obtain ⟨j, hj⟩ := D.R.m_even
    simp only [Formalism.BasicNotions.Ranks.rS]; omega
  omega

theorem locSet_encard_rel : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F G : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' G' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (P : Finset (PlF D)) (d0 : Dat Z FP), 4 * D.R.rS + 7 ≤ D.R.k → BaseOK (Tu D u) (Tu D u') F F' P d0 → StdOff Z P F G F' G' → ∀ (p : PlF D) (d d' : LocNG.Datum (FP p)), LocNG.Datum.Rel d d' → ((locSet G G' p d).encard : ℝ≥0∞) = ((locSet G G' p d').encard : ℝ≥0∞) := by
  intro D Z FP u u' F G F' G' P d0 _ hB _ p
  have aux : ∀ g ∈ (FP p).UW0, ∀ d d' : LocNG.Datum (FP p), LocNG.Datum.Moves g d d' →
      (locSet G G' p d).Nonempty → (locSet G G' p d).encard = (locSet G G' p d').encard := by
    intro g hg d d' hmv ⟨Λ, hΛ⟩
    obtain ⟨n, hn, hf, -⟩ := hΛ.1.2.2.1
    obtain ⟨n', hn', hf', -⟩ := hΛ.1.2.2.2.1
    have key := (GlobalTheory.T.unitaryComplement_moves_hermitianTerms (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p) (rank_Vp' D p)
      (hB.2.1 p) _ _ ⟨n, hn, hf⟩ ⟨n', hn', hf'⟩ g hg d d' hmv).2
    have hset : locSet G G' p d' = LocNG.img g '' locSet G G' p d := key.symm
    rw [hset]
    refine (Set.InjOn.encard_image fun x _ y _ hxy => ?_).symm
    exact Submodule.map_injective_of_injective (f := (g : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p).restrictScalars (Z.M p).L.O)
      g.injective hxy
  have back : ∀ g ∈ (FP p).UW0, ∀ d d' : LocNG.Datum (FP p), LocNG.Datum.Moves g d d' →
      LocNG.Datum.Moves g⁻¹ d' d := by
    intro g hg d d' hmv
    have hU := GlobalTheory.InnerDatumAct.inU_of_mem hg
    have hUi := GlobalTheory.InnerDatumAct.inU_of_mem ((FP p).UW0.inv_mem hg)
    have h1 := GlobalTheory.InnerDatumAct.moves_act hUi d'
    have h2 := GlobalTheory.InnerDatumAct.moves_comp hU hmv h1
    rw [inv_mul_cancel] at h2
    have h3 := GlobalTheory.InnerDatumAct.moves_unique (GlobalTheory.InnerDatumAct.inU_of_mem ((FP p).UW0.one_mem))
      (GlobalTheory.InnerDatumAct.moves_one d) h2
    rw [h3]
    exact h1
  rintro d d' ⟨g, hg, hmv⟩
  by_cases hne : (locSet G G' p d).Nonempty
  · rw [aux g hg d d' hmv hne]
  by_cases hne' : (locSet G G' p d').Nonempty
  · rw [aux g⁻¹ ((FP p).UW0.inv_mem hg) d' d (back g hg d d' hmv) hne']
  rw [Set.not_nonempty_iff_eq_empty.1 hne, Set.not_nonempty_iff_eq_empty.1 hne']

theorem encard_stab_smul {Γ α : Type} [Group Γ] [MulAction Γ α] (g : Γ) (a : α) :
    ((MulAction.stabilizer Γ (g • a) : Set Γ).encard) = ((MulAction.stabilizer Γ a : Set Γ).encard) := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, Subgroup.coe_map]
  exact (MulAut.conj g).injective.injOn.encard_image

end GlobalTheory.GlueCount

namespace GlobalTheory.GlueCount

theorem glue_count : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F G : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F' G' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (P : Finset (PlF D)) (d0 : Dat Z FP), 4 * D.R.rS + 7 ≤ D.R.k → BaseOK (Tu D u) (Tu D u') F F' P d0 → StdOff Z P F G F' G' → TotPos (Gval F F') → ∀ (R : ∀ p, LocNG.Reps (FP p)) (V : ℝ), 0 ≤ V → MassLaw F F' P d0 V → ∀ s : Finset (LV D), Glue G G' s → ENNReal.ofReal (glueSum G G' s) = ENNReal.ofReal V * ∏ p ∈ P, locSum G G' p (R p) (d0 p) := by
  intro D Z FP u u' F G F' G' P d0 hk hB hS hTP R V hV hM s hs
  set Γ := Formalism.L2.SG.Pf.Cnt.isomFix (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D G.fl G') with hΓ
  have hH0 : ∀ g : GV D, g ∈ H0 F F' ↔ g ∈ Γ := mem_isometriesFixingBothFrames_iff_unitriangular D F G F' G' hS.1 hS.2.1

  letI actL : MulAction Γ (LV D) :=
    { smul := fun g Λ => Formalism.HermitianLatticesTheory.gmap g.1 Λ
      one_smul := fun Λ => by
        show Λ.map (((1 : GV D) : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) = Λ
        exact Submodule.map_id Λ
      mul_smul := fun a b Λ => by
        show Λ.map (((a.1 * b.1 : GV D) : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E)) =
          (Λ.map (((b.1 : GV D) : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E))).map
            (((a.1 : GV D) : (VS D).V →ₗ[D.host.E] (VS D).V).restrictScalars (𝓞 D.host.E))
        rw [← Submodule.map_comp]
        rfl }
  have hsmulL : ∀ (g : Γ) (Λ : LV D), g • Λ = Formalism.HermitianLatticesTheory.gmap g.1 Λ := fun _ _ => rfl

  set GS := Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D G.fl G') (Formalism.L2.SG.Pf.Cnt.MMof D G.fl G') with hGS
  have hstab : ∀ (g : Γ) (Λ : LV D), Λ ∈ GS → g • Λ ∈ GS := fun g Λ hΛ =>
    glue_stable D _ _ g.1 g.2 Λ hΛ
  letI actS : MulAction Γ {Λ : LV D // Λ ∈ GS} :=
    { smul := fun g x => ⟨g • x.1, hstab g x.1 x.2⟩
      one_smul := fun x => Subtype.ext (one_smul Γ x.1)
      mul_smul := fun a b x => Subtype.ext (mul_smul a b x.1) }
  have hsmulS : ∀ (g : Γ) (x : {Λ : LV D // Λ ∈ GS}), (g • x).1 = Formalism.HermitianLatticesTheory.gmap g.1 x.1 := fun _ _ => rfl

  have hext : ∀ (g : Γ) (p : PlF D), ∃ g', GlobalTheory.Unfold.Ext p g.1 g' ∧ GlobalTheory.InnerDatumAct.InU (FP p) g' ∧
      ∀ g'', GlobalTheory.Unfold.Ext p g.1 g'' → g'' = g' := fun g p =>
    loc_ext D Z FP u u' F F' hB.1 g.1 ((hH0 g.1).2 g.2) p
  let ex : (g : Γ) → (p : PlF D) → (Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p) := fun g p => (hext g p).choose
  have hexE : ∀ g p, GlobalTheory.Unfold.Ext p g.1 (ex g p) := fun g p => (hext g p).choose_spec.1
  have hexU : ∀ g p, GlobalTheory.InnerDatumAct.InU (FP p) (ex g p) := fun g p => (hext g p).choose_spec.2.1
  have hexu : ∀ g p g'', GlobalTheory.Unfold.Ext p g.1 g'' → g'' = ex g p := fun g p => (hext g p).choose_spec.2.2
  let sm : Γ → Dat Z FP → Dat Z FP := fun g y p => GlobalTheory.InnerDatumAct.act (hexU g p) (y p)
  have keyY : ∀ (g : Γ) (y y' : Dat Z FP), RMoves g.1 y y' ↔ sm g y = y' := by
    intro g y y'
    constructor
    · intro h
      funext p
      obtain ⟨g', hE, hMv⟩ := h p
      rw [hexu g p g' hE] at hMv
      exact GlobalTheory.InnerDatumAct.moves_unique (hexU g p) (GlobalTheory.InnerDatumAct.moves_act _ _) hMv
    · rintro rfl p
      exact ⟨_, hexE g p, GlobalTheory.InnerDatumAct.moves_act _ _⟩
  letI actY : MulAction Γ (Dat Z FP) :=
    { smul := sm
      one_smul := fun y => (keyY 1 y y).1 (fun p => ⟨1, fun x => rfl, GlobalTheory.InnerDatumAct.moves_one _⟩)
      mul_smul := fun a b y => (keyY (a * b) y (sm a (sm b y))).1 (fun p =>
        ⟨ex a p * ex b p, fun x => by
            rw [LinearEquiv.mul_apply, hexE b p x, hexE a p]
            rfl,
          GlobalTheory.InnerDatumAct.moves_comp (hexU b p) (GlobalTheory.InnerDatumAct.moves_act _ _)
            (GlobalTheory.InnerDatumAct.moves_act _ _)⟩) }
  have hRM : ∀ (g : Γ) (y : Dat Z FP), RMoves g.1 y (sm g y) := fun g y => (keyY g y _).2 rfl
  have hGR : ∀ y y' : Dat Z FP, GRel F F' y y' ↔ ∃ g : Γ, sm g y = y' := by
    intro y y'
    constructor
    · rintro ⟨h, hh, hr⟩
      exact ⟨⟨h, (hH0 h).1 hh⟩, (keyY _ _ _).1 hr⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g.1, (hH0 _).2 g.2, hRM g y⟩
  have hstabY : ∀ y : Dat Z FP, stabY F F' y = Subtype.val '' (MulAction.stabilizer Γ y : Set Γ) := by
    intro y
    ext h
    constructor
    · rintro ⟨hh, hr⟩
      exact ⟨⟨h, (hH0 h).1 hh⟩, (keyY _ _ _).1 hr, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨(hH0 _).2 g.2, (keyY g y y).2 hg⟩
  have hstabYe : ∀ y : Dat Z FP, (stabY F F' y).encard = (MulAction.stabilizer Γ y : Set Γ).encard := by
    intro y
    rw [hstabY]
    exact Subtype.val_injective.injOn.encard_image

  have hGD := fun Λ => GlobalTheory.T.mem_gluedLattices_iff_existsUnique_localDatum D Z FP u u' F G F' G' P d0 hk hB hS Λ
  let π : {Λ : LV D // Λ ∈ GS} → Dat Z FP := fun x => ((hGD x.1).1.1 x.2).choose
  have hπ : ∀ x : {Λ : LV D // Λ ∈ GS}, x.1 ∈ globSet G G' (π x) := fun x => ((hGD x.1).1.1 x.2).choose_spec
  have hπu : ∀ (x : {Λ : LV D // Λ ∈ GS}) (y : Dat Z FP), x.1 ∈ globSet G G' y → π x = y :=
    fun x y hy => (hGD x.1).2.1 _ _ (hπ x) hy
  have hπeq : ∀ (g : Γ) (x : {Λ : LV D // Λ ∈ GS}), π (g • x) = sm g (π x) := by
    intro g x
    apply hπu
    exact ((hGD x.1).2.2.2 (π x) (sm g (π x)) g.1 ((hH0 _).2 g.2) (hRM g _)).1 (hπ x)
  have hfin : ∀ y : Dat Z FP, (∃ x, π x = y) → Finite (MulAction.stabilizer Γ y) := by
    rintro y ⟨x, rfl⟩
    have h1 := stab_finite D Z FP u u' F G F' G' P d0 hk hB hS hTP x.1 (π x) x.2 (hπ x)
    rw [hstabY] at h1
    exact (h1.of_finite_image Subtype.val_injective.injOn).to_subtype
  have horbit := GlobalTheory.T.tsum_inv_card_stabilizer_eq_tsum_mul_card_fiber π hπeq hfin

  let ι : s → {Λ : LV D // Λ ∈ GS} := fun a => ⟨a.1, hs.1 a.1 a.2⟩
  have hcover : ∀ x : {Λ : LV D // Λ ∈ GS}, True → ∃ (a : s) (g : Γ), g • ι a = x := by
    intro x _
    obtain ⟨Λ₁, ⟨hΛ₁, g, hg, he⟩, -⟩ := hs.2.1 x.1 x.2
    exact ⟨⟨Λ₁, hΛ₁⟩, ⟨g, hg⟩, Subtype.ext he⟩
  have hinj : ∀ a b : s, (∃ g : Γ, g • ι a = ι b) → a = b := by
    rintro a b ⟨g, hg⟩
    apply Subtype.ext
    exact (hs.2.1 b.1 (hs.1 b.1 b.2)).unique ⟨a.2, g.1, g.2, congrArg Subtype.val hg⟩
      ⟨b.2, 1, Γ.one_mem, one_smul Γ b.1⟩
  have htr := (GlobalTheory.tsum_transversal_eq_tsum_orbitQuotient ι (fun _ => True) (fun _ _ _ => trivial)
    (fun _ => trivial) hcover hinj).2 (fun x => ((MulAction.stabilizer Γ x : Set Γ).encard : ℝ≥0∞)⁻¹)
    (fun g x _ => by rw [encard_stab_smul])
  simp only [if_true] at htr
  have hfixS : ∀ x : {Λ : LV D // Λ ∈ GS}, Formalism.L2.SG.Pf.Cnt.stabFix (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D G.fl G') x.1 =
      Subtype.val '' (MulAction.stabilizer Γ x : Set Γ) := by
    intro x
    ext g
    constructor
    · rintro ⟨hg, he⟩
      exact ⟨⟨g, hg⟩, Subtype.ext he, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g.2, congrArg Subtype.val (MulAction.mem_stabilizer_iff.1 hg)⟩
  have hLHS : ENNReal.ofReal (glueSum G G' s) = ∑' a : s, ((MulAction.stabilizer Γ (ι a) : Set Γ).encard : ℝ≥0∞)⁻¹ := by
    unfold glueSum
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
    rw [← Finset.tsum_subtype s]
    congr 1
    funext a
    have hfin' := hs.2.2 a.1 a.2
    have he : (Formalism.L2.SG.Pf.Cnt.stabFix (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D G.fl G') a.1).encard =
        (MulAction.stabilizer Γ (ι a) : Set Γ).encard := by
      rw [hfixS (ι a)]
      exact Subtype.val_injective.injOn.encard_image
    rw [← he, Nat.card_coe_set_eq, ← hfin'.cast_ncard_eq]
    have hpos : 0 < (Formalism.L2.SG.Pf.Cnt.stabFix (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D G.fl G') a.1).ncard :=
      (Set.ncard_pos hfin').2 ⟨1, Γ.one_mem, one_smul Γ a.1⟩
    rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast hpos), ENNReal.ofReal_natCast]
    simp

  let g0 : Dat Z FP → ℝ≥0∞ := fun y =>
    ((MulAction.stabilizer Γ y : Set Γ).encard : ℝ≥0∞)⁻¹ * ((π ⁻¹' {y}).encard : ℝ≥0∞)
  have hfib : ∀ y : Dat Z FP, (π ⁻¹' {y}).encard = (globSet G G' y).encard := by
    intro y
    have : Subtype.val '' (π ⁻¹' {y}) = globSet G G' y := by
      ext Λ
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hx' : π x = y := hx
        exact hx' ▸ hπ x
      · intro hΛ
        have hΛG : Λ ∈ GS := (hGD Λ).1.2 ⟨y, hΛ⟩
        exact ⟨⟨Λ, hΛG⟩, hπu ⟨Λ, hΛG⟩ y hΛ, rfl⟩
    rw [← this]
    exact (Subtype.val_injective.injOn.encard_image).symm
  let φ : ∀ p, LocNG.Datum (FP p) → ℝ≥0∞ := fun p d => ((locSet G G' p d).encard : ℝ≥0∞)
  have hpt : ∀ y : Dat Z FP, (if (∀ p, p ∉ P → LocNG.Datum.Rel (d0 p) (y p)) ∧ {p | y p ≠ d0 p}.Finite then
      (((stabY F F' y).encard : ℝ≥0∞))⁻¹ * ∏ p ∈ P, φ p (y p) else 0) = g0 y := by
    intro y
    by_cases hc : (∀ p, p ∉ P → LocNG.Datum.Rel (d0 p) (y p)) ∧ {p | y p ≠ d0 p}.Finite
    · rw [if_pos hc, hstabYe]
      show _ = _ * _
      rw [hfib, GlobalTheory.T.globalLattices_count_eq_prod_localCounts_badPlaces D Z FP u u' F G F' G' P d0 hk hB hS y hc.1 hc.2]
    · rw [if_neg hc]
      have hemp : π ⁻¹' {y} = ∅ := by
        ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        intro hx
        exact hc ((hGD x.1).2.2.1 y (hx ▸ hπ x))
      show 0 = _ * _
      rw [hemp, Set.encard_empty, ENat.toENNReal_zero, mul_zero]
  have hcls : ∀ (g : Γ) (y : Dat Z FP), g0 (sm g y) = g0 y := by
    intro g y
    have h1 : (MulAction.stabilizer Γ (sm g y) : Set Γ).encard = (MulAction.stabilizer Γ y : Set Γ).encard :=
      @encard_stab_smul Γ (Dat Z FP) _ actY g y
    have h2 : π ⁻¹' {sm g y} = (fun x => g • x) '' (π ⁻¹' {y}) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_image]
      constructor
      · intro hx
        refine ⟨g⁻¹ • x, ?_, smul_inv_smul g x⟩
        rw [hπeq, hx]
        exact @inv_smul_smul Γ (Dat Z FP) _ actY g y
      · rintro ⟨x', hx', rfl⟩
        rw [hπeq, hx']
    show _ * _ = _ * _
    rw [h1, h2, (MulAction.injective g).injOn.encard_image]
  have hrel : ∀ a b : Dat Z FP, GRel (Z := Z) (FP := FP) F F' a b ↔ (@MulAction.orbitRel Γ (Dat Z FP) _ actY) b a := by
    intro a b
    rw [hGR, @MulAction.orbitRel_apply Γ (Dat Z FP) _ actY]
    rfl

  have hφrel : ∀ p d d', LocNG.Datum.Rel d d' → φ p d = φ p d' := fun p d d' h =>
    locSet_encard_rel D Z FP u u' F G F' G' P d0 hk hB hS p d d' h
  have hφzero : ∀ p d, (¬ ∃ τ, LocNG.IsTermOver (FP p) d τ) → φ p d = 0 := by
    intro p d hd
    have hemp : locSet G G' p d = ∅ := by
      ext Λ
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hΛ
      exact hd ⟨_, hΛ.1⟩
    show ((locSet G G' p d).encard : ℝ≥0∞) = 0
    rw [hemp, Set.encard_empty, ENat.toENNReal_zero]
  have hreg := GlobalTheory.T.tsum_rationalClasses_eq_prod_localSums D Z FP u u' F F' P d0 R V hV hB hM φ hφrel hφzero
  let e : Quot (GRel (Z := Z) (FP := FP) F F') ≃ @MulAction.orbitRel.Quotient Γ (Dat Z FP) _ actY :=
    Quot.congr (Equiv.refl _) (fun a b => (hrel a b).trans ⟨fun h => (@MulAction.orbitRel Γ (Dat Z FP) _ actY).symm' h, fun h => (@MulAction.orbitRel Γ (Dat Z FP) _ actY).symm' h⟩)
  have hq : ∑' o : Quot (GRel (Z := Z) (FP := FP) F F'), g0 o.out =
      ∑' o : @MulAction.orbitRel.Quotient Γ (Dat Z FP) _ actY, g0 o.out := by
    rw [← e.tsum_eq]
    congr 1
    funext o
    have he : e o = Quotient.mk (@MulAction.orbitRel Γ (Dat Z FP) _ actY) o.out := by
      conv_lhs => rw [← Quot.out_eq o]
      rfl
    have h2 : (@MulAction.orbitRel Γ (Dat Z FP) _ actY) (e o).out o.out := by
      rw [he]
      exact Quotient.mk_out (s := @MulAction.orbitRel Γ (Dat Z FP) _ actY) o.out
    rw [@MulAction.orbitRel_apply Γ (Dat Z FP) _ actY] at h2
    obtain ⟨g, hg⟩ := h2
    have hg' : sm g o.out = (e o).out := hg
    rw [← hg', hcls]
  refine hLHS.trans (htr.trans (horbit.trans ?_))
  calc _ = ∑' o : @MulAction.orbitRel.Quotient Γ (Dat Z FP) _ actY, g0 o.out := rfl
    _ = ∑' o : Quot (GRel (Z := Z) (FP := FP) F F'), g0 o.out := hq.symm
    _ = _ := tsum_congr fun o => (hpt o.out).symm
    _ = _ := hreg

end GlobalTheory.GlueCount
