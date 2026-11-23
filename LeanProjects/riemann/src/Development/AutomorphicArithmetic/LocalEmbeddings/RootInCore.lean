import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoversOfLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLeOfDetEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelActionMemCuspFormsOfActionLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelAtEachIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelLiftModuliLawsOfCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepLevelCoverPrincipalLevelLawsGalois
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionPullbackExistsUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivAtRecordOfEquivRow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVecMemOfFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullActLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreConstantIffCoveringGroupInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCoverCuspFormPullbackInjectiveDescentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTypeFrameCoverLevelMapsReductionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelCharacterEqProdSuperdiagonalSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCuspFormsFullLattice
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovTop.BadRep

section Forms

open NumberField Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CovTop
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.LevPull (CongMod)
open GlobalTheory.LevDesc (transl)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FieldBC

set_option maxHeartbeats 1000000 in

theorem pull_data : ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), LawsJ T → InR D j → Y.Good e o →
    ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ (G : Type) [Group G]
    (lev : G → (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La),
    ActLev (Xo := T.Q.Xo j) T.Q.c (fun g => (lev g, (LinearMap.id : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La))) →
    (∀ g, ∀ f ∈ T.cuspA j a n, actLev (Xo := T.Q.Xo j) T.Q.c (fun g => (lev g, (LinearMap.id : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La))) g f ∈ T.cuspA j a n) →
    ∀ (θ : LevelAut (T.Q.Dw j) Y.d.l₂ →* G), (∀ γ, CongMod T.Q.l.Mb (liftLa γ) (lev (θ γ))) →
    ∃ π : cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n) →ₛₗ[((Y.d.eF : Y.c'.F →+* Y.d.c₂.F).comp (incF T.Q.c Y.c' Y.hle))] Y.V (wtZ a n),
      (∀ (m : ℕ) (b : Fin m → cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)), LinearIndependent T.Q.c.F b →
        LinearIndependent Y.d.c₂.F fun k => π (b k)) ∧
      (∀ γ (v : cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)), ∃ hv : actLev (Xo := T.Q.Xo j) T.Q.c (fun g => (lev g, (LinearMap.id : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La))) (θ γ) v ∈ cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n),
        transl Y.d.Xo₂ Y.d.c₂ γ (π v) = π ⟨_, hv⟩) ∧
      (∀ g : Y.V (wtZ a n), (∀ γ, CongMod T.Q.l.Mb (liftLa γ) LinearMap.id → transl Y.d.Xo₂ Y.d.c₂ γ g = g) →
        g ∈ Submodule.span Y.d.c₂.F (Set.range π)) := by
  intro D T j Y e o hT hj hG a n hD G _ lev hact hkeep θ hθ
  obtain ⟨hL₂, hgal, hP⟩ := GlobalTheory.DeepLaws.laws_galois_pull D T j Y e o hT hj hG hG.unit hG.modelW
  have hL := (GlobalTheory.LevGeo.laws_of_coreJ D T j hT hj).1
  have hpq : (T.Q.Dw j).p ≠ (T.Q.Dw j).q ∧ 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    obtain ⟨hp, hq, -⟩ := hL.dat
    obtain ⟨h1, h2⟩ := hj
    have hk := D.R.m_add_three_le_k
    rw [hp, hq]
    simp only [Ranks.sigW]
    omega
  obtain ⟨π, p1, p2, -, -, p5, -⟩ := GlobalTheory.T.levelCover_cuspForm_pullback_injective_descent D j _ _ _ _ _ Y.c' Y.hle _ _ Y.d _ _ hL hL₂ hG.lev.1 hgal a n hD hD.2
  have hC : ∀ {f}, f ∈ cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n) ↔ f ∈ T.cuspA j a n := fun {f} => by rw [cuspW_wtZ]
  have s₁ : ∀ {f}, f ∈ cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n) → f ∈ sec (T.Q.Xo j) T.Q.c a n :=
    fun h => cusp_le_sec _ _ _ a n (hC.1 h)
  have s₂ : ∀ {f}, f ∈ Y.V (wtZ a n) → f ∈ sec Y.d.Xo₂ Y.d.c₂ a n := fun h => by
    rw [Deep.V, cuspW_wtZ] at h
    exact cusp_le_sec _ _ _ a n h
  have hact₂ : ActLev (Xo := Y.d.Xo₂) Y.d.c₂ (GlobalTheory.FormTies.levFull (T.Q.Dw j) Y.d.l₂) :=
    GlobalTheory.FullLevelAction.actLaws_levFull Y.d.Xo₂ Y.d.c₂ hpq.2 (hG.lev.2 ▸ Nat.coprime_one_left _)
  obtain ⟨hact', hbc⟩ := GlobalTheory.FieldBC.actLev_and_actBC D _ _ _ _ _ Y.c' Y.hle G _ hact
  have hO : GlobalTheory.CoverSec.AllOver Y.d := GlobalTheory.CoverSec.allOver_of_overBase Y.d hG.lev.1.1.2.2
    (GlobalTheory.ClsVal.Cmp.overBase_of_ne hpq.1 hL.levA Y.d)
  have geo : ∀ {f f' : Rul (T.Q.Xo j) Y.c'} {u u' : Rul Y.d.Xo₂ Y.d.c₂}, GlobalTheory.LevPull.Pull Y.d f u → GlobalTheory.LevPull.Pull Y.d f' u' →
      f = f' → ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra Y.d.c₂.F k] (y : FrPt Y.d.Xo₂ Y.d.c₂ k),
        evR Y.d.Xo₂ Y.d.c₂ u y = evR Y.d.Xo₂ Y.d.c₂ u' y := by
    rintro f _ u u' h h' rfl k _ _ _ y₂
    letI := GlobalTheory.CoverSec.algBelow Y.d k
    obtain ⟨y, hy⟩ := GlobalTheory.CoverSec.exists_frOver_below Y.d (fun _ => rfl) y₂ (hO k (fun _ => rfl) y₂)
    rw [h k (fun _ => rfl) y₂ y hy, h' k (fun _ => rfl) y₂ y hy]
  let act := actLev (Xo := T.Q.Xo j) T.Q.c (fun g => (lev g, (LinearMap.id : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La)))
  let π' := (Y.V (wtZ a n)).subtype.comp π
  have hc : ∀ γ (v : cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)) (hv : act (θ γ) v ∈ cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)),
      (transl Y.d.Xo₂ Y.d.c₂ γ).toLinearMap (π' v) = π' ⟨_, hv⟩ := by
    intro γ v hv'
    have hv := ((GlobalTheory.T.ruleBaseChange_section_values_semilinear _ _ _ _ _ _ _ Y.hle).1 a n _ (s₁ v.2)).1
    have h1 := GlobalTheory.LevPullEquiv.pull_actLev D j _ _ _ _ _ Y.d hpq.2 hG.lev.1 hG.lev.2
      (GlobalTheory.ClsVal.Cmp.overBase_of_ne hpq.1 hL.levA Y.d) G _ lev liftLa hact' hact₂ (θ γ) γ (hθ γ) a n _ hv _
      (s₂ (π v).2) (p1 v)
    refine GlobalTheory.CoverSec.eq_of_geometric (GlobalTheory.LevelEquivCompare.actLev_mem_sec hact₂ γ (s₂ (π v).2)).1 (s₂ (π _).2).1 (geo h1 (p1 ⟨_, hv'⟩) ?_)
    refine GlobalTheory.CoverSec.eq_of_geometric (GlobalTheory.LevelEquivCompare.actLev_mem_sec hact' _ hv).1
      ((GlobalTheory.T.ruleBaseChange_section_values_semilinear _ _ _ _ _ _ _ Y.hle).1 a n _ (s₁ hv')).1.1 fun k _ _ _ y => ?_
    letI := resAlg Y.hle k
    exact (hbc a n (θ γ) 1 _ _ _ hv (fun _ => s₁ v.2) (GlobalTheory.LevelEquivCompare.isBC_rulBC Y.hle (s₁ v.2)) k (fun _ => rfl) y).trans
      (GlobalTheory.LevelEquivCompare.isBC_rulBC Y.hle (s₁ hv') k (fun _ => rfl) y).symm
  refine ⟨π, fun m b hb => p2 m b hb, fun γ v => ⟨hC.2 (hkeep _ _ (hC.1 v.2)), hc γ v _⟩, fun g hg => ?_⟩
  have h1 : GlobalTheory.LevPull.FibConst Y.d g := by
    refine (GlobalTheory.T.fibreConstant_iff_coveringGroup_invariant D j _ _ _ _ _ Y.d hpq.2 hG.lev.1 hG.lev.2 (Or.inl ⟨hpq.1, hL.levA⟩) liftLa (fun γ => LinearMap.ext (liftLa_spec γ)) a n g
      (s₂ g.2)).2 fun γ hγ => hg γ hγ
  exact (p5 g).2 h1

end Forms

section Point

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.BigTop GlobalTheory.AllWt GlobalTheory.CovTop GlobalTheory.BadCount
open GlobalTheory.LevDesc (TypeFrame IsTypeLevel typeRed typeEmb grpHR grpGHR transl)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters (Sq LevelGroup levelU psiU unitri superDiag)
open GlobalTheory.LevPull (CongMod)
open Formalism.MainNotions.ArithmeticCylinders
open scoped TensorProduct

theorem isUniUp_iff {k : Type} [Field k] {r : ℕ} (g : GL (Fin r) k) :
    IsUniUp (g : Matrix (Fin r) (Fin r) k) ↔ g ∈ unitri r k :=
  ⟨fun h => ⟨fun a b hab => (h a b).1 hab, fun a => (h a a).2 rfl⟩,
    fun h a b => ⟨fun hab => h.1 hab, fun e => e ▸ h.2 a⟩⟩

theorem sum_entN {k : Type} [Field k] {r : ℕ} (M : Matrix (Fin r) (Fin r) k) :
    ∑ i ∈ Finset.range (r - 1), entN M i (i + 1) = superDiag M := by
  have h1 : ∀ i : Fin r, (∑ j : Fin r, if j.val = i.val + 1 then M i j else 0) = entN M i (i + 1) := by
    intro i
    unfold entN
    split_ifs with h
    · rw [Finset.sum_eq_single ⟨i.val + 1, h.2⟩ (fun b _ hb => if_neg fun e => hb (Fin.ext e)) (by simp)]
      simp
    · refine Finset.sum_eq_zero fun j _ => if_neg fun e => h ⟨i.2, by have := j.2; omega⟩
  rw [superDiag, Finset.sum_congr rfl fun i _ => h1 i, Fin.sum_univ_eq_sum_range (fun i => entN M i (i + 1)) r]
  refine Finset.sum_subset (Finset.range_subset_range.2 (Nat.sub_le r 1)) fun x hx hx' => ?_
  simp only [Finset.mem_range] at hx hx'
  unfold entN
  rw [dif_neg]
  omega

theorem root_in_core {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (k : Fin 2) :
    ∃ ζ : p.T.Q.c.F, IsPrimitiveRoot ζ (D.host.g k) := by
  have hN0 : p.T.Q.l.M' ≠ 0 := Nat.lcm_ne_zero (by have := p.T.Q.l.three_le; omega) p.T.Q.l.A_pos.ne'
  have hM : p.T.Q.l.M = D.host.g 0 * D.host.g 1 := p.fw.laws.pins.2.1.1
  have hz : IsPrimitiveRoot (⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.zeta p.T.Q.l.M', p.T.Q.c.zeta_mem⟩ : p.T.Q.c.F) p.T.Q.l.M' :=
    IsPrimitiveRoot.of_map_of_injective (f := p.T.Q.c.F.val) (Complex.isPrimitiveRoot_exp _ hN0) Subtype.val_injective
  obtain ⟨c, hc⟩ : D.host.g k ∣ p.T.Q.l.M' :=
    dvd_trans (hM ▸ GlobalTheory.LevDesc.g_dvd k) (Nat.dvd_lcm_left p.T.Q.l.M p.T.Q.l.A)
  exact ⟨_, hz.pow (Nat.pos_of_ne_zero hN0) (hc.trans (mul_comm _ _))⟩

theorem idx_eq {D : D7} {k k' : Fin 2} {X X' : Type} [Semiring X] [Semiring X'] (e : ZMod (D.host.g k) ≃+* X)
    (e' : ZMod (D.host.g k') ≃+* X') (hX : Nat.card X = Nat.card X') : k = k' := by
  haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
  haveI : NeZero (D.host.g k') := ⟨(D.host.g_prime k').ne_zero⟩
  have h : D.host.g k = D.host.g k' := by
    rw [← Nat.card_zmod (D.host.g k), ← Nat.card_zmod (D.host.g k'), Nat.card_congr e.toEquiv, Nat.card_congr e'.toEquiv, hX]
  fin_cases k <;> fin_cases k'
  · rfl
  · exact absurd h D.host.g_ne
  · exact absurd h.symm D.host.g_ne
  · rfl

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}

set_option maxHeartbeats 1000000 in

theorem frame_data (p : PtAt ex Csz) (i : Fin D.R.m) (Y : Cov p i) {e : ℕ} {o : ℝ} (hY : Y.Good e o) :
    ∃ (fr : TypeFrame (dat p i) Y.d.l₂) (ε : Sq D.host ≃ p.R.toRealDat.Pg) (iso' : ∀ v : Sq D.host, ZMod (D.host.g v.1) ≃+* kP (ε v).1)
      (t : LevelGroup D.host ≃* p.P.Gp), IsTypeLevel Y.d.l₂ ∧
      (∀ γ, CongMod p.T.Q.l.Mb (liftLa γ) ((p.O i).lev (t (typeRed fr γ)))) ∧
      (∀ γ, CongMod p.T.Q.l.Mb (liftLa γ) LinearMap.id → typeRed fr γ = 1) ∧
      (∀ u v, p.R.toRealDat.eG (t u) (ε v) = Formalism.UG.bc (iso' v : ZMod (D.host.g v.1) →+* kP (ε v).1) (u v)) ∧
      (∀ u, t u ∈ (p.F.lv2.lvl false).P ↔ u ∈ levelU D.host) := by
  have hJ := p.fw.laws
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.succ_pos _, i.2⟩
  have hM : p.T.Q.l.M = D.host.g 0 * D.host.g 1 := hJ.pins.2.1.1
  have hA : p.T.Q.l.A = 1 := hJ.pins.2.1.2
  have hl₂ : IsTypeLevel Y.d.l₂ :=
    (GlobalTheory.LevDesc.isTypeLevel_of_eq hY.lev.2 (hY.lev.1.2.1.trans (by rw [hM])) (hM ▸ hY.lev.1.2.2.1.symm)).1
  have hMb := ((p.pins i).2.tuple ()).half.1
  have hr : (dat p i).p + (dat p i).q = D.R.r := (GlobalTheory.Member.exists_iotaOK D p.T.Q hJ.pins _ hj).2.1
  have hle : Y.d.l₂.Mb ≤ p.T.Q.l.Mb := hY.lev.1.2.2.2.1.le.trans Ideal.mul_le_left
  obtain ⟨fr, ε, iso, h1, h2⟩ := GlobalTheory.T.exists_typeFrame_cover_levelMaps_reductions D _ _ _ _ _ p.R.toRealDat i (p.charW.base.lev.βW i) _ (dat p i) _ Y.d.l₂ _
    (GlobalTheory.LevelAction.latEmb_iotaW p.T hJ i) hr hA hM hl₂ hle hMb _ (p.pins i).2.lift.lev
  obtain ⟨t, ψ, t1, t2, t3, t4⟩ := GlobalTheory.TypeBase.base_level_unip_char D _ _ _ _ _ p.R.toRealDat p.F.lv2 p.charW.base.grp.levels p.charW.base.grp.chiW
    (root_in_core p) ε iso
  exact ⟨fr, ε, iso, t, hl₂, fun γ => h1 γ _ (t1 _), h2, t1, t3⟩

end Point

end GlobalTheory.CovTop.BadRep
