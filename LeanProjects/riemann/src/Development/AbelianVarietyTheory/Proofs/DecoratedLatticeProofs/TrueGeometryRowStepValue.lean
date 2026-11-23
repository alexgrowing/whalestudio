import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepBeforeLastEqSSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleFreeLevelLeCompact
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneSubIdemQMulSelf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepIndexLeS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsContinuousLocalGLEmbeddingSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGAtAllPlacesMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistLocalData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdAtToEAfEqZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryClassRepresentativesBijective
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentMulEntryEqZeroOfCutInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EmbFColZeroMemMram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfRat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsUnique
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCosetRelationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalLevelComparisonStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section
namespace GlobalTheory.PenLevOff

section Cut

open GlobalTheory.FinPl GlobalTheory.FinPl.SetCut

set_option synthInstance.maxHeartbeats 200000

variable {D : D7}

theorem prV_comm (v : GlobalTheory.FinPl.Pl D) (z : Af ↥D.host.F ⊗[↥D.host.F] D.host.E) :
    Formalism.UG.prV (E := D.host.E) v ((Algebra.TensorProduct.comm (↥D.host.F) (Af ↥D.host.F) D.host.E) z) =
      (Algebra.TensorProduct.comm _ _ _) (GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D v z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul a e =>
    rw [Algebra.TensorProduct.comm_tmul]
    simp only [Formalism.UG.prV, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.comm_tmul]
    rfl
  | add a b ha hb =>
    simp only [map_add]
    exact congrArg₂ (· + ·) ha hb

theorem prV_toEAf_congr (v : GlobalTheory.FinPl.Pl D) {y y' : AE D} (h : GlobalTheory.FinPl.compAt D v y = GlobalTheory.FinPl.compAt D v y') :
    Formalism.UG.prV (E := D.host.E) v (toEAf D y) = Formalism.UG.prV (E := D.host.E) v (toEAf D y') := by
  unfold GlobalTheory.FinPl.compAt at h
  unfold toEAf
  simp only [RingHom.comp_apply] at h ⊢
  generalize finPart D y = z at h ⊢
  generalize finPart D y' = z' at h ⊢
  refine (prV_comm v z).trans (Eq.trans ?_ (prV_comm v z').symm)
  rw [h]

theorem bc_congr (V : HSp D) {n : ℕ} (hn : V.rank = n) (v : GlobalTheory.FinPl.Pl D) {g h : GA D V} {x y : GL (Fin n) (EF D)}
    (hx : x.1 = finM V hn g) (hy : y.1 = finM V hn h)
    (e : ∀ i j, GlobalTheory.FinPl.compAt D v (Formalism.L2.Theta.mt V g i j) = GlobalTheory.FinPl.compAt D v (Formalism.L2.Theta.mt V h i j)) :
    Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x = Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) y := by
  apply Units.ext
  ext i j
  change Formalism.UG.prV (E := D.host.E) v (x.1 i j) = Formalism.UG.prV (E := D.host.E) v (y.1 i j)
  rw [hx, hy]
  simp only [GlobalTheory.AdForm.finM, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.map_apply]
  exact prV_toEAf_congr v (e _ _)

theorem bc_eq_one (V : HSp D) {n : ℕ} (hn : V.rank = n) {P : GlobalTheory.FinPl.Pl D → Prop} {v : GlobalTheory.FinPl.Pl D} (hv : ¬ P v) {g : GA D V}
    (hg : g ∈ grpAt V P) {x : GL (Fin n) (EF D)} (hx : x.1 = finM V hn g) :
    Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) x = 1 := by
  have h1 : (1 : GL (Fin n) (EF D)).1 = finM V hn 1 := by
    subst hn
    rw [GlobalTheory.AdForm.CongAtIdem.finM_rfl, GlobalTheory.SplitCut.mt_one, Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  rw [bc_congr V hn v hx h1 fun i j => ?_, map_one]
  have := ((mem_grpAt_iff_parts V P g).1 hg i j).2 v hv
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at this
  rw [this, GlobalTheory.SplitCut.mt_one]

abbrev cutAt (V : HSp D) (v : GlobalTheory.FinPl.Pl D) : GA D V →* GA D V := cutG V _ (idemQ_mul_self {v})

theorem cutAt_mem (V : HSp D) (v : GlobalTheory.FinPl.Pl D) (g : GA D V) : cutAt V v g ∈ grpAt V (· ∈ ({v} : Finset (GlobalTheory.FinPl.Pl D))) :=
  cutG_mem_Q V {v} g

theorem compAt_cutAt (V : HSp D) (v : GlobalTheory.FinPl.Pl D) (g : GA D V) (i j) :
    GlobalTheory.FinPl.compAt D v (Formalism.L2.Theta.mt V (cutAt V v g) i j) = GlobalTheory.FinPl.compAt D v (Formalism.L2.Theta.mt V g i j) := by
  rw [mt_cutG, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, RingHom.map_add, RingHom.map_mul,
    RingHom.map_mul, RingHom.map_sub, RingHom.map_one, (parts_idemQ {v}).2 v, if_pos (Finset.mem_singleton_self v), sub_self,
    zero_mul, one_mul, add_zero]

theorem grpAt_mono (V : HSp D) {P Q : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ v, P v → Q v) : grpAt V P ≤ grpAt V Q := fun g hg =>
  (mem_grpAt_iff_parts V Q g).2 fun i j =>
    ⟨((mem_grpAt_iff_parts V P g).1 hg i j).1, fun w hw => ((mem_grpAt_iff_parts V P g).1 hg i j).2 w fun h' => hw (h w h')⟩

theorem cutAt_eq_one (V : HSp D) {P : GlobalTheory.FinPl.Pl D → Prop} {v : GlobalTheory.FinPl.Pl D} (hv : ¬ P v) {g : GA D V} (hg : g ∈ grpAt V P) :
    cutAt V v g = 1 := by
  have h := cutG_left V {v} (one_mem _) (grpAt_mono V (Q := (· ∉ ({v} : Finset (GlobalTheory.FinPl.Pl D))))
    (fun w hw hm => hv (Finset.mem_singleton.1 hm ▸ hw)) hg)
  rwa [one_mul] at h

end Cut

section Level

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
  {Ch : ℕ → Type} {A : TwDat I l Z u a Ch}

set_option maxHeartbeats 1000000 in

theorem mem_U_iff (hA : A.Is) (j : ℕ) (hj : j ≤ B.R.m) (β : Ch j) (g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) :
    g ∈ A.U j β ↔ g ∈ GfC _ ∧ ∀ v, cutAt _ v g ∈ A.U j β := by
  have ex := GlobalTheory.AdForm.RdVal.finM_mem ((I.rec7 l Z).sp.X j) (rankN (I.rec7 l Z) j hj) (gramN (I.rec7 l Z) j hj) rfl
  constructor
  · intro hg
    obtain ⟨hC, κ, hκ⟩ := (hA.U j hj β g).1 hg
    refine ⟨hC, fun v => (hA.U j hj β _).2 ⟨GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ (cutAt_mem _ v g), ?_⟩⟩
    obtain ⟨x, hx⟩ := ex (cutAt _ v g)
    refine ⟨⟨x.1, ((A.K j hj β).lev.U_eq _).2 ⟨x.2, fun w => ?_⟩⟩, hx⟩
    by_cases hw : w = v
    · subst hw
      rw [bc_congr _ _ w hx hκ (compAt_cutAt _ w g)]
      exact (((A.K j hj β).lev.U_eq _).1 κ.2).2 w
    · rw [bc_eq_one _ _ (P := (· ∈ ({v} : Finset _))) (fun h => hw (Finset.mem_singleton.1 h)) (cutAt_mem _ v g) hx]
      exact one_mem _
  · rintro ⟨hC, h⟩
    refine (hA.U j hj β _).2 ⟨hC, ?_⟩
    obtain ⟨x, hx⟩ := ex g
    refine ⟨⟨x.1, ((A.K j hj β).lev.U_eq _).2 ⟨x.2, fun w => ?_⟩⟩, hx⟩
    obtain ⟨-, κ, hκ⟩ := (hA.U j hj β _).1 (h w)
    rw [← bc_congr _ _ w hκ hx (compAt_cutAt _ w g)]
    exact (((A.K j hj β).lev.U_eq _).1 κ.2).2 w

set_option maxHeartbeats 1000000 in

theorem mem_of_uloc_le {a' : I.ι} {Ch' : ℕ → Type} {A' : TwDat I l Z u a' Ch'} (hA : A.Is) (hA' : A'.Is) (j : ℕ) (hj : j ≤ B.R.m) (β : Ch j)
    (β' : Ch' j) (v : GlobalTheory.FinPl.Pl (I.rec7 l Z)) (hle : (A.K j hj β).lev.Uloc v ≤ (A'.K j hj β').lev.Uloc v)
    {g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)} (hv : g ∈ GlobalTheory.FinPl.grpAt _ (· ∈ ({v} : Finset _))) (hg : g ∈ A.U j β) :
    g ∈ A'.U j β' := by
  obtain ⟨hC, κ, hκ⟩ := (hA.U j hj β g).1 hg
  refine (hA'.U j hj β' g).2 ⟨hC, ⟨κ.1, ((A'.K j hj β').lev.U_eq _).2 ⟨(((A.K j hj β).lev.U_eq _).1 κ.2).1, fun w => ?_⟩⟩, hκ⟩
  by_cases hw : w = v
  · subst hw
    exact hle ((((A.K j hj β).lev.U_eq _).1 κ.2).2 w)
  · rw [bc_eq_one _ _ (P := (· ∈ ({v} : Finset _))) (fun h => hw (Finset.mem_singleton.1 h)) hv hκ]
    exact one_mem _

end Level

end GlobalTheory.PenLevOff
end

set_option maxHeartbeats 2000000 in

theorem GlobalTheory.PenLevOff.uloc_le : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : QJ a t), J.Reads → ∀ (α : J.Ch j) t' (J' : QJ a t'), J'.Reads → ∀ (α' : J'.Ch j) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ¬ GlobalTheory.PenBridge.plF J v → ¬ GlobalTheory.PenBridge.plF J' v → (J.A.K j (show j ≤ B.R.m by omega) (J.ι j α)).lev.Uloc v ≤ (J'.A.K j (show j ≤ B.R.m by omega) (J'.ι j α')).lev.Uloc v := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT j hj t J hJ α t' J' hJ' α' v hv hv'
  have hjm : j ≤ B.R.m := by omega
  by_cases hTv : ((B.T u : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal
  · exact GlobalTheory.T.true_geometry_coset_value W hW u a ha haT j hj t J hJ α t' J' hJ' α' v hTv
  by_cases hb : v ∈ J'.A.bad j
  · rcases hJ'.is.bad_le j hjm v hb with hg | hq
    · exact GlobalTheory.T.true_geometry_coset_relation W hW u a ha haT j hj t J hJ α t' J' hJ' α' v hg hTv hv hv'
    · exfalso
      obtain ⟨P, hP, hPv⟩ := hq
      obtain ⟨i, hi⟩ := hJ'.surj P ((hW.tq.Q t' P).2 hP)
      exact hv' ⟨i, (((GlobalTheory.Fam.QJPlaces.places_under W hW u a ha haT t' J' hJ').2 i).trans (congrArg _ hi)).trans hPv⟩
  · rw [(J'.A.K j hjm (J'.ι j α')).lev.Uloc_hyp v hb hTv]
    refine ((J.A.K j hjm (J.ι j α)).lev.Uloc_lev v).trans (le_of_eq ?_)
    congr 1
    ext z
    exact ((hJ.is.reads j hjm).lb _ z).trans ((hJ'.is.reads j hjm).lb _ z).symm

set_option maxHeartbeats 2000000 in

theorem GlobalTheory.PenLevOff.cut_mem_U : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : QJ a t), J.Reads → ∀ (α : J.Ch j) t' (J' : QJ a t'), J'.Reads → ∀ (α' : J'.Ch j) (Q : Finset (GlobalTheory.FinPl.Pl (I.rec7 l Z))), (∀ p, GlobalTheory.PenBridge.plF J p → p ∈ Q) → (∀ p, GlobalTheory.PenBridge.plF J' p → p ∈ Q) → ∀ x ∈ J.A.U j (J.ι j α), GlobalTheory.FinPl.SetCut.cutG _ _ (GlobalTheory.FinPl.SetCut.one_sub_idemQ_mul_self Q) x ∈ J'.A.U j (J'.ι j α') := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT j hj t J hJ α t' J' hJ' α' Q hQ hQ' x hx
  have hjm : j ≤ B.R.m := by omega
  have hxG : x ∈ GfC _ := ((hJ.is.U j hjm _ x).1 hx).1
  have h1 := GlobalTheory.FinPl.SetCut.cutG_mem_Q _ Q x
  have h2 := GlobalTheory.FinPl.SetCut.cutG_mem_Qc _ Q hxG
  have e := GlobalTheory.FinPl.SetCut.cutG_mul_cutG _ Q x
  generalize GlobalTheory.FinPl.SetCut.cutG _ _ (GlobalTheory.FinPl.SetCut.idemQ_mul_self Q) x = g₁ at h1 e
  generalize GlobalTheory.FinPl.SetCut.cutG _ _ (GlobalTheory.FinPl.SetCut.one_sub_idemQ_mul_self Q) x = g₂ at h2 e ⊢
  refine (GlobalTheory.PenLevOff.mem_U_iff hJ'.is j hjm _ g₂).2 ⟨GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ h2, fun v => ?_⟩
  by_cases hv : v ∈ Q
  · rw [GlobalTheory.PenLevOff.cutAt_eq_one _ (P := (· ∉ Q)) (not_not.2 hv) h2]
    exact one_mem _
  · have h4 := ((GlobalTheory.PenLevOff.mem_U_iff hJ.is j hjm _ x).1 hx).2 v
    rw [← e, map_mul, GlobalTheory.PenLevOff.cutAt_eq_one _ (P := (· ∈ Q)) hv h1, one_mul] at h4
    exact GlobalTheory.PenLevOff.mem_of_uloc_le hJ.is hJ'.is j hjm _ _ v
      (GlobalTheory.PenLevOff.uloc_le W hW u a ha haT j hj t J hJ α t' J' hJ' α' v (fun h => hv (hQ v h)) (fun h => hv (hQ' v h)))
      (GlobalTheory.PenLevOff.cutAt_mem _ v _) h4
