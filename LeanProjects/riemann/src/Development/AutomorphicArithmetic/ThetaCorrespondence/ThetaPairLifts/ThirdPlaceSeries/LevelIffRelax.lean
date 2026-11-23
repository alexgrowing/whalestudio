import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTupleFreeValue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TupleFreeLevelLeCompact
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepBeforeLastEqSSucc
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MovedAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacesUnder
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
section LocalPart
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
open GlobalTheory.SymBridge (toLoc IsOrd yPos xPos IsCompl)
open GlobalTheory.PenVol GlobalTheory.TwBridge.Lev GlobalTheory.TwBridge.LevOrb
open scoped TensorProduct
namespace GlobalTheory.PenLoc
section Stab
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A : Type} [Fintype A] [DecidableEq A]
  {J : Subgroup (GL (A ⊕ Fin 0) k)}
end Stab
section Read
variable {k : Type} [Field k] {R : Type} [CommRing R] {Y : Type} [Fintype Y] [DecidableEq Y] {n : ℕ}
end Read
section Cong
variable {F E k : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
end Cong
section Seam
open Formalism.L2.Ker Formalism.MainNotions
variable {D : D7} {X : Fields} (s : Seam D X) {n : ℕ}
end Seam
end GlobalTheory.PenLoc
end LocalPart
section GlobalPart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
namespace GlobalTheory.PenLoc
section Split
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Split
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
  {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T}
set_option maxHeartbeats 2000000 in
theorem bc_prV_of_mem_UPts (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (ha : a.Is) (hTr : a.True) (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (hJ : J.Reads) (i : Fin J.r) (j : ℕ)
    (e : j = (J.G i).s + 1) (hm : j ≤ B.R.m) (β : J.Ch₀ j) (g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))
    (κ : GL (Fin (B.R.N j)) (EF (I.rec7 l Z))) (hg : κ.1 = finM _ (rankN (I.rec7 l Z) j hm) g)
    (hκ : κ ∈ Formalism.UG.UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hm) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) :
    Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) (J.G i).q.v) κ ∈ (J.A.K j hm β).lev.Uloc (J.G i).q.v ↔
      _root_.GlobalTheory.PenBridge.reductionHomAtLevel J j i e g ∈ GlobalTheory.PenVol.cosStab (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J
        (box _ ((J.G i).ϖ ^ (J.E i).M)) ((J.E i).cos (cast (congrArg (J.E i).Ch e) (J.π i j β))) := by
  subst e
  obtain ⟨e', he', hF⟩ := (ha.stdQ (J.pl i) ⟨t, J.mem i⟩).1 ((J.G i).s + 1) le_rfl
  let e : XIx (Fin B.R.k) (Fin B.R.t) ((J.G i).s + 1) ≃ Fin (B.R.N ((J.G i).s + 1)) :=
    e'.trans (finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm))
  have he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e := fun x => he' x
  obtain ⟨K, hKJ, hK, -⟩ := (_root_.GlobalTheory.Fam.QuadraticExtensionData.Reads.movedAt W hW u a ha t J hJ i).pen hm β e he
  have hKe : GlobalTheory.TwBridge.Lev.phi (E := B.fields.E) ((J.G i).q.pr.comp (incA (I.rec7 l Z))) ((Equiv.sumEmpty _ (Fin 0)).trans e)
      (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((J.G i).s + 1) β).1.1 (J.P i)) = K := by
    refine Units.ext (Matrix.ext ?_)
    rintro (x | x) (y | y)
    · exact (hK (e' x) y).trans (GlobalTheory.Fam.MovedJoin.frameβ_mul_std _ e' hF _ x y)
    · exact y.elim0
    · exact x.elim0
    · exact x.elim0
  have hv : Formalism.L2.Col.IsOver (J.G i).q.v (J.pl i) :=
    congrArg HeightOneSpectrum.asIdeal ((_root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha hTr t J hJ).2 i)
  have hrd : _root_.GlobalTheory.PenBridge.reductionHomAtLevel J _ i rfl g = locG ((J.G i).q.prF (J.G i).idem) ((Equiv.sumEmpty _ (Fin 0)).trans e) κ := by
    refine Units.ext (Matrix.ext ?_)
    rintro (x | x) (y | y)
    · refine (locHom_std (J.G i).q _ _ e' hF g x y).trans ?_
      refine ((J.G i).q.prF_toEAf (J.G i).idem _).symm.trans (congrArg _ ?_)
      exact (congrFun (congrFun hg (e x)) (e y)).symm
    · exact y.elim0
    · exact x.elim0
    · exact x.elim0
  rw [hrd]
  refine (uloc_iff hW.tr.ok hW.tr.pins.some J.A hJ.is (J.P i) (J.G i).q (J.pl i) (hJ.eq i) (J.G i).idem (J.G i).s
    ((J.E i).tw (J.hψ i) (J.sg i)) _ (fun _ => rfl) (hJ.tw i) hm β e he (hKe ▸ hKJ) (J.E i).M (hJ.M i) _ hv κ hκ).trans ?_
  exact Iff.of_eq (congrArg (fun c => locG ((J.G i).q.prF (J.G i).idem) ((Equiv.sumEmpty _ (Fin 0)).trans e) κ ∈
    GlobalTheory.PenVol.cosStab (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J
      (box _ ((J.G i).ϖ ^ (J.E i).M)) c) (hJ.cos i β e he).symm)
end GlobalTheory.PenLoc
set_option maxHeartbeats 2000000 in
open scoped Pointwise in
theorem GlobalTheory.PenLoc.level_iff_relax_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ α : J.Ch j, ∃ c : (i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1) ⊕ Fin 0) (J.G i).k, (∀ i, c i ∈ (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J) ∧ ∀ g, g ∈ J.A.U j (J.ι j α) ↔ g ∈ _root_.GlobalTheory.PenLev.relaxedLevelSubgroup J j hj α ∧ ∀ i, c i * _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J j hj g i * (c i)⁻¹ ∈ GlobalTheory.PenVol.cosStab (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J (GlobalTheory.StepData.box _ ((J.G i).ϖ ^ (J.E i).M)) ((J.E i).cos (cast (congrArg (J.E i).Ch (show j = (J.G i).s + 1 by have h1 := (J.G i).hs; have h2 : (I.rec7 l Z).R.m = B.R.m := rfl; omega)) (α i))) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α
  have hm : j ≤ B.R.m := by omega
  refine ⟨1, fun i => one_mem _, fun g => ?_⟩
  simp only [Pi.one_apply, one_mul, inv_one, mul_one]
  have key := fun i => _root_.GlobalTheory.PenLoc.bc_prV_of_mem_UPts hW ha hTr J hJ i j (_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J hj i) hm (J.ι j α)
  simp only [hJ.sec j hm α] at key
  have fwd := fun x (hx : x ∈ J.A.U j (J.ι j α)) i =>
    ((hJ.is.U j hm _ x).1 hx).2.elim fun κ hκ =>
      (key i x κ.1 hκ (((J.A.K j hm _).lev.U_eq _).1 κ.2).1).1 ((((J.A.K j hm _).lev.U_eq _).1 κ.2).2 _)
  constructor
  · intro hg
    exact ⟨(_root_.GlobalTheory.PenLev.mem_relax_iff' J j hj α g).2 ⟨Subgroup.mem_sup_left hg, ((hJ.is.U j hm _ g).1 hg).1,
      fun i => (J.E i).le _ _ _ (GlobalTheory.PenVol.cosStab_le _ _ _ (fwd g hg i))⟩, fwd g hg⟩
  · rintro ⟨hr, hH⟩
    obtain ⟨hs, hgf, -⟩ := (_root_.GlobalTheory.PenLev.mem_relax_iff' J j hj α g).1 hr
    have hN : (GlobalTheory.FinPl.grpAt ((I.rec7 l Z).sp.X j) (_root_.GlobalTheory.PenBridge.finitePlaceCondition J)).Normal := by
      unfold GlobalTheory.FinPl.grpAt GlobalTheory.FinPl.congGrp; exact MonoidHom.normal_ker _
    have : g ∈ ((J.A.U j (J.ι j α) : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) *
        (GlobalTheory.FinPl.grpAt ((I.rec7 l Z).sp.X j) (_root_.GlobalTheory.PenBridge.finitePlaceCondition J) : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)))) := by
      rw [← Subgroup.mul_normal]; exact hs
    obtain ⟨x, hx, n, hn, rfl⟩ := this
    refine mul_mem hx ?_
    have hnf : n ∈ GfC ((I.rec7 l Z).sp.X j) := (Subgroup.mul_mem_cancel_left _ ((hJ.is.U j hm _ x).1 hx).1).1 hgf
    obtain ⟨φ, hφ⟩ := GlobalTheory.FinPartIso.exists_finIso (I.rec7 l Z) _ _ (rankN (I.rec7 l Z) j hm)
    refine (hJ.is.U j hm _ n).2 ⟨hnf, ⟨(φ ⟨n, hnf⟩).1, ((J.A.K j hm _).lev.U_eq _).2 ⟨(φ ⟨n, hnf⟩).2, fun v => ?_⟩⟩, hφ ⟨n, hnf⟩⟩
    by_cases hv : _root_.GlobalTheory.PenBridge.finitePlaceCondition J v
    · obtain ⟨i, rfl⟩ := hv
      refine (key i n _ (hφ ⟨n, hnf⟩) (φ ⟨n, hnf⟩).2).2 ?_
      have h2 := hH i
      rw [map_mul, Pi.mul_apply] at h2
      exact (Subgroup.mul_mem_cancel_left _ (fwd x hx i)).1 h2
    · rw [GlobalTheory.PenLoc.bc_prV_eq_one _ hn _ _ (hφ ⟨n, hnf⟩) v hv]
      exact one_mem _
end GlobalPart
end
end
