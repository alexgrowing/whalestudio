import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitOfGPl
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameEquivApply
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteStabFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDefiniteSpacesStandardAndLarge
import Development.AbelianVarietyTheory.Definitions.Divisors.MemStdLatticeIffIntegralCoords
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.AddCharThetaLawRearrangementIdentity
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ActEEqOfConjRelated
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
  Formalism.IndefR.RecTie Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.CoefDuty GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option maxHeartbeats 1000000

namespace GlobalTheory.FormInner

theorem ipVia_apply {H N : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [AddCommGroup N] [Module ℂ N]
    (e : H →ₗ[ℂ] N) (he : Function.Injective e) (u v : H) : ipVia e (e u) (e v) = ⟪u, v⟫_ℂ := by
  unfold ipVia
  split_ifs with h
  · rw [he h.1.choose_spec, he h.2.choose_spec]
  · exact absurd ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩ h

section Gen

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}

theorem classSum_of_ad (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (hM : R.toRealDat.IsModels)
    (hB : ∀ i, IsBaseFrame (Vc D i) (R.βV i) (R.ΛV i) 1) {M : MtFam D} (ad : MtAd Y M) (hrat : ∀ i, RatFrame (ad.PV i))
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (i : Fin D.R.m) (hX : IsBounded (M μ (i.1 + 1) (by omega) (by omega)).J) :
    ClassSum (M μ (i.1 + 1) (by omega) (by omega)) := by
  classical
  set t := Y.tupT μ
  have hHV := hM.HV i t
  have hcV := hM.cV i
  have hrange : ∀ x : D.what₂.Mt μ (i.1 + 1), ∃ h, R.toRealDat.extV i t h = (Y.IL.jMt μ hμ i x).1 := fun x =>
    ((Y.IL.jMt μ hμ i x).2.1 : _)
  choose hv hhv using hrange
  let Fm : D.what₂.Mt μ (i.1 + 1) → Bridge.Gf (Vc D i) → (R.cV i).W := fun x => (R.HV i t).e (hv x)
  have hFm : ∀ x, Fm x ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv _ (R.βV i) (R.datVt i t)).J
      (levEnv _ (R.βV i) (R.datVt i t)).χ := fun x => hHV.2.1 ▸ LinearMap.mem_range_self _ _
  have hread : ∀ x g, ad.eW μ hμ i ((M μ (i.1 + 1) (by omega) (by omega)).real x g) = Fm x (frameEquiv (ad.PV i) g) := by
    intro x g
    rw [ad.read, ← hhv]
    show (R.cV i).ρ ((ad.PV i).ψ g)⁻¹ (Fm x ((finHom (Vc D i)).rangeRestrict ((ad.PV i).ψ g))) = _
    rw [hcV.1 _ ((GfC (Vc D i)).inv_mem ((ad.PV i).into g))]
    rfl
  have hip : ∀ x x' : D.what₂.Mt μ (i.1 + 1), inner ℂ x x' = (((RealDat.nP F.lv2 false)⁻¹ : ℝ) : ℂ) *
      Bridge.adInner (Bridge.ratF (Vc D i)) (levEnv _ (R.βV i) (R.datVt i t)).J (R.B.L i t).pres.y (Fm x) (Fm x') := by
    intro x x'
    rw [Y.tied.lift.mt μ hμ i x x']
    show (((RealDat.nP F.lv2 false)⁻¹ : ℝ) : ℂ) * ipVia (R.toRealDat.extV i t) (Y.IL.jMt μ hμ i x).1 (Y.IL.jMt μ hμ i x').1 = _
    rw [← hhv, ← hhv, ipVia_apply _ (Y.hinj i t), hHV.2.2]
  have hnP : 0 < (RealDat.nP F.lv2 false)⁻¹ := by
    unfold RealDat.nP
    exact inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)
  exact classSum_of_read (M μ (i.1 + 1) (by omega) (by omega)) (Bridge.ratF (Vc D i)) (frameEquiv (ad.PV i))
    (R.cV i).coef.ρ _ (levEnv _ (R.βV i) (R.datVt i t)).χ (ad.eW μ hμ i) Fm (R.B.L i t).pres.y (R.B.L i t).pres.reps
    (ratF_injective _) (RatFrame.iff (hrat i)) (fun δ a b => hcV.2.1 _ a b)
    ⟨{1}, fun κ hκ => ⟨1, by simp, by simpa using comap_le_Umax (ad.std i) (hB i) (R.datVt i t) hκ⟩⟩ hX hFm
    hread _ hnP hip (fun _ => GlobalTheory.InvFormBdd.exists_isInvForm _ _ _)

theorem classSum_twisted (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (hM : R.toRealDat.IsModels)
    (hB : ∀ i, IsBaseFrame (Vc D i) (R.βV i) (R.ΛV i) 1) {M : MtFam D} (ad : MtAd Y M) (hrat : ∀ i, RatFrame (ad.PV i))
    {tup : D.what₂.Tup → Fin D.R.m → Formalism.L2.Host.HChar D.host.E} {Q : D.what₂.places.Pl → Finset (PlE D.host)}
    (hin : MtInput D M tup Q) (v : D.what₂.places.Pl) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hv : TwistedAt D v) :
    ClassSum (M (D.what₂.muTw v) j h1 h2) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hμ : Used0 D (D.what₂.muTw v) := Or.inr ⟨v, ((D.what₂.muAt_or v).resolve_left hv).symm⟩
  exact classSum_of_ad Y hM hB ad hrat _ hμ ⟨k, by omega⟩
    ⟨{1}, fun κ hκ => ⟨1, by simp, by simpa using level_le_Umax hin v ⟨k, by omega⟩ hκ⟩⟩

theorem classSum_of_std (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (hM : R.toRealDat.IsModels)
    (hB : ∀ i, IsBaseFrame (Vc D i) (R.βV i) (R.ΛV i) 1) {M : MtFam D} (ad : MtAd Y M) (hV : ∀ i, GlobalTheory.StdFrame.OrthFrame (Vc D i))
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (i : Fin D.R.m) (hX : IsBounded (M μ (i.1 + 1) (by omega) (by omega)).J) :
    ClassSum (M μ (i.1 + 1) (by omega) (by omega)) := by
  classical
  set t := Y.tupT μ
  have hHV := hM.HV i t
  have hcV := hM.cV i
  have hrange : ∀ x : D.what₂.Mt μ (i.1 + 1), ∃ h, R.toRealDat.extV i t h = (Y.IL.jMt μ hμ i x).1 := fun x =>
    ((Y.IL.jMt μ hμ i x).2.1 : _)
  choose hv hhv using hrange
  let Fm : D.what₂.Mt μ (i.1 + 1) → Bridge.Gf (Vc D i) → (R.cV i).W := fun x => (R.HV i t).e (hv x)
  have hFm : ∀ x, Fm x ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv _ (R.βV i) (R.datVt i t)).J
      (levEnv _ (R.βV i) (R.datVt i t)).χ := fun x => hHV.2.1 ▸ LinearMap.mem_range_self _ _
  have hread : ∀ x g, ad.eW μ hμ i ((M μ (i.1 + 1) (by omega) (by omega)).real x g) = Fm x (frameEquiv (ad.PV i) g) := by
    intro x g
    rw [ad.read, ← hhv]
    show (R.cV i).ρ ((ad.PV i).ψ g)⁻¹ (Fm x ((finHom (Vc D i)).rangeRestrict ((ad.PV i).ψ g))) = _
    rw [hcV.1 _ ((GfC (Vc D i)).inv_mem ((ad.PV i).into g))]
    rfl
  have hip : ∀ x x' : D.what₂.Mt μ (i.1 + 1), inner ℂ x x' = (((RealDat.nP F.lv2 false)⁻¹ : ℝ) : ℂ) *
      Bridge.adInner (Bridge.ratF (Vc D i)) (levEnv _ (R.βV i) (R.datVt i t)).J (R.B.L i t).pres.y (Fm x) (Fm x') := by
    intro x x'
    rw [Y.tied.lift.mt μ hμ i x x']
    show (((RealDat.nP F.lv2 false)⁻¹ : ℝ) : ℂ) * ipVia (R.toRealDat.extV i t) (Y.IL.jMt μ hμ i x).1 (Y.IL.jMt μ hμ i x').1 = _
    rw [← hhv, ← hhv, ipVia_apply _ (Y.hinj i t), hHV.2.2]
  have hnP : 0 < (RealDat.nP F.lv2 false)⁻¹ := by
    unfold RealDat.nP
    exact inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)
  exact classSum_of_frame (M μ (i.1 + 1) (by omega) (by omega)) (Bridge.ratF (Vc D i)) (frameEquiv (ad.PV i))
    (R.cV i).coef.ρ _ (levEnv _ (R.βV i) (R.datVt i t)).χ (ad.eW μ hμ i) Fm (R.B.L i t).pres.y (R.B.L i t).pres.reps
    (ratF_injective _) (finite_stab_frame (hV i) (ad.std i)) (fun δ a b => hcV.2.1 _ a b)
    (comap_le_Umax (ad.std i) (hB i) (R.datVt i t)) hX hFm
    hread _ hnP hip

theorem classSum_twisted_std (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (hM : R.toRealDat.IsModels)
    (hB : ∀ i, IsBaseFrame (Vc D i) (R.βV i) (R.ΛV i) 1) {M : MtFam D} (ad : MtAd Y M) (hV : ∀ i, GlobalTheory.StdFrame.OrthFrame (Vc D i))
    {tup : D.what₂.Tup → Fin D.R.m → Formalism.L2.Host.HChar D.host.E} {Q : D.what₂.places.Pl → Finset (PlE D.host)}
    (hin : MtInput D M tup Q) (v : D.what₂.places.Pl) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hv : TwistedAt D v) :
    ClassSum (M (D.what₂.muTw v) j h1 h2) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hμ : Used0 D (D.what₂.muTw v) := Or.inr ⟨v, ((D.what₂.muAt_or v).resolve_left hv).symm⟩
  exact classSum_of_std Y hM hB ad hV _ hμ ⟨k, by omega⟩
    ⟨{1}, fun κ hκ => ⟨1, by simp, by simpa using level_le_Umax hin v ⟨k, by omega⟩ hκ⟩⟩

end Gen

theorem classSum_mtL {D : D7} (L : LocAll (lay0 D)) (M : MtFam D) (μ : D.what₂.Tup) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (h : ClassSum (M μ j h1 h2)) : ClassSum (mtL L M μ j h1 h2) := h

theorem classSum_states : AllSt fun _ _ _ _ w P x => ∀ m : InMt x.r.Y (cfOf x) w.I.xi (QOf P), (∀ i, RatFrame (m.ad.PV i)) →
    ∀ v j h1 h2, TwistedAt (Dof x) v → ClassSum (m.M ((Dof x).what₂.muTw v) j h1 h2) := by
  refine GlobalTheory.Mem.Top.Bl.StepW.of_all fun K B f T w _ _ _ P x m hrat v j h1 h2 hv => ?_
  obtain ⟨hB, hM⟩ : (∀ i, IsBaseFrame (Vc (Dof x) i) (x.m.z.R.βV i) (x.m.z.R.ΛV i) 1) ∧ x.m.z.R.toRealDat.IsModels := by
    refine ⟨fun i => ?_, x.m.z.pins.char.base.models⟩
    obtain ⟨c, hc⟩ := x.m.z.pins.char.base.lev.βV i
    rwa [one_pow] at hc
  exact classSum_twisted x.r.Y hM hB m.ad hrat m.mt v j h1 h2 hv

theorem exists_std_rat {D : D7} {V : HSp D} (h : GlobalTheory.StdFrame.OrthFrame V) :
    ∃ P : principalLevelFrame.RowPsi V V.rank, StdFrame (GlobalTheory.StdFrameModel.hostF_eq D) P ∧ RatFrame P :=
  ⟨_, GlobalTheory.StdFrameModel.stdPsi_unitPsi h, fun g => by simpa using GlobalTheory.NJoin.Inh.rat_unit h.gram_eq g⟩

theorem orthFrame_of_vStd {D : D7} (i : Fin D.R.m) (h : Formalism.IndefR.FWT.VStd D i) : GlobalTheory.StdFrame.OrthFrame (Vc D i) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.StdFrameCounterexample.vstd_iff i).1 h
  refine ⟨fun a b => (congrFun (congrFun h1 a) b).trans Matrix.one_apply, fun a => ?_⟩
  have := (h2 (Pi.single a 1)).2 fun b => by
    rw [Pi.single_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  simpa [Pi.single_apply] using this

theorem sumTw_rows : OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ (M : MtFam (w.st Z).toD7) tup Q, MtAd Y M → MtInput (w.st Z).toD7 M tup Q → SumTw (w.st Z).toD7 M := by
  refine (GlobalTheory.Mem.Top.evG_of_ev GlobalTheory.Mem.StdSize.vstd_size_ev).imp fun K _ _ _ _ hK =>
    GlobalTheory.Mem.Top.GroupRetwisting.lg_all K fun B f T hO _ w _ Z Wt hX z p0 Y _ _ _ _ _ M tup Q a hin v hv j h1 h2 => ?_
  obtain ⟨hV, -⟩ := hK (w.st Z) hO
  obtain ⟨hB, hM⟩ : (∀ i, Formalism.IndefR.Lev.IsBaseFrame (Formalism.IndefR.Links.Vc (w.st Z).toD7 i) (z.R.βV i) (z.R.ΛV i) 1) ∧
      z.R.toRealDat.IsModels := by
    refine ⟨fun i => ?_, z.pins.char.base.models⟩
    obtain ⟨c, hc⟩ := z.pins.char.base.lev.βV i
    rwa [one_pow] at hc
  exact classSum_twisted_std Y hM hB a (fun i => orthFrame_of_vStd i (hV i)) hin v j h1 h2 hv

end GlobalTheory.FormInner

end
