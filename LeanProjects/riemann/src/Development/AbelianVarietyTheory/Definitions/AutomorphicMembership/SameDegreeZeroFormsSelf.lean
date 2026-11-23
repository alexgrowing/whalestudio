import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SpectralTiesReal
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists
import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RefilledStagesRecord
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff

noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure SPack (D : D7) (F : ∀ u, Forms0 D u) where
  X : HidaSetting D
  hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I
  Y : Formalism.L2.SG.Full.Full X
  fin : FinX Y
  ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ
  measTie : X.MeasTie hb
  ψ_char : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ
  ψ_std : Formalism.L2.SG.LocVol.IsStdChar ψ
  measCompat : Formalism.L2.SG.MassDataConc.MeasCompatψ X ψ
  locCompat : ∀ w, Formalism.L2.SG.LocVol.LocCompatX X ψ w
  tr : ∀ u, Transport X u (F u)
  into : ∀ u, ColDictInto X (tr u) Y.hK
  bij : ∀ u, ColDictBij X (tr u) Y.hK
  lev : ∀ u, LevelMatch X (tr u) Y.hK
  isom : ∀ u, ColDictIsom X (tr u) Y.hK (Y.cs u) (fin.shInj u)
  inst : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D
  G : GoodOp X

  pin : ∀ x : X.B.I.E, HEq (X.ιE x) x

structure SRest {D : D7} {F : ∀ u, Forms0 D u} (P : SPack D F) where
  hI : SIso D.s (sOf P.fin)
  autTie : Formalism.MainNotions.S.AutTie D P.X.B P.X.pl
  colPin : ∀ (u : D.what₂.Word) (x : D.s.Cu u),
    colDict P.X (P.tr u) P.Y.hK (P.into u) (P.bij u) (hI.eCu u x) = D.s_Cu u x
  j : D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G
  rowPin : ∀ x : D.what₂.EE, hI.eHH (D.sEE x) = conjHH P.X P.G (j x)
  locTied : Formalism.L2.SG.Pf.LocCP.LocTied D

def SRest.toSTies {D : D7} {F : ∀ u, Forms0 D u} {P : SPack D F} (S : SRest P) : Formalism.L2.SG.SpectralTiesReal.STies D where
  X := P.X
  hb := P.hb
  Y := P.Y
  hI := fun _ => S.hI
  ψ := P.ψ
  autTie := S.autTie
  measTie := P.measTie
  ψ_char := P.ψ_char
  ψ_std := P.ψ_std
  measCompat := P.measCompat
  locCompat := P.locCompat

theorem SRest.rowTie {D : D7} {F : ∀ u, Forms0 D u} {P : SPack D F} (S : SRest P) : RowDictTie P.X P.G S.hI.eHH :=
  ⟨S.j, S.rowPin⟩

def SPack.toNew {D : D7} {F : ∀ u, Forms0 D u} (P : SPack D F) (hD : Module.finrank ℂ (HHX P.X) = D.what₂.Dall)
    (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC P.X P.G) : SNew D where
  s := sOf P.fin
  s_HH := hD
  s_Cu := fun u => colDictT P.X (P.tr u) P.Y.hK (P.fin.shInj u) (P.into u) (P.bij u)
  s_PlF := Equiv.refl _
  s_Cu_isom := fun u x y => P.isom u x y
  sEE := (conjHH P.X P.G).comp j.toLinearIsometry

def SameDegreeZeroForms {D : D7} (Z : SNew D) (F : ∀ u, Forms0 D u) (F' : ∀ u, Forms0 (reS D Z) u) : Prop :=
  ∀ u : D.what₂.Word, (F' u).cls0.lev = (F u).cls0.lev ∧ (F' u).cls0.y = (F u).cls0.y ∧ (F' u).val0.eY = (F u).val0.eY

theorem pl_heq_of_pin {D : D7} (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (pin : ∀ x : X.B.I.E, HEq (X.ιE x) x) :
    HEq X.pl (Formalism.L2.Host.tauPl D).symm := by
  have key : ∀ (I : AutInst) (_ : I = Formalism.L2.SG.InstExistsPf.instOf D) (ι : I.E ≃+* D.host.E)
      (pl : InfinitePlace I.F ≃ D.what₂.Tau), (∀ x : I.E, HEq (ι x) x) →
      (∀ v (x : I.E), I.φ v x = Formalism.MainNotions.S.embS D (pl v) (ι x)) → HEq pl (Formalism.L2.Host.tauPl D).symm := by
    intro I e ι pl hι hφ
    subst e
    refine heq_of_eq (Equiv.ext fun v => ?_)
    apply (Formalism.L2.Host.tauPl D).injective
    refine Eq.trans ?_ ((Formalism.L2.Host.tauPl D).apply_symm_apply v).symm
    have hv : (Formalism.L2.Host.tauPl D (pl v)).embedding = InfinitePlace.embedding (K := D.host.F) v := by
      refine RingHom.ext fun a => ?_
      have h1 := hφ v (algebraMap D.host.F D.host.E a)
      have h2 := congrArg (Formalism.MainNotions.S.embS D (pl v)) (eq_of_heq (hι (algebraMap D.host.F D.host.E a)))
      exact (Formalism.L2.SG.InstExistsPf.embS_over D (pl v) a).symm.trans
        ((h1.trans h2).symm.trans ((Formalism.L2.SG.InstExistsPf.instOf D).φ_over v a))
    exact (InfinitePlace.mk_embedding _).symm.trans
      ((congrArg InfinitePlace.mk hv).trans (InfinitePlace.mk_embedding (K := D.host.F) v))
  exact key _ h X.ιE X.pl pin X.φ_eq

theorem SPack.ιE_heq {D : D7} {F : ∀ u, Forms0 D u} (P : SPack D F) : HEq P.X.ιE (RingEquiv.refl D.host.E) := by
  have key : ∀ (I : AutInst) (_ : I = Formalism.L2.SG.InstExistsPf.instOf D) (ι : I.E ≃+* D.host.E),
      (∀ x : I.E, HEq (ι x) x) → HEq ι (RingEquiv.refl D.host.E) := by
    intro I e ι hι
    subst e
    exact heq_of_eq (RingEquiv.ext fun x => eq_of_heq (hι x))
  exact key _ P.inst P.X.ιE P.pin

theorem SPack.pl_heq {D : D7} {F : ∀ u, Forms0 D u} (P : SPack D F) : HEq P.X.pl (Formalism.L2.Host.tauPl D).symm :=
  pl_heq_of_pin P.X P.inst P.pin

example (D : D7) (x : (Formalism.L2.SG.InstExistsPf.instanceOfRecord D).I.E) : HEq ((Formalism.L2.SG.InstExistsPf.instanceOfRecord D).ιE x) x := HEq.rfl

theorem SPack.locTied_of_sIso {D : D7} {F : ∀ u, Forms0 D u} (P : SPack D F) (h : SIso D.s (sOf P.fin)) :
    Formalism.L2.SG.Pf.LocCP.LocTied D :=
  fun p => ⟨h.atP p⟩

theorem SRest.finrank_HHX {D : D7} {F : ∀ u, Forms0 D u} {P : SPack D F} (S : SRest P) :
    Module.finrank ℂ (HHX P.X) = D.what₂.Dall :=
  (dall_eq P.X S.hI.eHH).symm

theorem SRest.toNew_s_Cu {D : D7} {F : ∀ u, Forms0 D u} {P : SPack D F} (S : SRest P) (u : D.what₂.Word) (x : D.s.Cu u) :
    (P.toNew S.finrank_HHX S.j).s_Cu u (S.hI.eCu u x) = D.s_Cu u x := S.colPin u x

theorem SRest.toNew_sEE {D : D7} {F : ∀ u, Forms0 D u} {P : SPack D F} (S : SRest P) (x : D.what₂.EE) :
    (P.toNew S.finrank_HHX S.j).sEE x = S.hI.eHH (D.sEE x) := (S.rowPin x).symm

theorem exists_sRest_of_sTies {D : D7} (F : ∀ u, Forms0 D u) (T : Formalism.L2.SG.SpectralTiesReal.STies D) (hF : FinX T.Y)
    (tr : ∀ u, Transport T.X u (F u)) (into : ∀ u, ColDictInto T.X (tr u) T.Y.hK) (bij : ∀ u, ColDictBij T.X (tr u) T.Y.hK)
    (lev : ∀ u, LevelMatch T.X (tr u) T.Y.hK)
    (colPin : ∀ (u : D.what₂.Word) (x : D.s.Cu u),
      colDict T.X (tr u) T.Y.hK (into u) (bij u) ((T.hI hF).eCu u x) = D.s_Cu u x)
    (inst : T.X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (pin : ∀ x : T.X.B.I.E, HEq (T.X.ιE x) x)
    (G : GoodOp T.X) (rowTie : RowDictTie T.X G (T.hI hF).eHH)
    (locTied : Formalism.L2.SG.Pf.LocCP.LocTied D) : ∃ (P : SPack D F) (S : SRest P), S.toSTies = T := by
  obtain ⟨j, hj⟩ := rowTie
  have isom : ∀ u, ColDictIsom T.X (tr u) T.Y.hK (T.Y.cs u) (hF.shInj u) := by
    intro u a b
    obtain ⟨x, rfl⟩ := ((T.hI hF).eCu u).surjective a
    obtain ⟨y, rfl⟩ := ((T.hI hF).eCu u).surjective b
    have hx := congrArg Subtype.val (colPin u x)
    have hy := congrArg Subtype.val (colPin u y)
    have h := D.s_Cu_isom u x y
    rw [← hx, ← hy] at h
    exact (((T.hI hF).eCu u).inner_map_map x y).trans h
  exact ⟨⟨T.X, T.hb, T.Y, hF, T.ψ, T.measTie, T.ψ_char, T.ψ_std, T.measCompat, T.locCompat, tr, into, bij, lev, isom, inst, G, pin⟩,
    ⟨T.hI hF, T.autTie, colPin, j, hj, locTied⟩, rfl⟩

theorem sameDegreeZeroForms_self {D : D7} (F : ∀ u, Forms0 D u) : SameDegreeZeroForms (SNew.self D) F F := fun _ => ⟨rfl, rfl, rfl⟩

theorem nonempty_sPack_of_steps {D : D7} (F : ∀ u, Forms0 D u) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D)
    (hC : Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc) (s1 : Formalism.L2.SG.SplitPrimeNormLemmas.LatExists D) (s2 : Formalism.L2.SG.SplitPrimeNormLemmas.PsiExists D)
    (s3 : Formalism.L2.SG.SplitPrimeNormLemmas.RefExists D) (s4 : Formalism.L2.SG.SplitPrimeNormLemmas.XuExists D) (s5 : Formalism.L2.SG.SplitPrimeNormLemmas.BunExists D)
    (s6 : Formalism.L2.SG.SplitPrimeNormLemmas.PiExists D) (s7 : Formalism.L2.SG.SplitPrimeNormLemmas.MuExists D) (s8 : GlobalTheory.St.WBlkExists D)
    (s9 : Formalism.L2.SG.SplitPrimeNormLemmas.MExists D) (s10 : GlobalTheory.St.RescaleStep3 D) (tw : GlobalTheory.St.WittExists D) (t0 : GlobalTheory.St.GenusMatch D F)
    (t3 : GlobalTheory.St.LevelConj D F) (t4 : GlobalTheory.St.HcExists D F) (t5 : GlobalTheory.St.JExists D F)
    (hY : ∀ X : HidaSetting D, Nonempty (Formalism.L2.SG.Full.Full X))
    (hF : ∀ (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X), FinX Y) (hD : GlobalTheory.St.ColDictCore D)
    (hN : ∀ (X : HidaSetting D) (hK : X.LevelSubgroupCharacter) (u : D.what₂.Word), Formalism.L2.SG.ColsDim.StabTriv (iotaF X u) (Ku X u hK))
    (hg : ∀ X : HidaSetting D, Nonempty (GoodOp X)) : Nonempty (SPack D F) := by
  let A := Formalism.L2.SG.InstExistsPf.instanceOfRecord D
  obtain ⟨L⟩ := s1
  obtain ⟨P⟩ := s2 A
  obtain ⟨Rf⟩ := s3 A L
  obtain ⟨Xu⟩ := s4 A L Rf
  obtain ⟨Bu⟩ := s5 hC hG A L P Rf
  obtain ⟨Pi⟩ := s6 A L
  obtain ⟨Mu⟩ := s7 A L
  obtain ⟨Wb⟩ := s8 hG A L P Rf Bu Pi Mu
  obtain ⟨Mb, hb, hM⟩ := s9 A L P Rf Xu Bu Pi Mu Wb
  obtain ⟨mg, hg', mw, hw, hM', ψ, hψ, hstd, hCm, hL⟩ := s10 (Formalism.L2.SG.SplitPrimeNormLemmas.mk A L P Rf Xu Bu Pi Mu Wb Mb) hb hM
  let X : HidaSetting D :=
    Formalism.L2.SG.SettingExistsMeasured.withMeas (Formalism.L2.SG.SplitPrimeNormLemmas.mk A L P Rf Xu Bu Pi Mu Wb Mb) mg hg' mw hw
  obtain ⟨Y⟩ := hY X
  obtain ⟨G⟩ := hg X
  have ht : ∀ u, ∃ Tr : Transport X u (F u), LevelMatch X Tr Y.hK := by
    intro u
    obtain ⟨wt, hw⟩ := tw X u
    obtain ⟨ιA, hι⟩ : ∃ ιA, GlobalTheory.St.IsAdeleIso X ιA := ⟨RingEquiv.refl _, fun _ => rfl, fun _ => Iff.rfl⟩
    obtain ⟨g0, hg0⟩ := t0 X u wt ιA hw hι
    obtain ⟨h0, hL, hKm⟩ := t3 X Y.hK u wt ιA g0 hw hι hg0
    choose hcf hcr using t4 X u wt ιA h0 hw hι
    obtain ⟨J, hJ1, hJ2, hJ3⟩ := t5 X u wt hw
    exact ⟨⟨wt, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2, ιA, hι.1, hι.2, h0, hcf, hcr, J, hJ1, hJ2, hJ3⟩, hL, hKm⟩
  choose tr hlev using ht
  have hd := fun u => hD X u (F u) (tr u) Y.hK (hlev u) (hN X Y.hK u)
  exact ⟨⟨X, hb, Y, hF X Y, ψ, hM', hψ, hstd, hCm, hL, tr, fun u => (hd u).2.1, fun u => (hd u).2.2.1, hlev,
    fun u => (hd u).2.2.2 _ _ _ (Y.colReps u), rfl, G, fun _ => HEq.rfl⟩⟩

end GlobalTheory.Mem.SRe

end
