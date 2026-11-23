import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCommutationIdentity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadsLow
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnifOfReadStatement

set_option synthInstance.maxHeartbeats 200000

section
set_option genSizeOfSpec false
set_option genInjectivity false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.PenChart
section Orbits
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n]
end Orbits
section Restr
variable {D : D7} {c : Comm D} {v : VCom c} {Bs : GlobalTheory.Fam.Base c} {PP : Pl D.host.E} {G : QGeo v Bs PP} {χ : ℕ → (AE D)ˣ →* Circle}
end Restr
section Place
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
  {Ch₀ : ℕ → Type} (A : TwDat I l Z u a Ch₀)
  {c : Comm (I.rec7 l Z)} {v : VCom c} {Bs : GlobalTheory.Fam.Base c} {PP : Pl (I.rec7 l Z).host.E} {G : QGeo v Bs PP}
  {χ : ℕ → (AE (I.rec7 l Z))ˣ →* Circle} (E : QExt G χ)
variable {A E} {P : BadPr I a} {hψ : Continuous G.ψk} {sg : ℂ}
end Place
section Level
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
  {Ch₀ : ℕ → Type} {A : TwDat I l Z u a Ch₀} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Level
set_option maxHeartbeats 4000000 in
theorem exists_readsStd_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).Is → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.ReadsLow → ∃ J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t, J'.ReadsStd := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha ha' hc t J h
  have hI := hW.tr.ok
  have ht := hW.tr.tw
  have h2 := B.R.two_le_m
  have hs : ∀ i, (J.G i).s + 1 + 1 = B.R.m := fun i => (J.G i).hs
  have hPi : Function.Injective J.P := fun i i' e => h.inj ((h.eq i).symm.trans ((congrArg Subtype.val e).trans (h.eq i')))
  have hPs : ∀ P : BadPr I (W.P.I.tup t), P.1 ∈ I.Q (W.P.I.tup t) → ∃ i, J.P i = P := fun P hP => by
    obtain ⟨i, e⟩ := h.surj P.1 ((hW.tq.Q t P.1).2 hP)
    exact ⟨i, Subtype.ext ((h.eq i).trans e)⟩
  have hQ : ∀ i, (J.P i).1 ∈ I.Q (W.P.I.tup t) := fun i => (Finset.mem_union.1 (J.P i).2).resolve_left (h.tw i).nmem
  have hbox : ∀ i j, j + 1 ≠ B.R.m → ∀ y, InBox (J.E i) j y := fun i j hj y e => hj ((congrArg (· + 1) e).trans (hs i)) |>.elim
  have kπ : ∀ i j (β : J.Ch₀ j), ∃ y : {y : (J.E i).Ch j // InBox (J.E i) j y},
      (j + 1 ≠ B.R.m → y.1 = J.π i j β) ∧ OrbAt J.A (J.E i) j y.1 β := fun i j β => by
    by_cases hj : j + 1 = B.R.m
    · obtain ⟨y, h1, h3⟩ := exists_orbAt hI h.is (h.tw i) (h.M i) hj β (h.std j (by omega) β)
      exact ⟨⟨y, h1⟩, fun e => absurd hj e, h3⟩
    · exact ⟨⟨J.π i j β, hbox i j hj _⟩, fun _ => rfl, fun e => (hj ((congrArg (· + 1) e).trans (hs i))).elim⟩
  choose π hπ hπ' using kπ
  have kι : ∀ j (y : ∀ i, {y : (J.E i).Ch j // InBox (J.E i) j y}), ∃ β : J.Ch₀ j,
      (j + 1 ≠ B.R.m → β = J.ι j fun i => (y i).1) ∧
      (j + 1 = B.R.m → Good (J.A.p0 j β) ∧ ∀ i, OrbAt J.A (J.E i) j (y i).1 β) := fun j y => by
    by_cases hj : j + 1 = B.R.m
    · let b := J.A.b0 j (J.ι j fun i => (y i).1)
      choose z hz hz' using fun i => exists_vec hI h.is (h.tw i) (h.M i) hj b (y i).2
      obtain ⟨β, hβ, hβ'⟩ := exists_chart hI ht h.is hj b (Function.extend J.P z 0) fun P hP => by
        obtain ⟨i, rfl⟩ := hPs P ((Finset.mem_union.1 P.2).resolve_left hP)
        rw [hPi.extend_apply]
        exact hz i
      refine ⟨β, fun e => absurd hj e, fun _ => ⟨hβ, fun i => hz' i (hQ i) β (h.std j (by omega) β) ?_⟩⟩
      have := hβ' (J.P i) (hQ i)
      rwa [hPi.extend_apply] at this
    · exact ⟨_, fun _ => rfl, fun e => absurd e hj⟩
  choose ι hι hι' using kι
  have hsec : ∀ j, j ≤ B.R.m → ∀ y i, π i j (ι j y) = y i := fun j hj y i => by
    refine Subtype.ext ?_
    by_cases e : j + 1 = B.R.m
    · exact orbAt_unique e (hπ' i j _) ((hι' j y e).2 i)
    · rw [hπ i j _ e, hι j y e]
      exact h.sec j hj e _ i
  have hlift : ∀ j, j + 1 ≠ B.R.m → ∀ y, J.ι j y ∈ Set.range (ι j) := fun j hj y =>
    ⟨fun i => ⟨y i, hbox i j hj _⟩, hι j _ hj⟩
  let J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t := ⟨J.Ch₀, J.A, J.r, J.pl, J.mem, fun i => restr (J.E i), J.P, J.hψ, J.sg, π, ι⟩
  refine ⟨J', h.is, h.inj, h.surj, h.chr, h.res, h.eq, h.sg, h.tw, h.M, fun i j d e hj β => ?_, fun i β => hπ' i _ β rfl, h.std, h.last,
    hsec, fun n y e he r => ?_, fun j => ?_, fun β => ?_, fun β => ?_, fun j hj γ hγ α z => ?_⟩
  · have e' : j + d = (J.G i).s := e
    have := h.rep i j d e hj β
    rw [← hπ i j β (by have := hs i; omega)] at this
    exact this
  · have hn : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
    have hP : (a.pl n).1 ∈ (B.primes X).vGs := (hW.lev.2.1 _).1 (a.pl n).2
    obtain ⟨h3, h4⟩ := _root_.GlobalTheory.T.true_geometry_commutation_twist_alt W hW u a ha ha' hc n
    exact couplingCoset_sub_basePoint_integral_typePrime hI h.is hn (a.G n).S ((a.G n).q.pr.comp (incA (I.rec7 l Z))) ⟨(a.pl n).1, Finset.mem_union_left _ hP⟩ hP h3 h4 _
      (h.std _ (by omega) _) (hι' _ y hn).1 e he r
  · by_cases e : j + 1 = B.R.m
    · exact fun y y' hy => funext fun i => (hsec j (by omega) y i).symm.trans
        ((congrArg (π i j) hy).trans (hsec j (by omega) y' i))
    · intro y y' hy
      have h3 := h.injCh j e ((hι j y e).symm.trans (hy.trans (hι j y' e)))
      exact funext fun i => Subtype.ext (congrFun h3 i)
  · obtain ⟨y, rfl⟩ := h.first β
    exact hlift 0 (by omega) y
  · obtain ⟨y, rfl⟩ := h.onto β
    exact hlift _ (by omega) y
  · by_cases e : j + 1 + 1 = B.R.m
    · by_contra hz
      refine hγ ⟨fun i => π i (j + 1) γ, ?_⟩
      refine chart_ext hI ht h.is e (J.A.b0 _ γ) _ _ (hι' _ _ e).1 (good_of_xi hI ht e hj α γ z hz) fun P hP => ?_
      obtain ⟨i, rfl⟩ := hPs P hP
      exact lev_of_orbAt hI h.is (h.tw i) (h.M i) e _ hP (h.std _ (by omega) _) (h.std _ (by omega) _) ((hι' _ _ e).2 i) (hπ' i _ γ)
    · refine h.dead j hj e γ ?_ α z
      rintro ⟨y, rfl⟩
      exact hγ (hlift _ e y)
end GlobalTheory.PenChart
end
end
