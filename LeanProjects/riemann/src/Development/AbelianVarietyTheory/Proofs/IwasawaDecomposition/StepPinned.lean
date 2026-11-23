import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvLgCanonical
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHalfSelectionSplitPlacesBaseStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawsOfOk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormsEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpreadLamOfLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColumnInputAssembled
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharConj
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl.PinW

theorem valsRoots (K : Ctx) : large₂ K fun B f T => ∀ (px : PreX B.toPre) (I : ColIn B px), I.Ok →
    I.S = {p | p ∈ offSet B.toPre ∧ p ≠ B.host.pde ∧ p ≠ B.host.pde'} → Set.range I.xi = T.set f →
    (∀ a P, (I.xi a).UnrAt P → ∃ z : B.LL, B.embLL z = (((I.xi a).val P : ℂˣ) : ℂ)) ∧
    ∀ a, ∀ P ∈ I.Q a, ∃ z : B.LL, IsPrimitiveRoot z (Nat.card (𝓞 B.fields.E ⧸ P.asIdeal)) := by
  classical
  choose Z hZ gZ using fun (B : Pre) (Ξ : Set (HChar B.host.E)) => GlobalTheory.Mem.Col2.InEx.exists_holds 1 Ξ
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun B _ _ _ Ξ => Z B Ξ, by simp,
    fun B _ _ _ Ξ z hz => hZ B Ξ z hz, fun B f T _ hH _ _ => ?_⟩
  intro px I h hS hxi
  refine ⟨fun a P _ => ⟨_, (h.xi_reads a _).symm⟩, fun a P hP => ?_⟩
  have hm : I.xi a ∈ T.set f := hxi ▸ Set.mem_range_self a
  have ht := GlobalTheory.Mem.Col2.InEx.isTwist_of_mem_set B f T _ hm
  have hf := (GlobalTheory.Mem.Top.TwFin.tw_fin B f T).1
  have hold := gZ B.toPre _ hf B.LL B.embLL (fun z hz => B.mem_LLC.1 (hH.2 z hz)) _ hm ht.1
  have ht' : Chr.IsTwist B.host I.S (I.xi a) := by rw [hS]; exact ht
  obtain ⟨P', a1, a2⟩ := GlobalTheory.Mem.Col2.InEx.exists_ram_of_mem_QE B h.sel_ok (I.tup a) ht' (h.xi_reads a) hP
  obtain ⟨ζ, hζ⟩ := (hold.2 P' a1).2
  refine ⟨ζ, ?_⟩
  rw [pow_one] at hζ
  have e : Nat.card (𝓞 B.fields.E ⧸ P.asIdeal) = Ideal.absNorm P.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [e, a2]
  exact hζ

theorem step_pinned (h2b : StandardLattice.SiegelMassRatioCM) :
    Step KPx (fun _ _ _ _ => True) (fun K B f T => ∃ w : ColW B f T, Pinned K B f T w) := by
  have e1 := evG_of_ev (ev_preX_frame h2b)
  have e2 := evG_of_ev GlobalTheory.Mem.Col2.TwIdxEx.evLg_canonical
  have e3 := evG_all fun K => (valsRoots K).inter (GlobalTheory.Mem.Col2.InEx.lg_colIn K)
  refine ((e1.inter e2).inter e3).imp fun K _ _ _ _ H => ?_
  obtain ⟨⟨hfr, h41⟩, hv⟩ := H
  refine (h41.inter hv).imp fun B f T hO G hk _ _ => ?_
  obtain ⟨H, V, Lc⟩ := G
  obtain ⟨⟨δ, hδ⟩, hp⟩ := hk
  obtain ⟨Pv, d, hsel, habove, hhalf, hd1, hd2⟩ := GlobalTheory.T.exists_half_selection_split_places_base B
  obtain ⟨X, I, hok, hpins, htw, hjets, hsel', hC, hS, hxi, hval⟩ := H hp (hfr _ hO).1 Pv hsel
  obtain ⟨hv1, hv2⟩ := V X I hok hS hxi
  subst hsel'
  exact ⟨⟨X, I, hok, hC, hS, hxi, hpins, GlobalTheory.Mem.Col2.TC.laws_of_ok I hok, StepZero.law0 I hok _, δ, hδ, Lc.2.2,
      fun C W V S N G => (hval C W V S N G).1⟩,
    ⟨⟨htw, hjets, GlobalTheory.Mem.FieldsLaws.fields_ok B, habove, hhalf, d, ⟨hd1, hd2⟩, hv1, hv2⟩⟩⟩

end GlobalTheory.Mem.Top.Bl.PinW
