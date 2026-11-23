import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotConditionOfFalse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JetsInOfIsTw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHalfSelectionSplitPlacesBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColumnInputAssembled

noncomputable section

namespace GlobalTheory.Mem.Top.Bl

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain

theorem lg_vals_roots (K : Ctx) : large₂ K fun B f T =>
    (∀ ξ ∈ T.set f, ∀ P, ∃ z : B.LL, B.embLL z = ((ξ.val P : ℂˣ) : ℂ)) ∧
    ∀ ξ ∈ T.set f, ∀ P, ¬ ξ.UnrAt P → ∃ ζ : B.LL, IsPrimitiveRoot ζ (Ideal.absNorm P.asIdeal) := by
  choose Z hZ gZ using fun (B : Pre) (Ξ : Set (HChar B.host.E)) => InEx.exists_holds 1 Ξ
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun B _ _ _ Ξ => Z B Ξ, by simp,
    fun B _ _ _ Ξ => hZ B Ξ, fun B f T _ hH _ _ => ?_⟩
  have hf := (TwFin.tw_fin B f T).1
  have ht := InEx.isTwist_of_mem_set B f T
  have h2 : ∀ z ∈ Z B.toPre (T.set f), ∃ x, B.embLL x = z := fun z hz => B.mem_LLC.1 (hH.2 z hz)
  have hold := fun ξ hξ => gZ B.toPre _ hf B.LL B.embLL h2 ξ hξ (ht ξ hξ).1
  refine ⟨fun ξ hξ P => RingHom.mem_range.1 ((hold ξ hξ).1 _), fun ξ hξ P hP => ?_⟩
  obtain ⟨ζ, hζ⟩ := ((hold ξ hξ).2 P hP).2
  exact ⟨ζ, by simpa using hζ⟩

theorem step_colW_pinned (h2b : StandardLattice.SiegelMassRatioCM) :
    Step KPx (fun _ _ _ _ => True) fun K B f T => ∃ w : ColW B f T, Pinned K B f T w := by
  refine EvG.imp ((evG_of_ev (ev_preX_frame h2b)).inter (evG_of_ev TwEx.evLg_canonical)) fun K _ _ _ _ H => ?_
  refine ((H.2.inter (InEx.lg_colIn K)).inter (lg_vals_roots K)).imp ?_
  rintro B f T hO ⟨⟨hc, hl⟩, hv, hr⟩ ⟨⟨δ, hδ⟩, hp⟩ - -
  obtain ⟨X₀⟩ := (H.1 _ hO).1
  obtain ⟨Pv, d, hsel, habove, hhalf, hd1, hd2⟩ := exists_half_selection_split_places B
  obtain ⟨X, I, a1, pins, ht, hj, es, a2, a3, a4, -⟩ := hc hp ⟨X₀⟩ Pv hsel
  have hxi : ∀ a, I.xi a ∈ T.set f := fun a => a4 ▸ ⟨a, rfl⟩
  refine ⟨⟨X, I, a1, a2, a3, a4, pins, TrueColsTest.laws a1, TrueColsTest.law0 a1 _, δ, hδ, hl.2.2, hl.2.1⟩, ⟨?_⟩⟩
  refine
    { isTw := ht
      jets := hj
      hX := FieldsLaws.fields_ok B
      above := fun v => es ▸ habove v
      half := es ▸ hhalf
      d3b := d
      selectedPlacesAgree := ⟨fun v hv => es ▸ hd1 v hv, fun v hv => es ▸ hd2 v hv⟩
      vals := fun a P _ => hv _ (hxi a) P
      roots := fun a P hP => ?_ }
  have htw : Chr.IsTwist B.host I.S (I.xi a) := by
    rw [a3]
    exact InEx.isTwist_of_mem_set B f T _ (hxi a)
  obtain ⟨P', h1, h2⟩ := InEx.exists_ram_of_mem_QE B (es ▸ hsel) (I.tup a) htw (a1.xi_reads a) hP
  obtain ⟨ζ, hζ⟩ := hr _ (hxi a) P' h1
  refine ⟨ζ, ?_⟩
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, h2]
  exact hζ

end GlobalTheory.Mem.Top.Bl

end
