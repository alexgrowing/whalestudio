import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ZsVolOrb
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CntIso
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OFRepAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OrbitCountSecondStage
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.OrbitFiniteOf

noncomputable section

namespace Formalism.L2.SG.Pf.ZsVolFin

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal PI.UnitaryGroupMassFormula.CntFormula
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem reps (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hR : RowsOf u F0 what₂) (Z : MatZ D)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) :
    ∃ K : Set ((Fin D.R.rS → (VS D).V) × (VS D).V), K.Finite ∧
      ∀ F' ∈ EZ (Tn u') F0 Λ Z, ∃ n ∈ N0 F0 Λ, ((fun a => n (F'.fl.e a)), n F'.fl.z) ∈ K := by
  by_cases hne : (EZ (Tn u') F0 Λ Z).Nonempty
  · obtain ⟨F₁, hF₁⟩ := hne
    simp only [EZ, Set.mem_ofPred_eq] at hF₁
    have hG := hF₁.1.2.2
    rw [gz_eq, hF₁.2.2.2.2] at hG
    obtain ⟨R, hR1⟩ := rank_gram D _ _ Z hG
    have hfix := fixedOK_of_rows D u F0 what₂ hR hΛ
    obtain ⟨Wf, hWf, hW⟩ := orbit_count_first_stage D (Tn u') F0 Λ hfix Z R hR1
    obtain ⟨Af, hAf, hA⟩ := orbit_count_second_stage D (Tn u') F0 Λ hfix Z R hR1 Wf hWf
    refine ⟨_, finite_level_index D (Tn u') F0 Λ hfix Z R hR1 Wf Af hWf hAf, ?_⟩
    intro F' hF'
    have hx := good_places_integral D (Tn u') F0 Λ Z F' hF'
    obtain ⟨n₁, hn₁, h₁⟩ := hW _ hx
    have hx₁ := good_move D (Tn u') F0 Λ Z hx hn₁
    obtain ⟨n₂, hn₂, h₂, h₃⟩ := hA _ hx₁ h₁
    refine ⟨n₁.trans n₂, (unipotent_integral_isGroup D F0 Λ).2.2 n₁ hn₁ n₂ hn₂, ?_⟩
    refine ⟨good_move D (Tn u') F0 Λ Z hx₁ hn₂, ?_, h₃⟩
    have h₄ : pWf D (act D n₂ (act D n₁ (F'.fl.e, F'.fl.z))) ∈ Wf := h₂ ▸ h₁
    exact h₄
  · exact ⟨∅, Set.finite_empty, fun F' hF' => (hne ⟨F', hF'⟩).elim⟩

theorem fin0 (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hR : RowsOf u F0 what₂) (Z : MatZ D)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) : cntE (Tn u') F0 Λ Z ≠ ⊤ := by
  obtain ⟨K, hK, hKrep⟩ := reps D u u' F0 what₂ hR Z Λ hΛ
  have hgrp := unipotent_integral_isGroup D F0 Λ
  let g : ((Fin D.R.rS → (VS D).V) × (VS D).V) → Set (LFlag (VS D) D.R.rS (Tn u')) :=
    fun k => {F'' | F'' ∈ EZ (Tn u') F0 Λ Z ∧
      ∃ n ∈ N0 F0 Λ, ((fun a => n (F''.fl.e a)), n F''.fl.z) = k}
  have hsub : {O | ∃ F' ∈ EZ (Tn u') F0 Λ Z,
      O = {F'' | F'' ∈ EZ (Tn u') F0 Λ Z ∧ NilradicalFlagMoved F0 Λ F' F''}} ⊆ g '' K := by
    rintro O ⟨F', hF', rfl⟩
    obtain ⟨n, hn, hk⟩ := hKrep F' hF'
    refine ⟨_, hk, ?_⟩
    ext F''
    simp only [g, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hF'', m, hm, hme⟩
      refine ⟨hF'', n.trans m.symm, hgrp.2.2 n hn _ (hgrp.2.1 m hm), fun a => ?_, ?_⟩
      · have h := congrFun (congrArg Prod.fst hme) a
        simp only at h
        simp [← h]
      · have h := congrArg Prod.snd hme
        simp only at h
        simp [← h]
    · rintro ⟨hF'', m, hm, he, hz⟩
      refine ⟨hF'', m.symm.trans n, hgrp.2.2 _ (hgrp.2.1 m hm) n hn, ?_⟩
      ext a <;> simp [← he, ← hz]
  simp only [cntE]
  exact ((hK.image g).subset hsub).encard_lt_top.ne

theorem finR (D : Formalism.BasicNotions.D7) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS (Tn u))
    (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)) (hR : IsRowReps D F0 what₂) (Z : MatZ D)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hΛ : Λ ∈ what₂) : cntE (Tn u') F0 Λ Z ≠ ⊤ := by
  obtain ⟨F1, he1, hz1⟩ := Formalism.MainNotions.S.Inh.tie_flagG_nonempty D u
  have hT : Tn u ≠ 0 := by exact_mod_cast (Formalism.MainNotions.BridgeLemma.tie_Tu_pos D u).ne'
  obtain ⟨β, hβ, hβe, hβz⟩ := Formalism.L2.SG.Pf.WittFlags.flag_witt hT rfl F0 F1
  have hrows := Formalism.L2.SG.Pf.WittFlags.RowRepsIso_holds D β hβ F0 what₂ hR
  have hmem : Formalism.HermitianLatticesTheory.gmap β Λ ∈ what₂.image (Formalism.HermitianLatticesTheory.gmap β) := Finset.mem_image_of_mem _ hΛ
  have hRo : RowsOf u (Formalism.L2.SG.Saturated.mapFlag β hβ F0) (what₂.image (Formalism.HermitianLatticesTheory.gmap β)) := by
    refine ⟨?_, ?_, hrows, ⟨_, hmem⟩⟩
    · rw [← he1]
      funext a
      exact hβe a
    · rw [← hz1]
      exact hβz
  have h := fin0 D u u' _ _ hRo Z _ hmem
  rwa [Formalism.L2.SG.Pf.Cnt.counting_iso_inverse D β hβ (Tn u') F0 Λ Z] at h

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

theorem orbitFinite_holds : Formalism.L2.SG.Pf.ZsVolOrb.OrbFinE M δ u u' F0 what₂ := by
  intro γ w F' L U hH
  have hfin := finR D u u' F0 what₂ hH.2.2.1 (ZhatL (lf D F0) F') γ.lam γ.mem
  unfold cntE at hfin
  refine (Set.encard_ne_top_iff.mp hfin).subset ?_
  rintro O ⟨F'', hF'', _, rfl⟩
  exact ⟨F'', hF'', rfl⟩

end Formalism.L2.SG.Pf.ZsVolFin

end
