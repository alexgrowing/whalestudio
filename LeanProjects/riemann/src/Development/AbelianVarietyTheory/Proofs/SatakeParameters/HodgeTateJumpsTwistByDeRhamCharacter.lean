import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactGroupRepDefinedOverFiniteExtension
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepERankOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCompletionEmbeddingInducingHostEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamGaloisSideIffDeRhamAtLocalEmbedding
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompletionDegrees.NormLeOneOfInteger
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.TwistJumpsW
open Formalism.BasicNotions.Loc

theorem jumpsW_twist : ∀ (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (i : D.nd.Loc) (ι : Qbar (D.nd.l i) ≃+* ℂ) (a : ℕ) (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i))) (χ : G D.host.E D.nd.Om →* GL (Fin 1) (Qbar (D.nd.l i))), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ → Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i χ → ∀ (τ : D.host.E →+* Qbar (D.nd.l i)) (c : ℤ), (∀ w, InducesW D.nd i τ w → W.IsdRW (D.nd.l i) ι ρ w ∧ W.IsdRW (D.nd.l i) ι χ w) → W.jumpsW (D.nd.l i) ι χ τ = {c} → W.jumpsW (D.nd.l i) ι (Formalism.MainNotions.SumRepresentations.At.twGL ρ (Matrix.GeneralLinearGroup.det.comp χ)) τ = (W.jumpsW (D.nd.l i) ι ρ τ).map (· + c) := by
  intro D T W i ι a ρ χ hρ hχ τ c hdR hc
  let w := PI.CompDegEF.plOf τ
  have hw : w ∈ placesOver D.host.E (D.nd.l i) := PI.CompDegEF.natCast_mem_plIdeal τ
  have hIW : InducesW D.nd i τ w := fun x => Iff.rfl
  obtain ⟨hdρ, hdχ⟩ := hdR w hIW
  have hj : GlobalTheory.Pst.Induces (D.nbr i w hw) := D.nbr_ind i w hw
  obtain ⟨L₁, hL₁, hm₁⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem (D.nd.l i) (G D.host.E D.nd.Om) a ρ hρ
    (D.nbr i w hw).LL
  obtain ⟨L, hL, hm⟩ := GlobalTheory.CompactRepField.exists_finExt_entries_mem (D.nd.l i) (G D.host.E D.nd.Om) 1 χ hχ L₁
  have hBL : (D.nbr i w hw).LL.1 ≤ L.1 := hL₁.trans hL
  obtain ⟨τ', hτ'⟩ := GlobalTheory.EmbExt.main D (D.nd.l i) w _ (D.nbr i w hw) hj τ hIW L hBL
  obtain ⟨ρ₁, cρ, rfl⟩ := GlobalTheory.DeRhamRead.exists_model_of_mem ρ hρ L (fun g i j => hL (hm₁ g i j))
  obtain ⟨χ₁, cχ, rfl⟩ := GlobalTheory.DeRhamRead.exists_model_of_mem χ hχ L hm
  obtain ⟨-, H⟩ := W.loc (D.nd.l i) ι w hw _ (D.nbr i w hw) hj
    ((algebraMap ↥(D.nbr i w hw).LL.1 (Om (D.nd.l i))).comp (D.nbr i w hw).toLL) (fun _ => rfl)
  let tw₁ : G D.host.E D.nd.Om →* GL (Fin a) ↥L.1 := GlobalTheory.TwistAbove.twGL (Matrix.GeneralLinearGroup.det.comp χ₁) ρ₁
  have htw : Formalism.MainNotions.SumRepresentations.At.twGL (mapRep (algebraMap ↥L.1 (Qbar (D.nd.l i))) ρ₁)
      (Matrix.GeneralLinearGroup.det.comp (mapRep (algebraMap ↥L.1 (Qbar (D.nd.l i))) χ₁)) =
      mapRep (algebraMap ↥L.1 (Qbar (D.nd.l i))) tw₁ := by
    refine MonoidHom.ext fun g => Units.ext ?_
    ext p q
    simp [tw₁, mapRep, Formalism.MainNotions.SumRepresentations.At.twGL, Matrix.det_unique, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_mul]
  have ctw : Continuous (fun g => ((tw₁ g : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1)) := by
    have h1 : Continuous (fun g => ((χ₁ g : GL (Fin 1) ↥L.1) : Matrix (Fin 1) (Fin 1) ↥L.1).det) := cχ.matrix_det
    refine continuous_matrix fun p q => ?_
    refine (h1.mul (cρ.matrix_elem p q)).congr fun g => ?_
    simp [tw₁, GlobalTheory.TwistAbove.twGL_val, Matrix.GeneralLinearGroup.val_det_apply]
  rw [htw]
  have Hρ := H L hBL a ρ₁ cρ
  have Hχ := H L hBL 1 χ₁ cχ
  have Htw := H L hBL a tw₁ ctw
  have dρ := Hρ.2.1.1 hdρ
  have dχ := Hχ.2.1.1 hdχ
  have hcom := GlobalTheory.TwistAbove.twist_common (D.nbr i w hw) (ρ₁.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype)
    (χ₁.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) (D.locT (D.nd.l i))
  have dtw : (D.nbr i w hw).IsdRE (D.loc (D.nd.l i)) L (tw₁.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) :=
    hcom.1 dρ dχ
  have mχ : ∀ n, (D.nbr i w hw).multE (D.loc (D.nd.l i)) L (χ₁.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) τ' n =
      if n = c then 1 else 0 := by
    intro n
    rw [← (Hχ.2.2.2 τ τ' hτ').2 dχ n, hc, Multiset.count_singleton]
    split_ifs <;> simp
  ext n
  have e1 := (Htw.2.2.2 τ τ' hτ').2 dtw n
  have e2 := hcom.2.2.2 τ' c dχ mχ (n - c)
  have e3 := (Hρ.2.2.2 τ τ' hτ').2 dρ (n - c)
  have e4 := Multiset.count_map_eq_count' (fun x : ℤ => x + c) (W.jumpsW (D.nd.l i) ι (mapRep (algebraMap ↥L.1 (Qbar (D.nd.l i))) ρ₁) τ)
    (add_left_injective c) (n - c)
  simp only [sub_add_cancel] at e2 e4
  rw [e4]
  exact_mod_cast e1.trans (e2.trans e3.symm)

end GlobalTheory.TwistJumpsW
end
