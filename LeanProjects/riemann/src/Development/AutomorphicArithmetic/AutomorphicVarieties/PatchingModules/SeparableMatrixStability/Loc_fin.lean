import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PlProps
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PlMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PlGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.HomlDesc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QuotProf

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

theorem UpperTheory.V.Pa.loc_fin :
    ∀ (l : ℕ) [Fact l.Prime] (Y : Type) [Group Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [CompactSpace Y] [TotallyDisconnectedSpace Y] (H : Subgroup Y) [H.Normal], IsOpen (H : Set Y) → PhiCond Y l → ∃ (P : Subgroup Y) (_ : P.Normal), TopFG (Y ⧸ P) ∧ ∀ (Z : Type) [Group Z] [TopologicalSpace Z] [IsTopologicalGroup Z] [CompactSpace Z] [TotallyDisconnectedSpace Z] (f : Y →* Z) (H' : Subgroup Z), Continuous f → PL l H' = ⊥ → H ≤ H'.comap f → P ≤ f.ker := by
  intro l _ Y _ _ _ _ _ H _ hH hphi
  obtain ⟨hPn, hPc, hPH, -, -, -⟩ := pl_props l Y H hH
  refine ⟨PL l H, hPn, ?_, ?_⟩
  · let P := PL l H
    let m : Y →* Y ⧸ P := QuotientGroup.mk' P
    have hmc : Continuous m := continuous_quot_mk
    have hms : Function.Surjective m := QuotientGroup.mk'_surjective P
    haveI : TotallyDisconnectedSpace (Y ⧸ P) := (totallyDisconnected_quot Y P hPc).1
    let H' : Subgroup (Y ⧸ P) := H.map m
    haveI : H'.Normal := Subgroup.Normal.map inferInstance m hms
    have hcm : H'.comap m = H := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
      exact sup_eq_left.mpr hPH
    have hH'open : IsOpen (H' : Set (Y ⧸ P)) := by
      have : (H' : Set (Y ⧸ P)) = m '' (H : Set Y) := by simp [H']
      rw [this]
      exact QuotientGroup.isOpenMap_coe _ hH
    have hPL' : PL l H' = ⊥ := by
      rw [← pl_map l Y (Y ⧸ P) m H' hH'open hmc hms, hcm]
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    have hfin : Finite (HomL l (H'.comap m)) := by
      rw [hcm]
      exact hphi H hH
    exact (pl_gen l (Y ⧸ P) H' hH'open hPL' (homl_desc l Y (Y ⧸ P) m H' hmc hms hfin).1).1
  · intro Z _ _ _ _ _ f H' hf hPL hle g hg
    rw [MonoidHom.mem_ker]
    have hmem : f g ∈ PL l H' := by
      simp only [PL, Subgroup.mem_iInf] at hg ⊢
      intro U hU
      let V : OpenNormalSubgroup Y :=
        { toOpenSubgroup := U.toOpenSubgroup.comap f hf
          isNormal' := Subgroup.Normal.comap U.isNormal' f }
      have hV : ∀ y : Y, y ∈ V ↔ f y ∈ U := fun y => Iff.rfl
      have := hg V (by
        intro h hh
        obtain ⟨e, he⟩ := hU (f h) (hle hh)
        exact ⟨e, (hV _).mpr (by simpa using he)⟩)
      exact (hV g).mp this
    rw [hPL] at hmem
    exact (Subgroup.mem_bot).mp hmem
