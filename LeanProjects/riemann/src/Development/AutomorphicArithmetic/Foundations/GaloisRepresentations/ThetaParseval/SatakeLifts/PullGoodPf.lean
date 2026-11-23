import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SatakeLifts.CompUnit
open NumberField IsDedekindDomain ValuativeRel Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.CuspRep UpperTheory.Gal.TP.Loc
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem map_surj {k k' : Type} [Field k] [Field k'] (c : k →+* k') (hs : Function.Surjective c) (n : ℕ) :
    Function.Surjective (Matrix.GeneralLinearGroup.map (n := Fin n) c) := by
  intro g
  let e : k ≃+* k' := RingEquiv.ofBijective c ⟨c.injective, hs⟩
  refine ⟨Matrix.GeneralLinearGroup.map (n := Fin n) (e.symm : k' →+* k) g, ?_⟩
  apply Units.ext
  ext i j
  have : c (e.symm ((g : Matrix (Fin n) (Fin n) k') i j)) = (g : Matrix (Fin n) (Fin n) k') i j :=
    e.apply_symm_apply _
  simpa using this

private theorem map_cont {k k' : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [Field k']
    [TopologicalSpace k'] [IsTopologicalRing k'] (c : k →+* k') (hc : Continuous c) (n : ℕ) :
    Continuous (Matrix.GeneralLinearGroup.map (n := Fin n) c) := by
  have h : Continuous (RingHom.mapMatrix (m := Fin n) c : Matrix (Fin n) (Fin n) k →+* Matrix (Fin n) (Fin n) k') :=
    Continuous.matrix_map continuous_id hc
  exact Continuous.units_map (RingHom.mapMatrix (m := Fin n) c : Matrix (Fin n) (Fin n) k →+* Matrix (Fin n) (Fin n) k').toMonoidHom h

private theorem irr_comp {H H' X : Type} [Group H] [Group H'] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ H X) (φ : H' →* H) (hφ : Function.Surjective φ) (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp φ) := by
  obtain ⟨h0, h1⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 h
  refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h1 W fun g v hv => ?_⟩
  obtain ⟨g', rfl⟩ := hφ g
  exact hW g' v hv

theorem UpperTheory.Gal.TP.Loc.pullGood :
    UpperTheory.Gal.TP.Loc.PullGood := by
  intro k k' _ _ _ _ _ _ c hc hs n V _ _ ρ
  refine ⟨fun h => isSmooth_comp h _ (map_cont c hc n), fun h => irr_comp ρ _ (map_surj c hs n) h, ?_⟩
  rintro ⟨B, h1, h2, h3⟩
  exact ⟨B, h1, h2, fun g v w => h3 _ v w⟩
