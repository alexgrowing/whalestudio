import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.SpacesExOf
import GroundTheory.IdeleRoots.TorusPowers.HeckeIdem
open scoped nonZeroDivisors Matrix NumberField.AdeleRing
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.Gal.TP.Skew GroundTheory.Global.AdeleBaseChange GroundTheory.Global.SemiLocal

theorem UpperTheory.Gal.TP.Skew.ordEmb :
    UpperTheory.Gal.TP.Skew.OrdEmb := by
  intro F E _ _ _ _ _ hu a w
  have he : w.asIdeal.ramificationIdx (𝓞 F) = 1 := Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 F)
  have hc : ((ideleEmbedding F E a : IdeleGroup E) : 𝔸[E]).2 w =
      completionMap (below F w) w ((a : 𝔸[F]).2 (below F w)) := by
    rw [coe_ideleEmbedding]
    exact GroundTheory.BlockD.ThmBHecke.adeleMap_snd_apply _ w
  unfold ord
  rw [hc, valued_completionMap, he, pow_one]
  rfl
