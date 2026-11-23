import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.MatchPowAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.PowIndep

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open UpperTheory.Gal.InertialTypesAlt.G

theorem UpperTheory.Gal.InertialTypesAlt.G.powNe :
    UpperTheory.Gal.InertialTypesAlt.G.PowNe := by
  intro Z hZ h0
  by_contra h
  rw [Filter.not_frequently] at h
  obtain ⟨ζ, hζ⟩ := Multiset.exists_mem_of_ne_zero hZ
  have h1 := UpperTheory.ConvolutionTheory.C.powIndep Unit (fun _ => 1) (fun _ => Z) (fun _ => h0)
    (h.mono fun j hj => by simpa using hj) ζ
  have h2 : ((Multiset.filter (· = ζ) Z).card : ℂ) = 0 := by simpa only [Finset.univ_unique, Finset.sum_singleton, one_mul] using h1
  have h3 : (Multiset.filter (· = ζ) Z).card = 0 := by exact_mod_cast h2
  have h4 : 0 < (Multiset.filter (· = ζ) Z).card :=
    Multiset.card_pos_iff_exists_mem.2 ⟨ζ, Multiset.mem_filter.2 ⟨hζ, rfl⟩⟩
  exact h4.ne' h3
