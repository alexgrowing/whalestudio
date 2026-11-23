import Mathlib
import Formalism.LocalToGlobal.Columns.RecLevelTop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralDefiniteQuotientEqClassSum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
open GlobalTheory.Mem.Col2.AdT
open Filter Topology

namespace GlobalTheory.TwU.NearOne

theorem congAt_eventually_nhds_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n N : ℕ) (P : HeightOneSpectrum (𝓞 E)), letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F); ∀ᶠ u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) in nhds 1, GlobalTheory.TwU.CongAt P N u := by
  intro F E _ _ _ _ _ n N P
  letI : TopologicalSpace (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := Formalism.L2.Col.rlt_top (F := F) (E := E)
  haveI : IsTopologicalRing (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := Formalism.L2.Col.rlt_topRing (F := F) (E := E)
  show ∀ᶠ u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) in nhds 1, ∀ a b, _
  refine Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b => ?_
  have hop : IsOpen ((fun y : E ⊗[F] FiniteAdeleRing (𝓞 F) F =>
      Formalism.L2.Col.iA F E (((Formalism.L2.Col.qOf P : ℕ) : E) ^ N)⁻¹ * y) ⁻¹'
      (Formalism.L2.Herm.intAf F E : Set (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) :=
    Formalism.L2.Col.rlt_isOpen_intAf.preimage (continuous_const.mul continuous_id)
  have h0 : (0 : E ⊗[F] FiniteAdeleRing (𝓞 F) F) ∈ (fun y : E ⊗[F] FiniteAdeleRing (𝓞 F) F =>
      Formalism.L2.Col.iA F E (((Formalism.L2.Col.qOf P : ℕ) : E) ^ N)⁻¹ * y) ⁻¹'
      (Formalism.L2.Herm.intAf F E : Set (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := by
    simp only [Set.mem_preimage, mul_zero]
    exact zero_mem _
  have hcont : Continuous fun u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) =>
      (u : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b -
        (1 : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b :=
    (Units.continuous_val.matrix_elem a b).sub continuous_const
  have ht := hcont.tendsto' 1 0 (by simp)
  filter_upwards [ht (hop.mem_nhds h0)] with u hu
  refine ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), ?_⟩
  simpa [Matrix.sub_apply] using hu

end GlobalTheory.TwU.NearOne
