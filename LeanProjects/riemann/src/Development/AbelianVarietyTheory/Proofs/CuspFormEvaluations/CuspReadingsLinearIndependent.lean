import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupNormFromNet
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ReadingLinearIndependentAndInjective

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory

theorem cusp_readings_linearIndependent : ReciprocityTheory.ChartRestriction.G.PullbackSections.AlgInjAtSt := by
  unfold ReciprocityTheory.ChartRestriction.G.PullbackSections.AlgInjAtSt
  intro D T h j hj ka σ hσ m f hf
  have hlin := hf.map' (T.C j ka).subtype (T.C j ka).ker_subtype
  have hmem : ∀ i, (f i : T.R j) ∈ sec (T.Q.Xo j) T.Q.c (wtA ka) ka.n := fun i =>
    Formalism.L2.Pj.cusp_le_sec (T.Q.Xo j) T.Q.c (T.U j) (wtA ka) ka.n (f i).2
  have hU := h.unf j hj σ hσ
  have hB : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt := GlobalTheory.lawsFieldsSeparately.2.1
  have key := (GlobalTheory.reading_linearIndependent_and_injective hB _ _ _ _ (T.Q.Xo j) T.Q.c σ _
    (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) ((Formalism.L2.PjFree.isUnf_ofPj (T.U j σ)).2 hU)
    (wtA ka) ka.n).1 m (fun i => (f i : T.R j)) hmem hlin
  simp only [Formalism.L2.PjFree.rdU_ofPj] at key
  exact key

end GlobalTheory
