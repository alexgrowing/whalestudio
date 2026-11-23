import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkIdComapOfAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasiRegularSeqOfIsFreeGen
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.PrincStalk

theorem stalkId_comap_pow_isPrincipal : ∀ {Y V : Scheme.{0}} (D : EffCartierData Y) (n : ℕ) (g : V ⟶ Y) (v : V),
    (FinalTheorems.stalkId ((D.idealSheaf ^ n).comap g) v).IsPrincipal := by
  intro Y V D n g v
  obtain ⟨i, hi⟩ := D.exists_mem (g v)
  rw [GlobalTheory.VanStalk.stalkId_comap, GlobalTheory.Vanishing.stalkId_pow, D.stalkId_idealSheaf i _ hi,
    Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton]
  exact ⟨_, rfl⟩

end GlobalTheory.PrincStalk
