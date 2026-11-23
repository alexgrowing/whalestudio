import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussPropertyCodimOneChartHeightOnePrimeStatement
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularSmooth
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem ringKrullDim_stalk_le_of_flat {X Y : Scheme.{0}} (f : X ⟶ Y) [Flat f] (z : X) :
    ringKrullDim (Y.presheaf.stalk (f z)) ≤ ringKrullDim (X.presheaf.stalk z) := by
  letI : Algebra (Y.presheaf.stalk (f z)) (X.presheaf.stalk z) := (f.stalkMap z).hom.toAlgebra
  haveI : Module.Flat (Y.presheaf.stalk (f z)) (X.presheaf.stalk z) := Flat.stalkMap f z
  haveI : IsLocalHom (algebraMap (Y.presheaf.stalk (f z)) (X.presheaf.stalk z)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap z).hom)
  haveI : Algebra.HasGoingDown (Y.presheaf.stalk (f z)) (X.presheaf.stalk z) := Algebra.HasGoingDown.of_flat
  exact GroundTheory.Arith.SchemeCoh.ringKrullDim_le_of_hasGoingDown

theorem Setup.height_under_vert (σ : Setup) (x : Sp σ.R) (z : (σ.C x).G.left)
    (hz : Vert (σ.C x).G.hom (σ.ρ x σ.f) z) :
    (spMap (σ.ρ x) ((σ.C x).G.hom z)).asIdeal.height = 1 := by
  haveI := (σ.C x).semi.smooth
  haveI : Flat (spMap (σ.ρ x)) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact σ.flat x
  have h1 := (ringKrullDim_stalk_le_of_flat (spMap (σ.ρ x)) ((σ.C x).G.hom z)).trans
    (ringKrullDim_stalk_le_of_flat (σ.C x).G.hom z)
  rw [hz.1] at h1
  have hf : σ.f ∈ (spMap (σ.ρ x) ((σ.C x).G.hom z)).asIdeal := hz.2
  generalize spMap (σ.ρ x) ((σ.C x).G.hom z) = p at h1 hf ⊢
  letI : Algebra σ.R ((Sp σ.R).presheaf.stalk p) := StructureSheaf.stalkAlgebra σ.R p
  haveI : p.asIdeal.IsPrime := PrimeSpectrum.isPrime (R := σ.R) p
  haveI : IsLocalization.AtPrime ((Sp σ.R).presheaf.stalk p) p.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk σ.R p
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal] at h1
  refine le_antisymm (by exact_mod_cast h1) ?_
  have hlt : (⊥ : Ideal σ.R) < p.asIdeal := bot_lt_iff_ne_bot.2 fun h => σ.hf (by rwa [h, Ideal.mem_bot] at hf)
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  exact le_add_self.trans h2

theorem Setup.forall_mem_W_iff : ∀ (σ : Setup) (u : σ.A.left.functionField),
    (∀ x : Sp σ.R, u ∈ σ.W x) ↔ ∀ p : Sp σ.R, p.asIdeal.height = 1 → σ.f ∈ p.asIdeal → u ∈ σ.W p := by
  intro σ u
  refine ⟨fun h p _ _ => h p, fun h x z hz => ?_⟩
  have h1 := h _ (σ.height_under_vert x z hz) hz.2
  rw [← (GlobalTheory.T.gaussProperty_codimOne_chart_heightOnePrime σ x z hz).2] at h1
  exact h1

end GlobalTheory.Desc
