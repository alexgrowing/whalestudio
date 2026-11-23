import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlowProjSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.TorRef

theorem blowup_finite_noeth_sep (K : Type) [Field K] [NumberField K] (X X' N : Scheme.{0}) (s : X ⟶ Sp (𝓞 K))
    (J : X.IdealSheafData) (b : X' ⟶ X) (ν : N ⟶ X') :
    IsProjOver s → FinalTheorems.Blowup b J → IsFinite ν → IsLocallyNoetherian N ∧ IsSeparated (ν ≫ b ≫ s) := by
  intro hs hb hν
  obtain ⟨X'', π, hπ, M, i, hi, hpi⟩ := blowProjSt (𝓞 K) X s J hs
  obtain ⟨h, hh, -⟩ := hπ.2 X' b hb.1
  obtain ⟨k, hk, -⟩ := hb.2 X'' π hπ.1
  have e1 : h ≫ k = 𝟙 _ := by
    obtain ⟨u, -, hu⟩ := hb.2 X' b hb.1
    rw [hu (h ≫ k) (by simp [hk, hh]), hu (𝟙 _) (by simp)]
  have e2 : k ≫ h = 𝟙 _ := by
    obtain ⟨u, -, hu⟩ := hπ.2 X'' π hπ.1
    rw [hu (k ≫ h) (by simp [hk, hh]), hu (𝟙 _) (by simp)]
  have : IsIso h := ⟨⟨k, e1, e2⟩⟩
  have hbs : b ≫ s = h ≫ i ≫ PSpace.str (𝓞 K) M := by rw [hpi, ← Category.assoc, hh]
  have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str (𝓞 K) M
  rw [hbs]
  exact ⟨LocallyOfFiniteType.isLocallyNoetherian (ν ≫ h ≫ i ≫ PSpace.str (𝓞 K) M), inferInstance⟩

end GlobalTheory.TorRef
