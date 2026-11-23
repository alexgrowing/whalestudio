import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardAbelianVarietyTorsionSepClosed
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

theorem two_mul_relDim_eq_finrank : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (K : Type) [Field K] (β : R →+* K) (o : Obj b N (spMap β)) (g : ℕ), SmoothOfRelativeDimension g o.A.hom → 2 * g = Module.finrank ℤ D.La := by
  intro p _ D R _ b N K _ β o g hg
  haveI := D.freeLa
  haveI := D.finLa
  obtain ⟨ℓ, hℓp, hℓ⟩ := Nat.exists_infinite_primes (p + 1)
  have hcop : ℓ.Coprime p := (Nat.coprime_primes hℓ (Fact.out)).2 (by omega)
  have hℓ0 : 0 < ℓ := hℓ.pos
  have hℓK : (ℓ : K) ≠ 0 := by
    have h := (b.unit ℓ hcop).map β
    rw [map_natCast] at h
    exact h.ne_zero
  have hx : spMap (algebraMap K (AlgebraicClosure K)) ≫ spMap β =
      spMap ((algebraMap K (AlgebraicClosure K)).comp β) := by
    simp only [spMap, ← Spec.map_comp]
    rfl
  obtain ⟨I, -⟩ := o.geom (AlgebraicClosure K) (spMap (algebraMap K (AlgebraicClosure K)))
    ((algebraMap K (AlgebraicClosure K)).comp β) hx
  have hc := GlobalTheory.SepClosedTorsion.card_torsion_sepClosed K (AlgebraicClosure K) o.A o.ab g hg ℓ hℓK
  let f : D.La →+ Additive (Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ o.A) :=
    AddMonoidHom.mk' (fun a => Additive.ofMul (I.ev ℓ a)) fun a b => congrArg Additive.ofMul (I.add ℓ a b)
  have hk : f.ker = (nsmulAddMonoidHom ℓ : D.La →+ D.La).range := by
    ext a
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
    exact (I.ker ℓ hℓ0 hcop a).trans ⟨fun ⟨b, h⟩ => ⟨b, h.symm⟩, fun ⟨b, h⟩ => ⟨b, h.symm⟩⟩
  have h2 : Nat.card {x : ptOver K (AlgebraicClosure K) ⟶ o.A // x ^ ℓ = 1} = ℓ ^ Module.finrank ℤ D.La := by
    rw [← AddSubgroup.index_range_nsmul, ← hk, AddSubgroup.index_ker]
    exact Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul fun u => I.onto ℓ hℓ0 hcop u)
  rw [hc] at h2
  exact Nat.pow_right_injective hℓ.two_le h2

end GlobalTheory.UPel.HT
