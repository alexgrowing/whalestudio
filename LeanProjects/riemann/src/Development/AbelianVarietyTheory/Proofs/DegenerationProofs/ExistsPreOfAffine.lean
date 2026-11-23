import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsFractionRingR
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH.PreInh
variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem perp_top (S : ThetaSys o Ω) : S.perp ⊤ = ⊥ := by
  refine (AddSubgroup.eq_bot_iff_forall _).2 fun a ha => ?_
  have ha' : ∀ h : S.Gam, eStd S.g _ a h = 0 := fun h => ha h trivial
  funext k
  rcases k with i | i
  · have := ha' (Pi.single (Sum.inr i) 1)
    simpa [eStd, Pi.single_apply] using this
  · have := ha' (Pi.single (Sum.inl i) 1)
    simpa [eStd, Pi.single_apply] using this

theorem TT_ofAffine (S : ThetaSys o Ω) [Algebra.FiniteType o S.R] [IsFractionRing S.R Ω]
    (hu : ∀ x, S.th x ≠ 0 → (S.th x)⁻¹ ∈ S.R) (z : (RatModel.ofAffine o Ω S.R).Z) :
    S.TT (RatModel.ofAffine o Ω S.R) z = ⊥ := by
  have h : S.supI (RatModel.ofAffine o Ω S.R) z = {x | S.th x ≠ 0} := by
    refine Set.ext fun x => ⟨fun hx => hx.1, fun hx => ⟨hx, fun j => ?_⟩⟩
    refine (RatModel.mem_O_ofAffine (A := S.R) (z := z)).2
      ⟨⟨S.th j * (S.th x)⁻¹, S.R.mul_mem (S.th_mem j) (hu x hx)⟩, 1,
        (Ideal.ne_top_iff_one _).1 (PrimeSpectrum.isPrime z).ne_top, ?_⟩
    rw [map_one, div_one, div_eq_mul_inv]
    rfl
  unfold ThetaSys.TT ThetaSys.HH
  rw [h, S.supp, perp_top]

theorem exists_pre_ofAffine :
    Laws → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) [Algebra.FiniteType o S.R] [IsFractionRing S.R Ω], ∃ Q : ZHPre ρ (RatModel.ofAffine o Ω S.R) ⊤, Q.G = ρ.P.A ∧ Q.Sec ∧ ((∀ x, S.th x ≠ 0 → (S.th x)⁻¹ ∈ S.R) → Q.Ab) := by
  intro hL o Ω _ _ _ hB S ρ _ _
  have : Algebra.FiniteType ℤ o := hB.ft
  have : IsNoetherianRing o := Algebra.FiniteType.isNoetherianRing ℤ o
  have : IsNoetherianRing S.R := Algebra.FiniteType.isNoetherianRing o S.R
  obtain ⟨c⟩ := (hL.cube (Sp S.R) ρ.P ⟨ρ.P.L, ρ.rig, ρ.P.isLB, ρ.rig_gen⟩ rfl).1
  obtain ⟨h1, h2, h3⟩ := PreModel.pre_sec ρ c
  refine ⟨PreModel.pre ρ c, rfl, h1, fun hu => ⟨h2.trans ?_, fun W _ => h3 W⟩⟩
  exact (Set.eq_univ_of_forall fun z => TT_ofAffine S hu z).symm

end GlobalTheory.ZH.PreInh
end
