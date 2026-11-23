import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DFactor
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DChKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DPull
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

theorem UpperTheory.V.Th.Coc.chQuot :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E), ∃ (E' : Type) (_ : Ring E') (_ : Algebra A E') (π : E →ₐ[A] E') (D' : Det n A E'), Function.Surjective π ∧ D'.pull π = D ∧ D'.IsCH ∧ ∀ y, π y = 0 → y ∈ D.ker := by
  intro n A E _ _ _ D
  let π : E →ₐ[A] D.CH.ringCon.Quotient := RingCon.mkₐ A D.CH.ringCon
  have hmem : ∀ x, π x = 0 ↔ x ∈ D.CH := fun x => by
    rw [← map_zero π]
    exact (RingCon.eq _)
  have hsurj : Function.Surjective π := fun q => Quotient.exists_rep q
  have hk : ∀ y, π y = 0 → y ∈ D.ker := fun y hy => UpperTheory.V.CA.d_ch_ker D ((hmem y).1 hy)
  obtain ⟨D', hD', -⟩ := UpperTheory.V.CA.d_factor D π hsurj hk
  refine ⟨_, _, _, π, D', hsurj, hD', ?_, hk⟩
  refine eq_bot_iff.2 fun y hy => ?_
  obtain ⟨x, hx, rfl⟩ := ((UpperTheory.V.CA.d_pull D' π).2.2.2 hsurj).2 y hy
  rw [hD'] at hx
  rw [TwoSidedIdeal.mem_bot, hmem]
  exact hx
