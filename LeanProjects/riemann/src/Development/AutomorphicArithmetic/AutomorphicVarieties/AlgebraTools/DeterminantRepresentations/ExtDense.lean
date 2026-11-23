import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DGext

open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.extDense :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] [TopologicalSpace A] [T2Space A] [TopologicalSpace G] (D D' : GDet n A G) (S : Set G), Dense S →
    (∀ i ≤ n, Continuous fun g : G => D.lam i (MonoidAlgebra.single g 1)) →
    (∀ i ≤ n, Continuous fun g : G => D'.lam i (MonoidAlgebra.single g 1)) →
    (∀ g ∈ S, D.chi (MonoidAlgebra.single g 1) = D'.chi (MonoidAlgebra.single g 1)) → D = D' := by
  intro n A G _ _ _ _ _ D D' S hS hc hc' hchi
  apply UpperTheory.V.CA.d_gext
  intro g i _ hi
  have h := Continuous.ext_on hS (hc i hi) (hc' i hi) (fun x hx => by
    show (-1) ^ i * (D.chi _).coeff (n - i) = (-1) ^ i * (D'.chi _).coeff (n - i)
    rw [hchi x hx])
  exact congrFun h g
