import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrossNormallyAtOfForallMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NadelVanishingCanonicalAddBoundary
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Discrepancy GlobalTheory.Cartier GlobalTheory.QCoh
open GlobalTheory.TopForm

namespace GlobalTheory.Discrepancy.DivOver

theorem sum_ord_sub_one_le_formOrd_dOn : ∀ {k : Type} [Field k] [PerfectField k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    [LocallyOfFiniteType p] {n : ℕ}, topologicalKrullDim X = n → ∀ (E : DivOver p) {U : X.Opens} {y : X}
    (hy : y ∈ U), E.Through y → ∀ (z : Fin n → Γ(X, U)), formOf U (gen_mem hy) (dOn p z) ≠ 0 →
    ∀ {J : Type} [Fintype J] (e : J → Fin n), Function.Injective e → ∀ (u : J → X.functionFieldˣ),
    (∀ j, (u j : X.functionField) = fnOf U (gen_mem hy) (z (e j))) →
    ∑ j, E.ord (u j) - 1 ≤ E.formOrd (formOf U (gen_mem hy) (dOn p z)) := by
  intro k _ _ X _ p _ n hn E U y hy hE z hz0 J _ e he u hu
  classical
  letI := (Cartier.constFn p).toAlgebra
  letI := E.const.toAlgebra
  haveI : IsScalarTower k E.ring X.functionField := IsScalarTower.of_algebraMap_eq' rfl
  let x : Fin n → X.functionField := fun i => fnOf U (gen_mem hy) (z i)
  have hxV : ∀ i, x i ∈ E.ring := fun i => hE _ (regAt_fnOf hy _ (z i))
  have hη : formOf U (gen_mem hy) (dOn p z) = dWedge k x := by
    change TopForm.formMap n _ _ (dForm _ z) = _
    rw [formMap_dForm]
    rfl
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible E.ring
  have ht0 : algebraMap E.ring X.functionField t ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective E.ring X.functionField)).mpr ht.ne_zero
  let S : Finset (Fin n) := Finset.univ.map ⟨e, he⟩
  have hxe : ∀ j, x (e j) = (u j : X.functionField) := fun j => (hu j).symm
  have hxS : ∀ i ∈ S, x i ≠ 0 := by
    intro i hi
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.1 hi
    change x (e j) ≠ 0
    rw [hxe j]
    exact (u j).ne_zero
  obtain ⟨γ, hγ⟩ := GlobalTheory.smul_dlogWedge_mem_regForms k t ht0 S x
    (fun i hi => exists_eq_unit_mul_zpow ht (hxS i hi)) (fun i _ => ⟨⟨x i, hxV i⟩, rfl⟩)
  obtain ⟨ω, hω⟩ := E.exists_isFreeGen hn
  obtain ⟨a, rfl⟩ := hω.2 γ
  have hbr : ∀ θ, GlobalTheory.formMap k E.ring X.functionField n θ = E.toRat n θ := fun _ => rfl
  have hP : (∏ i ∈ S, x i) = ∏ j, (u j : X.functionField) := by
    rw [Finset.prod_map]
    exact Finset.prod_congr rfl fun j _ => hxe j
  have hPne : (∏ i ∈ S, x i) ≠ 0 := Finset.prod_ne_zero_iff.2 hxS
  have h2 : dWedge k x = (∏ i ∈ S, x i) • dlogWedge k S x := by
    rw [GlobalTheory.dlogWedge_eq_smul, smul_smul, mul_inv_cancel₀ hPne, one_smul]
  have h3 : (algebraMap E.ring X.functionField t) • dlogWedge k S x =
      (algebraMap E.ring X.functionField a) • E.toRat n ω := by
    calc (algebraMap E.ring X.functionField t) • dlogWedge k S x = t • dlogWedge k S x :=
          algebraMap_smul _ t _
      _ = GlobalTheory.formMap k E.ring X.functionField n (a • ω) := hγ.symm
      _ = a • E.toRat n ω := by rw [map_smul, hbr]
      _ = (algebraMap E.ring X.functionField a) • E.toRat n ω := (algebraMap_smul _ a _).symm
  have key : formOf U (gen_mem hy) (dOn p z) =
      ((∏ i ∈ S, x i) * (algebraMap E.ring X.functionField t)⁻¹ *
        algebraMap E.ring X.functionField a) • E.toRat n ω := by
    rw [hη, h2, mul_assoc, mul_smul, mul_smul, ← h3, inv_smul_smul₀ ht0]
  have ha0 : algebraMap E.ring X.functionField a ≠ 0 := by
    intro h
    apply hz0
    rw [key, h, mul_zero, zero_smul]
  let f : X.functionFieldˣ := (∏ j, u j) * (Units.mk0 _ ht0)⁻¹ * Units.mk0 _ ha0
  have hf : formOf U (gen_mem hy) (dOn p z) = (f : X.functionField) • E.toRat n ω := by
    rw [key, hP]
    simp [f]
  have hsum : ∀ s : Finset J, E.ord (∏ j ∈ s, u j) = ∑ j ∈ s, E.ord (u j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, E.ord_mul, ih]
  have hordt : E.ord (Units.mk0 _ ht0) = 1 :=
    (congrArg WithZero.log (Ring.ordFrac_irreducible (K := X.functionField) ht)).trans
      (WithZero.log_exp 1)
  have horda : 0 ≤ E.ord (Units.mk0 _ ha0) := (E.ord_nonneg_iff _).2 a.2
  rw [IsFormOrd.formOrd_eq hz0 ⟨ω, hω, f, hf, rfl⟩]
  simp only [f, E.ord_mul, E.ord_inv, hsum, hordt]
  omega

end GlobalTheory.Discrepancy.DivOver
