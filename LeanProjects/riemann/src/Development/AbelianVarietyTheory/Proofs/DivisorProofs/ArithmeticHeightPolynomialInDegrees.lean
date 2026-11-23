import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapSumSwap
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleSectionsAvoidClosedPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeModLProjective
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open GlobalTheory.Cartier GlobalTheory.CovTest.SwapLine
open scoped Classical

namespace GlobalTheory.VertFun

noncomputable def iterD {ι : Type} : (m : ℕ) → (Fin m → ι) → (MvPolynomial ι ℝ →ₗ[ℝ] MvPolynomial ι ℝ)
  | 0, _ => LinearMap.id
  | m + 1, a => (MvPolynomial.pderiv (a 0)).toLinearMap ∘ₗ iterD m (Fin.tail a)

theorem pderiv_lin {ι : Type} [Fintype ι] (x : ι → ℝ) (j : ι) :
    MvPolynomial.pderiv j (lin x) = MvPolynomial.C (x j) := by
  rw [lin, map_sum, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [MvPolynomial.pderiv_X, Pi.single_apply, hb, hb.symm]
  · simp

theorem iterD_lin_pow {ι : Type} [Fintype ι] (x : ι → ℝ) (N : ℕ) : ∀ (m : ℕ) (a : Fin m → ι),
    iterD m a (lin x ^ N) = MvPolynomial.C ((N.descFactorial m : ℝ) * ∏ j, x (a j)) * lin x ^ (N - m)
  | 0, a => by simp [iterD]
  | m + 1, a => by
    rw [iterD, LinearMap.comp_apply, iterD_lin_pow x N m, Derivation.coeFn_coe, MvPolynomial.pderiv_C_mul,
      MvPolynomial.pderiv_pow, pderiv_lin, Nat.descFactorial_succ, Fin.prod_univ_succ, Nat.sub_sub]
    simp only [Fin.tail, Nat.cast_mul, map_mul, map_natCast]
    ring

theorem exists_functional {ι : Type} [Fintype ι] (e : ℕ) (I : (Fin e → ι) → ℝ) :
    ∃ T : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, ∀ x : ι → ℝ, T (lin x ^ e) = ∑ a : Fin e → ι, (∏ j, x (a j)) * I a := by
  refine ⟨∑ a : Fin e → ι, (I a / (e.factorial : ℝ)) • (MvPolynomial.lcoeff ℝ 0 ∘ₗ iterD e a), fun x => ?_⟩
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  have he : (e.factorial : ℝ) ≠ 0 := by exact_mod_cast e.factorial_ne_zero
  rw [LinearMap.smul_apply, LinearMap.comp_apply, iterD_lin_pow, Nat.sub_self, pow_zero, mul_one,
    MvPolynomial.lcoeff_apply, MvPolynomial.coeff_zero_C, Nat.descFactorial_self, smul_eq_mul]
  field_simp

theorem topSelf_comb_pull {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} {κ : Type} [Field κ]
    {Z : Scheme.{0}} [Algebra κ Γ(Z, ⊤)] (hp : IsProjOver (strHom κ Z)) (hd : topologicalKrullDim Z = D) (i : Z ⟶ X)
    {ι : Type} [Fintype ι] (N : ι → HermLB p) (n : ι → ℤ) :
    (topSelfIntersection κ ((comb N n).B.pull i) D : ℝ) =
      ∑ a : Fin D → ι, (∏ j, (n (a j) : ℝ)) * (interNum κ (structureModule Z) (fun j => (N (a j)).B.pull i) : ℝ) := by
  have HD := diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom κ Z) (structureModule Z) hp (d := D)
    (by rw [QCoh.suppDim_structureModule, hd])
  have hL : ∀ j, ((N j).B.pull i).IsLB := fun j => LB.isLB_pull (N j).isLB i
  have e := HD.interNum_of_cls_eq_sum (L := fun j => (N j).B.pull i) hL (Q := fun _ => (comb N n).B.pull i)
    (fun _ => LB.isLB_pull (comb N n).isLB i) (fun _ => n) fun _ => by
      rw [CechPic.cls_pull (comb N n).isLB, GenFibreSecs.cls_comb, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_zsmul, CechPic.cls_pull (N j).isLB]
  rw [topSelf_def, e]
  push_cast
  rfl

theorem exists_vertical_functional : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (D : ℕ), IsArithVar p D →
    ∀ (Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] [IsIntegral Z] (ℓ : ℕ) [Fact ℓ.Prime]
    [Algebra (ZMod ℓ) Γ(Z, ⊤)] (e : ℕ), topologicalKrullDim Z = e → ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p),
    ∃ T : MvPolynomial ι ℝ →ₗ[ℝ] ℝ, ∀ (n : ι → ℤ) (g : Y → ℝ), (comb L n).IsArithHeight g →
      g (i (genericPoint Z)) = T (lin (fun j => (n j : ℝ)) ^ e) := by
  intro k _ Y p D hY Z i _ _ ℓ _ _ e he ι _ L
  have hp := GlobalTheory.VertProj.isProjOver_strHom_zmod k Y p D hY Z i ℓ
  obtain ⟨T, hT⟩ := exists_functional e fun a : Fin e → ι =>
    (interNum (ZMod ℓ) (structureModule Z) (fun j => (L (a j)).B.pull i) : ℝ) * Real.log ℓ
  refine ⟨T, fun n g hg => ?_⟩
  rw [hg.vertical Z i (ZMod ℓ) e he, Nat.card_zmod, topSelf_comb_pull hp he i L n, hT, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => mul_assoc _ _ _

end GlobalTheory.VertFun
