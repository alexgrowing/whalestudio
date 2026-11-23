import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperH2SumOfCupsExactStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh.SpanCup

theorem sum_append {R M N P : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (B : M →ₗ[R] N →ₗ[R] P) {n m : ℕ} (a : Fin n → M) (b : Fin n → N)
    (a' : Fin m → M) (b' : Fin m → N) :
    ∑ k, B (a k) (b k) + ∑ k, B (a' k) (b' k) = ∑ k, B (Fin.append a a' k) (Fin.append b b' k) := by
  rw [Fin.sum_univ_add]; simp [Fin.append_left, Fin.append_right]

theorem exists_sum_ιMulti {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (w : ⋀[R]^2 M) :
    ∃ (n : ℕ) (x y : Fin n → M), w = ∑ k, exteriorPower.ιMulti R 2 ![x k, y k] := by
  have hw : w ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 2 (M := M))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hw using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨v, rfl⟩ := hv
    refine ⟨1, fun _ ↦ v 0, fun _ ↦ v 1, ?_⟩
    rw [Fin.sum_univ_one]
    congr 1
    ext i; fin_cases i <;> rfl
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨n, x, y, rfl⟩ := hu
    obtain ⟨m, x', y', rfl⟩ := hv
    refine ⟨n + m, Fin.append x x', Fin.append y y', ?_⟩
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]
  | smul r v _ hv =>
    obtain ⟨n, x, y, rfl⟩ := hv
    refine ⟨n, fun k ↦ r • x k, y, ?_⟩
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have e : (![r • x k, y k] : Fin 2 → M) = Function.update ![x k, y k] 0 (r • ![x k, y k] 0) := by
      ext i; fin_cases i <;> simp
    rw [e, AlternatingMap.map_update_smul, Function.update_eq_self]

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)

def fn2 : cechDeRhamTotalCocyclesTwo F →ₗ[R] Z2 F where
  toFun c := ⟨c.1.1, (mem_cechDeRhamTotalCocyclesTwo_iff.1 c.2).1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cechDeRhamFunctionPart_cup_eq_cup (a b : cechDeRhamTotalCocyclesOne F) : fn2 F (cupZZ F a b) = cupZ F (cechDeRhamTotalCocyclesOne.fn F a) (cechDeRhamTotalCocyclesOne.fn F b) := rfl

end GlobalTheory.AbCoh.SpanCup

open GlobalTheory.AbCoh.SpanCup in

theorem GlobalTheory.AbCoh.hyp2_eq_sum_cupHyp : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C]
    (F : C ⥤ CommAlgCat.{0} R), HasFrame F → CohomZeroIsConstants F → Closed1 F = ⊤ → Function.Surjective (toO F) →
    WedgeO F → ∀ z : Hyp2 F, ∃ (n : ℕ) (a b : Fin n → Hyp1 F), z = ∑ k, cupHyp F (a k) (b k) := by
  intro R _ C _ F hfr h0 hc hsurj hw z
  obtain ⟨c, rfl⟩ := Hyp2.mk_surjective F z
  obtain ⟨e, he⟩ := hw
  obtain ⟨n, x, y, hxy⟩ := exists_sum_ιMulti (e.symm (H2.mk F (fn2 F c)))
  have hrep : ∀ u : H1 F, ∃ p : cechDeRhamTotalCocyclesOne F, toO F (Hyp1.mk F p) = u := fun u ↦ by
    obtain ⟨q, hq⟩ := hsurj u
    obtain ⟨p, rfl⟩ := Hyp1.mk_surjective F q
    exact ⟨p, hq⟩
  choose p hp using hrep
  have hcls : H2.mk F (fn2 F c) = ∑ k, cup F (x k) (y k) := by
    have h := congrArg e hxy
    rw [LinearEquiv.apply_symm_apply] at h
    rw [h, map_sum]
    simp only [he]
  obtain ⟨c', hc'⟩ : ∃ c' : cechDeRhamTotalCocyclesTwo F, c' = c - ∑ k, cupZZ F (p (x k)) (p (y k)) := ⟨_, rfl⟩
  have hfn : ∃ f, d1 F f = c'.1.1 := by
    have h : H2.mk F (fn2 F c') = 0 := by
      rw [hc']
      simp only [map_sub, map_sum]
      rw [hcls, sub_eq_zero]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [cechDeRhamFunctionPart_cup_eq_cup, ← cup_mk, ← toO_mk, ← toO_mk, hp, hp]
    exact H2.mk_eq_zero.1 h
  obtain ⟨m, a, w, hm⟩ := GlobalTheory.T.hyper_h2_sum_of_cups_exact R C F hfr h0 hc hsurj c' hfn
  refine ⟨m + n, Fin.append a (fun k ↦ Hyp1.mk F (p (x k))),
    Fin.append (fun k ↦ clAll F hc (w k)) (fun k ↦ Hyp1.mk F (p (y k))), ?_⟩
  rw [← sum_append, ← hm, hc']
  simp only [map_sub, map_sum, cupHyp_mk, sub_add_cancel]
