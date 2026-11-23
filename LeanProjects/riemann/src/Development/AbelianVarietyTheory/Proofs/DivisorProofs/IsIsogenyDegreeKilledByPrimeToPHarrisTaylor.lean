import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KilledByIdealFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyDegreeOfPointCount
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorCardKilledByIdealEqAbsNormPowStatement

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IwLevel.PrimeToP

theorem isIsogDeg_killedBy : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : GlobalTheory.UPel.HT.Obj b N s), (∀ c : 𝓞 D.F, c ≠ 0 → GlobalTheory.IwLevel.IsIsogDeg (o.act.act (algebraMap (𝓞 D.F) D.O c)) ((Algebra.norm ℤ c).natAbs ^ (D.m * D.n))) → ∀ (𝔟 : Ideal (𝓞 D.F)), 𝔟 ⊔ Ideal.span {(p : 𝓞 D.F)} = ⊤ → ∀ (K : Over S) (i : K ⟶ o.A), Mono i → (∀ (T : Over S) (x : T ⟶ o.A), GlobalTheory.IwLevel.InSub i x ↔ GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) (𝔟.map (algebraMap (𝓞 D.F) D.O)) x) → GlobalTheory.IwLevel.IsIsogDeg (toUnit K) (Ideal.absNorm 𝔟 ^ (D.m * D.n)) := by
  intro p _ D R _ b N S s o _hdeg 𝔟 h𝔟 K i hi hK
  obtain ⟨K', i', hi', hfin, het, hK'⟩ := GlobalTheory.T.killed_by_ideal_finite_etale p D R b N S s o 𝔟 h𝔟
  have hne : 𝔟 ≠ ⊥ := by
    rintro rfl
    rw [bot_sup_eq] at h𝔟
    have h1 := congrArg Ideal.absNorm h𝔟
    rw [Ideal.absNorm_span_singleton, Ideal.absNorm_top] at h1
    have h2 : Algebra.norm ℤ ((p : ℤ) : 𝓞 D.F) = (p : ℤ) ^ Module.finrank ℤ (𝓞 D.F) := by
      rw [← Algebra.norm_algebraMap]; rfl
    rw [Int.cast_natCast] at h2
    rw [h2, Int.natAbs_pow, Int.natAbs_natCast] at h1
    have hp := (Fact.out : p.Prime).one_lt
    have hr : 0 < Module.finrank ℤ (𝓞 D.F) := Module.finrank_pos
    have := Nat.one_lt_pow hr.ne' hp
    omega
  have hd : 1 ≤ Ideal.absNorm 𝔟 ^ (D.m * D.n) :=
    Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (fun h => hne (Ideal.absNorm_eq_zero_iff.1 h)))
  obtain ⟨u, hu⟩ : GlobalTheory.IwLevel.InSub i' i := (hK' K i).2 ((hK K i).1 ⟨𝟙 _, Category.id_comp _⟩)
  obtain ⟨v, hv⟩ : GlobalTheory.IwLevel.InSub i i' := (hK K' i').2 ((hK' K' i').1 ⟨𝟙 _, Category.id_comp _⟩)
  have : IsIso u := ⟨⟨v, by rw [← cancel_mono i, Category.assoc, hv, hu, Category.id_comp],
    by rw [← cancel_mono i', Category.assoc, hu, hv, Category.id_comp]⟩⟩
  have h3 := GlobalTheory.T.isogeny_degree_of_point_count o.A K' i' hi' hfin het _ hd fun k _ _ t => by
    rw [← GlobalTheory.T.harrisTaylor_card_killed_by_ideal_eq_absNorm_pow p D R b N S s o 𝔟 h𝔟 k t]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun y => hK' _ y)
  have h4 := (GlobalTheory.IwLevel.IsIsogDeg.of_isIso u).comp h3
  rwa [_root_.one_mul, toUnit_unique (u ≫ toUnit K') (toUnit K)] at h4

end GlobalTheory.IwLevel.PrimeToP
