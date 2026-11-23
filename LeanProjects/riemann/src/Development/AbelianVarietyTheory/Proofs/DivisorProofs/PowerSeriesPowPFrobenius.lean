import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionFiniteFlat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UPel.HT.PrimTors

theorem exists_finite_flat_wPow : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)), w0.IsMaximal → (p : 𝓞 D.F) ∈ w0 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (r : ℕ), ∃ r' : ℕ, r ≤ r' ∧ ∃ (H : Over S) (i : H ⟶ o.A), IsFinite H.hom ∧ Flat H.hom ∧ (∀ c ∈ w0 ^ r', i ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) ∧ ∀ (T : Over S) (x : T ⟶ o.A), (∀ c ∈ w0 ^ r', x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1) → ∃! y : T ⟶ H, y ≫ i = x := by
  intro p _ D R _ b N w0 _ hp S _ s o r
  have hw0 : w0 ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hp
    exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) hp
  have hwr : w0 ^ r ≠ ⊥ := by
    rw [Ne, ← Ideal.zero_eq_bot] at *
    exact pow_ne_zero r hw0
  obtain ⟨K, _, i, -, _, hfin, hflat, hK⟩ :=
    GlobalTheory.IwLevel.HTTorsionFF.exists_torsion_finite_flat p D R b N (w0 ^ r) S s o hwr
  have key : ∀ (T : Over S) (x : T ⟶ o.A),
      GlobalTheory.IwLevel.KilledBy (GlobalTheory.IwLevel.htAct o) ((w0 ^ r).map (algebraMap (𝓞 D.F) D.O)) x ↔
        ∀ c ∈ w0 ^ r, x ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
    intro T x
    unfold Ideal.map
    rw [GlobalTheory.IwLevel.killedBy_span]
    constructor
    · intro h c hc
      exact h _ ⟨c, hc, rfl⟩
    · rintro h _ ⟨c, hc, rfl⟩
      exact h c hc
  refine ⟨r, le_rfl, K, i, hfin, hflat, (key _ i).1 ((hK _ i).1 ⟨𝟙 _, Category.id_comp _⟩), fun T x hx => ?_⟩
  obtain ⟨y, hy⟩ := (hK T x).2 ((key T x).2 hx)
  exact ⟨y, hy, fun y' hy' => (cancel_mono i).1 (hy'.trans hy.symm)⟩

end GlobalTheory.UPel.HT.PrimTors
