import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsLocallyNoetherian
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTorsionSectionsOfRoot

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem eq_one_iff_isUnit_of_isIdempotentElem {R : Type} [CommRing R] {u : R} (hu : IsIdempotentElem u) :
    u = 1 ↔ IsUnit u := by
  constructor
  · rintro rfl
    exact isUnit_one
  · intro h
    exact h.mul_left_cancel (by rw [hu.eq, _root_.mul_one])

private theorem isUnit_iff_forall_primeSpectrum_notMem {R : Type} [CommRing R] (x : R) :
    IsUnit x ↔ ∀ q : PrimeSpectrum R, x ∉ q.asIdeal := by
  constructor
  · intro h q hq
    exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hq h)
  · intro h
    by_contra hx
    obtain ⟨I, hI, hxI⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hx)
    exact h ⟨I, hI.isPrime⟩ hxI

theorem exists_isIdempotentElem_range_spMap_subset {B : Type} [CommRing B] {U : Set (Sp B)} (hU : IsClopen U) :
    ∃ e : B, IsIdempotentElem e ∧ ∀ (T : Type) [CommRing T] (χ : B →+* T), χ e = 1 ↔ Set.range (spMap χ) ⊆ U := by
  let s : TopologicalSpace.Clopens (PrimeSpectrum B) := ⟨U, hU⟩
  have he : IsIdempotentElem (PrimeSpectrum.isIdempotentElemEquivClopens.symm s).1 :=
    (PrimeSpectrum.isIdempotentElemEquivClopens.symm s).2

  have hmem : ∀ p : PrimeSpectrum B,
      p ∈ U ↔ (PrimeSpectrum.isIdempotentElemEquivClopens.symm s).1 ∉ p.asIdeal := by
    intro p
    have h := congrArg (fun o : TopologicalSpace.Opens (PrimeSpectrum B) => p ∈ o)
      (PrimeSpectrum.basicOpen_isIdempotentElemEquivClopens_symm s)
    simp only [eq_iff_iff] at h
    rw [PrimeSpectrum.mem_basicOpen] at h
    exact h.symm
  refine ⟨_, he, fun T _ χ => ?_⟩
  rw [eq_one_iff_isUnit_of_isIdempotentElem (he.map χ), isUnit_iff_forall_primeSpectrum_notMem]
  constructor
  · rintro h _ ⟨q, rfl⟩
    exact (hmem _).2 (h q)
  · intro h q
    exact (hmem _).1 (h ⟨q, rfl⟩)

theorem exists_isIdempotentElem_torsion_eq :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (B : Type) [CommRing B] (x0 : Sp B ⟶ Xo.X) (k : ℕ), 0 < k → ∀ (a b : ptO Xo x0 ⟶ Xo.univ.t.G), a ^ k = 1 → b ^ k = 1 → ∃ e : B, IsIdempotentElem e ∧ ∀ (T : Type) [CommRing T] (χ : B →+* T), χ e = 1 ↔ spMap χ ≫ a.left = spMap χ ≫ b.left := by
  intro _ E _ _ _ H Dw l Xo B _ x0 k hk a b ha hb
  obtain ⟨-, -, hunit, hab, -⟩ := moduli_univ_polAV E H Dw l Xo
  obtain ⟨Z, et, hZf, hZe, hadd, hpow, huniv⟩ :=
    exists_finiteEtale_latticeTorsionHom Xo.X Xo.univ.t.G k ℤ hab (hunit k hk)
  have R : LevCover.RepTors Xo.univ.t.G k ℤ Z et := ⟨hZf, hZe, hadd, hpow, huniv⟩

  have hz : ∀ c : ptO Xo x0 ⟶ Xo.univ.t.G, c ^ k = 1 → ∀ m : ℤ, (c ^ m) ^ k = 1 := by
    intro c hc m
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hc, one_zpow]
  obtain ⟨U, hUc, hU⟩ := R.clopenCond (T := ptO Xo x0) (fun m => a ^ m) (fun m => b ^ m)
    (fun m c => zpow_add a m c) (hz a ha) (fun m c => zpow_add b m c) (hz b hb)
  let V : Set (Sp B) := (U : Set (ptO Xo x0).left)
  obtain ⟨e, he, hE⟩ := exists_isIdempotentElem_range_spMap_subset (B := B) (U := V) ⟨hUc, U.isOpen⟩
  refine ⟨e, he, fun T _ χ => ?_⟩
  rw [hE T χ]
  let h : Over.mk (spMap χ ≫ x0) ⟶ ptO Xo x0 := Over.homMk (spMap χ) rfl
  have hh : Set.range (spMap χ) ⊆ V ↔ Set.range h.left ⊆ U := Iff.rfl
  rw [hh, ← hU _ h]
  simp only [GrpObj.comp_zpow]
  constructor
  · intro hm
    have h1 : h ≫ a = h ≫ b := by simpa using hm 1
    simpa [h] using congrArg CommaMorphism.left h1
  · intro hl m
    have h1 : h ≫ a = h ≫ b := Over.OverMorphism.ext (by simpa [h] using hl)
    rw [h1]

end GlobalTheory
