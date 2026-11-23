import Development.EtaleCohomology.EtaleSheaves.LChartPf
import Mathlib

noncomputable section

namespace LateralTheory.E.LSurjChartPf

theorem zmt_etale_at (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
    (q : Ideal A') [q.IsPrime] :
    ∃ S' : Subalgebra A A', S'.toSubmodule.FG ∧ ∃ r : S',
      r.1 ∉ q ∧ Function.Bijective (Localization.awayMap S'.val.toRingHom r) :=
  (Algebra.ZariskisMainProperty.of_finiteType q).exists_fg_and_exists_notMem_and_awayMap_bijective _

def GraphPatch : Prop :=
  ∀ (A : Type) [CommRing A] (I : Ideal A) (A' : Type) [CommRing A'] [Algebra A A']
    (φ : A' →ₐ[A] A ⧸ I),
    (∀ q : Ideal A', q.IsPrime → RingHom.ker φ ≤ q → ∃ S' : Subalgebra A A', S'.toSubmodule.FG ∧
      ∃ r : S', r.1 ∉ q ∧ Function.Bijective (Localization.awayMap S'.val.toRingHom r)) →
    ∃ (S : Subalgebra A A') (_ : S.toSubmodule.FG) (r : S),
      IsUnit (φ r.1) ∧ Function.Bijective (Localization.awayMap S.val.toRingHom r)

def FiniteGraphChart : Prop :=
  ∀ (A : Type) [CommRing A] (I : Ideal A) (A' : Type) [CommRing A'] [Algebra A A'] [Algebra.Etale A A']
    (φ : A' →ₐ[A] A ⧸ I), ∃ (S : Subalgebra A A') (_ : S.toSubmodule.FG) (r : S),
      IsUnit (φ r.1) ∧ Function.Bijective (Localization.awayMap S.val.toRingHom r)

def FiniteChartSurj : Prop :=
  ∀ (A : Type) [CommRing A] (I : Ideal A), I ≤ Ideal.jacobson ⊥ → LateralTheory.E.LChartPf.IdemLiftInt A I →
  ∀ (A' : Type) [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (φ : A' →ₐ[A] A ⧸ I)
    (S : Subalgebra A A') (_ : S.toSubmodule.FG) (r : S),
    IsUnit (φ r.1) → Function.Bijective (Localization.awayMap S.val.toRingHom r) →
    ∃ g : A', IsUnit (φ g) ∧ Function.Surjective (algebraMap A (Localization.Away g))

theorem FiniteGraphChart_of (hP : GraphPatch) : FiniteGraphChart := by
  intro A _ I A' _ _ _ φ
  exact hP A I A' φ (fun q hq _ => zmt_etale_at A A' q)

theorem LSurjChart_of' (hA : FiniteGraphChart) (hB : FiniteChartSurj) :
    LateralTheory.E.LChartPf.LSurjChart := by
  intro A _ I hI hid A' _ _ _ φ
  obtain ⟨S, hS, r, hr, hb⟩ := hA A I A' φ
  exact hB A I hI hid A' φ S hS r hr hb

theorem LSurjChart_of (hP : GraphPatch) (hB : FiniteChartSurj) : LateralTheory.E.LChartPf.LSurjChart :=
  LSurjChart_of' (FiniteGraphChart_of hP) hB

end LateralTheory.E.LSurjChartPf
