import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AlgPointsLocal

theorem exists_pow_mul_of_locally_integral : ∀ (R K : Type) [CommRing R] [Field K] [Algebra R K] (A : Type) [CommRing A] [Algebra R A] [Finite (A →ₐ[R] K)] (r : A) (f : (A →ₐ[R] K) → K), (∀ (P : Ideal A) [P.IsPrime], r ∉ P → ∃ c : Localization.AtPrime P, ∀ ψ : Localization.AtPrime P →ₐ[R] K, ψ c = f (ψ.comp (IsScalarTower.toAlgHom R A (Localization.AtPrime P)))) → ∃ (k : ℕ) (a : A), ∀ ψ : A →ₐ[R] K, ψ a = ψ r ^ k * f ψ := by
  intro R K _ _ _ A _ _ _ r f h
  classical
  haveI := Fintype.ofFinite (A →ₐ[R] K)
  let J : Ideal A :=
    { carrier := {u | ∃ a : A, ∀ ψ : A →ₐ[R] K, ψ a = ψ u * f ψ}
      add_mem' := by
        rintro u v ⟨a, ha⟩ ⟨b, hb⟩
        exact ⟨a + b, fun ψ => by rw [map_add, map_add, ha, hb, add_mul]⟩
      zero_mem' := ⟨0, fun ψ => by simp⟩
      smul_mem' := by
        rintro c u ⟨a, ha⟩
        exact ⟨c * a, fun ψ => by rw [smul_eq_mul, map_mul, map_mul, ha, _root_.mul_assoc]⟩ }
  have memJ : ∀ u : A, u ∈ J ↔ ∃ a : A, ∀ ψ : A →ₐ[R] K, ψ a = ψ u * f ψ := fun u => Iff.rfl
  have key : ∀ (P : Ideal A), P.IsPrime → r ∉ P → ∃ u ∈ J, u ∉ P := by
    intro P hP hr
    obtain ⟨c, hc⟩ := @h P hP hr
    obtain ⟨⟨b, v⟩, hbv⟩ := IsLocalization.surj P.primeCompl c
    have hw : ∀ ψ : A →ₐ[R] K, ∃ w : A, w ∉ P ∧ ((∀ s : A, s ∉ P → ψ s ≠ 0) ∨ ψ w = 0) := by
      intro ψ
      by_cases hg : ∀ s : A, s ∉ P → ψ s ≠ 0
      · exact ⟨1, fun h1 => hP.ne_top ((Ideal.eq_top_iff_one P).2 h1), Or.inl hg⟩
      · push_neg at hg
        obtain ⟨w, hwP, hw0⟩ := hg
        exact ⟨w, hwP, Or.inr hw0⟩
    choose w hwP hwor using hw
    have hWP : (∏ ψ, w ψ) ∉ P := by
      have : (∏ ψ, w ψ) ∈ P.primeCompl := Submonoid.prod_mem _ (fun ψ _ => hwP ψ)
      exact this
    refine ⟨(v : A) * ∏ ψ, w ψ, (memJ _).2 ⟨b * ∏ ψ, w ψ, fun ψ => ?_⟩, ?_⟩
    · rcases hwor ψ with hg | h0
      · have hunit : ∀ y : P.primeCompl, IsUnit (ψ (y : A)) := fun y => (hg y y.2).isUnit
        let ψ' : Localization.AtPrime P →ₐ[R] K := IsLocalization.liftAlgHom (M := P.primeCompl) (f := ψ) hunit
        have e : ∀ x : A, ψ' (algebraMap A _ x) = ψ x := fun x => by
          simp [ψ', IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
        have hcomp : ψ'.comp (IsScalarTower.toAlgHom R A (Localization.AtPrime P)) = ψ := by
          ext x; exact e x
        have h1 := hc ψ'
        rw [hcomp] at h1
        have h2 := congrArg ψ' hbv
        rw [map_mul, h1, e, e] at h2
        rw [map_mul, map_mul, ← h2]; ring
      · have h3 : ψ (∏ φ, w φ) = 0 := by
          rw [map_prod]
          exact Finset.prod_eq_zero (Finset.mem_univ ψ) h0
        rw [map_mul, map_mul, h3]; simp
    · exact fun hm => (hP.mem_or_mem hm).elim v.2 hWP
  have hr : r ∈ J.radical := by
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro P ⟨hJP, hP⟩
    by_contra hrP
    obtain ⟨u, huJ, huP⟩ := key P hP hrP
    exact huP (hJP huJ)
  obtain ⟨k, hk⟩ := hr
  obtain ⟨a, ha⟩ := (memJ _).1 hk
  exact ⟨k, a, fun ψ => by rw [ha, map_pow]⟩

end GlobalTheory.AlgPointsLocal
