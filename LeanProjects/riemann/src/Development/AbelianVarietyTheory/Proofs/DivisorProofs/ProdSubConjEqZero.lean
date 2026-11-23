import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalEqZeroOfDvd
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.GalSec.Tens

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]

open Classical in

def conj (θ : Ω) : Finset Ω := ((minpoly K θ).aroots Ω).toFinset

def DependsOn (k : ℕ) (θ : Ω) (φ : LCRing K Ω k) : Prop :=
  ∀ g g' : Fin k → (Ω ≃ₐ[K] Ω), (∀ i, g i θ = g' i θ) → φ g = φ g'

open Classical in

def pick (k : ℕ) (θ : Ω) (t : Fin k → Ω) : Fin k → (Ω ≃ₐ[K] Ω) :=
  if h : ∃ g : Fin k → (Ω ≃ₐ[K] Ω), ∀ i, g i θ = t i then h.choose else 1

variable {K Ω}
variable {B : Type} [CommRing B]

open Classical in

def idem (g₀ : Ω →+* B) (θ : Ω) (b : B) (s : conj K Ω θ) : B :=
  g₀ (∏ j ∈ (Finset.univ : Finset (conj K Ω θ)).erase s, ((s : Ω) - (j : Ω)))⁻¹ *
    ∏ j ∈ (Finset.univ : Finset (conj K Ω θ)).erase s, (b - g₀ (j : Ω))

def lev (g₀ : Ω →+* B) {k : ℕ} (gs : Fin k → (Ω →+* B)) (θ : Ω) (φ : LCRing K Ω k) : B :=
  ∑ t : Fin k → conj K Ω θ, g₀ (φ (pick K Ω k θ (fun i => (t i : Ω)))) * ∏ i, idem g₀ θ (gs i θ) (t i)

end GlobalTheory.EtC.GalSec.Tens

namespace GlobalTheory.EtC.GalSec.Tens

open Polynomial

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

theorem mem_conj_iff [Algebra.IsAlgebraic K Ω] [Normal K Ω] (θ s : Ω) :
    s ∈ conj K Ω θ ↔ ∃ σ : Ω ≃ₐ[K] Ω, σ θ = s := by
  classical
  have hne : minpoly K θ ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral θ)
  simp only [conj, Multiset.mem_toFinset, mem_aroots, ne_eq, hne, not_false_eq_true, true_and]
  constructor
  · intro h
    have hm : minpoly K s = minpoly K θ :=
      (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible (Algebra.IsIntegral.isIntegral θ)) h
        (minpoly.monic (Algebra.IsIntegral.isIntegral θ))).symm
    obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit Ω).1 hm
    exact ⟨σ, hσ⟩
  · rintro ⟨σ, rfl⟩
    rw [aeval_algEquiv, AlgHom.comp_apply, minpoly.aeval, map_zero]

theorem self_mem_conj [Algebra.IsAlgebraic K Ω] [Normal K Ω] (θ : Ω) : θ ∈ conj K Ω θ :=
  (mem_conj_iff θ θ).2 ⟨1, rfl⟩

theorem prod_conj [Algebra.IsAlgebraic K Ω] [Normal K Ω] [Algebra.IsSeparable K Ω] (θ : Ω) :
    ∏ s ∈ conj K Ω θ, (X - C s) = (minpoly K θ).map (algebraMap K Ω) := by
  classical
  have hint := Algebra.IsIntegral.isIntegral (R := K) θ
  have hsp : Splits ((minpoly K θ).map (algebraMap K Ω)) := Normal.splits inferInstance θ
  have hmo : ((minpoly K θ).map (algebraMap K Ω)).Monic := (minpoly.monic hint).map _
  have hnd : ((minpoly K θ).map (algebraMap K Ω)).roots.Nodup :=
    nodup_roots (Polynomial.Separable.map (Algebra.IsSeparable.isSeparable K θ))
  conv_rhs => rw [hsp.eq_prod_roots_of_monic hmo]
  rw [conj, aroots, Finset.prod_eq_multiset_prod, Multiset.toFinset_val, hnd.dedup]

end GlobalTheory.EtC.GalSec.Tens

namespace GlobalTheory.EtC.GalSec.Tens

open Polynomial

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

theorem apply_mem_conj [Algebra.IsAlgebraic K Ω] [Normal K Ω] (θ : Ω) (σ : Ω ≃ₐ[K] Ω) :
    σ θ ∈ conj K Ω θ :=
  (mem_conj_iff θ (σ θ)).2 ⟨σ, rfl⟩

theorem prod_sub_conj_eq_zero [Algebra.IsAlgebraic K Ω] [Normal K Ω] [Algebra.IsSeparable K Ω]
    {B : Type} [CommRing B] (g₀ σ' : Ω →+* B)
    (h : σ'.comp (algebraMap K Ω) = g₀.comp (algebraMap K Ω)) (θ : Ω) :
    ∏ s ∈ conj K Ω θ, (σ' θ - g₀ s) = 0 := by
  have h1 : (∏ s ∈ conj K Ω θ, (X - C s)).eval₂ g₀ (σ' θ) = ∏ s ∈ conj K Ω θ, (σ' θ - g₀ s) := by
    rw [eval₂_finset_prod]; simp
  rw [← h1, prod_conj, eval₂_map, ← h, ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]

theorem idem_spec [Algebra.IsAlgebraic K Ω] [Normal K Ω] {B : Type} [CommRing B] (g₀ : Ω →+* B)
    (θ : Ω) (b : B) (hb : ∏ s ∈ conj K Ω θ, (b - g₀ s) = 0) :
    CompleteOrthogonalIdempotents (idem (K := K) g₀ θ b) ∧ (∀ s : conj K Ω θ, b * idem (K := K) g₀ θ b s = g₀ s * idem (K := K) g₀ θ b s) ∧
      b = ∑ s : conj K Ω θ, g₀ s * idem (K := K) g₀ θ b s := by
  classical
  letI : Algebra Ω B := g₀.toAlgebra
  haveI : Nonempty (conj K Ω θ) := ⟨⟨θ, self_mem_conj θ⟩⟩
  have hid : idem (K := K) g₀ θ b = GlobalTheory.Pat.lagIdem b (fun j : conj K Ω θ => (j : Ω)) := by
    funext s
    rw [idem, GlobalTheory.Pat.lagIdem, Ring.inverse_eq_inv', Algebra.smul_def, map_prod]
    simp only [map_sub, aeval_X, aeval_C, RingHom.algebraMap_toAlgebra]
  have hu : ∀ i j : conj K Ω θ, i ≠ j → IsUnit ((i : Ω) - j) := fun i j h =>
    (sub_ne_zero.2 (Subtype.coe_injective.ne h)).isUnit
  have hP : aeval b (∏ j : conj K Ω θ, (X - C (j : Ω))) = 0 := by
    rw [map_prod]
    simp only [map_sub, aeval_X, aeval_C, RingHom.algebraMap_toAlgebra]
    rw [Finset.prod_coe_sort (conj K Ω θ) (fun s => b - g₀ s)]
    exact hb
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.lagIdem_spec Ω B (conj K Ω θ) b _ hu hP
  rw [hid]
  refine ⟨h1, fun s => ?_, ?_⟩
  · rw [h2 s, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  · conv_lhs => rw [h3]
    simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra]

theorem pick_spec [Algebra.IsAlgebraic K Ω] [Normal K Ω] (k : ℕ) (θ : Ω) (t : Fin k → Ω)
    (ht : ∀ i, t i ∈ conj K Ω θ) (i : Fin k) : pick K Ω k θ t i θ = t i := by
  have hex : ∃ g : Fin k → (Ω ≃ₐ[K] Ω), ∀ i, g i θ = t i := by
    choose g hg using fun i => (mem_conj_iff θ (t i)).1 (ht i)
    exact ⟨g, hg⟩
  classical
  rw [pick, dif_pos hex]
  exact hex.choose_spec i

end GlobalTheory.EtC.GalSec.Tens

end
