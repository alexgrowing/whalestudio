import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelaf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralFiniteAdeleCompleteSeparated

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.IntAdeleComplete

open Formalism.UG Formalism.UG.P

variable {E : Type} [Field E] [NumberField E]

local notation "𝔸" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "𝒮" => tensInt (F := ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ) (intOE E) (intAd ℚ)

def ratBasis (E : Type) [Field E] [NumberField E] :
    Module.Basis (Fin (Module.finrank ℤ (𝓞 E))) ℚ E :=
  (Module.finBasis ℤ (𝓞 E)).localizationLocalization ℚ (nonZeroDivisors ℤ) E

theorem ratBasis_apply (j : Fin (Module.finrank ℤ (𝓞 E))) :
    ratBasis E j = algebraMap (𝓞 E) E (Module.finBasis ℤ (𝓞 E) j) :=
  Module.Basis.localizationLocalization_apply _ _ _ _ _

def coord (i : Fin (Module.finrank ℤ (𝓞 E))) : E ⊗[ℚ] 𝔸 →ₗ[ℚ] 𝔸 :=
  (TensorProduct.lid ℚ 𝔸).toLinearMap ∘ₗ LinearMap.rTensor 𝔸 ((ratBasis E).coord i)

def comb : (Fin (Module.finrank ℤ (𝓞 E)) → 𝔸) →+ E ⊗[ℚ] 𝔸 where
  toFun r := ∑ j, algebraMap (𝓞 E) E (Module.finBasis ℤ (𝓞 E) j) ⊗ₜ[ℚ] r j
  map_zero' := by simp
  map_add' a b := by simp [TensorProduct.tmul_add, Finset.sum_add_distrib]

theorem coord_comb (r : Fin (Module.finrank ℤ (𝓞 E)) → 𝔸) (i : Fin (Module.finrank ℤ (𝓞 E))) :
    coord i (comb r) = r i := by
  change coord i (∑ j, algebraMap (𝓞 E) E (Module.finBasis ℤ (𝓞 E) j) ⊗ₜ[ℚ] r j) = r i
  rw [map_sum, Finset.sum_eq_single i]
  · rw [← ratBasis_apply]
    simp [coord]
  · intro j _ hj
    rw [← ratBasis_apply]
    simp [coord, Finsupp.single_apply, hj]
  · simp

theorem comb_mem (r : Fin (Module.finrank ℤ (𝓞 E)) → 𝔸) (hr : ∀ j, r j ∈ intAd ℚ) :
    comb r ∈ 𝒮 := by
  change (∑ j, algebraMap (𝓞 E) E (Module.finBasis ℤ (𝓞 E) j) ⊗ₜ[ℚ] r j) ∈ 𝒮
  exact sum_mem fun j _ => levelaf_tmul_mem _ (hr j)

theorem exists_comb {s : E ⊗[ℚ] 𝔸} (hs : s ∈ 𝒮) :
    ∃ r : Fin (Module.finrank ℤ (𝓞 E)) → 𝔸, (∀ j, r j ∈ intAd ℚ) ∧ s = comb r :=
  levelaf_decomp (fun j => Module.finBasis ℤ (𝓞 E) j) (Module.finBasis ℤ (𝓞 E)).span_eq hs

theorem coord_mem {s : E ⊗[ℚ] 𝔸} (hs : s ∈ 𝒮) (i : Fin (Module.finrank ℤ (𝓞 E))) :
    coord i s ∈ intAd ℚ := by
  obtain ⟨r, hr, rfl⟩ := exists_comb hs
  rw [coord_comb]
  exact hr i

theorem comb_coord {s : E ⊗[ℚ] 𝔸} (hs : s ∈ 𝒮) : comb (fun i => coord i s) = s := by
  obtain ⟨r, -, rfl⟩ := exists_comb hs
  simp only [coord_comb]

theorem tensInt_separated_complete (E : Type) [Field E] [NumberField E] :
    (∀ y : E ⊗[ℚ] 𝔸, (∀ N : ℕ, 0 < N →
      ∃ w ∈ tensInt (F := ℚ) 𝔸 (intOE E) (intAd ℚ), y = (N : E ⊗[ℚ] 𝔸) * w) → y = 0) ∧
    ∀ x : ℕ → E ⊗[ℚ] 𝔸, (∀ N, x N ∈ tensInt (F := ℚ) 𝔸 (intOE E) (intAd ℚ)) →
      (∀ N m : ℕ, 0 < N → 0 < m → ∃ w ∈ tensInt (F := ℚ) 𝔸 (intOE E) (intAd ℚ),
        x (N * m) = x N + (N : E ⊗[ℚ] 𝔸) * w) →
      ∃ y ∈ tensInt (F := ℚ) 𝔸 (intOE E) (intAd ℚ), ∀ N : ℕ, 0 < N →
        ∃ w ∈ tensInt (F := ℚ) 𝔸 (intOE E) (intAd ℚ), y = x N + (N : E ⊗[ℚ] 𝔸) * w := by
  obtain ⟨hsep, hcpl⟩ := GlobalTheory.AdLat.integral_finiteAdele_complete_separated ℚ
  simp only [← nsmul_eq_mul]
  constructor
  · intro z hz
    have hz1 : z ∈ tensInt (F := ℚ) 𝔸 (intOE E) (intAd ℚ) := by
      obtain ⟨w, hw, h⟩ := hz 1 one_pos
      rw [h, one_smul]; exact hw
    have : (fun i => coord i z) = 0 := by
      funext i
      refine hsep _ fun N hN => ?_
      obtain ⟨w, hw, h⟩ := hz N hN
      exact ⟨_, coord_mem hw i, by rw [h, map_nsmul]⟩
    rw [← comb_coord hz1, this, map_zero]
  · intro x hx hxx
    have key : ∀ i, ∃ y : 𝔸, ∀ N : ℕ, 0 < N → ∃ a : 𝔸,
        (∀ v, a v ∈ v.adicCompletionIntegers ℚ) ∧ y = coord i (x N) + N • a := by
      intro i
      refine hcpl (fun N => coord i (x N)) (fun N => coord_mem (hx N) i) fun N k hN hk => ?_
      obtain ⟨w, hw, h⟩ := hxx N k hN hk
      exact ⟨_, coord_mem hw i, by rw [h, map_add, map_nsmul]⟩
    choose y hy using key
    have main : ∀ N : ℕ, 0 < N → ∃ w ∈ tensInt (F := ℚ) 𝔸 (intOE E) (intAd ℚ),
        comb y = x N + N • w := by
      intro N hN
      choose a ha hya using fun i => hy i N hN
      refine ⟨comb a, comb_mem a ha, ?_⟩
      have : y = (fun i => coord i (x N)) + N • a := funext hya
      rw [this, map_add, map_nsmul, comb_coord (hx N)]
    refine ⟨comb y, ?_, main⟩
    obtain ⟨w, hw, h⟩ := main 1 one_pos
    rw [h]
    exact add_mem (hx 1) (nsmul_mem hw 1)

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.StandardLatticesGL3 in

theorem integral_separated_complete : ∀ (D : D7), (∀ y : AE D, (∀ N : ℕ, 0 < N → ∃ w ∈ OhE D, y = (N : AE D) * w) → y = 0) ∧ ∀ x : ℕ → AE D, (∀ N, x N ∈ OhE D) → (∀ N m : ℕ, 0 < N → 0 < m → ∃ w ∈ OhE D, x (N * m) = x N + (N : AE D) * w) → ∃ y ∈ OhE D, ∀ N : ℕ, 0 < N → ∃ w ∈ OhE D, y = x N + (N : AE D) * w :=
  fun D => tensInt_separated_complete D.host.E

end GlobalTheory.IntAdeleComplete
