import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnCVInCC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BXiAsm

open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField

namespace Formalism.FourierDecayAlt.P.CutMP.En

theorem inCC_fold (hC : CVInCC) {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (A : ℝ) (s : ℂ)
    (F : B.Mat k r → E) : ∀ (b : List C.Letter) (m : ℕ),
      B.InCC A (m + (2 * r + k + 1) * b.length) F → B.InCC A m (foldCV k r s b F)
  | [], m, h => by rw [foldCV_nil]; simpa using h
  | x :: b, m, h => by
    rw [foldCV_cons]
    refine hC k r E A m _ (x.2 : ℂ) s ?_
    refine inCC_fold hC A s F b (m + (2 * r + k + 1)) ?_
    have e : m + (2 * r + k + 1) + (2 * r + k + 1) * b.length = m + (2 * r + k + 1) * (x :: b).length := by
      simp [List.length_cons]; ring
    rw [e]; exact h

theorem weight_budget_L2_inequality (k r N : ℕ) (A₀ : ℝ) (hk : 2 ≤ k) (j : ℕ) (hj : j ≤ 5)
    (hA : 100 * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (r : ℝ) + k + 1) ^ 2 + (2 * (r : ℝ) + k + 1) ^ 3) ≤ A₀)
    (ℓ : ℕ) (hℓ : ℓ ≤ N) :
    B.AB k r + 2 * ((r : ℝ) + 1) * ((j + (2 * r + k + 1) * ℓ : ℕ) : ℝ) ≤ A₀ := by
  unfold B.AB
  have hR : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hK : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hj' : (j : ℝ) ≤ 5 := by exact_mod_cast hj
  have hℓ' : (ℓ : ℝ) ≤ N := by exact_mod_cast hℓ
  have hℓ0 : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
  set n : ℝ := 2 * (r : ℝ) + k + 1 with hn
  have hcast : ((j + (2 * r + k + 1) * ℓ : ℕ) : ℝ) = j + n * ℓ := by rw [hn]; push_cast; ring
  rw [hcast]
  have hn3 : (3 : ℝ) ≤ n := by rw [hn]; linarith
  have hR1 : (1 : ℝ) ≤ (r : ℝ) + 1 := by linarith
  have h4 : (r : ℝ) + 1 ≤ ((r : ℝ) + 1) ^ 4 := by
    have : (1 : ℝ) ≤ ((r : ℝ) + 1) ^ 3 := one_le_pow₀ hR1
    nlinarith

  have hkr : 2 * ((k : ℝ) + r) ≤ 2 * n := by rw [hn]; linarith
  have hb : 2 * ((k : ℝ) + r) + 1 + 2 * (j + n * ℓ) ≤ 100 * ((N : ℝ) * n ^ 2 + n ^ 3) := by
    have h1 : 2 * n * ℓ ≤ (N : ℝ) * n ^ 2 := by
      have : (ℓ : ℝ) * (2 * n) ≤ N * (n * n) := by
        apply mul_le_mul hℓ' (by nlinarith) (by positivity) (by positivity)
      nlinarith
    have h2 : 2 * n + 1 + 10 ≤ 100 * n ^ 3 := by nlinarith
    have hNn : 0 ≤ (N : ℝ) * n ^ 2 := by positivity
    nlinarith
  have hpos : 0 ≤ 100 * ((N : ℝ) * n ^ 2 + n ^ 3) := by positivity
  calc 2 * ((k : ℝ) + r) * ((r : ℝ) + 1) + 1 + 2 * ((r : ℝ) + 1) * (j + n * ℓ)
      ≤ ((r : ℝ) + 1) * (2 * ((k : ℝ) + r) + 1 + 2 * (j + n * ℓ)) := by nlinarith
    _ ≤ ((r : ℝ) + 1) * (100 * ((N : ℝ) * n ^ 2 + n ^ 3)) := by gcongr
    _ ≤ ((r : ℝ) + 1) ^ 4 * (100 * ((N : ℝ) * n ^ 2 + n ^ 3)) := by gcongr
    _ = 100 * ((r : ℝ) + 1) ^ 4 * ((N : ℝ) * n ^ 2 + n ^ 3) := by ring
    _ ≤ A₀ := hA

theorem l2BoundAtBuiltPlace_of_cvInCC (hC : CVInCC) : L2BoundAtTowerPlace := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v ε hε a hlen
  obtain ⟨⟨_, _, _, hbuilt, _, _, _, _, _, _, hk2, hA, _⟩, _, _, _⟩ := hB
  obtain ⟨hχ, hv⟩ := hbuilt
  obtain ⟨_, _, _, _, hCC, _⟩ := hv v
  have hF : ∀ j ≤ 5, B.InCC (B.AB S.G.k S.G.r) (j + (2 * S.G.r + S.G.k + 1) * a.length)
      (D.cutF (T v).base χ (f v) ε) := fun j hj =>
    Formalism.FourierDecayAlt.P.PBE.cutF_inCC (T v).base hχ hCC hε _ _ (weight_budget_L2_inequality S.G.k S.G.r S.Ntop A₀ hk2 j hj hA a.length hlen)
  have h5 := inCC_fold hC (B.AB S.G.k S.G.r) (M.sgn (D.parOf S v) (S.l + 1)) _ a 5 (hF 5 le_rfl)
  have h4 := inCC_fold hC (B.AB S.G.k S.G.r) (M.sgn (D.parOf S v) (S.l + 1)) _ a 4 (hF 4 (by norm_num))
  obtain ⟨_, _, _, hB1, _⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base
    (B.AB S.G.k S.G.r) le_rfl
  obtain ⟨C0, hC0⟩ := hB1
  obtain ⟨c4, hc4⟩ := h4
  exact (hC0 _ _ c4 c4 h5 h5 hc4 hc4).1

theorem L2_bound_at_built_place_holds : L2BoundAtTowerPlace := l2BoundAtBuiltPlace_of_cvInCC coefficient_vector_in_L2_class

end Formalism.FourierDecayAlt.P.CutMP.En
