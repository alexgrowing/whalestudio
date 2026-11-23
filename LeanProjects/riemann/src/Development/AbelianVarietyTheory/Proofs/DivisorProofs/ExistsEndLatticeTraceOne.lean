import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisAutMemAdelicCompletionIntegral

noncomputable section

namespace GlobalTheory.LieDisc

open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def rankOne (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) : Matrix (Fin r) (Fin r) E :=
  Matrix.of fun a b => x a * ∑ k, G b k * cc (y k)

theorem rankOne_mulVec (G : Matrix (Fin r) (Fin r) E) (x y v : Fin r → E) :
    rankOne G x y *ᵥ v = herm G v y • x := by
  ext a
  simp only [rankOne, mulVec, dotProduct, of_apply, herm, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem trace_rankOne (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    (rankOne G x y).trace = herm G x y := by
  simp only [Matrix.trace, diag, rankOne, of_apply, herm, Finset.mul_sum, mul_assoc]

def traceIdeal (Λ : Submodule (𝓞 E) (Fin r → E)) : Ideal (𝓞 E) where
  carrier := {s | ∃ Z ∈ endLat Λ, Z.trace = (s : E)}
  zero_mem' := ⟨0, (endLat Λ).zero_mem, by simp⟩
  add_mem' {s t} hs ht := by
    obtain ⟨Z, hZ, e⟩ := hs
    obtain ⟨Z', hZ', e'⟩ := ht
    exact ⟨Z + Z', (endLat Λ).add_mem hZ hZ', by rw [trace_add, e, e']; push_cast; rfl⟩
  smul_mem' c {s} hs := by
    obtain ⟨Z, hZ, e⟩ := hs
    refine ⟨(c : E) • Z, smul_mem_endLat c.isIntegral_coe hZ, ?_⟩
    rw [trace_smul, e, smul_eq_mul, smul_eq_mul]
    push_cast; rfl

theorem exists_endLat_trace_eq_one (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (hr : 1 ≤ r)
    (h : SelfDualLat G Λ) : ∃ Z ∈ endLat Λ, Z.trace = 1 := by
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (herm G x y) := fun x hx => (h.2.2.2.2 x).2 hx
  have htop : traceIdeal Λ = ⊤ := by
    by_contra hT
    refine GlobalTheory.UCls.Det.exists_herm_notMem hr h (traceIdeal Λ) hT fun x hx y hy =>
      ⟨⟨herm G x y, hint x hx y hy⟩, ⟨rankOne G x y, fun v hv => ?_, trace_rankOne G x y⟩, rfl⟩
    rw [rankOne_mulVec]
    exact smul_mem_of_isIntegral (hint v hv y hy) hx
  have h1 : (1 : 𝓞 E) ∈ traceIdeal Λ := htop ▸ Submodule.mem_top
  obtain ⟨Z, hZ, e⟩ := h1
  exact ⟨Z, hZ, by rw [e]; simp⟩

example : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E)
    (Λ : Submodule (𝓞 E) (Fin r → E)), 1 ≤ r → SelfDualLat G Λ → ∃ Z ∈ endLat Λ, Z.trace = 1 :=
  exists_endLat_trace_eq_one

end GlobalTheory.LieDisc
