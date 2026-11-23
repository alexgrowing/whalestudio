import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFrameTranslatedPerpOfIsFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousWordTranslate
open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec

namespace UpperTheory.Lit.Bur.SobConj

theorem sobCont_conj {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) {J G Q Qi : Matrix (Fin n) (Fin n) ℂ} (h1 : Q * Qi = 1)
    (h2 : Qi * Q = 1) (hg : Qᴴ * J * Q = G) {l : H →ₗ[ℂ] ℂ} (hl : Sobolev₂ (lieG J) σ l) :
    Sobolev₂ (lieG G) (fun g => σ (Q * g * Qi)) l := by
  have back : ∀ a : Matrix (Fin n) (Fin n) ℂ, Q * (Qi * a * Q) * Qi = a := fun a => by
    calc Q * (Qi * a * Q) * Qi = (Q * Qi) * a * (Q * Qi) := by simp only [Matrix.mul_assoc]
      _ = a := by rw [h1, Matrix.one_mul, Matrix.mul_one]
  have lie : ∀ X ∈ lieG J, Qi * X * Q ∈ lieG G := fun X hX =>
    GlobalTheory.SmoothCyclic.conj_lie h2 hg hX
  have e : ∀ X w, dRep (fun g => σ (Q * g * Qi)) (Qi * X * Q) w = dRep σ X w := fun X w => by
    simp only [dRep, GlobalTheory.SmoothCyclic.exp_conj_of_mul h2, back]
  have hsm : ∀ w, SmoothVec (lieG G) (fun g => σ (Q * g * Qi)) w → SmoothVec (lieG J) σ w :=
    fun w hw k Xs hX => by
      simpa only [GlobalTheory.SmoothCyclic.expProd_conj h2, back] using
        hw k (fun i => Qi * Xs i * Q) fun i => lie _ (hX i)
  obtain ⟨S, C, hS, hb⟩ := hl
  refine ⟨S.map fun L => L.map fun X => Qi * X * Q, C, fun L hL X hX => ?_, fun w hw => ?_⟩
  · obtain ⟨L', hL', rfl⟩ := List.mem_map.1 hL
    obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
    exact lie Y (hS L' hL' Y hY)
  · simpa only [e, List.map_map, Function.comp_def, List.foldr_map] using hb w (hsm w hw)

end UpperTheory.Lit.Bur.SobConj

open Matrix GlobalTheory.RealBessel GlobalTheory.BesselMapOne Formalism.L2.Theta GlobalTheory.SmVec
set_option maxHeartbeats 1000000 in
theorem _root_.UpperTheory.Lit.Bur.sobolevCont_of_conj_gram_form : ∀ {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) {J G Q Qi : Matrix (Fin n) (Fin n) ℂ} (h1 : Q * Qi = 1) (h2 : Qi * Q = 1) (hg : Qᴴ * J * Q = G) {l : H →ₗ[ℂ] ℂ} (hl : Sobolev₂ (lieG J) σ l), Sobolev₂ (lieG G) (fun g => σ (Q * g * Qi)) l := by
  first | exact @UpperTheory.Lit.Bur.SobConj.sobCont_conj | exact UpperTheory.Lit.Bur.SobConj.sobCont_conj | (intros; apply UpperTheory.Lit.Bur.SobConj.sobCont_conj <;> assumption)
