import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift

open scoped TensorProduct Topology
open NumberField IsDedekindDomain Filter GlobalTheory.LFun

section Defs

variable {K : Type} [Field K] [NumberField K]

def liftFam (c : Fam K) (m x : HeightOneSpectrum (𝓞 K) → ℂˣ) (t : ℕ) : Fam K :=
  twist c (x * m⁻¹) + segFam x t

def IsZetaCont (T : Set (HeightOneSpectrum (𝓞 K))) (Z : ℂ → ℂ) : Prop :=
  MeromorphicOn Z Set.univ ∧ ∀ s : ℂ, 1 < s.re → Z s = zetaOff T s

def HasSimplePole (Λ : ℂ → ℂ) (s₀ : ℂ) : Prop :=
  MeromorphicAt Λ s₀ ∧ meromorphicOrderAt Λ s₀ = ((-1 : ℤ) : WithTop ℤ) ∧
    ∃ ρ : ℂ, ρ ≠ 0 ∧ Tendsto (fun s => (s - s₀) * Λ s) (𝓝[≠] s₀) (𝓝 ρ)

end Defs

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def rhs (S : Set (HeightOneSpectrum (𝓞 F))) (c : Fam E) (m : HeightOneSpectrum (𝓞 E) → ℂˣ) (t : ℕ)
    (Z : ℂ → ℂ) (s : ℂ) : ℂ :=
  LSTw S c m s * ∏ i ∈ Finset.range t, Z (s + ((t : ℂ) - 1) / 2 - i)

def Hyp (S : Set (HeightOneSpectrum (𝓞 F))) (r t : ℕ) (c P : Fam E) (m x : HeightOneSpectrum (𝓞 E) → ℂˣ) : Prop :=
  S.Finite ∧ r + 5 ≤ t ∧
    ∀ w ∉ above E S, (c w).card = r ∧
      (∀ b ∈ c w, ‖(b : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((r : ℝ) - 1) / 2)) ∧
      ‖(m w : ℂ)‖ = 1 ∧ ‖(x w : ℂ)‖ = 1 ∧ P w = liftFam c m x t w

def Concl (S : Set (HeightOneSpectrum (𝓞 F))) (r t : ℕ) (c P : Fam E) (m x : HeightOneSpectrum (𝓞 E) → ℂˣ) :
    Prop :=
  (∀ s : ℂ, ((t : ℝ) + 1) / 2 < s.re →
    Converges (above E S) (twist P x⁻¹) s ∧
      (∀ i < t, Converges (above E S) (fun _ => {1}) (s + ((t : ℂ) - 1) / 2 - i)) ∧
      LSTw S P x s = rhs S c m t (zetaOff (above E S)) s) ∧
  ((∀ s : ℂ, ((r : ℝ) + 1) / 2 < s.re → Converges (above E S) (twist c m⁻¹) s ∧ LSTw S c m s ≠ 0) ∧
    DifferentiableOn ℂ (LSTw S c m) {s | ((r : ℝ) + 1) / 2 < s.re}) ∧
  (∃ Z, IsZetaCont (above E S) Z) ∧
  ∀ Z, IsZetaCont (above E S) Z →
    MeromorphicOn (rhs S c m t Z) {s | ((r : ℝ) + 1) / 2 < s.re} ∧
      ((r : ℝ) + 1) / 2 < ((1 + (t : ℂ)) / 2).re ∧
      (∀ s : ℂ, ((t : ℝ) + 1) / 2 < s.re → rhs S c m t Z s = LSTw S P x s) ∧
      HasSimplePole (rhs S c m t Z) ((1 + (t : ℂ)) / 2)

def SimplePole : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (S : Set (HeightOneSpectrum (𝓞 F))) (r t : ℕ) (c P : Fam E) (m x : HeightOneSpectrum (𝓞 E) → ℂˣ),
    Hyp S r t c P m x → Concl S r t c P m x

section Rep

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU

theorem SimplePole.rep (h : SimplePole) (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (L : Submodule (𝓞 E) (Fin n → E)) {Vl : HeightOneSpectrum (𝓞 F) → Type} [∀ v, AddCommGroup (Vl v)]
    [∀ v, Module ℂ (Vl v)] (π : ∀ v, Representation ℂ (GLoc σ J v) (Vl v))
    {S : Set (HeightOneSpectrum (𝓞 F))} (hS : S.Finite) {r t : ℕ} (ht : r + 5 ≤ t) {c : Fam E}
    (μ χ : (AF F ⊗[F] E)ˣ →* Circle)
    (hc : ∀ w ∉ above E S, (c w).card = r ∧
      ∀ b ∈ c w, ‖(b : ℂ)‖ ≤ ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((r : ℝ) - 1) / 2))
    (hπ : ∀ w ∉ above E S, paramFam σ J L π w = liftFam c (val μ) (val χ) t w) :
    ∃ Λ : ℂ → ℂ, MeromorphicOn Λ {s | ((r : ℝ) + 1) / 2 < s.re} ∧
      (∀ s : ℂ, ((t : ℝ) + 1) / 2 < s.re → Λ s = LSRep σ J L S π (val χ) s) ∧
      HasSimplePole Λ ((1 + (t : ℂ)) / 2) := by
  obtain ⟨-, -, ⟨Z, hZ⟩, h4⟩ := h F E S r t c _ (val μ) (val χ)
    ⟨hS, ht, fun w hw => ⟨(hc w hw).1, (hc w hw).2, norm_val μ w, norm_val χ w, hπ w hw⟩⟩
  exact ⟨_, (h4 Z hZ).1, (h4 Z hZ).2.2.1, (h4 Z hZ).2.2.2⟩

end Rep

theorem twist_liftFam (c : Fam E) (m x : HeightOneSpectrum (𝓞 E) → ℂˣ) (t : ℕ) :
    twist (liftFam c m x t) x⁻¹ = twist c m⁻¹ + segFam 1 t := by
  rw [liftFam, twist_add, twist_twist, twist_segFam, inv_mul_cancel_left, inv_mul_cancel]

example : Hyp (F := F) (E := E) ∅ 1 7 (fun _ => {1}) (liftFam (fun _ => {1}) 1 1 7) 1 1 :=
  ⟨Set.finite_empty, by norm_num, fun w _ => by simp⟩

example : HasSimplePole (fun s => s⁻¹) 0 := by
  refine ⟨(MeromorphicAt.id 0).inv, ?_, 1, one_ne_zero, ?_⟩
  · have h : meromorphicOrderAt (id⁻¹ : ℂ → ℂ) 0 = -meromorphicOrderAt (id : ℂ → ℂ) 0 := meromorphicOrderAt_inv
    rw [meromorphicOrderAt_id] at h
    exact h
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [sub_zero, mul_inv_cancel₀ hs]

end GlobalTheory.IndefiniteRowSideFullHecke.SimplePoleTwistedLift

end
