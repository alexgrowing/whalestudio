import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal

noncomputable section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.KapLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def stdH (w : Pl E) {n : ℕ} (v v' : Fin n → w.adicCompletion E) : w.adicCompletion E :=
  ∑ k, v k * cj w (v' k)

def Bridge (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) : Prop :=
  (∀ x, e (K.c x) = cj w (e x)) ∧ (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) ∧
    (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) ∧ qV E w = K.q ^ 2

def Fits (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K)
    (Q : (w.adicCompletion E)[X]) (u : B.A) : Prop :=
  Algebra.adjoin K.E {u} = ⊤ ∧ aeval u (Q.map e.symm.toRingHom) = 0 ∧ Module.finrank K.E B.A = Q.natDegree ∧
    u * B.σ u = 1

def IsModel (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K)
    (u x : B.A) {n : ℕ} (γ : GLw n w) : Prop :=
  ∃ ψ : B.A ≃+ (Fin n → w.adicCompletion E), (∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) ∧
    (∀ y, ψ (u * y) = γ.val *ᵥ ψ y) ∧ ∀ y z, stdH w (ψ y) (ψ z) = e (B.herm x y z)

def congSet (w : Pl E) (n k : ℕ) : Set (GLw n w) :=
  {g | g ∈ GlobalTheory.LFun.KGL w n ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤
    WithZero.exp (-(k : ℤ))}

theorem clRel_equiv {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) :
    Equivalence (fun x y : {x : B.Aˣ // B.σ (x : B.A) = x} =>
      ∃ u : B.Aˣ, (y.1 : B.A) = x.1 * (u * B.σ (u : B.A))) where
  refl x := ⟨1, by simp⟩
  symm := by
    rintro x y ⟨u, hu⟩
    refine ⟨u⁻¹, ?_⟩
    have h1 : ((u : B.A) * ((u⁻¹ : B.Aˣ) : B.A)) * (B.σ (u : B.A) * B.σ ((u⁻¹ : B.Aˣ) : B.A)) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one, one_mul]
    rw [hu]
    calc (x.1 : B.A) = x.1 * (((u : B.A) * ((u⁻¹ : B.Aˣ) : B.A)) * (B.σ (u : B.A) * B.σ ((u⁻¹ : B.Aˣ) : B.A))) := by
          rw [h1, mul_one]
      _ = _ := by ring
  trans := by
    rintro x y z ⟨u, hu⟩ ⟨v, hv⟩
    exact ⟨u * v, by rw [hv, hu, Units.val_mul, map_mul]; ring⟩

theorem conjRel_equiv (G : Type) [Group G] :
    Equivalence (fun x y : G => ∃ g, y = g⁻¹ * x * (MonoidHom.id G) g) where
  refl x := ⟨1, by simp⟩
  symm := by
    rintro x y ⟨g, rfl⟩
    exact ⟨g⁻¹, by simp [mul_assoc]⟩
  trans := by
    rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
    exact ⟨g * h, by simp [mul_assoc]⟩

theorem cast_finsum {α : Type*} (f : α → ℚ) : ((∑ᶠ a, f a : ℚ) : ℂ) = ∑ᶠ a, (f a : ℂ) := by
  by_cases h : (Function.support f).Finite
  · exact map_finsum (Rat.castHom ℂ) h
  · have h' : ¬ (Function.support fun a => (f a : ℂ)).Finite := by
      simpa [Function.support] using h
    rw [finsum_of_infinite_support h, finsum_of_infinite_support h']
    simp

end GlobalTheory.KapLat
