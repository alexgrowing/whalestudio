import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicWitt

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.SWACase

open GlobalTheory.SWLit

def WeilRange : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → 2 * n < m →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ Φ ∈ schA F κ, FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om (1, k) Φ}) →
  ∀ (ν : Measure (UA σ JV)) (𝓕 : Set (UA σ JV)), ν.IsHaarMeasure → IsFundamentalDomain (ratU σ JV) 𝓕 ν →
  ∀ g, Cont.HolValueAt
    (fun s => Eis.cosetSum (siegelOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype) (ratU σ J₂)
      (flatOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K (fun g => om (1, g) Φ 0)
        (((m : ℂ) - (n : ℂ)) / 2) s) g)
    (((m : ℂ) - (n : ℂ)) / 2) ((if n < m then 1 else 2 : ℂ) * ⨍ h in 𝓕, thetaSum F (om (h, g) Φ) ∂ν)

def MidRange : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → n < m ∧ m ≤ 2 * n →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ Φ ∈ schA F κ, FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om (1, k) Φ}) →
  ∀ (ν : Measure (UA σ JV)) (𝓕 : Set (UA σ JV)), ν.IsHaarMeasure → IsFundamentalDomain (ratU σ JV) 𝓕 ν →
  ∀ g, Cont.HolValueAt
    (fun s => Eis.cosetSum (siegelOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype) (ratU σ J₂)
      (flatOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K (fun g => om (1, g) Φ 0)
        (((m : ℂ) - (n : ℂ)) / 2) s) g)
    (((m : ℂ) - (n : ℂ)) / 2) ((if n < m then 1 else 2 : ℂ) * ⨍ h in 𝓕, thetaSum F (om (h, g) Φ) ∂ν)

def LowRange : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m → m ≤ n →
  ∀ (l : E) (JV : Matrix (Fin m) (Fin m) E) (J : Matrix (Fin n) (Fin n) E) (J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E),
    l ≠ 0 → IsHermND σ (l • JV) → (∀ x, form σ JV x x = 0 → x = 0) →
    (∀ i j, σ ((l⁻¹ • J) j i) = -(l⁻¹ • J) i j) → J₂ = dblGram finSumFinEquiv J →
  ∀ T : GL (Fin (n + n)) E, IsWittBasis σ J l T →
  ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JV) (incM F J₂)) κ), IsAdapted σ co →
  ∀ [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), IsTamagawa F κ μ →
  ∀ χ : Chr F E, IsHecke F E χ → ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ m →
  ∀ om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ), IsWeilFormulas σ ψ χ T co μ om →
  ∀ K : Subgroup (UA σ J₂), IsStdK σ T K → IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K →
  ∀ Φ ∈ schA F κ, FiniteDimensional ℂ (Submodule.span ℂ {Ψ | ∃ k ∈ K, Ψ = om (1, k) Φ}) →
  ∀ (ν : Measure (UA σ JV)) (𝓕 : Set (UA σ JV)), ν.IsHaarMeasure → IsFundamentalDomain (ratU σ JV) 𝓕 ν →
  ∀ g, Cont.HolValueAt
    (fun s => Eis.cosetSum (siegelOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype) (ratU σ J₂)
      (flatOf finSumFinEquiv (UG (cA σ) (incM F J₂)).subtype (absE F E) K (fun g => om (1, g) Φ 0)
        (((m : ℂ) - (n : ℂ)) / 2) s) g)
    (((m : ℂ) - (n : ℂ)) / 2) ((if n < m then 1 else 2 : ℂ) * ⨍ h in 𝓕, thetaSum F (om (h, g) Φ) ∂ν)

theorem range_cases (n m : ℕ) : 2 * n < m ∨ (n < m ∧ m ≤ 2 * n) ∨ m ≤ n := by omega

theorem weilRange_of_all (h : GlobalTheory.Published.SiegelWeilAnisotropicWitt) : WeilRange :=
  fun F E _ _ _ _ _ σ hCM hU ψ hψ n m hn hm _ => h F E σ hCM hU ψ hψ n m hn hm

theorem midRange_of_all (h : GlobalTheory.Published.SiegelWeilAnisotropicWitt) : MidRange :=
  fun F E _ _ _ _ _ σ hCM hU ψ hψ n m hn hm _ => h F E σ hCM hU ψ hψ n m hn hm

theorem lowRange_of_all (h : GlobalTheory.Published.SiegelWeilAnisotropicWitt) : LowRange :=
  fun F E _ _ _ _ _ σ hCM hU ψ hψ n m hn hm _ => h F E σ hCM hU ψ hψ n m hn hm

theorem all_of_ranges (h₁ : WeilRange) (h₂ : MidRange) (h₃ : LowRange) : GlobalTheory.Published.SiegelWeilAnisotropicWitt := by
  intro F E _ _ _ _ _ σ hCM hU ψ hψ n m hn hm
  rcases range_cases n m with h | h | h
  · exact h₁ F E σ hCM hU ψ hψ n m hn hm h
  · exact h₂ F E σ hCM hU ψ hψ n m hn hm h
  · exact h₃ F E σ hCM hU ψ hψ n m hn hm h

theorem all_iff_ranges : GlobalTheory.Published.SiegelWeilAnisotropicWitt ↔ WeilRange ∧ MidRange ∧ LowRange :=
  ⟨fun h => ⟨weilRange_of_all h, midRange_of_all h, lowRange_of_all h⟩, fun h => all_of_ranges h.1 h.2.1 h.2.2⟩

example (n m : ℕ) :
    ¬ (2 * n < m ∧ n < m ∧ m ≤ 2 * n) ∧ ¬ (2 * n < m ∧ m ≤ n) ∧ ¬ ((n < m ∧ m ≤ 2 * n) ∧ m ≤ n) := by omega

example (n : ℕ) (hn : 1 ≤ n) :
    (∃ m, 1 ≤ m ∧ 2 * n < m) ∧ (∃ m, 1 ≤ m ∧ n < m ∧ m ≤ 2 * n) ∧ ∃ m, 1 ≤ m ∧ m ≤ n :=
  ⟨⟨2 * n + 1, by omega⟩, ⟨2 * n, by omega⟩, ⟨n, by omega⟩⟩

example (n m : ℕ) :
    (2 * n < m → (if n < m then 1 else 2 : ℂ) = 1) ∧ (n < m ∧ m ≤ 2 * n → (if n < m then 1 else 2 : ℂ) = 1) ∧
    (m ≤ n → (if n < m then 1 else 2 : ℂ) = 2) :=
  ⟨fun h => if_pos (by omega), fun h => if_pos h.1, fun h => if_neg (by omega)⟩

example (n m : ℕ) : 2 * n < m ↔ (n : ℝ) / 2 < ((m : ℝ) - (n : ℝ)) / 2 := by
  constructor
  · intro h
    have : (2 * n : ℝ) < m := by exact_mod_cast h
    linarith
  · intro h
    have : (2 * n : ℝ) < m := by linarith
    exact_mod_cast this

end GlobalTheory.SWACase

end
