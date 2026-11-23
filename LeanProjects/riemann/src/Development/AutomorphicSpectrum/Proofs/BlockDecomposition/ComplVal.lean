import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValThree

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.ComplVal

theorem side {T : Type} [CommRing T] (t : T) (hu : ∀ x : T, IsUnit (1 + t * x))
    (f f' a b w E : T) (N : ℕ) (hE : E * E = E) (hab : a * f + b * f' = t ^ N)
    (hw : E * f = t ^ (N + 1) * w) : ∃ c, c * f' = E * f := by
  obtain ⟨v, hv⟩ := (hu (-(w * a))).exists_left_inv
  have key : (1 + t * -(w * a)) * (E * f) = E * t * w * b * f' := by
    linear_combination E * hw - E * t * w * hab - f * hE
  exact ⟨v * (E * t * w * b), by linear_combination -v * key + E * f * hv⟩

theorem mid {T : Type} [CommRing T] (P Q E f F f' F' k v v' u' : T) (hP : P * P = P) (hQ : Q * Q = Q)
    (hA : P * f = P * F * v) (hB : Q * f' = Q * F' * v') (hu : v' * u' = 1)
    (hk : k * F' = P * Q * E * F) : ∃ c, c * f' = P * Q * E * f := by
  exact ⟨v * k * Q * u', by
    linear_combination v * k * u' * hB + v * k * Q * F' * hu + v * Q * hk + v * P * E * F * hQ - Q * E * hA⟩

theorem core {T : Type} [CommRing T] (t : T) (hu : ∀ x : T, IsUnit (1 + t * x))
    (f f' F F' a b s s' c c' d d' k k' E₁ E₂ E : T) (N : ℕ)
    (h₁ : E₁ * E₁ = E₁) (h₂ : E₂ * E₂ = E₂) (hE : E * E = E)
    (hab : a * f + b * f' = t ^ N)
    (hs : s * t ^ (N + 2) = f - F) (hs' : s' * t ^ (N + 2) = f' - F')
    (hc : c * t ^ (N + 1) = E₁ * F) (hc' : c' * t ^ (N + 1) = E₂ * F')
    (hd : d * F = (1 - E₁) * t ^ (N + 1)) (hd' : d' * F' = (1 - E₂) * t ^ (N + 1))
    (hk : k * F' = (1 - E₁) * (1 - E₂) * E * F)
    (hk' : k' * F = (1 - E₁) * (1 - E₂) * (1 - E) * F') :
    ∃ e : T, IsIdempotentElem e ∧ e * f ∈ Ideal.span {f'} ∧ (1 - e) * f' ∈ Ideal.span {f} := by
  obtain ⟨c₁, hc₁⟩ := GlobalTheory.CompanionTheory.ComplVal.side t hu f f' a b (c + E₁ * s * t) E₁ N h₁ hab
    (by linear_combination -E₁ * hs - hc)
  obtain ⟨c₂, hc₂⟩ := GlobalTheory.CompanionTheory.ComplVal.side t hu f' f b a (c' + E₂ * s' * t) E₂ N h₂
    (by linear_combination hab) (by linear_combination -E₂ * hs' - hc')
  have hP : (1 - E₁) * (1 - E₁) = 1 - E₁ := by linear_combination h₁
  have hQ : (1 - E₂) * (1 - E₂) = 1 - E₂ := by linear_combination h₂
  have hA : (1 - E₁) * f = (1 - E₁) * F * (1 + t * (s * d)) := by
    linear_combination -(1 - E₁) * hs - s * t ^ (N + 2) * h₁ - s * t * (1 - E₁) * hd
  have hB : (1 - E₂) * f' = (1 - E₂) * F' * (1 + t * (s' * d')) := by
    linear_combination -(1 - E₂) * hs' - s' * t ^ (N + 2) * h₂ - s' * t * (1 - E₂) * hd'
  obtain ⟨u₁, hu₁⟩ := (hu (s' * d')).exists_right_inv
  obtain ⟨u₂, hu₂⟩ := (hu (s * d)).exists_right_inv
  obtain ⟨c₃, hc₃⟩ := GlobalTheory.CompanionTheory.ComplVal.mid (1 - E₁) (1 - E₂) E f F f' F' k (1 + t * (s * d))
    (1 + t * (s' * d')) u₁ hP hQ hA hB hu₁ hk
  obtain ⟨c₄, hc₄⟩ := GlobalTheory.CompanionTheory.ComplVal.mid (1 - E₂) (1 - E₁) (1 - E) f' F' f F k' (1 + t * (s' * d'))
    (1 + t * (s * d)) u₂ hQ hP hB hA hu₂ (by linear_combination hk')
  refine ⟨E₁ + (1 - E₁) * (1 - E₂) * E, ?_, ?_, ?_⟩
  · show (E₁ + (1 - E₁) * (1 - E₂) * E) * (E₁ + (1 - E₁) * (1 - E₂) * E) = E₁ + (1 - E₁) * (1 - E₂) * E
    linear_combination (1 - 2 * (1 - E₂) * E + (1 - E₂) ^ 2 * E ^ 2) * h₁ + (1 - E₁) * E ^ 2 * h₂
      + (1 - E₁) * (1 - E₂) * hE
  · exact Ideal.mem_span_singleton'.2 ⟨c₁ + c₃, by linear_combination hc₁ + hc₃⟩
  · exact Ideal.mem_span_singleton'.2 ⟨(1 - E₁) * c₂ + c₄, by linear_combination (1 - E₁) * hc₂ + hc₄⟩

theorem compl_val : ∀ (B : Type) [CommRing B] (T : Type) [CommRing T] (π : B) (g : B →+* T), CrystallineSemistableComparison.D.IsCompl π g → VAL π → VAL (g π) := by
  intro B _ T _ π g hC hV
  unfold CrystallineSemistableComparison.D.VAL at hV ⊢
  have := hC.compl
  have hJ : g π ∈ (⊥ : Ideal T).jacobson :=
    IsAdicComplete.le_jacobson_bot (I := Ideal.span {g π}) (Ideal.mem_span_singleton_self (g π))
  have hu : ∀ x : T, IsUnit (1 + g π * x) := fun x => by
    rw [add_comm]; exact Ideal.mem_jacobson_bot.1 hJ x
  intro f₀ f₁ hN
  obtain ⟨N, hN⟩ := hN
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 hN
  obtain ⟨x₁, hx₁⟩ := hC.surj (N + 2) f₀
  obtain ⟨x₂, hx₂⟩ := hC.surj (N + 2) f₁
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.1 hx₁
  obtain ⟨s', hs'⟩ := Ideal.mem_span_singleton'.1 hx₂
  obtain ⟨e₁, he₁, h1a, h1b⟩ := hV x₁ (π ^ (N + 1)) ⟨N + 1, Ideal.mem_span_pair.2 ⟨0, 1, by ring⟩⟩
  obtain ⟨e₂, he₂, h2a, h2b⟩ := hV x₂ (π ^ (N + 1)) ⟨N + 1, Ideal.mem_span_pair.2 ⟨0, 1, by ring⟩⟩
  obtain ⟨c₀, hc₀⟩ := Ideal.mem_span_singleton'.1 h1a
  obtain ⟨d₀, hd₀⟩ := Ideal.mem_span_singleton'.1 h1b
  obtain ⟨c₁, hc₁⟩ := Ideal.mem_span_singleton'.1 h2a
  obtain ⟨d₁, hd₁⟩ := Ideal.mem_span_singleton'.1 h2b
  obtain ⟨P, hPdef⟩ : ∃ P : B, P = (1 - e₁) * (1 - e₂) := ⟨_, rfl⟩
  have hPP : P * P = P := by
    rw [hPdef]; linear_combination (1 - e₂) ^ 2 * he₁.eq + (1 - e₁) * he₂.eq
  have hPe : P * (1 - e₁) = P := by
    rw [hPdef]; linear_combination (1 - e₂) * he₁.eq
  obtain ⟨e, he, ha, hb⟩ := hV (P * x₁ + (1 - P)) (P * x₂) ⟨N + 1, Ideal.mem_span_pair.2
    ⟨P * d₀ + (1 - P) * π ^ (N + 1), 0, by
      linear_combination P * hd₀ + π ^ (N + 1) * hPe
        + (d₀ * x₁ - d₀ - π ^ (N + 1) * x₁ + π ^ (N + 1)) * hPP⟩⟩
  obtain ⟨m, hm⟩ := Ideal.mem_span_singleton'.1 ha
  obtain ⟨m', hm'⟩ := Ideal.mem_span_singleton'.1 hb
  have hkB : m * P * x₂ = (1 - e₁) * (1 - e₂) * e * x₁ := by
    linear_combination P * hm - (m * x₂ - e * x₁ + e) * hPP + e * x₁ * hPdef
  have hk'B : m' * P * x₁ = (1 - e₁) * (1 - e₂) * (1 - e) * x₂ := by
    linear_combination P * hm' - (m' * x₁ - m' - (1 - e) * x₂) * hPP + (1 - e) * x₂ * hPdef
  have i₁ : g e₁ * g e₁ = g e₁ := by rw [← map_mul, he₁.eq]
  have i₂ : g e₂ * g e₂ = g e₂ := by rw [← map_mul, he₂.eq]
  have i₃ : g e * g e = g e := by rw [← map_mul, he.eq]
  have hc : g c₀ * g π ^ (N + 1) = g e₁ * g x₁ := by
    have h := congrArg g hc₀; simp only [map_mul, map_pow] at h; linear_combination h
  have hc' : g c₁ * g π ^ (N + 1) = g e₂ * g x₂ := by
    have h := congrArg g hc₁; simp only [map_mul, map_pow] at h; linear_combination h
  have hd : g d₀ * g x₁ = (1 - g e₁) * g π ^ (N + 1) := by
    have h := congrArg g hd₀; simp only [map_mul, map_pow, map_sub, map_one] at h; linear_combination h
  have hd' : g d₁ * g x₂ = (1 - g e₂) * g π ^ (N + 1) := by
    have h := congrArg g hd₁; simp only [map_mul, map_pow, map_sub, map_one] at h; linear_combination h
  have hk : g m * g P * g x₂ = (1 - g e₁) * (1 - g e₂) * g e * g x₁ := by
    have h := congrArg g hkB; simp only [map_mul, map_sub, map_one] at h; linear_combination h
  have hk' : g m' * g P * g x₁ = (1 - g e₁) * (1 - g e₂) * (1 - g e) * g x₂ := by
    have h := congrArg g hk'B; simp only [map_mul, map_sub, map_one] at h; linear_combination h
  exact GlobalTheory.CompanionTheory.ComplVal.core (g π) hu f₀ f₁ (g x₁) (g x₂) a b s s' (g c₀) (g c₁) (g d₀) (g d₁)
    (g m * g P) (g m' * g P) (g e₁) (g e₂) (g e) N i₁ i₂ i₃ hab hs hs' hc hc' hd hd' hk hk'

end GlobalTheory.CompanionTheory.ComplVal
