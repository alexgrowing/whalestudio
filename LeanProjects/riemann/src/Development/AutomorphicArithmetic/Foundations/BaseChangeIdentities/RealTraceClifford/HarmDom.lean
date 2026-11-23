import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.ClifMod
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.DominantRearrangementProperties

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate
open PositivityTheory.RgTw (Mat)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr
open Formalism.REAL (GlRel IsWeight KHighest Cas)

private theorem mem_lo {n : ℕ} (S : Finset (Fin n)) (hS : ∀ b ∈ S, ∀ c, c ≤ b → c ∈ S) (c : Fin n) :
    c ∈ S ↔ (c : ℕ) < S.card := by
  constructor
  · intro hc
    have hsub : Finset.Iic c ⊆ S := fun b hb => hS c hc b (Finset.mem_Iic.1 hb)
    have h := Finset.card_le_card hsub
    rw [Fin.card_Iic] at h
    omega
  · intro hlt
    by_contra hc
    have hsub : S ⊆ Finset.Iio c := fun b hb => Finset.mem_Iio.2 (by
      by_contra h
      exact hc (hS b hb c (not_lt.1 h)))
    have h := Finset.card_le_card hsub
    rw [Fin.card_Iio] at h
    omega

private theorem mem_hi {n : ℕ} (S : Finset (Fin n)) (hS : ∀ b ∈ S, ∀ c, b ≤ c → c ∈ S) (c : Fin n) :
    c ∈ S ↔ n ≤ (c : ℕ) + S.card := by
  constructor
  · intro hc
    have hsub : Finset.Ici c ⊆ S := fun b hb => hS c hc b (Finset.mem_Ici.mp hb)
    have := Finset.card_le_card hsub
    rw [Fin.card_Ici] at this
    omega
  · intro hle
    by_contra hc
    have hsub : S ⊆ Finset.Ioi c := by
      intro b hb
      rw [Finset.mem_Ioi]
      by_contra hbc
      exact hc (hS b hb c (not_lt.mp hbc))
    have := Finset.card_le_card hsub
    rw [Fin.card_Ioi] at this
    have := c.isLt
    omega

private theorem harmonic_dominant_weight {n : ℕ} (lam : Fin n → ℤ) (hl : Antitone lam) (L : Fin n → ℕ) (hL : IsLev lam L) :
    Dom (muQ lam L) ∧ domC (muQ lam L - rhoV n) + rhoV n = twoL lam := by
  obtain ⟨hmono, hlev⟩ := hL
  obtain ⟨D, hD⟩ : ∃ D : Fin n → ℕ, ∀ a, D a = #{b | L b < L a} := ⟨_, fun _ => rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : Fin n → ℕ, ∀ a, U a = #{b | L a < L b} := ⟨_, fun _ => rfl⟩
  have hDlo : ∀ a c, L c < L a ↔ (c : ℕ) < D a := by
    intro a c
    have h := mem_lo (Finset.filter (fun b => L b < L a) Finset.univ)
      (fun b hb c hcb => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        exact lt_of_le_of_lt (hmono hcb) hb) c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    rw [hD]
    exact h
  have hUhi : ∀ a c, L a < L c ↔ n ≤ (c : ℕ) + U a := by
    intro a c
    have h := mem_hi (Finset.filter (fun b => L a < L b) Finset.univ)
      (fun b hb c hcb => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
        exact lt_of_lt_of_le hb (hmono hcb)) c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    rw [hU]
    exact h
  have hDa : ∀ a : Fin n, D a ≤ a := fun a => not_lt.mp (fun h => lt_irrefl _ ((hDlo a a).mpr h))
  have hUa : ∀ a : Fin n, (a : ℕ) + U a < n := fun a => not_le.mp (fun h => lt_irrefl _ ((hUhi a a).mpr h))
  let f : Fin n → Fin n := fun a => ⟨D a + (n - 1 - U a) - a, by
    have := hDa a
    have := hUa a
    omega⟩
  have hfv : ∀ a, ((f a : Fin n) : ℕ) = D a + (n - 1 - U a) - a := fun a => rfl
  have hLf : ∀ a, L (f a) = L a := by
    intro a
    rcases lt_trichotomy (L (f a)) (L a) with h | h | h
    · have h1 := (hDlo a (f a)).mp h
      rw [hfv] at h1
      have := hDa a
      have := hUa a
      omega
    · exact h
    · have h1 := (hUhi a (f a)).mp h
      rw [hfv] at h1
      have := hDa a
      have := hUa a
      omega
  have hDf : ∀ a, D (f a) = D a := by
    intro a
    rw [hD, hD, hLf]
  have hUf : ∀ a, U (f a) = U a := by
    intro a
    rw [hU, hU, hLf]
  have hinv : Function.Involutive f := by
    intro a
    apply Fin.ext
    rw [hfv (f a), hDf, hUf, hfv]
    have := hDa a
    have := hUa a
    omega
  refine ⟨fun a b hab => ?_, ?_⟩
  · have hLab := hmono hab.le
    have hlab := hl hab.le
    have hUab : U b ≤ U a := by
      rw [hU, hU]
      refine Finset.card_le_card (fun c hc => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact lt_of_le_of_lt hLab hc
    have hDab : D a ≤ D b := by
      rw [hD, hD]
      refine Finset.card_le_card (fun c hc => ?_)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      exact lt_of_lt_of_le hc hLab
    have e1 : ((lam a - lam b).toNat : ℤ) = lam a - lam b := Int.toNat_of_nonneg (by omega)
    have e2 : (((lam a - lam b).toNat : ℕ) : ℝ) = (lam a : ℝ) - lam b := by
      have h := congrArg (Int.cast : ℤ → ℝ) e1
      push_cast at h
      exact h
    refine ⟨2 * (lam a - lam b).toNat + (U a - U b) + (D b - D a), ?_⟩
    simp only [muQ, rhoU]
    rw [← hU a, ← hU b, ← hD a, ← hD b]
    push_cast [Nat.cast_sub hUab, Nat.cast_sub hDab, e2]
    ring
  · obtain ⟨y, hy⟩ : ∃ y : Wt n, ∀ a, y a = 2 * (lam a : ℝ) + rhoV n a := ⟨_, fun _ => rfl⟩
    have hyA : Antitone y := by
      intro a b hab
      rw [hy, hy]
      have h1 : (lam b : ℝ) ≤ lam a := by exact_mod_cast hl hab
      have h2 : ((a : ℕ) : ℝ) ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
      simp only [rhoV]
      linarith
    have hx : ∀ a, (muQ lam L - rhoV n) (f a) = y a := by
      intro a
      have hnat : ((f a : ℕ)) + a + 1 + U a = D a + n := by
        rw [hfv]
        have := hDa a
        have := hUa a
        omega
      have hreal : (((f a : ℕ)) : ℝ) + ((a : ℕ) : ℝ) + 1 + (U a : ℝ) = (D a : ℝ) + n := by
        exact_mod_cast hnat
      simp only [Pi.sub_apply, muQ, rhoU, rhoV]
      rw [← hU (f a), ← hD (f a), hUf, hDf, hlev _ _ (hLf a), hy]
      simp only [rhoV]
      linarith
    let w : Equiv.Perm (Fin n) := Function.Involutive.toPerm f hinv
    have hxy : muQ lam L - rhoV n = y ∘ w := by
      funext a
      have h := hx (f a)
      rw [hinv a] at h
      exact h
    have R := (rearr n).2.1 y
    rw [hxy, R.2.2.2.1 w, R.2.2.1 hyA]
    funext a
    simp only [Pi.add_apply, twoL, hy]
    ring

theorem UpperTheory.RealTr.harmDom :
    ∀ (n : ℕ) (lam : Fin n → ℤ), Antitone lam → ∀ μ ∈ harmSet lam, Dom μ ∧ domC (μ - rhoV n) + rhoV n = twoL lam := by
  intro n lam hl μ hμ
  simp only [harmSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hμ
  obtain ⟨lev, hlev, rfl⟩ := hμ
  exact harmonic_dominant_weight lam hl _ hlev
