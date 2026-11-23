import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PieceEqPieceT

noncomputable section

open GlobalTheory.KummerEisensteinGalois Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois

theorem glFibre_val_map {p n : ℕ} [NeZero p] (x : ZMod (p ^ (n + 1))) :
    (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) x).val = x.val % p ^ n := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]

theorem glFibre_isUnit_iff {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : 1 ≤ n) (x : ZMod (p ^ n)) :
    IsUnit x ↔ ¬ p ∣ x.val := by
  have hp : p.Prime := Fact.out
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm,
    hp.coprime_iff_not_dvd]

theorem glFibre_dvd_map_iff {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : 1 ≤ n) (x : ZMod (p ^ (n + 1))) :
    p ∣ (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) x).val ↔ p ∣ x.val := by
  rw [glFibre_val_map, Nat.dvd_mod_iff (dvd_pow_self p (by omega))]

theorem sum_unitSet_succ_fibre : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (K : Type) [CommRing K] (G : GL (Fin 2) (ZMod (p ^ n)) → K) (Φ : ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → K), 1 ≤ n → ∑ γ ∈ unitSet p (n + 1), G (Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ) * Φ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 1) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 1) = ∑ γ ∈ unitSet p n, G γ * ∑ y₀₀ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0)), ∑ y₀₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 1)), ∑ y₁₀ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0)), ∑ y₁₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 1)), Φ y₀₀ y₀₁ y₁₀ y₁₁ := by
  intro p _ n K _ G Φ hn
  set ρ := ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) with hρ
  have hent : ∀ (γ : GL (Fin 2) (ZMod (p ^ (n + 1)))) (a b : Fin 2),
      (Matrix.GeneralLinearGroup.map ρ γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) a b =
        ρ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) a b) := fun _ _ _ => rfl
  have hmaps : ∀ γ ∈ unitSet p (n + 1), Matrix.GeneralLinearGroup.map ρ γ ∈ unitSet p n := by
    intro γ hγ
    simp only [unitSet, mem_filter, mem_univ, true_and] at hγ ⊢
    rw [hent, hent, hρ, glFibre_dvd_map_iff hn, glFibre_dvd_map_iff hn]
    exact hγ
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl (fun g hg => ?_)
  rw [Finset.sum_congr rfl (fun γ hγ => by rw [(mem_filter.mp hγ).2]), ← Finset.mul_sum]
  congr 1
  simp only [← Finset.sum_product']
  refine Finset.sum_bij (fun γ _ => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 0),
      ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 1),
      ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 0),
      ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 1))) ?_ ?_ ?_ ?_
  · intro γ hγ
    obtain ⟨_, hγg⟩ := mem_filter.mp hγ
    simp only [mem_product, mem_filter, mem_univ, true_and, ← hγg, hent, and_self]
  · intro γ _ δ _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    ext a b
    fin_cases a <;> fin_cases b
    exacts [h1, h2, h3, h4]
  · rintro ⟨a, b, c, d⟩ hb
    simp only [mem_product, mem_filter, mem_univ, true_and] at hb
    obtain ⟨ha, hb', hc, hd⟩ := hb
    let B : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1))) := !![a, b; c, d]
    have hBm : ρ.mapMatrix B = (g : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) := by
      ext i j
      fin_cases i <;> fin_cases j
      exacts [ha, hb', hc, hd]
    have hdet : IsUnit B.det := by
      have h1 : IsUnit (ρ B.det) := by
        rw [RingHom.map_det, hBm]; exact (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
      rw [glFibre_isUnit_iff hn, hρ, glFibre_dvd_map_iff hn] at h1
      exact (glFibre_isUnit_iff (by omega) _).mpr h1
    obtain ⟨γ, hγ⟩ := (Matrix.isUnit_iff_isUnit_det B).mpr hdet
    have hmap : Matrix.GeneralLinearGroup.map ρ γ = g := by
      apply Units.ext
      rw [← hBm, ← hγ]; rfl
    refine ⟨γ, ?_, ?_⟩
    · refine mem_filter.mpr ⟨?_, hmap⟩
      simp only [unitSet, mem_filter, mem_univ, true_and] at hg ⊢
      rw [← glFibre_dvd_map_iff hn, ← glFibre_dvd_map_iff hn, ← hρ, ← hent, ← hent, hmap]
      exact hg
    · simp only [hγ, B]
      rfl
  · intro γ _
    rfl

end GlobalTheory.KummerEisensteinGalois
