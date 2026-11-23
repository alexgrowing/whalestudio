import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MinkowskiWeylOrthantConeIntegralConstraints

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem exists_nat_comb_of_toReal_mem_rcone (X : Type) [AddCommGroup X] (m : ℕ)
    (γ : Fin m → LinearMap.BilinForm ℤ X) (β : LinearMap.BilinForm ℤ X) (hβ : toReal β ∈ rcone γ) :
    ∃ (k : ℕ) (c : Fin m → ℕ), 0 < k ∧ k • β = ∑ i, c i • γ i := by
  obtain ⟨t, ht0, ht⟩ := hβ
  let vec : X × X → Fin (m + 1) → ℤ := fun p =>
    Fin.snoc (α := fun _ => ℤ) (fun i => γ i p.1 p.2) (-(β p.1 p.2))
  obtain ⟨r, v, hreal, -⟩ :=
    GlobalTheory.MinkWeylReal.cone_orthant_fg (m + 1) ∅ (Set.range vec) Set.finite_empty
  let T : Fin (m + 1) → ℝ := Fin.snoc (α := fun _ => ℝ) t 1
  have hpt : ∀ y z : X, (β y z : ℝ) = ∑ i, t i * (γ i y z : ℝ) := by
    intro y z
    have h := LinearMap.congr_fun (LinearMap.congr_fun ht y) z
    simpa [toReal, LinearMap.sum_apply] using h
  have hT : (∀ i, 0 ≤ T i) ∧ (∀ a ∈ (∅ : Set (Fin (m + 1) → ℤ)), ∑ i, (a i : ℝ) * T i ≤ 0) ∧
      (∀ b ∈ Set.range vec, ∑ i, (b i : ℝ) * T i = 0) := by
    refine ⟨fun i => ?_, fun a ha => absurd ha (Set.notMem_empty a), ?_⟩
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [T]
      · simpa [T] using ht0 j
    · rintro _ ⟨⟨y, z⟩, rfl⟩
      rw [Fin.sum_univ_castSucc]
      simp only [vec, T, Fin.snoc_castSucc, Fin.snoc_last]
      have h2 : ∑ x, ((γ x y z : ℤ) : ℝ) * t x = ∑ i, t i * (γ i y z : ℝ) :=
        Finset.sum_congr rfl fun i _ => mul_comm _ _
      have h3 := hpt y z
      push_cast
      linarith
  obtain ⟨c, hc0, hTc⟩ := (hreal T).1 hT
  have hlast : (1 : ℝ) = ∑ k, c k * (v k (Fin.last m) : ℝ) := by
    have h := congrFun hTc (Fin.last m)
    simpa [T, Finset.sum_apply] using h
  have hex : ∃ k, 0 < v k (Fin.last m) := by
    by_contra hno
    push_neg at hno
    have : ∑ k, c k * (v k (Fin.last m) : ℝ) = 0 :=
      Finset.sum_eq_zero fun k _ => by
        have : v k (Fin.last m) = 0 := Nat.le_zero.1 (hno k)
        simp [this]
    rw [this] at hlast
    exact one_ne_zero hlast
  obtain ⟨k, hk⟩ := hex
  have hv := (hreal (fun i => (v k i : ℝ))).2
    ⟨Pi.single k 1, fun j => by
      by_cases h : j = k
      · subst h; simp
      · simp [Pi.single_eq_of_ne h], by
      rw [Finset.sum_eq_single k (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
      simp⟩
  refine ⟨v k (Fin.last m), fun i => v k i.castSucc, hk, ?_⟩
  refine LinearMap.ext₂ fun y z => ?_
  have h := hv.2.2 (vec (y, z)) ⟨(y, z), rfl⟩
  rw [Fin.sum_univ_castSucc] at h
  simp only [vec, Fin.snoc_castSucc, Fin.snoc_last] at h
  have h' : ∑ i, γ i y z * (v k i.castSucc : ℤ) + -(β y z) * (v k (Fin.last m) : ℤ) = 0 := by
    exact_mod_cast h
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul]
  push_cast
  have h2 : ∑ i, (v k i.castSucc : ℤ) * γ i y z = ∑ i, γ i y z * (v k i.castSucc : ℤ) :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [h2]
  linarith

end GlobalTheory.CompanionTheory.Ar.Fan
