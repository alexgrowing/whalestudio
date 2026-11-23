import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsSmoothCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DicksonExistsFiniteSubfamilyBelow
open GlobalTheory.PolFan GlobalTheory.LocM

noncomputable section

namespace GlobalTheory.Poinc.MinSysLat

theorem finite_of_pos_lat {Y : Type} [AddCommGroup Y] {n : ℕ} (eb : Y ≃ₗ[ℤ] (Fin n → ℤ))
    (G : LinearMap.BilinForm ℤ Y) (hs : ∀ a b, G a b = G b a)
    (hn : ∀ x, 0 ≤ G x x) (hp : ∀ x, x ≠ 0 → 0 < G x x) (B : ℤ) : {x | G x x ≤ B}.Finite := by
  set G' : LinearMap.BilinForm ℤ (Fin n → ℤ) :=
    LinearMap.compl₁₂ G eb.symm.toLinearMap eb.symm.toLinearMap with hG'
  have happ : ∀ a b, G' a b = G (eb.symm a) (eb.symm b) := fun a b => rfl
  have h := GlobalTheory.Poinc.MinSys.finite_of_pos G' (fun a b => by rw [happ, happ, hs])
    (fun x => by rw [happ]; exact hn _)
    (fun x hx => by rw [happ]; exact hp _ (by simpa using hx)) B
  refine (h.preimage eb.injective.injOn).subset fun x hx => ?_
  simp only [Set.mem_preimage, Set.mem_setOf_eq, happ, LinearEquiv.symm_apply_apply]
  exact hx

theorem finite_minimiser_systems_lat : ∀ (Y : Type) [AddCommGroup Y] (n N : ℕ) [NeZero N] (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ Y), (∀ j x y, γ j x y = γ j y x) → (∀ j y, 0 ≤ γ j y y) → (∀ x, x ≠ 0 → 0 < ∑ j, γ j x x) → ∃ S : Finset ((Fin n → ZMod N) → Y), ∀ (b : LinearMap.BilinForm ℤ Y) (k : ℕ) (cf : Fin m → ℕ), 0 < k → (∀ j, 0 < cf j) → k • b = ∑ j, cf j • γ j → ∀ μ : (Fin n → ZMod N) → Y, (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) → (∀ cl (α : Y), (∀ i, ((eb α i : ℤ) : ZMod N) = cl i) → b (μ cl) (μ cl) ≤ b α α) → μ ∈ S := by
  intro Y _ n N _ eb m γ hsym hnn hdef
  classical
  set G : LinearMap.BilinForm ℤ Y := ∑ j, γ j with hG
  have hGapp : ∀ a b, G a b = ∑ j, γ j a b := fun a b => by simp [hG, LinearMap.sum_apply]
  have hGsym : ∀ a b, G a b = G b a := fun a b => by simp only [hGapp, hsym _ a b]
  have hGnn : ∀ y, 0 ≤ G y y := fun y => by rw [hGapp]; exact Finset.sum_nonneg fun j _ => hnn j y
  have hGpos : ∀ x, x ≠ 0 → 0 < G x x := fun x hx => by rw [hGapp]; exact hdef x hx
  let T : (Fin n → ZMod N) → Type := fun c =>
    {α : Y // ∀ i, ((eb α i : ℤ) : ZMod N) = c i}
  have hD : ∀ c, ∃ F : Finset (T c), ∀ α : T c, ∃ β ∈ F,
      (fun j => (γ j β.1 β.1).toNat) ≤ (fun j => (γ j α.1 α.1).toNat) :=
    fun c => GlobalTheory.dickson_finite_below_every m (fun (α : T c) j => (γ j α.1 α.1).toNat)
  choose F hF using hD
  let Bd : (Fin n → ZMod N) → ℤ := fun c => ∑ β ∈ F c, G β.1 β.1
  have hfin : {μ : (Fin n → ZMod N) → Y | ∀ c, μ c ∈ {α | G α α ≤ Bd c}}.Finite :=
    Set.Finite.pi' fun c => finite_of_pos_lat eb G hGsym hGnn hGpos (Bd c)
  refine ⟨hfin.toFinset, fun b k cf hk hcf hkb μ hμ hmin => ?_⟩
  simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  intro c
  obtain ⟨β, hβF, hβ⟩ := hF c ⟨μ c, hμ c⟩
  have hle : ∀ j, γ j β.1 β.1 ≤ γ j (μ c) (μ c) := fun j => by
    have h1 : (γ j β.1 β.1).toNat ≤ (γ j (μ c) (μ c)).toNat := hβ j
    have := hnn j β.1
    have := hnn j (μ c)
    omega
  have hkq : ∀ α, (k : ℤ) * b α α = ∑ j, (cf j : ℤ) * γ j α α := fun α => by
    have := congrArg (fun f : LinearMap.BilinForm ℤ Y => f α α) hkb
    simpa [LinearMap.sum_apply, LinearMap.smul_apply, nsmul_eq_mul] using this
  have h2 : ∑ j, (cf j : ℤ) * γ j (μ c) (μ c) ≤ ∑ j, (cf j : ℤ) * γ j β.1 β.1 := by
    rw [← hkq, ← hkq]
    exact mul_le_mul_of_nonneg_left (hmin c β.1 β.2) (by positivity)
  have h3 : ∀ j, γ j (μ c) (μ c) - γ j β.1 β.1 ≤
      (cf j : ℤ) * γ j (μ c) (μ c) - (cf j : ℤ) * γ j β.1 β.1 := fun j => by
    have h4 := hle j
    have h5 : (1 : ℤ) ≤ cf j := by exact_mod_cast hcf j
    nlinarith
  have h6 : ∑ j, γ j (μ c) (μ c) ≤ ∑ j, γ j β.1 β.1 := by
    have h7 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => h3 j
    simp only [Finset.sum_sub_distrib] at h7
    linarith
  have h8 : G β.1 β.1 ≤ Bd c :=
    Finset.single_le_sum (f := fun β : T c => G β.1 β.1)
      (fun β _ => hGnn β.1) hβF
  rw [hGapp] at h8 ⊢
  linarith

end GlobalTheory.Poinc.MinSysLat
