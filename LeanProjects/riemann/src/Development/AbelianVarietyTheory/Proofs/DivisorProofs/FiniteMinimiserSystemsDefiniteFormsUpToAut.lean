import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMinimiserSystemsSmoothConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosCombinationSmoothConeSymmIntFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntBilinFormToRealMemPsdConeOfPosStatement
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc.MinSysType

theorem finite_minimiser_systems_upTo_aut : ∀ (g : ℕ) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), PosW W →
    ∀ (N : ℕ) [NeZero N], 3 ≤ N → ∀ r : ℕ, r ≤ g → ∃ S : Finset ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)),
    ∀ b : LinearMap.BilinForm ℤ (Fin r → ℤ), (∀ x y, b x y = b y x) → (∀ x, x ≠ 0 → 0 < b x x) →
    ∃ e : (Fin r → ℤ) ≃ₗ[ℤ] (Fin r → ℤ), ∀ μ' : ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)),
    (∀ c u i, ((μ' c u i : ℤ) : ZMod N) = c u i) →
    (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod N) = c u i) →
      qW W (pull e.toLinearMap b) (μ' c) ≤ qW W (pull e.toLinearMap b) α) → μ' ∈ S := by
  intro g φ hφ W hW N _ hN r hr
  classical
  have hX : IsPolFanOn id φ (Fin r → ℤ) := hφ (Fin r → ℤ) (by simpa using hr)
  obtain ⟨S₀, hS₀, hfin⟩ := hX.finite
  set F := hS₀.toFinset with hF
  let ι := Σ m : Fin (F.card + 1), (Fin m.val → F)
  let P : ι → Prop := fun i => IsCone id φ (fun j => ((i.2 j : F) : LinearMap.BilinForm ℤ (Fin r → ℤ))) ∧
    ∀ x, x ≠ 0 → 0 < ∑ j, ((i.2 j : F) : LinearMap.BilinForm ℤ (Fin r → ℤ)) x x
  let T : ι → Finset ((Fin 8 → Fin r → ZMod N) → (Fin 8 → Fin r → ℤ)) := fun i =>
    if h : P i then Classical.choose (GlobalTheory.T.finite_minimiser_systems_smooth_cone φ W hW N hN r i.1.val _ h.1 h.2) else ∅
  refine ⟨Finset.univ.biUnion T, ?_⟩
  intro b hsym hpos
  have hpsd := GlobalTheory.T.intBilinFormToReal_mem_psdCone_of_pos r b hsym hpos
  obtain ⟨m, γ, cf, hcone, hcf, hb⟩ := GlobalTheory.T.exists_pos_combination_smoothCone_symmIntForm g φ hφ r hr b hsym hpsd
  obtain ⟨e, he⟩ := hfin m γ hcone
  refine ⟨e, fun μ' h1 h2 => ?_⟩
  let γ' : Fin m → F := fun j => ⟨pull e.toLinearMap (γ j), hS₀.mem_toFinset.2 (he j)⟩
  have hcone' := hcone.pull_equiv e
  have hinj : Function.Injective γ' := fun j k hjk => by
    have h := congrArg Subtype.val hjk
    simp only [γ'] at h
    exact hcone'.injective h
  have hm : m < F.card + 1 := by
    have := Fintype.card_le_of_injective γ' hinj
    simp only [Fintype.card_fin, Fintype.card_coe] at this
    omega
  let i : ι := ⟨⟨m, hm⟩, γ'⟩
  have hbyy : ∀ y, b y y = ∑ j, (cf j : ℤ) * γ j y y := fun y => by
    rw [hb]; simp [LinearMap.sum_apply]
  have hPi : P i := by
    refine ⟨hcone', fun x hx => ?_⟩
    simp only [i, γ', pull_apply]
    have hex : e x ≠ 0 := by simpa using hx
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ γ j (e x) (e x) := fun j _ => hcone.nonneg j _
    refine lt_of_le_of_ne (Finset.sum_nonneg hnn) fun h0 => ?_
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0.symm
    have := hpos _ hex
    rw [hbyy] at this
    simp [hz] at this
  have hmem : μ' ∈ T i := by
    simp only [T, dif_pos hPi]
    refine Classical.choose_spec (GlobalTheory.T.finite_minimiser_systems_smooth_cone φ W hW N hN r i.1.val _ hPi.1 hPi.2) (pull e.toLinearMap b) 1 cf
      one_pos hcf ?_ μ' h1 h2
    ext a c
    simp [i, γ', pull_apply, hb, LinearMap.sum_apply]
  exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hmem⟩

end GlobalTheory.Poinc.MinSysType
