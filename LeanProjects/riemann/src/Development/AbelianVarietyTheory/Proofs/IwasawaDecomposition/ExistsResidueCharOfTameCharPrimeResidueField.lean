import Mathlib
import ReciprocityTheory.GaloisValuations.Global
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootEqOfClose
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaActsOnTameRootStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharacterTameQuotientJointPowersTameGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRootOfUnityCongrUnitAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharEqOfApplyRootEqStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameCharEqOfTameRepCongrStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2

namespace GlobalTheory.TameTau

theorem tameChar_of_prime_residue : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (P : HeightOneSpectrum (𝓞 E)) (g : ℕ), g.Prime → normV P = g → ((g : ℕ) : 𝓞 E) ∈ P.asIdeal → ∀ {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (χ : G E Ω →* Oˣ), Continuous (fun g => ((χ g : Oˣ) : O)) → (∀ A : ValuationSubring Ω, IsPlaceOver A P → ∀ σ ∈ Ine (F := E) A, χ σ ^ (g - 1) = 1) → ∃ τ : (ZMod g)ˣ →* Oˣ, ∀ (x : (ZMod g)ˣ) (u : 𝓞 E), (((x : ZMod g).val : 𝓞 E) - u) ∈ P.asIdeal → τ x = NX.tameVal χ P 1 u := by
  intro E Ω _ _ _ _ _ P g hg hN hgP O _ _ _ _ _ hadic χ hχc hχI
  have : NeZero g := ⟨hg.ne_zero⟩
  have : Fact (1 < g) := ⟨hg.one_lt⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  set m := g - 1 with hm_def
  have hm0 : 0 < m := by have := hg.two_le; omega
  have hPtop : P.asIdeal ≠ ⊤ := P.isPrime.ne_top
  have hmP : ((m : ℕ) : 𝓞 E) ∉ P.asIdeal := by
    intro h
    apply hPtop
    rw [Ideal.eq_top_iff_one]
    have h1 : ((g : ℕ) : 𝓞 E) = (m : 𝓞 E) + 1 := by
      have : g = m + 1 := by have := hg.two_le; omega
      rw [this]; push_cast; ring
    have := P.asIdeal.sub_mem hgP h
    rwa [h1, add_sub_cancel_left] at this
  have hNm : normV P - 1 = m := by rw [hN]
  obtain ⟨ϖ, hϖ, hϖ2⟩ : ∃ ϖ : 𝓞 E, ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 := by
    have hlt : P.asIdeal ^ (1 + 1) < P.asIdeal ^ 1 := Ideal.pow_succ_lt_pow P.ne_bot 1
    rw [pow_one] at hlt
    exact SetLike.exists_of_lt hlt
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω (ϖ : E)) hm0
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hm0.ne', eq_comm, map_eq_zero_iff _ (algebraMap E Ω).injective] at hπ
    have hϖ0 : ϖ = 0 := by exact_mod_cast hπ
    exact hϖ2 (hϖ0 ▸ Ideal.zero_mem _)
  obtain ⟨A₀, hA₀⟩ := exists_isPlaceOver Ω P
  have hvm : ¬ A₀.valuation (m : Ω) < 1 := by
    intro h; apply hmP; rw [← hA₀]; simpa using h
  have hex : ∀ u : 𝓞 E, u ∉ P.asIdeal → ∃ σ : G E Ω, σ ∈ Ine (F := E) A₀ ∧ ∃ ζ : Ω, ζ ^ m = 1 ∧
      A₀.valuation (ζ - algebraMap E Ω (u : E)) < 1 ∧ σ π = ζ * π := by
    intro u hu
    obtain ⟨ζ, hζ, hζu⟩ := GlobalTheory.T.exists_rootOfUnity_congr_unit_at_place A₀ P hA₀ u hu
    rw [hNm] at hζ
    obtain ⟨σ, hσ, hσπ⟩ := GlobalTheory.T.inertia_acts_on_tame_root A₀ P hA₀ m hm0 hmP ϖ hϖ hϖ2 π hπ ζ hζ
    exact ⟨σ, hσ, ζ, hζ, hζu, hσπ⟩
  have hrep : ∀ σ ∈ Ine (F := E) A₀, ∀ u : 𝓞 E, A₀.valuation (σ π / π - algebraMap E Ω (u : E)) < 1 →
      NX.TameRep P 1 σ u := by
    intro σ hσ u h
    refine ⟨A₀, hA₀, hσ, ϖ, π, hϖ, hϖ2, by rw [hNm]; exact hπ, ?_⟩
    rw [zpow_one]; exact h
  have hkey : ∀ (σ : G E Ω) (u : 𝓞 E), NX.TameRep P 1 σ u → NX.tameVal χ P 1 u = χ σ := by
    intro σ u h
    rw [NX.tameVal, dif_pos ⟨σ, h⟩]
    exact GlobalTheory.T.tameChar_eq_of_tameRep_congr P hadic χ hχc (by rw [hNm]; exact hm0) (by rw [hNm]; exact hmP)
      (by intro A hA σ' hσ'; rw [hNm]; exact hχI A hA σ' hσ') _ σ u u (⟨σ, h⟩ : ∃ σ, NX.TameRep P 1 σ u).choose_spec h (by simp)
  have hlt : ∀ a b : Ω, A₀.valuation a ≤ 1 → A₀.valuation b < 1 → A₀.valuation (a * b) < 1 := by
    intro a b ha hb
    rw [map_mul]
    calc A₀.valuation a * A₀.valuation b ≤ 1 * A₀.valuation b := by gcongr
      _ = A₀.valuation b := one_mul _
      _ < 1 := hb
  have hle : ∀ a b : Ω, A₀.valuation a ≤ 1 → A₀.valuation (a - b) < 1 → A₀.valuation b ≤ 1 := by
    intro a b ha hab
    have e : b = a - (a - b) := by ring
    rw [e]
    exact (Valuation.map_sub _ _ _).trans (max_le ha hab.le)
  have hP1 : ∀ w : 𝓞 E, w ∈ P.asIdeal → A₀.valuation (algebraMap E Ω (w : E)) < 1 := fun w hw => (hA₀ w).2 hw
  let U : (ZMod g)ˣ → 𝓞 E := fun x => (((x : ZMod g)).val : 𝓞 E)
  have hcong : ∀ x y : (ZMod g)ˣ, U x * U y - U (x * y) ∈ P.asIdeal := by
    intro x y
    simp only [U, Units.val_mul, ZMod.val_mul]
    have e : (((x : ZMod g).val * (y : ZMod g).val : ℕ) : 𝓞 E) =
        (g : 𝓞 E) * (((x : ZMod g).val * (y : ZMod g).val / g : ℕ) : 𝓞 E) +
          (((x : ZMod g).val * (y : ZMod g).val % g : ℕ) : 𝓞 E) := by
      exact_mod_cast (Nat.div_add_mod ((x : ZMod g).val * (y : ZMod g).val) g).symm
    rw [← Nat.cast_mul, e, add_sub_cancel_right]
    exact P.asIdeal.mul_mem_right _ hgP
  have hU1 : U 1 = 1 := by
    show (((1 : (ZMod g)ˣ) : ZMod g).val : 𝓞 E) = 1
    rw [Units.val_one, ZMod.val_one, Nat.cast_one]
  have hUP : ∀ x, U x ∉ P.asIdeal := by
    intro x hx
    have h := hcong x x⁻¹
    rw [mul_inv_cancel, hU1] at h
    apply hPtop
    rw [Ideal.eq_top_iff_one]
    have e : (1 : 𝓞 E) = U x * U x⁻¹ - (U x * U x⁻¹ - 1) := by ring
    rw [e]
    exact P.asIdeal.sub_mem (P.asIdeal.mul_mem_right _ hx) h
  choose σx hσx ζx hζx hζu hσπ using fun x => hex (U x) (hUP x)
  have hq : ∀ x, σx x π / π = ζx x := fun x => by rw [hσπ x, mul_div_cancel_right₀ _ hπ0]
  have hζ1 : ∀ x, A₀.valuation (ζx x) = 1 := fun x => valuation_eq_one_of_pow_eq_one A₀ hm0.ne' (hζx x)
  have hrepx : ∀ x, NX.TameRep P 1 (σx x) (U x) := fun x => hrep _ (hσx x) _ (by rw [hq]; exact hζu x)
  refine ⟨MonoidHom.mk' (fun x => χ (σx x)) ?_, ?_⟩
  · intro x y
    rw [← map_mul, ← hkey _ _ (hrepx (x * y))]
    refine hkey _ _ (hrep _ ((Ine (F := E) A₀).mul_mem (hσx x) (hσx y)) _ ?_)
    rw [GlobalTheory.TameTau.quot_mul (hσx x) m hvm hπ0 hπ, hq, hq]
    have e : ζx x * ζx y - algebraMap E Ω (U (x * y) : E) =
        ζx x * (ζx y - algebraMap E Ω (U y : E)) + algebraMap E Ω (U y : E) * (ζx x - algebraMap E Ω (U x : E)) +
          algebraMap E Ω ((U x * U y - U (x * y) : 𝓞 E) : E) := by
      push_cast; ring
    rw [e]
    refine Valuation.map_add_lt _ (Valuation.map_add_lt _ (hlt _ _ (hζ1 x).le (hζu y))
      (hlt _ _ (hle _ _ (hζ1 y).le (hζu y)) (hζu x))) (hP1 _ (hcong x y))
  · intro x u hxu
    show χ (σx x) = _
    refine (hkey _ _ (hrep _ (hσx x) _ ?_)).symm
    rw [hq]
    have e : ζx x - algebraMap E Ω (u : E) = (ζx x - algebraMap E Ω (U x : E)) +
        algebraMap E Ω ((U x - u : 𝓞 E) : E) := by
      push_cast; ring
    rw [e]
    exact Valuation.map_add_lt _ (hζu x) (hP1 _ hxu)

end GlobalTheory.TameTau
