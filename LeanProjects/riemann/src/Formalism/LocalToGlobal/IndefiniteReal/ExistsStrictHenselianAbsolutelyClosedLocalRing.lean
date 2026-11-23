import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.AllPartsTransfer
import Lemmata.RankOneOrbitForms.RankOneForm

open Module NumberField

noncomputable section

namespace Formalism.IndefR.LatticeTransfer

open Formalism.IndefR.TransferLatticeStatement

namespace NormTraceLemmas

section Lin

variable {K : Type} [Field K] {G : Type} [Group G]
  {T : Type} [AddCommGroup T] [Module K T] [FiniteDimensional K T]

theorem exists_strictHenselian_absolutely_closed_local_ring (τ : Representation K G T)
    (hirr : ∀ W : Submodule K T, (∀ g : G, ∀ w ∈ W, τ g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (ε₀ ε : T →ₗ[K] T) (h1 : finrank K (LinearMap.range ε₀) = 1) :
    ∃ (γ δ : Fin (finrank K (LinearMap.range ε)) → G)
      (c : Matrix (Fin (finrank K (LinearMap.range ε))) (Fin (finrank K (LinearMap.range ε))) K),
      c.det ≠ 0 ∧
      (∀ i j, c i j = LinearMap.trace K T (ε₀ ∘ₗ τ (δ i) ∘ₗ ε ∘ₗ τ (γ j))) ∧
      (∀ i j, ε₀ ∘ₗ τ (δ i) ∘ₗ ε ∘ₗ τ (γ j) ∘ₗ ε₀ = c i j • ε₀) ∧
      ∑ j, ∑ i, c⁻¹ j i • (ε ∘ₗ τ (γ j) ∘ₗ ε₀ ∘ₗ τ (δ i) ∘ₗ ε) = ε := by
  first | exact Bl.RankOneOrbitForms.goal1 .. | (apply Bl.RankOneOrbitForms.goal1 <;> assumption) | (intros; apply Bl.RankOneOrbitForms.goal1 <;> assumption)

end Lin

section Char

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]
  {T : Type} [AddCommGroup T] [Module K T] [FiniteDimensional K T]

open Classical in

theorem trace_formula (τ : Representation K G T) (H₀ H : Subgroup G) (χ₀ : H₀ →* (𝓞 K)ˣ)
    (χ : H →* (𝓞 K)ˣ) (a b : G) :
    LinearMap.trace K T (epP H₀ χ₀ τ ∘ₗ τ a ∘ₗ epP H χ τ ∘ₗ τ b) =
      ((Nat.card H₀ : K)⁻¹ * (Nat.card H : K)⁻¹) *
        ∑ h₀ : H₀, ∑ h : H, ((((χ₀ h₀⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) *
          (((χ h⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K)) * charOf τ ((h₀ : G) * a * h * b) := by
  simp only [← Module.End.mul_eq_comp, epP, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, map_smul, map_sum, smul_eq_mul, ← map_mul, charOf, mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h₀ _ => Finset.sum_congr rfl fun h _ => ?_
  rw [map_mul (algebraMap (𝓞 K) K)]
  ring

theorem norm_chi (H : Subgroup G) [Finite H] (χ : H →* (𝓞 K)ˣ) (h : H) (σ : K →+* ℂ) :
    ‖σ (((χ h : (𝓞 K)ˣ) : 𝓞 K) : K)‖ = 1 := by
  have hu : ((χ h : (𝓞 K)ˣ) : 𝓞 K) ^ Nat.card H = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one', map_one, Units.val_one]
  have h2 : σ (((χ h : (𝓞 K)ˣ) : 𝓞 K) : K) ^ Nat.card H = 1 := by
    have := congrArg (σ.comp (algebraMap (𝓞 K) K)) hu
    rw [map_pow, map_one] at this
    exact this
  exact Complex.norm_eq_one_of_pow_eq_one h2 Nat.card_pos.ne'

variable [NumberField K]

theorem norm_trace_le (hC : CharFacts) (τ : Representation K G T) (H₀ H : Subgroup G)
    (χ₀ : H₀ →* (𝓞 K)ˣ) (χ : H →* (𝓞 K)ˣ) (a b : G) (σ : K →+* ℂ) :
    ‖σ (LinearMap.trace K T (epP H₀ χ₀ τ ∘ₗ τ a ∘ₗ epP H χ τ ∘ₗ τ b))‖ ≤ (finrank K T : ℝ) := by
  classical
  rw [trace_formula, map_mul, norm_mul]
  have hA : ‖σ ((Nat.card H₀ : K)⁻¹ * (Nat.card H : K)⁻¹)‖ =
      (Nat.card H₀ : ℝ)⁻¹ * (Nat.card H : ℝ)⁻¹ := by
    simp [map_mul, map_inv₀, map_natCast, norm_inv]
  rw [hA]
  have hB : ‖σ (∑ h₀ : H₀, ∑ h : H, ((((χ₀ h₀⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) *
          (((χ h⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K)) * charOf τ ((h₀ : G) * a * h * b))‖ ≤
      ∑ _h₀ : H₀, ∑ _h : H, (finrank K T : ℝ) := by
    rw [map_sum]
    refine norm_sum_le_of_le _ fun h₀ _ => ?_
    rw [map_sum]
    refine norm_sum_le_of_le _ fun h _ => ?_
    rw [map_mul, map_mul, norm_mul, norm_mul, norm_chi, norm_chi, one_mul, one_mul]
    exact ((hC K G T τ _).2 σ).2
  have hpos : (0 : ℝ) ≤ (Nat.card H₀ : ℝ)⁻¹ * (Nat.card H : ℝ)⁻¹ := by positivity
  calc (Nat.card H₀ : ℝ)⁻¹ * (Nat.card H : ℝ)⁻¹ * ‖_‖ ≤
        (Nat.card H₀ : ℝ)⁻¹ * (Nat.card H : ℝ)⁻¹ * ∑ _h₀ : H₀, ∑ _h : H, (finrank K T : ℝ) :=
        mul_le_mul_of_nonneg_left hB hpos
    _ = (finrank K T : ℝ) := by
        have h0 : (Nat.card H₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
        have h1 : (Nat.card H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
        field_simp

theorem integral_mem (hC : CharFacts) (τ : Representation K G T) (H₀ H : Subgroup G)
    (χ₀ : H₀ →* (𝓞 K)ˣ) (χ : H →* (𝓞 K)ˣ) (a b : G) :
    (Fintype.card G : K) ^ 2 * LinearMap.trace K T (epP H₀ χ₀ τ ∘ₗ τ a ∘ₗ epP H χ τ ∘ₗ τ b) ∈
      integralClosure ℤ K := by
  classical
  rw [trace_formula]
  have hG0 : (Fintype.card G : K) = (Nat.card H₀ : K) * (H₀.index : K) := by
    rw [← Nat.cast_mul, Subgroup.card_mul_index, Nat.card_eq_fintype_card]
  have hG1 : (Fintype.card G : K) = (Nat.card H : K) * (H.index : K) := by
    rw [← Nat.cast_mul, Subgroup.card_mul_index, Nat.card_eq_fintype_card]
  have hsq : (Fintype.card G : K) ^ 2 =
      ((Nat.card H₀ : K) * (H₀.index : K)) * ((Nat.card H : K) * (H.index : K)) := by
    rw [sq]
    nth_rw 1 [hG0]
    rw [hG1]
  have h0 : (Nat.card H₀ : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have h1 : (Nat.card H : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [hsq, show ∀ x : K, (Nat.card H₀ : K) * (H₀.index : K) * ((Nat.card H : K) * (H.index : K)) *
      ((Nat.card H₀ : K)⁻¹ * (Nat.card H : K)⁻¹ * x) = (H₀.index : K) * (H.index : K) * x from
      fun x => by field_simp]
  refine mul_mem (mul_mem (Subalgebra.natCast_mem _ _) (Subalgebra.natCast_mem _ _))
    (Subalgebra.sum_mem _ fun h₀ _ => Subalgebra.sum_mem _ fun h _ => mul_mem (mul_mem ?_ ?_) ?_)
  · exact RingOfIntegers.isIntegral_coe _
  · exact RingOfIntegers.isIntegral_coe _
  · exact (hC K G T τ _).1

end Char

section Alg

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

open Classical in

def epA (H : Subgroup G) (χ : H →* (𝓞 K)ˣ) : MonoidAlgebra K G :=
  ((Nat.card H : ℕ) : K)⁻¹ •
    ∑ h : H, MonoidAlgebra.single (h : G) ((((χ h⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K))

theorem asAlg_epA (H : Subgroup G) (χ : H →* (𝓞 K)ˣ) {V : Type} [AddCommGroup V] [Module K V]
    (ρ : Representation K G V) : ρ.asAlgebraHom (epA H χ) = epP H χ ρ := by
  simp only [epA, epP, map_smul, map_sum, Representation.asAlgebraHom_single]

def eA {T : Type} [AddCommGroup T] [Module K T] (τ : Representation K G T) : MonoidAlgebra K G :=
  (charOf τ 1 / (Fintype.card G : K)) • ∑ x : G, MonoidAlgebra.single x (charOf τ x⁻¹)

theorem asAlg_eA {T : Type} [AddCommGroup T] [Module K T] (τ : Representation K G T)
    {V : Type} [AddCommGroup V] [Module K V] (ρ : Representation K G V) :
    ρ.asAlgebraHom (eA τ) = eS τ ρ := by
  simp only [eA, eS, map_smul, map_sum, Representation.asAlgebraHom_single]

end Alg

end NormTraceLemmas

open NormTraceLemmas in

theorem core_of (hC : CharFacts) (hK : KeyZero) (hS : Schur) (hP : IdemP) : Core := by
  intro K _ _ G _ _ S T _ _ _ τ H₀ χ₀ H χ hgood hM1 s
  obtain ⟨γ, δ, c, hdet, htr, he1, he2⟩ :=
    exists_strictHenselian_absolutely_closed_local_ring (τ s) (hgood.2.1 s) (epP H₀ χ₀ (τ s)) (epP H χ (τ s)) (hM1 s)
  refine ⟨γ, δ, c, fun i j => ⟨(Fintype.card G : K) ^ 2 * c i j, ?_⟩, hdet, fun i j => rfl, ?_, ?_⟩
  · rw [htr i j]
    exact integral_mem hC (τ s) H₀ H χ₀ χ (δ i) (γ j)
  · intro i j σ
    rw [htr i j]
    exact norm_trace_le hC (τ s) H₀ H χ₀ χ (δ i) (γ j) σ
  · intro V _ _ ρ
    let _ : Module (𝓞 K) V := Module.compHom V (algebraMap (𝓞 K) K)
    have : IsScalarTower (𝓞 K) K V := ⟨fun x y v => by
      change (x • y) • v = (algebraMap (𝓞 K) K x) • (y • v)
      rw [Algebra.smul_def, mul_smul]⟩
    obtain ⟨hPe, hPε⟩ := hP K G V ρ
    obtain ⟨hcg, hcε, -⟩ := hPe (T s) (τ s)
    have ce_g : ∀ g x, eS (τ s) ρ (ρ g x) = ρ g (eS (τ s) ρ x) :=
      fun g x => LinearMap.congr_fun (hcg g) x
    have ce₀ : ∀ x, eS (τ s) ρ (epP H₀ χ₀ ρ x) = epP H₀ χ₀ ρ (eS (τ s) ρ x) :=
      fun x => LinearMap.congr_fun (hcε H₀ χ₀) x
    have ce : ∀ x, eS (τ s) ρ (epP H χ ρ x) = epP H χ ρ (eS (τ s) ρ x) :=
      fun x => LinearMap.congr_fun (hcε H χ) x
    have ii₀ : ∀ x, epP H₀ χ₀ ρ (epP H₀ χ₀ ρ x) = epP H₀ χ₀ ρ x :=
      fun x => LinearMap.congr_fun (hPε H₀ χ₀).1 x
    have ii : ∀ x, epP H χ ρ (epP H χ ρ x) = epP H χ ρ x :=
      fun x => LinearMap.congr_fun (hPε H χ).1 x
    have hee : ∀ x, eS (τ s) ρ (eS (τ s) ρ x) = eS (τ s) ρ x := by
      intro x
      have h0 : (τ s).asAlgebraHom (eA (τ s) - 1) = 0 := by
        rw [map_sub, asAlg_eA, (hS K G S T τ hgood).1 s, map_one, Module.End.one_eq_id, sub_self]
      have := LinearMap.congr_fun (hK K G (T s) (τ s) V ρ _ h0) x
      simp only [LinearMap.comp_apply, map_sub, asAlg_eA, map_one, LinearMap.sub_apply,
        Module.End.one_apply, LinearMap.zero_apply, sub_eq_zero] at this
      exact this
    constructor
    · intro i j a ha
      have ea : eS (τ s) ρ a = a := by
        calc eS (τ s) ρ a = eS (τ s) ρ (epP H₀ χ₀ ρ (eS (τ s) ρ a)) := by rw [ha]
          _ = a := by rw [ce₀, hee, ha]
      have e0a : epP H₀ χ₀ ρ a = a := by
        calc epP H₀ χ₀ ρ a = epP H₀ χ₀ ρ (epP H₀ χ₀ ρ (eS (τ s) ρ a)) := by rw [ha]
          _ = a := by rw [ii₀, ha]
      have hx : (τ s).asAlgebraHom (epA H₀ χ₀ * MonoidAlgebra.of K G (δ i) * epA H χ *
          MonoidAlgebra.of K G (γ j) * epA H₀ χ₀ - c i j • epA H₀ χ₀) = 0 := by
        simp only [map_sub, map_mul, map_smul, asAlg_epA, Representation.asAlgebraHom_of,
          Module.End.mul_eq_comp, LinearMap.comp_assoc]
        rw [he1 i j, sub_self]
      have := LinearMap.congr_fun (hK K G (T s) (τ s) V ρ _ hx) a
      simp only [LinearMap.comp_apply, map_sub, map_mul, map_smul, asAlg_epA,
        Representation.asAlgebraHom_of, LinearMap.sub_apply, Module.End.mul_apply,
        LinearMap.smul_apply, LinearMap.zero_apply, ce₀, ce_g, ce, ea, e0a, sub_eq_zero] at this
      exact this
    · intro a ha
      have ea : eS (τ s) ρ a = a := by
        calc eS (τ s) ρ a = eS (τ s) ρ (epP H χ ρ (eS (τ s) ρ a)) := by rw [ha]
          _ = a := by rw [ce, hee, ha]
      have Ea : epP H χ ρ a = a := by
        calc epP H χ ρ a = epP H χ ρ (epP H χ ρ (eS (τ s) ρ a)) := by rw [ha]
          _ = a := by rw [ii, ha]
      have hy : (τ s).asAlgebraHom (∑ j, ∑ i, c⁻¹ j i • (epA H χ * MonoidAlgebra.of K G (γ j) *
          epA H₀ χ₀ * MonoidAlgebra.of K G (δ i) * epA H χ) - epA H χ) = 0 := by
        simp only [map_sub, map_sum, map_mul, map_smul, asAlg_epA, Representation.asAlgebraHom_of,
          Module.End.mul_eq_comp, LinearMap.comp_assoc]
        rw [he2, sub_self]
      have := LinearMap.congr_fun (hK K G (T s) (τ s) V ρ _ hy) a
      simp only [LinearMap.comp_apply, map_sub, map_sum, map_mul, map_smul, asAlg_epA,
        Representation.asAlgebraHom_of, LinearMap.sub_apply, LinearMap.sum_apply,
        Module.End.mul_apply, LinearMap.smul_apply, LinearMap.zero_apply, ce₀, ce_g, ce, ea, Ea,
        sub_eq_zero] at this
      exact this

end Formalism.IndefR.LatticeTransfer
