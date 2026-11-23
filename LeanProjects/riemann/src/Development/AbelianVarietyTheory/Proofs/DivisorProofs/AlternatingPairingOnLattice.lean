import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingFormLatticeIntegralityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeFormIdealGeneratesDualVectorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeFormIdealDualVectorIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeVectorPairingOneIdealMultipleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeFormIdealPairOfVectorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealCoprimeElementExistsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AltLattice

variable {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V]

theorem exists_bilin_ext (hV : Module.finrank F V = 2) (L : Set V)
    (hLadd : ∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) (hLsmul : ∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L)
    (P : V → V → F)
    (halt : ∀ x ∈ L, ∀ x' ∈ L, P x x' = -P x' x)
    (hadd : ∀ x₁ ∈ L, ∀ x₂ ∈ L, ∀ x' ∈ L, P (x₁ + x₂) x' = P x₁ x' + P x₂ x')
    (hsmul : ∀ (a : 𝓞 F), ∀ x ∈ L, ∀ x' ∈ L, P ((a : F) • x) x' = (a : F) * P x x')
    {x x' : V} (hx : x ∈ L) (hx' : x' ∈ L) (hP : P x x' ≠ 0) :
    ∃ B : LinearMap.BilinForm F V, (∀ z, B z z = 0) ∧ ∀ z ∈ L, ∀ w ∈ L, P z w = B z w :=
  GlobalTheory.T.alternating_form_lattice_integrality hV L hLadd hLsmul P halt hadd hsmul hx hx' hP

theorem fracIdeal_pairing (hV : Module.finrank F V = 2) (B : LinearMap.BilinForm F V)
    (hB : ∀ z, B z z = 0) (L : Set V) (hL0 : (0 : V) ∈ L)
    (hLadd : ∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) (hLsmul : ∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L)
    (J : FractionalIdeal (𝓞 F)⁰ F) (hJ : J ≠ 0) (hval : ∀ z ∈ L, ∀ w ∈ L, B z w ∈ J)
    (hspan : ∀ t ∈ J, t ∈ Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w})
    {v : V} (hv : v ≠ 0) :
    ∃ K : FractionalIdeal (𝓞 F)⁰ F, K ≠ 0 ∧ ∀ t, t ∈ K ↔ ∃ z ∈ L, t = B z v :=
  GlobalTheory.T.lattice_form_ideal_generates_dual_vector hV B hB L hL0 hLadd hLsmul J hJ hval hspan hv

theorem fracIdeal_line (hV : Module.finrank F V = 2) (B : LinearMap.BilinForm F V)
    (hB : ∀ z, B z z = 0) (L : Set V) (hL0 : (0 : V) ∈ L)
    (hLadd : ∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) (hLsmul : ∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L)
    (J : FractionalIdeal (𝓞 F)⁰ F) (hJ : J ≠ 0) (hval : ∀ z ∈ L, ∀ w ∈ L, B z w ∈ J)
    (hspan : ∀ t ∈ J, t ∈ Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w})
    {v : V} (hv : v ≠ 0) :
    ∃ I : FractionalIdeal (𝓞 F)⁰ F, I ≠ 0 ∧ ∀ a : F, a ∈ I ↔ a • v ∈ L :=
  GlobalTheory.T.lattice_form_ideal_dual_vector_integral hV B hB L hL0 hLadd hLsmul J hJ hval hspan hv

theorem exists_section (B : LinearMap.BilinForm F V) (L : Set V) (hL0 : (0 : V) ∈ L)
    (hLadd : ∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) (hLsmul : ∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L)
    {v : V} (K : FractionalIdeal (𝓞 F)⁰ F) (hK : K ≠ 0) (hKL : ∀ t, t ∈ K ↔ ∃ z ∈ L, t = B z v) :
    ∃ w : V, B w v = 1 ∧ ∀ t ∈ K, t • w ∈ L :=
  GlobalTheory.T.lattice_vector_pairing_one_ideal_multiple B L hL0 hLadd hLsmul K hK hKL

theorem decomp_of_section (hV : Module.finrank F V = 2) (B : LinearMap.BilinForm F V)
    (hB : ∀ z, B z z = 0) (L : Set V) (hL0 : (0 : V) ∈ L)
    (hLadd : ∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) (hLsmul : ∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L)
    (J : FractionalIdeal (𝓞 F)⁰ F) (hval : ∀ z ∈ L, ∀ w ∈ L, B z w ∈ J)
    (hspan : ∀ t ∈ J, t ∈ Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w})
    {v w : V} (hv : v ≠ 0) (I K : FractionalIdeal (𝓞 F)⁰ F) (hI : ∀ a : F, a ∈ I ↔ a • v ∈ L)
    (hK : ∀ t, t ∈ K ↔ ∃ z ∈ L, t = B z v) (hw : B w v = 1) (hwL : ∀ t ∈ K, t • w ∈ L) :
    (∀ x, x ∈ L ↔ ∃ a ∈ I, ∃ t ∈ K, x = a • v + t • w) ∧ I * K = J :=
  GlobalTheory.T.lattice_form_ideal_pair_of_vectors hV B hB L hL0 hLadd hLsmul J hval hspan hv I K hI hK hw hwL

theorem exists_mem_coprime (Y N : FractionalIdeal (𝓞 F)⁰ F) (hY : Y ≠ 0) (hN : N ≠ 0) (hN1 : N ≤ 1) :
    ∃ β ∈ Y, FractionalIdeal.spanSingleton (𝓞 F)⁰ β * Y⁻¹ + N = 1 :=
  GlobalTheory.T.fractional_ideal_coprime_element_exists Y N hY hN hN1

theorem exists_comb_eq (A B C : FractionalIdeal (𝓞 F)⁰ F) (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    ∃ α β : F, FractionalIdeal.spanSingleton (𝓞 F)⁰ α * A + FractionalIdeal.spanSingleton (𝓞 F)⁰ β * B = C := by
  have hCA : C * A⁻¹ ≠ 0 := mul_ne_zero hC (inv_ne_zero hA)
  obtain ⟨α, hα, hα0⟩ : ∃ α ∈ C * A⁻¹, α ≠ 0 := by
    by_contra h
    push_neg at h
    apply hCA
    ext t
    rw [FractionalIdeal.mem_zero_iff]
    exact ⟨h t, fun ht => ht ▸ Submodule.zero_mem ((C * A⁻¹ : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F)⟩
  set N := FractionalIdeal.spanSingleton (𝓞 F)⁰ α * A * C⁻¹ with hNdef
  have hsα : FractionalIdeal.spanSingleton (𝓞 F)⁰ α ≤ C * A⁻¹ :=
    FractionalIdeal.spanSingleton_le_iff_mem.2 hα
  have hN1 : N ≤ 1 := by
    calc N ≤ C * A⁻¹ * A * C⁻¹ := by rw [hNdef]; exact mul_le_mul_left (mul_le_mul_left hsα A) C⁻¹
      _ = 1 := by
        rw [_root_.mul_assoc C, inv_mul_cancel₀ hA, _root_.mul_one, mul_inv_cancel₀ hC]
  have hN0 : N ≠ 0 :=
    mul_ne_zero (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 hα0) hA) (inv_ne_zero hC)
  obtain ⟨β, -, hβN⟩ := exists_mem_coprime (C * B⁻¹) N (mul_ne_zero hC (inv_ne_zero hB)) hN0 hN1
  refine ⟨α, β, ?_⟩
  have e1 : N * C = FractionalIdeal.spanSingleton (𝓞 F)⁰ α * A := by
    rw [hNdef, _root_.mul_assoc _ C⁻¹, inv_mul_cancel₀ hC, _root_.mul_one]
  have e2 : FractionalIdeal.spanSingleton (𝓞 F)⁰ β * (C * B⁻¹)⁻¹ * C =
      FractionalIdeal.spanSingleton (𝓞 F)⁰ β * B := by
    rw [mul_inv, inv_inv, _root_.mul_assoc, _root_.mul_assoc, mul_comm B C, ← _root_.mul_assoc C⁻¹,
      inv_mul_cancel₀ hC, _root_.one_mul]
  calc FractionalIdeal.spanSingleton (𝓞 F)⁰ α * A + FractionalIdeal.spanSingleton (𝓞 F)⁰ β * B
      = (FractionalIdeal.spanSingleton (𝓞 F)⁰ β * (C * B⁻¹)⁻¹ + N) * C := by
        rw [add_mul, e1, e2, add_comm]
    _ = C := by rw [hβN, _root_.one_mul]

theorem pairing_change (B : LinearMap.BilinForm F V) (hB : ∀ z, B z z = 0) (L : Set V) {v w : V}
    (hw : B w v = 1) (I K : FractionalIdeal (𝓞 F)⁰ F)
    (hL : ∀ x, x ∈ L ↔ ∃ a ∈ I, ∃ t ∈ K, x = a • v + t • w) (α β t : F) :
    (∃ z ∈ L, t = B z (α • v + β • w)) ↔
      t ∈ FractionalIdeal.spanSingleton (𝓞 F)⁰ α * K + FractionalIdeal.spanSingleton (𝓞 F)⁰ β * I := by
  have hvw : B v w = -1 := by
    have := hB (v + w)
    simp only [map_add, LinearMap.add_apply, hB, hw] at this
    linear_combination this
  have hval : ∀ a s : F, B (a • v + s • w) (α • v + β • w) = α * s + β * (-a) := by
    intro a s
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hB, hw, hvw]
    ring
  show _ ↔ t ∈ ((FractionalIdeal.spanSingleton (𝓞 F)⁰ α * K + FractionalIdeal.spanSingleton (𝓞 F)⁰ β * I :
    FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F)
  rw [FractionalIdeal.coe_add, Submodule.add_eq_sup, Submodule.mem_sup]
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨a, ha, s, hs, rfl⟩ := (hL z).1 hz
    rw [hval]
    exact ⟨α * s, FractionalIdeal.mem_singleton_mul.2 ⟨s, hs, rfl⟩, β * (-a),
      FractionalIdeal.mem_singleton_mul.2 ⟨-a, Submodule.neg_mem (I : Submodule (𝓞 F) F) ha, rfl⟩, rfl⟩
  · rintro ⟨p, hp, q, hq, rfl⟩
    obtain ⟨s, hs, rfl⟩ := FractionalIdeal.mem_singleton_mul.1 hp
    obtain ⟨b, hb, rfl⟩ := FractionalIdeal.mem_singleton_mul.1 hq
    exact ⟨(-b) • v + s • w, (hL _).2 ⟨-b, Submodule.neg_mem (I : Submodule (𝓞 F) F) hb, s, hs, rfl⟩,
      by rw [hval, neg_neg]⟩

end GlobalTheory.AltLattice

namespace GlobalTheory.AltLattice

variable {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V]

theorem exists_sympl_basis (hV : Module.finrank F V = 2) (L : Set V) (hL0 : (0 : V) ∈ L)
    (hLadd : ∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) (hLsmul : ∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L)
    (M 𝔟 : FractionalIdeal (𝓞 F)⁰ F) (hM : M ≠ 0) (h𝔟 : 𝔟 ≠ 0) (P : V → V → F)
    (halt : ∀ x ∈ L, ∀ x' ∈ L, P x x' = -P x' x)
    (hadd : ∀ x₁ ∈ L, ∀ x₂ ∈ L, ∀ x' ∈ L, P (x₁ + x₂) x' = P x₁ x' + P x₂ x')
    (hsmul : ∀ (a : 𝓞 F), ∀ x ∈ L, ∀ x' ∈ L, P ((a : F) • x) x' = (a : F) * P x x')
    (hval : ∀ x ∈ L, ∀ x' ∈ L, P x x' ∈ M * 𝔟)
    (hspan : ∀ t ∈ M * 𝔟, t ∈ Submodule.span (𝓞 F) {t | ∃ x ∈ L, ∃ x' ∈ L, t = P x x'}) :
    ∃ ω₁ ω₂ : V, (∀ x, x ∈ L ↔ ∃ m ∈ M, ∃ β ∈ 𝔟, x = m • ω₁ + β • ω₂) ∧
      ∀ m ∈ M, ∀ β ∈ 𝔟, ∀ m' ∈ M, ∀ β' ∈ 𝔟,
        P (m • ω₁ + β • ω₂) (m' • ω₁ + β' • ω₂) = β * m' - m * β' := by
  have hJ : M * 𝔟 ≠ 0 := mul_ne_zero hM h𝔟
  obtain ⟨x, hx, x', hx', hP⟩ : ∃ x ∈ L, ∃ x' ∈ L, P x x' ≠ 0 := by
    by_contra h
    push_neg at h
    apply hJ
    ext t
    rw [FractionalIdeal.mem_zero_iff]
    refine ⟨fun ht => ?_, fun ht => ?_⟩
    swap
    · subst ht; exact Submodule.zero_mem ((M * 𝔟 : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F)
    have h1 := hspan t ht
    have hs : {t | ∃ x ∈ L, ∃ x' ∈ L, t = P x x'} ⊆ ({0} : Set F) := by
      rintro _ ⟨z, hz, w, hw, rfl⟩; exact h z hz w hw
    have h2 := Submodule.span_mono (R := 𝓞 F) hs h1
    rw [Submodule.span_singleton_eq_bot.2 rfl, Submodule.mem_bot] at h2
    exact h2
  obtain ⟨B, hB, hPB⟩ := exists_bilin_ext hV L hLadd hLsmul P halt hadd hsmul hx hx' hP
  have hvalB : ∀ z ∈ L, ∀ w ∈ L, B z w ∈ M * 𝔟 := fun z hz w hw => hPB z hz w hw ▸ hval z hz w hw
  have hsetB : {t | ∃ x ∈ L, ∃ x' ∈ L, t = P x x'} = {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w} := by
    ext t; constructor
    · rintro ⟨z, hz, w, hw, rfl⟩; exact ⟨z, hz, w, hw, hPB z hz w hw⟩
    · rintro ⟨z, hz, w, hw, rfl⟩; exact ⟨z, hz, w, hw, (hPB z hz w hw).symm⟩
  have hspanB : ∀ t ∈ M * 𝔟, t ∈ Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w} :=
    fun t ht => hsetB ▸ hspan t ht
  have hx0 : x ≠ 0 := by
    rintro rfl; apply hP; rw [hPB 0 hx x' hx']; simp
  have hvw : ∀ v w : V, B w v = 1 → B v w = -1 := fun v w h => by
    have := hB (v + w)
    simp only [map_add, LinearMap.add_apply, hB, h] at this
    linear_combination this

  obtain ⟨K₀, hK₀, hK₀L⟩ := fracIdeal_pairing hV B hB L hL0 hLadd hLsmul _ hJ hvalB hspanB hx0
  obtain ⟨I₀, hI₀, hI₀L⟩ := fracIdeal_line hV B hB L hL0 hLadd hLsmul _ hJ hvalB hspanB hx0
  obtain ⟨w₀, hw₀, hw₀L⟩ := exists_section B L hL0 hLadd hLsmul K₀ hK₀ hK₀L
  obtain ⟨hL₀, -⟩ := decomp_of_section hV B hB L hL0 hLadd hLsmul _ hvalB hspanB hx0 I₀ K₀ hI₀L hK₀L hw₀ hw₀L

  obtain ⟨α, β, hαβ⟩ := exists_comb_eq K₀ I₀ 𝔟 hK₀ hI₀ h𝔟
  set v := α • x + β • w₀ with hvdef
  have hv : v ≠ 0 := by
    intro h0
    have h1 : B w₀ v = α := by
      simp [hvdef, hB, hw₀]
    have h2 : B x v = -β := by
      simp [hvdef, hB, hvw x w₀ hw₀]
    rw [h0] at h1 h2
    simp only [map_zero] at h1 h2
    have hα : α = 0 := h1.symm
    have hβ : β = 0 := by linear_combination h2
    apply h𝔟
    rw [← hαβ, hα, hβ]; simp
  obtain ⟨K, hK, hKL⟩ := fracIdeal_pairing hV B hB L hL0 hLadd hLsmul _ hJ hvalB hspanB hv
  obtain ⟨I, hI, hIL⟩ := fracIdeal_line hV B hB L hL0 hLadd hLsmul _ hJ hvalB hspanB hv
  obtain ⟨w, hw, hwL⟩ := exists_section B L hL0 hLadd hLsmul K hK hKL
  obtain ⟨hL, hIK⟩ := decomp_of_section hV B hB L hL0 hLadd hLsmul _ hvalB hspanB hv I K hIL hKL hw hwL
  have hK𝔟 : K = 𝔟 := by
    ext t
    rw [hKL t, pairing_change B hB L hw₀ I₀ K₀ hL₀ α β t, hαβ]
  have hIM : I = M := by
    rw [hK𝔟] at hIK
    exact mul_right_cancel₀ h𝔟 hIK
  subst hK𝔟 hIM
  refine ⟨v, w, hL, ?_⟩
  intro m hm b hb m' hm' b' hb'
  rw [hPB _ ((hL _).2 ⟨m, hm, b, hb, rfl⟩) _ ((hL _).2 ⟨m', hm', b', hb', rfl⟩)]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hB, hw, hvw v w hw]
  ring

end GlobalTheory.AltLattice

namespace GlobalTheory.AltLattice

theorem dualLat_mul_inv {F : Type} [Field F] [NumberField F] (𝔞 𝔟 : FracId F) :
    dualLat (𝔞 * 𝔟⁻¹) = dualLat 𝔞 * (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := by
  simp only [dualLat, Units.val_mul, Units.val_inv_eq_inv_val]
  rw [FractionalIdeal.dual_eq_mul_inv ℤ ℚ, FractionalIdeal.dual_eq_mul_inv ℤ ℚ (𝔞 : FractionalIdeal (𝓞 F)⁰ F),
    mul_inv, inv_inv]
  exact (_root_.mul_assoc _ _ _).symm

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
    ∀ (𝔞 𝔟 : FracId (FR E)) (P : E → E → FR E),
    (∀ x ∈ lattice c y, ∀ x' ∈ lattice c y, P x x' = -P x' x) →
    (∀ x₁ ∈ lattice c y, ∀ x₂ ∈ lattice c y, ∀ x' ∈ lattice c y, P (x₁ + x₂) x' = P x₁ x' + P x₂ x') →
    (∀ (a : 𝓞 (FR E)), ∀ x ∈ lattice c y, ∀ x' ∈ lattice c y, P (((a : FR E) : E) * x) x' = (a : FR E) * P x x') →
    (∀ x ∈ lattice c y, ∀ x' ∈ lattice c y, P x x' ∈ dualLat (𝔞 * 𝔟⁻¹)) →
    (∀ t ∈ dualLat (𝔞 * 𝔟⁻¹), t ∈ Submodule.span (𝓞 (FR E)) {t | ∃ x ∈ lattice c y, ∃ x' ∈ lattice c y, t = P x x'}) →
    ∃ ω₁ ω₂ : E, (∀ x, x ∈ lattice c y ↔ ∃ m ∈ dualLat 𝔞, ∃ β ∈ 𝔟.elt, x = (m : E) * ω₁ + (β : E) * ω₂) ∧
      ∀ m ∈ dualLat 𝔞, ∀ β ∈ 𝔟.elt, ∀ m' ∈ dualLat 𝔞, ∀ β' ∈ 𝔟.elt,
        P ((m : E) * ω₁ + (β : E) * ω₂) ((m' : E) * ω₁ + (β' : E) * ω₂) = β * m' - m * β' := by
  intro E _ _ _ c y _ 𝔞 𝔟 P halt hadd hsmul hval hspan
  have hsm : ∀ (a : FR E) (x : E), a • x = (a : E) * x := fun _ _ => rfl
  have hV : Module.finrank (FR E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hM : dualLat 𝔞 ≠ 0 := FractionalIdeal.dual_ne_zero ℤ ℚ (Units.ne_zero 𝔞)
  rw [dualLat_mul_inv] at hval hspan
  obtain ⟨ω₁, ω₂, h1, h2⟩ := exists_sympl_basis (F := FR E) (V := E) hV (lattice c y)
    (latticeSub c y).zero_mem (fun x hx x' hx' => (latticeSub c y).add_mem hx hx')
    (fun a x hx => by rw [hsm]; exact mul_mem_lattice (algebraMap_mem_orderC c a) hx)
    (dualLat 𝔞) 𝔟 hM (Units.ne_zero 𝔟) P halt hadd
    (fun a x hx x' hx' => by rw [hsm]; exact hsmul a x hx x' hx') hval hspan
  refine ⟨ω₁, ω₂, fun x => ?_, fun m hm β hβ m' hm' β' hβ' => ?_⟩
  · have h := h1 x
    simp only [hsm] at h
    exact h
  · have h := h2 m hm β hβ m' hm' β' hβ'
    simp only [hsm] at h
    exact h

end GlobalTheory.AltLattice
