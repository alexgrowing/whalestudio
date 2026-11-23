import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorPreservesWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointValueEqQuotientSectionByPowerAtFieldStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatLoc

variable {F : Type} [Field F]

theorem der_bracket (d : Derivation ℤ F F) (x y β : F) (M : ℕ) :
    x * β ^ M * d (y * β ^ M) - y * β ^ M * d (x * β ^ M) = β ^ (2 * M) * (x * d y - y * d x) := by
  simp only [Derivation.leibniz, smul_eq_mul]
  ring

theorem der_mul_pow (d : Derivation ℤ F F) (x β : F) (hβ : β ≠ 0) (m : ℕ) :
    d (x * β ^ (m + 1)) = β ^ (m + 1) * (d x + ((m + 1 : ℕ) : F) * x * (d β / β)) := by
  simp only [Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel]
  field_simp
  ring

theorem symb_eq {n : ℕ} (δ : Fin n → Derivation ℤ F F) (δ₀ : Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F)
    (x y β : F) (hβ : β ≠ 0) (k m : ℕ) :
    ((k * (m + 1) : ℕ) : F) * (x * β ^ (m + 1)) * (x * β ^ (m + 1) * δ₀ (y * β ^ (m + 1)) - y * β ^ (m + 1) * δ₀ (x * β ^ (m + 1))) -
      ∑ a, ∑ e, Λ a e * δ a (x * β ^ (m + 1)) *
        (x * β ^ (m + 1) * δ e (y * β ^ (m + 1)) - y * β ^ (m + 1) * δ e (x * β ^ (m + 1))) =
    β ^ (3 * (m + 1)) * (((k * (m + 1) : ℕ) : F) * x * (x * δ₀ y - y * δ₀ x) -
      ∑ a, ∑ e, Λ a e * (δ a x + ((m + 1 : ℕ) : F) * x * (δ a β / β)) * (x * δ e y - y * δ e x)) := by
  rw [mul_sub (β ^ (3 * (m + 1))), Finset.mul_sum]
  simp only [Finset.mul_sum]
  congr 1
  · rw [der_bracket]; ring
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    rw [der_bracket, der_mul_pow _ _ _ hβ]; ring

theorem symb_one {n : ℕ} (δ : Fin n → Derivation ℤ F F) (δ₀ : Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F)
    (y β : F) (k m : ℕ) :
    ((k * (m + 1) : ℕ) : F) * 1 * (1 * δ₀ y - y * δ₀ 1) -
      ∑ a, ∑ e, Λ a e * (δ a 1 + ((m + 1 : ℕ) : F) * 1 * (δ a β / β)) * (1 * δ e y - y * δ e 1) =
    ((m + 1 : ℕ) : F) * ((k : F) * δ₀ y - ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e y) := by
  simp only [Derivation.map_one_eq_zero, mul_zero, sub_zero, zero_add, one_mul, mul_one]
  rw [mul_sub, Finset.mul_sum]
  simp only [Finset.mul_sum]
  congr 1
  · push_cast; ring
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    ring

def derivationBracketSum {n : ℕ} (δ : Fin n → Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F) (x y : F) : F :=
  ∑ a, ∑ e, Λ a e * δ a x * (x * δ e y - y * δ e x)

theorem symb_two {n : ℕ} (δ : Fin n → Derivation ℤ F F) (δ₀ : Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F)
    (x y β : F) (k m : ℕ) :
    ((k * (m + 1) : ℕ) : F) * x * (x * δ₀ y - y * δ₀ x) -
      ∑ a, ∑ e, Λ a e * (δ a x + ((m + 1 : ℕ) : F) * x * (δ a β / β)) * (x * δ e y - y * δ e x) =
    ((m + 1 : ℕ) : F) * x * (x * ((k : F) * δ₀ y - ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e y) -
      y * ((k : F) * δ₀ x - ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e x)) - derivationBracketSum δ Λ x y := by
  have hs : ∑ a, ∑ e, Λ a e * (δ a x + ((m + 1 : ℕ) : F) * x * (δ a β / β)) * (x * δ e y - y * δ e x) =
      derivationBracketSum δ Λ x y + ((m + 1 : ℕ) : F) * x * (x * ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e y -
        y * ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e x) := by
    unfold derivationBracketSum
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    ring
  rw [hs]; push_cast; ring

theorem tsum_add_one {n : ℕ} (δ : Fin n → Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F) (x y : F) :
    derivationBracketSum δ Λ (x + 1) y - derivationBracketSum δ Λ x y = ∑ a, ∑ e, Λ a e * δ a x * δ e y := by
  unfold derivationBracketSum
  simp only [map_add, Derivation.map_one_eq_zero, add_zero, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
  ring

end GlobalTheory.HeatLoc

namespace GlobalTheory.HeatLoc

theorem valR_ne_zero_sec {X : Scheme.{0}} (L : LB X) {F : Type} [Field F] (ξ : Sp F ⟶ X) (j₀ : L.ι)
    (h : ⊤ ≤ ξ ⁻¹ᵁ L.U j₀) (k : ℕ) (s : SecM (𝟙 X) L k) (hs : ⊤ ≤ ξ ⁻¹ᵁ nonzeroLocus s) :
    valR ξ _ (s.f fun _ => j₀) ≠ 0 := by
  have hk : ⊤ ≤ ξ ⁻¹ᵁ (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) fun _ => (k : ℤ)).U (fun _ => j₀) :=
    fun p hp => Set.mem_iInter.2 fun _ => h hp
  have h₁ := (GlobalTheory.AmpleSpan.isUnit_gs_iff ξ (IsLocalRing.closedPoint F) _ (hk trivial) _).1
    ((GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs s ξ _ (hk trivial)).1 (hs trivial))
  exact ((GlobalTheory.Points.le_preimage_basicOpen_iff ξ hk _).1
    (Scheme.preimage_eq_top_of_closedPoint_mem (R := CommRingCat.of F) ξ h₁).ge).ne_zero

theorem symb_regular : ∀ (K : Type) [Field K] [CharZero K] (P₀ : Out.PolAV (Sp K)) (n : ℕ) (v : Module.Basis (Fin n) K (TanM (𝟙 (Sp K)) P₀.A)) (dd : Fin n → Fld P₀.A.left), (∀ a, IsInv P₀.A (v a) (dd a)) → ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ (δ : Fin n → Derivation ℤ F F), (∀ a O f, ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O (dd a O f) = δ a (valR ξ O f)) → ∀ (j₀ : P₀.L.ι), ⊤ ≤ ξ ⁻¹ᵁ P₀.L.U j₀ → ∀ (δ₀ : Derivation ℤ F F) (Λ : Matrix (Fin n) (Fin n) F), (∀ (k : ℕ), 1 ≤ k → ∀ σ τ : SecM (𝟙 P₀.A.left) P₀.L k, ∃ ρ : SecM (𝟙 P₀.A.left) P₀.L (3 * k), ∀ b c : F, b = valR ξ _ (σ.f fun _ => j₀) → c = valR ξ _ (τ.f fun _ => j₀) → (k : F) * b * (b * δ₀ c - c * δ₀ b) - ∑ a, ∑ e, Λ a e * δ a b * (b * δ e c - c * δ e b) = valR ξ _ (ρ.f fun _ => j₀)) → ∀ (k : ℕ), 1 ≤ k → ∀ s : SecM (𝟙 P₀.A.left) P₀.L k, ⊤ ≤ ξ ⁻¹ᵁ (Out.nonzeroLocus s) → (∀ f f' : Γ(P₀.A.left, (Out.nonzeroLocus s)), ∃ h : Γ(P₀.A.left, (Out.nonzeroLocus s)), valR ξ _ h = ∑ a, ∑ e, Λ a e * δ a (valR ξ _ f) * δ e (valR ξ _ f')) ∧ (∀ f : Γ(P₀.A.left, (Out.nonzeroLocus s)), ∃ f' : Γ(P₀.A.left, (Out.nonzeroLocus s)), valR ξ _ f' = (k : F) * δ₀ (valR ξ _ f) - ∑ a, ∑ e, Λ a e * (δ a (valR ξ _ (s.f fun _ => j₀)) / valR ξ _ (s.f fun _ => j₀)) * δ e (valR ξ _ f)) := by
  intro K _ _ P₀ n v dd hdd F _ ψ ξ hξ hinj δ hδ j₀ hj₀ δ₀ Λ hyp k hk s hs
  haveI := P₀.isAb.proper
  haveI : CompactSpace P₀.A.left := QuasiCompact.compactSpace_of_compactSpace P₀.A.hom
  haveI : QuasiSeparatedSpace P₀.A.left := quasiSeparatedSpace_of_quasiSeparated P₀.A.hom
  obtain ⟨G₁, G₂⟩ := GlobalTheory.T.pointValue_eq_quotient_section_by_power_at_field P₀.A.left P₀.L P₀.isLB F ξ j₀ hj₀ k s hs
  have hβ := valR_ne_zero_sec P₀.L ξ j₀ hj₀ k s hs
  set β := valR ξ _ (s.f fun _ => j₀) with hβdef
  have v1 : valR ξ (nonzeroLocus s) 1 = 1 := by rw [WtAlg.valR_eq' ξ _ hs, map_one, map_one]
  have hM : ∀ m : ℕ, ((m + 1 : ℕ) : F) ≠ 0 := fun m h => by
    have : ψ ((m + 1 : ℕ) : K) = 0 := by rw [map_natCast]; exact h
    exact (Nat.cast_ne_zero.2 (Nat.succ_ne_zero m)) ((map_eq_zero ψ).1 this)

  have partD : ∀ f : Γ(P₀.A.left, nonzeroLocus s), ∃ f' : Γ(P₀.A.left, nonzeroLocus s),
      valR ξ _ f' = (k : F) * δ₀ (valR ξ _ f) - ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e (valR ξ _ f) := by
    intro f
    obtain ⟨m₁, h₁⟩ := G₁ 1
    obtain ⟨m₂, h₂⟩ := G₁ f
    set m := max m₁ m₂
    obtain ⟨σ, hσ⟩ := h₁ (m + 1) (k * (m + 1)) (by omega) rfl
    obtain ⟨τ, hτ⟩ := h₂ (m + 1) (k * (m + 1)) (by omega) rfl
    obtain ⟨ρ, hρ⟩ := hyp (k * (m + 1)) (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))) σ τ
    obtain ⟨g, hg⟩ := G₂ (3 * (m + 1)) (3 * (k * (m + 1))) (by ring) ρ
    have e := hρ _ _ rfl rfl
    rw [hσ, hτ, hg, v1, symb_eq δ δ₀ Λ _ _ β hβ k m, symb_one] at e
    have e' : valR ξ _ g = ((m + 1 : ℕ) : F) * ((k : F) * δ₀ (valR ξ _ f) -
        ∑ a, ∑ e, Λ a e * (δ a β / β) * δ e (valR ξ _ f)) := by
      have h3 : β ^ (3 * (m + 1)) ≠ 0 := pow_ne_zero _ hβ
      rw [mul_comm (valR ξ _ g)] at e
      exact (mul_left_cancel₀ h3 e).symm
    refine ⟨constFn P₀.A.hom _ (((m + 1 : ℕ) : K)⁻¹) * g, ?_⟩
    rw [WtAlg.valR_mul'' ξ _ hs, GlobalTheory.LogKSBal.valR_constFn P₀.A.hom ξ hs hξ, e', map_inv₀, map_natCast,
      ← _root_.mul_assoc, inv_mul_cancel₀ (hM m), _root_.one_mul]

  have partT : ∀ f f' : Γ(P₀.A.left, nonzeroLocus s), ∃ h : Γ(P₀.A.left, nonzeroLocus s),
      valR ξ _ h = derivationBracketSum δ Λ (valR ξ _ f) (valR ξ _ f') := by
    intro f f'
    obtain ⟨m₁, h₁⟩ := G₁ f
    obtain ⟨m₂, h₂⟩ := G₁ f'
    obtain ⟨d, hd⟩ := partD f
    obtain ⟨d', hd'⟩ := partD f'
    set m := max m₁ m₂
    obtain ⟨σ, hσ⟩ := h₁ (m + 1) (k * (m + 1)) (by omega) rfl
    obtain ⟨τ, hτ⟩ := h₂ (m + 1) (k * (m + 1)) (by omega) rfl
    obtain ⟨ρ, hρ⟩ := hyp (k * (m + 1)) (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))) σ τ
    obtain ⟨g, hg⟩ := G₂ (3 * (m + 1)) (3 * (k * (m + 1))) (by ring) ρ
    have e := hρ _ _ rfl rfl
    rw [hσ, hτ, hg, symb_eq δ δ₀ Λ _ _ β hβ k m, symb_two, ← hd, ← hd'] at e
    have e' : valR ξ _ g = ((m + 1 : ℕ) : F) * valR ξ _ f * (valR ξ _ f * valR ξ _ d' - valR ξ _ f' * valR ξ _ d) -
        derivationBracketSum δ Λ (valR ξ _ f) (valR ξ _ f') := by
      have h3 : β ^ (3 * (m + 1)) ≠ 0 := pow_ne_zero _ hβ
      rw [mul_comm (valR ξ _ g)] at e
      exact (mul_left_cancel₀ h3 e).symm
    refine ⟨((m + 1 : ℕ) : Γ(P₀.A.left, nonzeroLocus s)) * f * (f * d' - f' * d) - g, ?_⟩
    rw [WtAlg.valR_sub' ξ _ hs, WtAlg.valR_mul'' ξ _ hs, WtAlg.valR_mul'' ξ _ hs, WtAlg.valR_sub' ξ _ hs,
      WtAlg.valR_mul'' ξ _ hs, WtAlg.valR_mul'' ξ _ hs, WtAlg.valR_natCast' ξ _ hs, e']
    ring
  refine ⟨fun f f' => ?_, partD⟩
  obtain ⟨h₁, e₁⟩ := partT (f + 1) f'
  obtain ⟨h₂, e₂⟩ := partT f f'
  refine ⟨h₁ - h₂, ?_⟩
  rw [WtAlg.valR_sub' ξ _ hs, e₁, e₂, WtAlg.valR_add' ξ _ hs, v1, tsum_add_one]

end GlobalTheory.HeatLoc
