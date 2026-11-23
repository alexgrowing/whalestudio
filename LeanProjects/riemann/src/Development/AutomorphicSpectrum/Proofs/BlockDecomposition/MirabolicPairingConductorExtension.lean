import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCoefficientContinuous
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedBoxIntegralIdentity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicTwistedKernelNonvanishingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorVanishingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingDepthVanishingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorFixedSmallShearStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearPreservesBoxMembershipStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearOrbitFiniteStatement

noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair.Nondeg

theorem box_subset_of_valuation_le {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {m : ℕ} {s t : kˣ} (h : valuation k (s : k) ≤ valuation k (t : k)) :
    (box m s : Set (Fin m → k)) ⊆ box m t := fun x hx j =>
  le_trans (show valuation k (x j) ≤ valuation k (s : k) from hx j) h

theorem exists_unit_bound {k : Type} [Field k] [ValuativeRel k] {W : Type} {S : Set W} (hS : S.Finite)
    (τ : W → kˣ) (t : kˣ) :
    ∃ u : kˣ, valuation k (t : k) ≤ valuation k (u : k) ∧
      ∀ w ∈ S, valuation k (τ w : k) ≤ valuation k (u : k) := by
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨t, le_rfl, by simp⟩
  | @insert a s _ _ ih =>
    obtain ⟨u, h1, h2⟩ := ih
    rcases le_total (valuation k (u : k)) (valuation k (τ a : k)) with h | h
    · refine ⟨τ a, h1.trans h, fun w hw => ?_⟩
      rcases Set.mem_insert_iff.1 hw with rfl | hw
      · exact le_rfl
      · exact (h2 w hw).trans h
    · refine ⟨u, h1, fun w hw => ?_⟩
      rcases Set.mem_insert_iff.1 hw with rfl | hw
      · exact h
      · exact h2 w hw

theorem exists_large_unit {k : Type} [Field k] [ValuativeRel k] (c r t₀ : kˣ) :
    ∃ t : kˣ, valuation k (t₀ : k) ≤ valuation k (t : k) ∧
      valuation k ((c * t⁻¹ : kˣ) : k) ≤ valuation k (r : k) := by
  rcases le_total (valuation k (t₀ : k)) (valuation k ((c * r⁻¹ : kˣ) : k)) with h | h
  · refine ⟨c * r⁻¹, h, ?_⟩
    have e : c * (c * r⁻¹)⁻¹ = r := by simp
    rw [e]
  · refine ⟨t₀, le_rfl, ?_⟩
    have e : ((c * t₀⁻¹ : kˣ) : k) = ((c * r⁻¹ : kˣ) : k) * ((t₀⁻¹ : kˣ) : k) * (r : k) := by
      push_cast
      field_simp
    have e1 : valuation k (t₀ : k) * valuation k ((t₀⁻¹ : kˣ) : k) = 1 := by
      rw [← map_mul]
      simp
    rw [e, map_mul, map_mul]
    calc valuation k ((c * r⁻¹ : kˣ) : k) * valuation k ((t₀⁻¹ : kˣ) : k) * valuation k (r : k)
        ≤ valuation k (t₀ : k) * valuation k ((t₀⁻¹ : kˣ) : k) * valuation k (r : k) := by gcongr
      _ = valuation k (r : k) := by rw [e1, one_mul]

theorem continuous_wt_mul_coef {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψ : Continuous ψ) {n : ℕ} {V V' : Type}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V)
    (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (hT : IsSmooth T) (v : V) (v' : V') :
    Continuous fun x => wt ψ n x * coef T B v v' x := by
  refine Continuous.mul ?_ (continuous_coef T B hT v v')
  have h : Continuous fun x : Fin (n + 1) → k => ψ (-x (Fin.last n)) :=
    hψ.comp (continuous_apply _).neg
  exact continuous_subtype_val.comp h

end GlobalTheory.CompanionTheory.MirPair.Nondeg

namespace GlobalTheory.CompanionTheory.MirPair

open GlobalTheory.CompanionTheory.MirPair.Nondeg in

theorem exists_evVal_ne_zero : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) → ∀ v : V, v ∉ twKer T (MirUin k (n + 1)) (mirChar k ψ n) → ∃ (v' : V') (A : ℂ), EvVal ν ψ T B v v' A ∧ A ≠ 0 := by
  intro k _ _ _ _ _ _ ν _ ψ c n V V' _ _ _ _ T T' B s hψ hc hT hT' hinv hnd v hv
  obtain ⟨r₁, hr₁, hfix⟩ := GlobalTheory.T.smooth_vector_fixed_small_shear T hT v
  obtain ⟨r₂, hr₂, hlat⟩ := GlobalTheory.T.shear_preserves_box_membership (k := k) (n := n) 1
  obtain ⟨r, hr, hrr₁, hrr₂⟩ : ∃ r : kˣ, valuation k (r : k) < 1 ∧
      valuation k (r : k) ≤ valuation k (r₁ : k) ∧ valuation k (r : k) ≤ valuation k (r₂ : k) := by
    rcases le_total (valuation k (r₁ : k)) (valuation k (r₂ : k)) with h | h
    · exact ⟨r₁, hr₁, le_rfl, h⟩
    · exact ⟨r₂, hr₂, h, le_rfl⟩
  obtain ⟨t₀, ht₀⟩ := GlobalTheory.T.mirabolic_twisted_kernel_nonvanishing ν ψ T B hψ hT hnd v hv
  obtain ⟨t, htt₀, htc⟩ := exists_large_unit c r t₀
  obtain ⟨v', hv'⟩ := ht₀ t htt₀
  by_contra hno
  push_neg at hno
  have hev : ∀ w : V', ∃ τ : kˣ, ∀ u : kˣ, valuation k (τ : k) ≤ valuation k (u : k) →
      JJ ν ψ T B (box (n + 1) u : Set (Fin (n + 1) → k)) v w = 0 := by
    intro w
    obtain ⟨A, hA⟩ := GlobalTheory.T.mirabolic_pairing_exists_eventual_value ν ψ c T T' B s hψ hc hT hT' hinv v w
    have h0 : A = 0 := hno w A hA
    obtain ⟨τ, hτ⟩ := hA
    exact ⟨τ, fun u hu => (hτ u hu).trans h0⟩
  choose τ hτ using hev
  obtain ⟨u, htu, hu⟩ := exists_unit_bound (GlobalTheory.T.shear_orbit_box_finite_of_isSmooth T' hT' v' r hr) τ t
  have hz : ∀ b ∈ box (n + 1) (c * t⁻¹), ∫ x in (box (n + 1) u : Set (Fin (n + 1) → k)),
      ((ψ (-(b ⬝ᵥ x)) : Circle) : ℂ) * (wt ψ n x * coef T B v v' x) ∂(piHaar ν (n + 1)) = 0 := by
    intro b hb
    have hbr : b ∈ (box (n + 1) r : Set (Fin (n + 1) → k)) := box_subset_of_valuation_le htc hb
    have hlast : valuation k (b (Fin.last n)) < 1 :=
      lt_of_le_of_lt (show valuation k (b (Fin.last n)) ≤ valuation k (r : k) from hbr _) hr
    rw [GlobalTheory.T.mirabolic_pairing_depth_vanishing ν ψ T T' B s hψ hT hinv b _ v v' hlast
      (hfix b (box_subset_of_valuation_le hrr₁ hbr)) ?_]
    · exact hτ _ u (hu _ ⟨b, hbr, rfl⟩)
    · intro x
      have h := hlat b (box_subset_of_valuation_le hrr₂ hbr) u x
      simpa using h
  have hm : MeasurableSet (box (n + 1) u : Set (Fin (n + 1) → k)) := by
    rw [coe_box]
    exact MeasurableSet.univ_pi fun _ => (isOpen_cball u).measurableSet
  have hfin := setIntegral_inter_box_of_twists ν ψ c hψ hc (n + 1) t
    (box (n + 1) u : Set (Fin (n + 1) → k)) (fun x => wt ψ n x * coef T B v v' x) 0
    (isCompact_box _ _) hm (continuous_wt_mul_coef ψ hψ T B hT v v') hz
  rw [Set.inter_eq_right.2 (box_subset_of_valuation_le htu)] at hfin
  exact hv' hfin

end GlobalTheory.CompanionTheory.MirPair

end
